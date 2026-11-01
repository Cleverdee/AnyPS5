#ifdef _WIN32
#include <windows.h>
#include <tlhelp32.h>
#include "prx/libc/include/CallTrace.hpp"
#include "prx/libc/include/FailureReport.hpp"
#include "prx/libc/include/GuestArena.hpp"
#include "prx/libc/include/LogFile.hpp"
#include "prx/libc/include/Shutdown.hpp"
#include "prx/libc/include/CrashText.hpp"
#include <algorithm>
#include <atomic>
#include <chrono>
#include <csignal>
#include <cstdint>
#include <cstdio>
#include <cstdarg>
#include <cstdlib>
#include <cstring>
#include <iterator>
#include <utility>
#include <mutex>
#include <string>
#include "Sse4aEmulation.hpp"

namespace {

// The reporter runs on a faulting thread that may itself hold the CRT stream lock (a fault inside
// printf), so it writes straight to the stderr handle.
void Report(const char* format, ...) {
    char buffer[1024];
    va_list args;
    va_start(args, format);
    int length = std::vsnprintf(buffer, sizeof(buffer), format, args);
    va_end(args);
    if (length <= 0) return;
    if (length > static_cast<int>(sizeof(buffer)) - 1) length = sizeof(buffer) - 1;
    log_file::CrashWrite(log_file::StandardError, buffer, static_cast<std::size_t>(length));
}

void ReportAllThreads();
void ReportStackCandidates(std::uint64_t rsp, int limit, std::uint64_t span);
void ReportCallTrace();

void DescribeAddress(std::uint64_t address, char* buffer, std::size_t size) {
    HMODULE module = nullptr;
    char path[MAX_PATH] = "?";
    if (GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT, reinterpret_cast<LPCSTR>(address), &module) && module) {
        GetModuleFileNameA(module, path, sizeof(path));
        const char* name = path;
        for (const char* cursor = path; *cursor; ++cursor) {
            if (*cursor == '\\' || *cursor == '/') name = cursor + 1;
        }
        std::snprintf(buffer, size, "0x%016llx %s+0x%llx", static_cast<unsigned long long>(address), name, static_cast<unsigned long long>(address - reinterpret_cast<std::uint64_t>(module)));
        return;
    }
    std::snprintf(buffer, size, "0x%016llx", static_cast<unsigned long long>(address));
}

bool IsExecutable(std::uint64_t address) {
    MEMORY_BASIC_INFORMATION memory{};
    if (VirtualQuery(reinterpret_cast<const void*>(address), &memory, sizeof(memory)) != sizeof(memory)) return false;
    if (memory.State != MEM_COMMIT) return false;
    const DWORD protection = memory.Protect & 0xff;
    return protection == PAGE_EXECUTE || protection == PAGE_EXECUTE_READ || protection == PAGE_EXECUTE_READWRITE || protection == PAGE_EXECUTE_WRITECOPY;
}

bool IsReadable(std::uint64_t address) {
    MEMORY_BASIC_INFORMATION memory{};
    if (VirtualQuery(reinterpret_cast<const void*>(address), &memory, sizeof(memory)) != sizeof(memory)) return false;
    return memory.State == MEM_COMMIT && (memory.Protect & (PAGE_NOACCESS | PAGE_GUARD)) == 0;
}

bool IsFatal(DWORD code) {
    switch (code) {
    case EXCEPTION_ACCESS_VIOLATION:
    case EXCEPTION_ILLEGAL_INSTRUCTION:
    case EXCEPTION_PRIV_INSTRUCTION:
    case EXCEPTION_STACK_OVERFLOW:
    case EXCEPTION_INT_DIVIDE_BY_ZERO:
    case EXCEPTION_ARRAY_BOUNDS_EXCEEDED:
    case EXCEPTION_IN_PAGE_ERROR:
        return true;
    default:
        return false;
    }
}

// Debug aid: APS5_WATCH_WRITE=<guest ELF vaddr> reports every write to that 8-byte location by
// making its page read-only and single-stepping each trapped write.
std::uintptr_t g_watchAddress = 0;
std::uintptr_t g_watchPage = 0;
thread_local bool t_watchStepping = false;
thread_local bool t_watchHit = false;
thread_local unsigned long long t_watchBefore = 0;
thread_local std::uintptr_t t_watchFault = 0;
thread_local char t_watchWhere[MAX_PATH + 64];

void ProtectWatchPage(DWORD protection) {
    DWORD old;
    VirtualProtect(reinterpret_cast<void*>(g_watchPage), 0x1000, protection, &old);
}

bool HandleWatch(EXCEPTION_POINTERS* info) {
    if (g_watchPage == 0) return false;
    const auto* record = info->ExceptionRecord;
    auto* context = info->ContextRecord;
    if (record->ExceptionCode == EXCEPTION_SINGLE_STEP && t_watchStepping) {
        t_watchStepping = false;
        ProtectWatchPage(PAGE_READONLY);
        const auto current = *reinterpret_cast<const unsigned long long*>(g_watchAddress);
        if (t_watchHit || current != t_watchBefore) {
            if (!t_watchHit) Report("[watch] thread %lu changed the value with a write starting at 0x%llx from %s\n", GetCurrentThreadId(), static_cast<unsigned long long>(t_watchFault), t_watchWhere);
            Report("[watch]   new value 0x%016llx at %lld ms\n", current, static_cast<long long>(std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now().time_since_epoch()).count()));
            t_watchHit = false;
        }
        return true;
    }
    if (record->ExceptionCode != EXCEPTION_ACCESS_VIOLATION || record->NumberParameters < 2 || record->ExceptionInformation[0] != 1) return false;
    const auto address = static_cast<std::uintptr_t>(record->ExceptionInformation[1]);
    if (address < g_watchPage || address >= g_watchPage + 0x1000) return false;
    // Block writes (memset, memcpy) fault on their first byte, so compare the value after the step
    // as well as matching the fault address.
    t_watchBefore = *reinterpret_cast<const unsigned long long*>(g_watchAddress);
    t_watchFault = address;
    DescribeAddress(context->Rip, t_watchWhere, sizeof(t_watchWhere));
    if (address + 32 > g_watchAddress && address < g_watchAddress + 8) {
        char line[MAX_PATH + 64];
        DescribeAddress(context->Rip, line, sizeof(line));
        Report("[watch] thread %lu writes 0x%llx at %s rcx=%llx rdx=%llx r8=%llx\n", GetCurrentThreadId(), static_cast<unsigned long long>(address), line, context->Rcx, context->Rdx, context->R8);
        for (std::uint64_t slot = context->Rsp; slot < context->Rsp + 0x80 && IsReadable(slot); slot += 8) {
            const auto value = *reinterpret_cast<const std::uint64_t*>(slot);
            if (!IsExecutable(value)) continue;
            DescribeAddress(value, line, sizeof(line));
            Report("[watch]     [rsp+0x%llx] %s\n", static_cast<unsigned long long>(slot - context->Rsp), line);
        }
        std::uint64_t frame = context->Rbp;
        for (int depth = 0; depth < 6 && frame != 0 && (frame & 7) == 0 && IsReadable(frame) && IsReadable(frame + 8); ++depth) {
            const auto returnAddress = reinterpret_cast<const std::uint64_t*>(frame)[1];
            if (!IsExecutable(returnAddress)) break;
            DescribeAddress(returnAddress, line, sizeof(line));
            Report("[watch]     #%d %s\n", depth, line);
            const auto next = reinterpret_cast<const std::uint64_t*>(frame)[0];
            if (next <= frame) break;
            frame = next;
        }
        t_watchHit = true;
    }
    ProtectWatchPage(PAGE_READWRITE);
    context->EFlags |= 0x100;
    t_watchStepping = true;
    return true;
}

// APS5_JOB_IDLE_SLEEP=1: Demon's Souls' job workers call their job poll in a loop that never yields, so about a
// dozen guest threads hold a host core each while there is no work. The one call site of the poll is redirected
// to a thunk that runs the poll and, when it found no job, sleeps APS5_JOB_IDLE_SLEEP_US (default 50) before
// returning. The thunk keeps every register, the flags and the x87/SSE/AVX state: the caller may rely on more
// than the SysV ABI promises. Matched by code shape (US 01.004 and EU 01.007 builds differ in offsets and
// displacements); nothing is patched unless exactly one call site and its poll match. Idea and thunk from
// KytyPS5 #599 (chenxiao07, GPL-2.0).
DWORD g_jobIdleTimerSlot = TLS_OUT_OF_INDEXES;
LONGLONG g_jobIdleSleep100ns = 500;

void JobIdleWait() {
    auto timer = static_cast<HANDLE>(TlsGetValue(g_jobIdleTimerSlot));
    if (timer == nullptr) {
        constexpr DWORD highResolution = 0x2;
        timer = CreateWaitableTimerExW(nullptr, nullptr, highResolution, TIMER_ALL_ACCESS);
        if (timer == nullptr) timer = CreateWaitableTimerExW(nullptr, nullptr, 0, TIMER_ALL_ACCESS);
        TlsSetValue(g_jobIdleTimerSlot, timer);
    }
    LARGE_INTEGER due{};
    due.QuadPart = -g_jobIdleSleep100ns;
    if (timer != nullptr && SetWaitableTimer(timer, &due, 0, nullptr, nullptr, FALSE)) WaitForSingleObject(timer, INFINITE);
    else SwitchToThread();
}

bool MatchesShape(const std::uint8_t* code, const std::int16_t* shape, std::size_t length) {
    for (std::size_t i = 0; i < length; ++i) {
        if (shape[i] >= 0 && code[i] != static_cast<std::uint8_t>(shape[i])) return false;
    }
    return true;
}

// Demon's Souls (PPSA01341, PPSA01342): the switches of test/ds-main7 turn on by themselves, tuned on an
// 8 GB RX 6600 XT with 32 GB of RAM. A variable already set wins; APS5_NO_DS_PRESET=1 turns all of this off.
// The title comes from app0\sce_sys\param.json, in the working directory or beside the executable.
bool ParamNamesDemonsSouls(const std::string& path) {
    const HANDLE file = CreateFileA(path.c_str(), GENERIC_READ, FILE_SHARE_READ, nullptr, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, nullptr);
    if (file == INVALID_HANDLE_VALUE) return false;
    std::string text(1u << 20u, '\0');
    DWORD read = 0;
    const BOOL ok = ReadFile(file, text.data(), static_cast<DWORD>(text.size()), &read, nullptr);
    CloseHandle(file);
    if (!ok) return false;
    text.resize(read);
    return text.find("\"PPSA01341\"") != std::string::npos || text.find("\"PPSA01342\"") != std::string::npos;
}

void ApplyDemonsSoulsPreset() {
    if (std::getenv("APS5_NO_DS_PRESET") != nullptr) return;
    char module[MAX_PATH]{};
    std::string beside;
    if (const auto length = GetModuleFileNameA(nullptr, module, MAX_PATH); length != 0 && length < MAX_PATH) {
        beside = module;
        beside.resize(beside.find_last_of("/\\") + 1u);
    }
    if (!ParamNamesDemonsSouls("app0/sce_sys/param.json") && !ParamNamesDemonsSouls(beside + "app0/sce_sys/param.json")) return;
    static constexpr std::pair<const char*, const char*> preset[] = {
        {"APS5_UNKEYED_TABLE_KEYS", "256"},
        {"APS5_THREAD_PRIORITY", "high"},
        {"APS5_JOB_IDLE_SLEEP", "1"},
        {"APS5_FIBER_HOST_STACK_KIB", "64"},
        {"APS5_INDIRECT_BASE_INSTANCE", "1"},
        {"APS5_INDIRECT_BASE_VERTEX", "1"},
        {"APS5_INDIRECT_PASS_CONTINUE", "1"},
        {"APS5_INDIRECT_NO_INDEX_CLAMP", "1"},
        {"APS5_TEXTURE_CACHE_MIB", "3072"},
        {"APS5_DEPTH_PLANE_COPY_MIB", "1024"},
        {"APS5_NO_BDA_STAGING", "1"},
        {"APS5_HOST_IMPORT_MIB", "10240"},
        {"APS5_PIPELINE_GPU_INDIRECT", "1"},
        {"APS5_DRAW_PIPELINE", "1"},
        {"APS5_PIPELINE_DISPATCH", "1"},
        {"APS5_TEXTURE_REDUCE", "1"},
        {"APS5_RESOURCE_CACHE_ENTRIES", "8192"},
        {"APS5_TARGET_MEMO", "1"},
    };
    int applied = 0;
    for (const auto& [name, value] : preset) {
        if (std::getenv(name) != nullptr) continue;
        _putenv_s(name, value);
        ++applied;
    }
    Report("[ds-preset] Demon's Souls: %d switches turned on (APS5_NO_DS_PRESET=1 turns this off)\n", applied);
}

void InstallJobIdleSleep() {
    const char* enabled = std::getenv("APS5_JOB_IDLE_SLEEP");
    if (enabled == nullptr || enabled[0] == '0') return;
    if (const char* micros = std::getenv("APS5_JOB_IDLE_SLEEP_US")) {
        const auto value = std::strtoll(micros, nullptr, 10);
        if (value > 0 && value <= 100000) g_jobIdleSleep100ns = value * 10;
    }
    // call poll; test al, al; je <loop>; mov r15, [rbp-0x38]; mov rsi, [r15+disp32]; test rsi, rsi; je
    static constexpr std::int16_t callShape[] = {0xe8, -1, -1, -1, -1, 0x84, 0xc0, 0x74, -1, 0x4c, 0x8b, 0x7d, 0xc8, 0x49, 0x8b, 0xb7, -1, 0x00, 0x00, 0x00, 0x48, 0x85, 0xf6, 0x74};
    // push rbp; mov rbp, rsp; push r15..rbx; sub rsp, imm32; mov r14, [rip+disp32]
    static constexpr std::int16_t pollShape[] = {0x55, 0x48, 0x89, 0xe5, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xec, -1, 0x00, 0x00, 0x00, 0x4c, 0x8b, 0x35};
    auto* image = reinterpret_cast<std::uint8_t*>(GetModuleHandleW(nullptr));
    const auto* dos = reinterpret_cast<const IMAGE_DOS_HEADER*>(image);
    const auto* nt = reinterpret_cast<const IMAGE_NT_HEADERS64*>(image + dos->e_lfanew);
    const auto* section = IMAGE_FIRST_SECTION(nt);
    std::uint8_t* site = nullptr;
    std::uint8_t* poll = nullptr;
    int matches = 0;
    for (unsigned s = 0; s < nt->FileHeader.NumberOfSections; ++s, ++section) {
        if ((section->Characteristics & IMAGE_SCN_MEM_EXECUTE) == 0) continue;
        auto* begin = image + section->VirtualAddress;
        const auto size = static_cast<std::size_t>(std::max(section->Misc.VirtualSize, section->SizeOfRawData));
        if (size < std::size(callShape)) continue;
        for (std::size_t at = 0; at + std::size(callShape) <= size; ++at) {
            if (begin[at] != 0xe8 || !MatchesShape(begin + at, callShape, std::size(callShape))) continue;
            if (static_cast<std::int8_t>(begin[at + 8]) >= 0) continue;
            std::int32_t rel = 0;
            std::memcpy(&rel, begin + at + 1, sizeof(rel));
            auto* target = begin + at + 5 + rel;
            if (target < begin || target + std::size(pollShape) > begin + size || !MatchesShape(target, pollShape, std::size(pollShape))) continue;
            ++matches;
            site = begin + at;
            poll = target;
        }
    }
    if (matches != 1) {
        Report("[job-idle] APS5_JOB_IDLE_SLEEP: %d matching job poll call sites, nothing patched\n", matches);
        return;
    }
    // The thunk must sit within rel32 reach of the call site: take the first free 64 KiB block after the image.
    auto* thunk = static_cast<std::uint8_t*>(nullptr);
    for (auto candidate = (reinterpret_cast<std::uintptr_t>(image) + nt->OptionalHeader.SizeOfImage + 0xffff) & ~std::uintptr_t{0xffff};
         candidate < reinterpret_cast<std::uintptr_t>(site) + 0x40000000ull && thunk == nullptr; candidate += 0x10000) {
        thunk = static_cast<std::uint8_t*>(VirtualAlloc(reinterpret_cast<void*>(candidate), 0x1000, MEM_RESERVE | MEM_COMMIT, PAGE_READWRITE));
    }
    // The address space around a low image can be all reserved: use the zero padding after an executable section instead.
    bool inImagePadding = false;
    constexpr std::size_t thunkBytes = 320;
    const auto* lastSection = IMAGE_FIRST_SECTION(nt) + nt->FileHeader.NumberOfSections;
    for (const auto* candidate = lastSection; thunk == nullptr && candidate != IMAGE_FIRST_SECTION(nt);) {
        --candidate;
        if ((candidate->Characteristics & IMAGE_SCN_MEM_EXECUTE) == 0) continue;
        auto* end = image + candidate->VirtualAddress + std::max(candidate->Misc.VirtualSize, candidate->SizeOfRawData);
        auto* start = reinterpret_cast<std::uint8_t*>((reinterpret_cast<std::uintptr_t>(end) + 15) & ~std::uintptr_t{15});
        const auto pageEnd = (reinterpret_cast<std::uintptr_t>(end) + 0xfff) & ~std::uintptr_t{0xfff};
        if (reinterpret_cast<std::uintptr_t>(start) + thunkBytes > pageEnd) continue;
        if (std::any_of(start, start + thunkBytes, [](std::uint8_t byte) { return byte != 0; })) continue;
        thunk = start;
        inImagePadding = true;
    }
    if (thunk == nullptr) {
        Report("[job-idle] APS5_JOB_IDLE_SLEEP: no free page near the image, nothing patched\n");
        return;
    }
    g_jobIdleTimerSlot = TlsAlloc();
    std::uint8_t code[320];
    std::size_t n = 0;
    const auto emit = [&](std::initializer_list<std::uint8_t> bytes) { for (auto b : bytes) code[n++] = b; };
    const auto emit32 = [&](std::int32_t value) { std::memcpy(code + n, &value, 4); n += 4; };
    emit({0x48, 0x83, 0xec, 0x08});                                   // sub rsp, 8
    emit({0xe8}); emit32(static_cast<std::int32_t>(poll - (thunk + n + 4))); // call poll
    emit({0x48, 0x83, 0xc4, 0x08});                                   // add rsp, 8
    emit({0x84, 0xc0});                                               // test al, al
    emit({0x0f, 0x85}); const auto done = n; emit32(0);               // jnz done
    emit({0x9c, 0x50, 0x51, 0x52, 0x56, 0x57, 0x41, 0x50, 0x41, 0x51, 0x41, 0x52, 0x41, 0x53, 0x55}); // pushfq; push rax rcx rdx rsi rdi r8-r11 rbp
    emit({0x48, 0x89, 0xe5});                                         // mov rbp, rsp
    emit({0x48, 0x83, 0xe4, 0xc0});                                   // and rsp, -64
    emit({0x48, 0x81, 0xec, 0x00, 0x04, 0x00, 0x00});                 // sub rsp, 0x400
    // XSAVE leaves the reserved bytes of the area's header as they were, and XRSTOR faults on any set: zero it.
    for (std::int32_t offset = 0x200; offset < 0x240; offset += 8) {
        emit({0x48, 0xc7, 0x84, 0x24}); emit32(offset); emit32(0);    // mov qword [rsp+offset], 0
    }
    emit({0xb8, 0x07, 0x00, 0x00, 0x00, 0x31, 0xd2});                 // mov eax, 7; xor edx, edx
    emit({0x48, 0x0f, 0xae, 0x24, 0x24});                             // xsave64 [rsp]
    emit({0x48, 0x83, 0xec, 0x20});                                   // sub rsp, 32 (shadow space)
    emit({0x48, 0xb8});                                               // mov rax, imm64
    const auto wait = reinterpret_cast<std::uint64_t>(&JobIdleWait);
    std::memcpy(code + n, &wait, 8); n += 8;
    emit({0xff, 0xd0});                                               // call rax
    emit({0x48, 0x83, 0xc4, 0x20});                                   // add rsp, 32
    emit({0xb8, 0x07, 0x00, 0x00, 0x00, 0x31, 0xd2});                 // mov eax, 7; xor edx, edx
    emit({0x48, 0x0f, 0xae, 0x2c, 0x24});                             // xrstor64 [rsp]
    emit({0x48, 0x89, 0xec});                                         // mov rsp, rbp
    emit({0x5d, 0x41, 0x5b, 0x41, 0x5a, 0x41, 0x59, 0x41, 0x58, 0x5f, 0x5e, 0x5a, 0x59, 0x58, 0x9d}); // pop rbp r11-r8 rdi rsi rdx rcx rax; popfq
    const auto ret = n;
    emit({0xc3});                                                     // done: ret
    const auto jump = static_cast<std::int32_t>(ret - (done + 4));
    std::memcpy(code + done, &jump, 4);
    DWORD old = 0;
    if (inImagePadding && !VirtualProtect(thunk, n, PAGE_EXECUTE_READWRITE, &old)) {
        Report("[job-idle] APS5_JOB_IDLE_SLEEP: cannot make the section padding writable (%lu), nothing patched\n", GetLastError());
        return;
    }
    std::memcpy(thunk, code, n);
    if (inImagePadding) {
        DWORD restoredPadding = 0;
        VirtualProtect(thunk, n, old, &restoredPadding);
    } else {
        VirtualProtect(thunk, 0x1000, PAGE_EXECUTE_READ, &old);
    }
    FlushInstructionCache(GetCurrentProcess(), thunk, n);
    // Rewrite the call's rel32 with one aligned 8-byte store (no guest thread runs yet, but stay atomic).
    auto* word = reinterpret_cast<std::uint8_t*>(reinterpret_cast<std::uintptr_t>(site + 1) & ~std::uintptr_t{7});
    if (site + 5 > word + 8) {
        Report("[job-idle] APS5_JOB_IDLE_SLEEP: call site straddles an 8-byte boundary, nothing patched\n");
        return;
    }
    if (!VirtualProtect(word, 8, PAGE_EXECUTE_READWRITE, &old)) {
        Report("[job-idle] APS5_JOB_IDLE_SLEEP: cannot make the call site writable (%lu), nothing patched\n", GetLastError());
        return;
    }
    std::uint64_t value = 0;
    std::memcpy(&value, word, 8);
    std::uint8_t bytes[8];
    std::memcpy(bytes, &value, 8);
    const auto newRel = static_cast<std::int32_t>(thunk - (site + 5));
    std::memcpy(bytes + (site + 1 - word), &newRel, 4);
    std::memcpy(&value, bytes, 8);
    reinterpret_cast<std::atomic<std::uint64_t>*>(word)->store(value, std::memory_order_release);
    DWORD restored = 0;
    VirtualProtect(word, 8, old, &restored);
    FlushInstructionCache(GetCurrentProcess(), site, 5);
    Report("[job-idle] APS5_JOB_IDLE_SLEEP: job poll call at image+0x%llx -> poll image+0x%llx redirected through a %zu-byte thunk at 0x%llx, idle sleep %lld us\n",
        static_cast<unsigned long long>(site - image), static_cast<unsigned long long>(poll - image), n, static_cast<unsigned long long>(reinterpret_cast<std::uintptr_t>(thunk)), g_jobIdleSleep100ns / 10);
}

void InstallWatch() {
    // APS5_WATCH_ADDR=<absolute hex address> watches guest data that is mapped later: the page is
    // protected once it has been committed.
    if (const char* absolute = std::getenv("APS5_WATCH_ADDR")) {
        g_watchAddress = std::strtoull(absolute, nullptr, 16);
        const auto page = g_watchAddress & ~static_cast<std::uintptr_t>(0xfff);
        CreateThread(nullptr, 0, [](void* parameter) -> DWORD {
            const auto page = reinterpret_cast<std::uintptr_t>(parameter);
            for (;;) {
                MEMORY_BASIC_INFORMATION memory{};
                if (VirtualQuery(reinterpret_cast<const void*>(page), &memory, sizeof(memory)) == sizeof(memory) && memory.State == MEM_COMMIT) break;
                Sleep(1);
            }
            g_watchPage = page;
            ProtectWatchPage(PAGE_READONLY);
            Report("[watch] watching 0x%llx (page 0x%llx)\n", static_cast<unsigned long long>(g_watchAddress), static_cast<unsigned long long>(page));
            return 0;
        }, reinterpret_cast<void*>(page), 0, nullptr);
        return;
    }
    const char* value = std::getenv("APS5_WATCH_WRITE");
    if (!value) return;
    const auto elfAddress = std::strtoull(value, nullptr, 0);
    g_watchAddress = reinterpret_cast<std::uintptr_t>(GetModuleHandleW(nullptr)) + 0x10000 + elfAddress;
    g_watchPage = g_watchAddress & ~static_cast<std::uintptr_t>(0xfff);
    ProtectWatchPage(PAGE_READONLY);
    Report("[watch] watching 0x%llx (page 0x%llx)\n", static_cast<unsigned long long>(g_watchAddress), static_cast<unsigned long long>(g_watchPage));
}

// SSE4a (EXTRQ / INSERTQ) is AMD-only: the PS5's Zen 2 has it and titles use it, so on an Intel host the
// instruction raises STATUS_ILLEGAL_INSTRUCTION and is emulated on the faulting thread's CONTEXT.
// APS5_NO_SSE4A_EMULATION=1 disables this (the fault is then reported as fatal as before) and
// APS5_TRACE_SSE4A=1 prints each emulated instruction once per rip.
bool g_sse4aEmulation = true;
bool g_sse4aTrace = false;
std::atomic<unsigned long long> g_sse4aEmulated{0};

bool IsEnvironmentSet(const char* name) {
    const char* value = std::getenv(name);
    return value != nullptr && *value != '\0' && !(value[0] == '0' && value[1] == '\0');
}

// Copies the bytes at `address` that are mapped; the read stays within readable pages.
std::size_t ReadCode(std::uint64_t address, std::uint8_t* buffer, std::size_t size) {
    std::size_t count = 0;
    while (count < size) {
        const auto cursor = address + count;
        if ((cursor & 0xfff) == 0 || count == 0) {
            if (!IsReadable(cursor)) break;
        }
        buffer[count++] = *reinterpret_cast<const std::uint8_t*>(cursor);
    }
    return count;
}

void TraceSse4a(std::uint64_t rip, const sse4a::Instruction& instruction, const sse4a::Field& field, unsigned long long count) {
    static std::mutex mutex;
    static std::uint64_t seen[128];
    static std::size_t seenCount = 0;
    {
        std::lock_guard lock(mutex);
        for (std::size_t i = 0; i < seenCount; ++i) {
            if (seen[i] == rip) return;
        }
        if (seenCount < sizeof(seen) / sizeof(seen[0])) seen[seenCount++] = rip;
    }
    char line[MAX_PATH + 64];
    DescribeAddress(rip, line, sizeof(line));
    const char* mnemonic = instruction.op == sse4a::Op::Extrq ? "extrq" : "insertq";
    char operands[64];
    if (instruction.op == sse4a::Op::Extrq && !instruction.registerForm) {
        std::snprintf(operands, sizeof(operands), "xmm%u, %u, %u", instruction.destination, instruction.length, instruction.index);
    } else if (!instruction.registerForm) {
        std::snprintf(operands, sizeof(operands), "xmm%u, xmm%u, %u, %u", instruction.destination, instruction.source, instruction.length, instruction.index);
    } else {
        std::snprintf(operands, sizeof(operands), "xmm%u, xmm%u", instruction.destination, instruction.source);
    }
    Report("[sse4a] #%llu %s %s (length %u, index %u, %u bytes) at %s on thread %lu\n", count, mnemonic, operands, field.length, field.index, static_cast<unsigned>(instruction.size), line, GetCurrentThreadId());
}

constexpr DWORD GccExceptionMask = 0x20ffffffu;
constexpr DWORD GccException = 0x20474343u;
constexpr std::uint64_t GccExceptionClass = 0x474e5543432b2b00ull;
constexpr std::uint64_t CxaExceptionTypeOffset = 80;

PWSTR ThreadDescription(HANDLE thread) {
    using GetDescription = HRESULT (WINAPI *)(HANDLE, PWSTR*);
    static const auto getDescription = reinterpret_cast<GetDescription>(GetProcAddress(GetModuleHandleW(L"kernel32.dll"), "GetThreadDescription"));
    PWSTR description = nullptr;
    if (!getDescription || FAILED(getDescription(thread, &description))) return nullptr;
    return description;
}

std::uint64_t FrameWithoutUnwindData(const CONTEXT& start) {
    const HMODULE runtime[] = {GetModuleHandleA("KERNELBASE.dll"), GetModuleHandleA("libgcc_s_seh-1.dll"), GetModuleHandleA("libstdc++-6.dll")};
    CONTEXT context = start;
    for (int depth = 0; depth < 64 && context.Rip != 0; ++depth) {
        HMODULE module = nullptr;
        GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT, reinterpret_cast<LPCSTR>(context.Rip), &module);
        DWORD64 imageBase = 0;
        const auto entry = RtlLookupFunctionEntry(context.Rip, &imageBase, nullptr);
        if (module == nullptr || std::find(std::begin(runtime), std::end(runtime), module) == std::end(runtime)) return entry == nullptr ? context.Rip : 0;
        if (entry == nullptr) return 0;
        PVOID handlerData = nullptr;
        DWORD64 establisher = 0;
        RtlVirtualUnwind(UNW_FLAG_NHANDLER, imageBase, context.Rip, entry, &context, &handlerData, &establisher, nullptr);
    }
    return 0;
}

bool ReadWord(std::uint64_t address, std::uint64_t* value) {
    return ReadCode(address, reinterpret_cast<std::uint8_t*>(value), sizeof(*value)) == sizeof(*value);
}

std::uint64_t EnvironmentNumber(const char* name) {
    char text[32];
    const DWORD length = GetEnvironmentVariableA(name, text, sizeof(text));
    if (length == 0 || length >= sizeof(text)) return 0;
    return std::strtoull(text, nullptr, 0);
}

void ReportStackWords(std::uint64_t rsp) {
    const auto bytes = std::min<std::uint64_t>(EnvironmentNumber("APS5_CRASH_STACK_BYTES"), std::uint64_t{1} << 20);
    if (bytes == 0) return;
    const auto* tib = reinterpret_cast<const NT_TIB*>(NtCurrentTeb());
    const auto stackLow = reinterpret_cast<std::uint64_t>(tib->StackLimit);
    const auto stackHigh = reinterpret_cast<std::uint64_t>(tib->StackBase);
    const auto first = rsp & ~std::uint64_t{7};
    Report("  stack words from rsp 0x%016llx (APS5_CRASH_STACK_BYTES):\n", static_cast<unsigned long long>(rsp));
    const auto limit = std::min(first + bytes, stackHigh);
    std::uint64_t end = first;
    std::uint64_t readablePage = 0;
    for (std::uint64_t at = first; at < limit; at += 32) {
        std::uint64_t words[4] = {};
        int count = 0;
        for (; count < 4; ++count) {
            const auto slot = at + static_cast<std::uint64_t>(count) * 8;
            const auto page = slot & ~std::uint64_t{0xfff};
            if (page != readablePage) {
                if (!IsReadable(slot)) break;
                readablePage = page;
            }
            words[count] = *reinterpret_cast<const std::uint64_t*>(slot);
        }
        if (count == 0) break;
        static char text[192];
        int used = std::snprintf(text, sizeof(text), "    +0x%04llx:", static_cast<unsigned long long>(at - first));
        for (int k = 0; k < count && used > 0 && used < static_cast<int>(sizeof(text)); ++k) used += std::snprintf(text + used, sizeof(text) - static_cast<std::size_t>(used), " %016llx", static_cast<unsigned long long>(words[k]));
        Report("%s\n", text);
        end = at + static_cast<std::uint64_t>(count) * 8;
        if (count < 4) break;
    }
    static std::uint64_t seen[256];
    std::size_t seenCount = 0;
    Report("  data at stack words that point outside the stack (8 words each):\n");
    for (std::uint64_t slot = first; slot + 8 <= end && seenCount < std::size(seen); slot += 8) {
        const auto value = *reinterpret_cast<const std::uint64_t*>(slot);
        if (value < 0x10000 || (value & 7) != 0 || value > 0x7fffffffffffull || (value >= stackLow && value < stackHigh)) continue;
        if (std::find(seen, seen + seenCount, value) != seen + seenCount) continue;
        if (IsExecutable(value) || !IsReadable(value) || !IsReadable(value + 0x38)) continue;
        seen[seenCount++] = value;
        const auto* words = reinterpret_cast<const std::uint64_t*>(value);
        Report("    [+0x%04llx] 0x%016llx: %016llx %016llx %016llx %016llx %016llx %016llx %016llx %016llx\n", static_cast<unsigned long long>(slot - first), static_cast<unsigned long long>(value), words[0], words[1], words[2], words[3], words[4], words[5], words[6], words[7]);
    }
}

void ReportUndeliverableException(const EXCEPTION_POINTERS* info, std::uint64_t frame) {
    const auto* record = info->ExceptionRecord;
    char type[256] = "of unknown type";
    const auto header = record->NumberParameters >= 1 ? static_cast<std::uint64_t>(record->ExceptionInformation[0]) : 0;
    std::uint64_t exceptionClass = 0;
    std::uint64_t typeInfo = 0;
    std::uint64_t namePointer = 0;
    if (ReadWord(header, &exceptionClass) && exceptionClass == GccExceptionClass && ReadWord(header - CxaExceptionTypeOffset, &typeInfo) && ReadWord(typeInfo + 8, &namePointer)) {
        std::uint8_t name[sizeof(type)];
        const auto copied = ReadCode(namePointer, name, sizeof(name));
        if (const auto* end = static_cast<const std::uint8_t*>(std::memchr(name, 0, copied))) std::memcpy(type, name, static_cast<std::size_t>(end - name) + 1);
    }
    char line[MAX_PATH + 64];
    DescribeAddress(frame, line, sizeof(line));
    Report("\nFATAL: C++ exception %s raised on thread %lu cannot be delivered: %s has no unwind data\n", type, GetCurrentThreadId(), line);
    ReportStackCandidates(info->ContextRecord->Rsp, 32, 0x4000);
}

bool HandleSse4a(EXCEPTION_POINTERS* info) {
    if (!g_sse4aEmulation) return false;
    const auto* record = info->ExceptionRecord;
    if (record->ExceptionCode != EXCEPTION_ILLEGAL_INSTRUCTION) return false;
    auto* context = info->ContextRecord;
    const auto rip = context->Rip;
    std::uint8_t bytes[sse4a::kMaxInstructionSize];
    const std::size_t available = ReadCode(rip, bytes, sizeof(bytes));
    sse4a::Instruction instruction;
    sse4a::Field field;
    if (!sse4a::Emulate(bytes, available, *context, &instruction, &field)) return false;
    const auto count = ++g_sse4aEmulated;
    if (g_sse4aTrace) TraceSse4a(rip, instruction, field, count);
    return true;
}

LONG WINAPI ReportCrash(EXCEPTION_POINTERS* info) {
    static std::atomic<bool> reported{false};
    const auto* fault = info->ExceptionRecord;
    if (fault->ExceptionCode == EXCEPTION_ACCESS_VIOLATION && fault->NumberParameters >= 2 && fault->ExceptionInformation[0] == 1 && GuestArena::GuestArenaHandleWrite_nid_postfix(fault->ExceptionInformation[1])) return EXCEPTION_CONTINUE_EXECUTION;
    if (fault->ExceptionCode == EXCEPTION_ACCESS_VIOLATION && fault->NumberParameters >= 2 && fault->ExceptionInformation[0] == 0 && GuestArena::GuestArenaHandleRead_nid_postfix(fault->ExceptionInformation[1])) return EXCEPTION_CONTINUE_EXECUTION;
    if (HandleWatch(info)) return EXCEPTION_CONTINUE_EXECUTION;
    if (HandleSse4a(info)) return EXCEPTION_CONTINUE_EXECUTION;
    const auto* record = info->ExceptionRecord;
    if ((record->ExceptionCode & GccExceptionMask) == GccException) {
        if (const auto frame = FrameWithoutUnwindData(*info->ContextRecord)) ReportUndeliverableException(info, frame);
        return EXCEPTION_CONTINUE_SEARCH;
    }
    if (!IsFatal(record->ExceptionCode)) return EXCEPTION_CONTINUE_SEARCH;
    if (reported.exchange(true)) {
        // Another thread is already reporting; let it finish before this fault ends the process.
        Sleep(INFINITE);
    }
    LibcRunEndFlush_nid_no_patch();
    const auto* context = info->ContextRecord;
    char line[MAX_PATH + 64];
    char threadName[128] = "";
    if (PWSTR description = ThreadDescription(GetCurrentThread())) {
        WideCharToMultiByte(CP_UTF8, 0, description, -1, threadName, sizeof(threadName), nullptr, nullptr);
        LocalFree(description);
    }
    Report("\nFATAL: unhandled exception 0x%08lx on thread %lu '%s'\n", record->ExceptionCode, GetCurrentThreadId(), threadName);
    DescribeAddress(context->Rip, line, sizeof(line));
    Report("  rip %s\n", line);
    if (record->ExceptionCode == EXCEPTION_ILLEGAL_INSTRUCTION) {
        std::uint8_t bytes[8];
        const std::size_t available = ReadCode(context->Rip, bytes, sizeof(bytes));
        char hex[3 * sizeof(bytes) + 1] = "";
        for (std::size_t i = 0; i < available; ++i) std::snprintf(hex + 3 * i, sizeof(hex) - 3 * i, "%02x ", bytes[i]);
        Report("  bytes %s(sse4a emulation %s, %llu emulated so far)\n", hex, g_sse4aEmulation ? "on" : "off", g_sse4aEmulated.load());
    }
    if (record->ExceptionCode == EXCEPTION_ACCESS_VIOLATION && record->NumberParameters >= 2) {
        const char* kind = record->ExceptionInformation[0] == 0 ? "read" : record->ExceptionInformation[0] == 1 ? "write" : "execute";
        Report("  %s of 0x%016llx\n", kind, static_cast<unsigned long long>(record->ExceptionInformation[1]));
        std::uint8_t trap[2];
        if (record->ExceptionInformation[0] == 0 && record->ExceptionInformation[1] == ~0ull && ReadCode(context->Rip, trap, sizeof(trap)) == sizeof(trap) && trap[0] == 0xcd) {
            if (trap[1] == 0x45) Report("  guest abort() (int 0x45)\n");
            else if (trap[1] == 0x41) Report("  guest assert/break (int 0x41)\n");
        }
    }
    Report("  rax %016llx rbx %016llx rcx %016llx rdx %016llx\n", context->Rax, context->Rbx, context->Rcx, context->Rdx);
    Report("  rsi %016llx rdi %016llx rbp %016llx rsp %016llx\n", context->Rsi, context->Rdi, context->Rbp, context->Rsp);
    Report("  r8  %016llx r9  %016llx r10 %016llx r11 %016llx\n", context->R8, context->R9, context->R10, context->R11);
    Report("  r12 %016llx r13 %016llx r14 %016llx r15 %016llx\n", context->R12, context->R13, context->R14, context->R15);
    // The words each register points at, to recognise which structure a bad pointer came from.
    {
        const DWORD indirectLength = GetEnvironmentVariableA("APS5_CRASH_INDIRECT_MEMORY", nullptr, 0);
        const bool indirectMemory = indirectLength > 1;
        const std::pair<const char*, std::uint64_t> pointers[] = {{"rax", context->Rax}, {"rbx", context->Rbx}, {"rcx", context->Rcx}, {"rdx", context->Rdx}, {"rsi", context->Rsi}, {"rdi", context->Rdi}, {"r12", context->R12}, {"r13", context->R13}, {"r14", context->R14}, {"r15", context->R15}};
        for (const auto& [name, value] : pointers) {
            if (value < 0x10000 || (value & 7) != 0 || !IsReadable(value) || !IsReadable(value + 0x38)) continue;
            const auto* words = reinterpret_cast<const std::uint64_t*>(value);
            Report("  [%s] %016llx %016llx %016llx %016llx %016llx %016llx %016llx %016llx\n", name, words[0], words[1], words[2], words[3], words[4], words[5], words[6], words[7]);
            if (!indirectMemory) continue;
            for (std::size_t i = 0; i < 8; ++i) {
                const auto address = words[i];
                if (address < 0x10000 || IsExecutable(address)) continue;
                std::uint64_t content[8]{};
                SIZE_T copied = 0;
                if (!ReadProcessMemory(GetCurrentProcess(), reinterpret_cast<const void*>(address), content, sizeof(content), &copied) || copied != sizeof(content)) continue;
                Report("  [[%s+0x%llx]] @%016llx %016llx %016llx %016llx %016llx %016llx %016llx %016llx %016llx\n",
                    name, static_cast<unsigned long long>(i * sizeof(*words)), static_cast<unsigned long long>(address),
                    content[0], content[1], content[2], content[3], content[4], content[5], content[6], content[7]);
            }
        }
    }
    {
        const std::pair<const char*, std::uint64_t> registers[] = {{"rax", context->Rax}, {"rbx", context->Rbx}, {"rcx", context->Rcx}, {"rdx", context->Rdx}, {"rsi", context->Rsi}, {"rdi", context->Rdi}, {"rbp", context->Rbp}, {"r8", context->R8}, {"r9", context->R9}, {"r10", context->R10}, {"r11", context->R11}, {"r12", context->R12}, {"r13", context->R13}, {"r14", context->R14}, {"r15", context->R15}};
        static std::uint8_t bytes[crash_text::MaximumBytes];
        static char text[960];
        for (const auto& [name, value] : registers) {
            if (value < 0x10000) continue;
            if (crash_text::Format(bytes, ReadCode(value, bytes, sizeof(bytes)), text, sizeof(text))) Report("  [%s] %s\n", name, text);
        }
    }
    Report("  frame pointer chain:\n");
    std::uint64_t frame = context->Rbp;
    for (int depth = 0; depth < 32 && frame != 0 && (frame & 7) == 0 && IsReadable(frame) && IsReadable(frame + 8); ++depth) {
        const auto returnAddress = reinterpret_cast<const std::uint64_t*>(frame)[1];
        if (!IsExecutable(returnAddress)) break;
        DescribeAddress(returnAddress, line, sizeof(line));
        Report("    #%d %s\n", depth, line);
        const auto next = reinterpret_cast<const std::uint64_t*>(frame)[0];
        if (next <= frame) break;
        frame = next;
    }
    ReportStackCandidates(context->Rsp, 16, 0x2000);
    ReportStackWords(context->Rsp);
    if (context->Rip == 0 ||!IsExecutable(context->Rip)) {
        // A jump into nothing usually follows a return through a clobbered frame; the frames that just
        // returned are still below rsp.
        Report("  recently popped return address candidates:\n");
        for (std::uint64_t slot = context->Rsp - 8; slot >= context->Rsp - 0x800; slot -= 8) {
            if (!IsReadable(slot)) break;
            const auto value = *reinterpret_cast<const std::uint64_t*>(slot);
            if (!IsExecutable(value)) continue;
            DescribeAddress(value, line, sizeof(line));
            Report("    [rsp-0x%llx] %s\n", static_cast<unsigned long long>(context->Rsp - slot), line);
        }
        // Registers often still point into the stack the code ran on before the bad return.
        const std::pair<const char*, std::uint64_t> registers[] = {{"rdi", context->Rdi}, {"rsi", context->Rsi}, {"rbx", context->Rbx}, {"r12", context->R12}, {"r13", context->R13}, {"r14", context->R14}, {"r15", context->R15}};
        for (const auto& [name, value] : registers) {
            if (value < 0x10000 || (value & 7) != 0 || !IsReadable(value)) continue;
            Report("  code addresses above %s (0x%llx):\n", name, static_cast<unsigned long long>(value));
            int found = 0;
            for (std::uint64_t slot = value; found < 24 && slot < value + 0x1000; slot += 8) {
                if (!IsReadable(slot)) break;
                const auto candidate = *reinterpret_cast<const std::uint64_t*>(slot);
                if (!IsExecutable(candidate)) continue;
                DescribeAddress(candidate, line, sizeof(line));
                Report("    [+0x%llx] %s\n", static_cast<unsigned long long>(slot - value), line);
                ++found;
            }
        }
    }
    ReportCallTrace();
    std::fflush(stderr);
    ReportAllThreads();
    LibcRunFailureReports_nid_no_patch();
    std::fflush(stderr);
    return EXCEPTION_CONTINUE_SEARCH;
}

void ReportCallTrace() {
    static CallTraceEntry entries[64];
    const std::size_t count = CopyCallTrace_nid_no_patch(entries, std::size(entries));
    if (count == 0) return;
    char line[MAX_PATH + 64];
    Report("  last traced system library calls (APS5_TRACE_CALLS):\n");
    for (std::size_t index = 0; index < count; ++index) {
        DescribeAddress(entries[index].returnAddress, line, sizeof(line));
        Report("    #%llu thread %llu %s %s from %s\n", static_cast<unsigned long long>(entries[index].sequence),
            static_cast<unsigned long long>(entries[index].thread), entries[index].library, entries[index].name, line);
    }
    static CallTraceEntry own[32];
    const std::uint64_t thread = GetCurrentThreadId();
    const std::size_t owned = CopyThreadCallTrace_nid_no_patch(thread, own, std::size(own));
    if (owned != 0) {
        Report("  last traced calls of thread %llu:\n", static_cast<unsigned long long>(thread));
        for (std::size_t index = 0; index < owned; ++index) {
            DescribeAddress(own[index].returnAddress, line, sizeof(line));
            Report("    #%llu %s %s from %s\n", static_cast<unsigned long long>(own[index].sequence), own[index].library, own[index].name, line);
        }
    }
    static CallTraceCount counts[32];
    std::uint64_t total = 0;
    const std::size_t counted = CopyCallCounts_nid_no_patch(counts, std::size(counts), &total);
    if (counted == 0) return;
    Report("  most called traced imports (%llu calls in total):\n", static_cast<unsigned long long>(total));
    for (std::size_t index = 0; index < counted; ++index) {
        Report("    %12llu %s %s\n", static_cast<unsigned long long>(counts[index].calls), counts[index].library, counts[index].name);
    }
}

std::size_t CaptureFrames(const CONTEXT* context, std::uint64_t* frames, std::size_t capacity) {
    std::size_t count = 0;
    std::uint64_t frame = context->Rbp;
    while (count < capacity && frame != 0 && (frame & 7) == 0 && IsReadable(frame) && IsReadable(frame + 8)) {
        const auto returnAddress = reinterpret_cast<const std::uint64_t*>(frame)[1];
        if (!IsExecutable(returnAddress)) break;
        frames[count++] = returnAddress;
        const auto next = reinterpret_cast<const std::uint64_t*>(frame)[0];
        if (next <= frame) break;
        frame = next;
    }
    return count;
}

std::size_t CaptureStackCandidates(std::uint64_t rsp, std::uint64_t* candidates, std::size_t capacity) {
    std::size_t count = 0;
    for (std::uint64_t slot = rsp; count < capacity && slot < rsp + 0x8000; slot += 8) {
        if (!IsReadable(slot)) break;
        const auto value = *reinterpret_cast<const std::uint64_t*>(slot);
        if (IsExecutable(value)) candidates[count++] = value;
    }
    return count;
}

void ReportThreadContext(const CONTEXT* context, DWORD threadId, const char* name, const std::uint64_t* frames, std::size_t frameCount, const std::uint64_t* candidates, std::size_t candidateCount) {
    char line[MAX_PATH + 64];
    Report("  thread %lu '%s': rip ", static_cast<unsigned long>(threadId), name ? name : "");
    DescribeAddress(context->Rip, line, sizeof(line));
    Report("%s rsp 0x%016llx rbp 0x%016llx\n", line, static_cast<unsigned long long>(context->Rsp), static_cast<unsigned long long>(context->Rbp));
    for (std::size_t depth = 0; depth < frameCount; ++depth) {
        DescribeAddress(frames[depth], line, sizeof(line));
        Report("    #%llu %s\n", static_cast<unsigned long long>(depth), line);
    }
    if (candidateCount != 0) Report("    stack return address candidates:\n");
    for (std::size_t index = 0; index < candidateCount; ++index) {
        DescribeAddress(candidates[index], line, sizeof(line));
        Report("      %s\n", line);
    }
}

void ReportAllThreads() {
    const DWORD current = GetCurrentThreadId();
    const DWORD pid = GetCurrentProcessId();
    HANDLE snapshot = CreateToolhelp32Snapshot(TH32CS_SNAPTHREAD, 0);
    if (snapshot == INVALID_HANDLE_VALUE) return;
    THREADENTRY32 entry{};
    entry.dwSize = sizeof(entry);
    struct CapturedThread {
        DWORD id;
        char name[128];
        CONTEXT context;
        std::uint64_t frames[12];
        std::size_t frameCount;
        std::uint64_t candidates[24];
        std::size_t candidateCount;
    };
    static CapturedThread captured[128];
    std::size_t capturedCount = 0;
    std::size_t skippedCount = 0;
    if (Thread32First(snapshot, &entry)) {
        do {
            if (entry.th32OwnerProcessID != pid || entry.th32ThreadID == current) continue;
            if (capturedCount >= sizeof(captured) / sizeof(captured[0])) {
                ++skippedCount;
                continue;
            }
            HANDLE thread = OpenThread(THREAD_SUSPEND_RESUME | THREAD_GET_CONTEXT | THREAD_QUERY_INFORMATION, FALSE, entry.th32ThreadID);
            if (!thread) continue;
            if (SuspendThread(thread) == static_cast<DWORD>(-1)) {
                CloseHandle(thread);
                continue;
            }
            CONTEXT context{};
            context.ContextFlags = CONTEXT_FULL;
            const BOOL haveContext = GetThreadContext(thread, &context);
            std::uint64_t frames[12] = {};
            const std::size_t frameCount = haveContext ? CaptureFrames(&context, frames, sizeof(frames) / sizeof(frames[0])) : 0;
            std::uint64_t candidates[24] = {};
            const std::size_t candidateCount = haveContext && frameCount < 2 ? CaptureStackCandidates(context.Rsp, candidates, sizeof(candidates) / sizeof(candidates[0])) : 0;
            ResumeThread(thread);
            char name[128] = "";
            if (PWSTR description = ThreadDescription(thread)) {
                WideCharToMultiByte(CP_UTF8, 0, description, -1, name, sizeof(name), nullptr, nullptr);
                LocalFree(description);
            }
            CloseHandle(thread);
            if (!haveContext) continue;
            captured[capturedCount].id = entry.th32ThreadID;
            std::memcpy(captured[capturedCount].name, name, sizeof(captured[capturedCount].name));
            captured[capturedCount].context = context;
            std::memcpy(captured[capturedCount].frames, frames, sizeof(captured[capturedCount].frames));
            captured[capturedCount].frameCount = frameCount;
            std::memcpy(captured[capturedCount].candidates, candidates, sizeof(captured[capturedCount].candidates));
            captured[capturedCount].candidateCount = candidateCount;
            ++capturedCount;
        } while (Thread32Next(snapshot, &entry));
    }
    CloseHandle(snapshot);
    Report("  all threads:\n");
    for (std::size_t i = 0; i < capturedCount; ++i) {
        ReportThreadContext(&captured[i].context, captured[i].id, captured[i].name, captured[i].frames, captured[i].frameCount, captured[i].candidates, captured[i].candidateCount);
    }
    if (skippedCount != 0) Report("  %llu further thread(s) left out\n", static_cast<unsigned long long>(skippedCount));
}

DWORD WINAPI HangWatchdog(LPVOID param) {
    const auto seconds = static_cast<unsigned long long>(reinterpret_cast<std::uintptr_t>(param));
    Sleep(static_cast<DWORD>(seconds * 1000ull));
    Report("\nFATAL: timed dump after %llu s (APS5_HANG_DUMP_SECS); aborting\n", seconds);
    std::fflush(stderr);
    std::abort();
    return 0;
}

void ReportStackCandidates(std::uint64_t rsp, int limit, std::uint64_t span) {
    char line[256];
    Report("  stack return address candidates:\n");
    int printed = 0;
    for (std::uint64_t slot = rsp; printed < limit && slot < rsp + span; slot += 8) {
        if (!IsReadable(slot)) break;
        const auto value = *reinterpret_cast<const std::uint64_t*>(slot);
        if (!IsExecutable(value)) continue;
        DescribeAddress(value, line, sizeof(line));
        Report("    [rsp+0x%llx] %s\n", static_cast<unsigned long long>(slot - rsp), line);
        ++printed;
    }
}

// abort() and the UCRT's invalid-parameter path end the process with a silent fast fail
// (0xc0000409); both are reported with the calling thread's stack first.
void ReportBacktrace(const char* what, bool reportThreads) {
    void* frames[48];
    const auto count = RtlCaptureStackBackTrace(0, 48, frames, nullptr);
    Report("FATAL: %s on thread %lu\n", what, static_cast<unsigned long>(GetCurrentThreadId()));
    char line[256];
    for (USHORT i = 0; i < count; ++i) {
        DescribeAddress(reinterpret_cast<std::uint64_t>(frames[i]), line, sizeof(line));
        Report("    #%u %s\n", static_cast<unsigned>(i), line);
    }
    ReportStackCandidates(reinterpret_cast<std::uint64_t>(__builtin_frame_address(0)), 32, 0x4000);
    ReportCallTrace();
    if (reportThreads) ReportAllThreads();
    std::fflush(stderr);
}

void AbortSignalHandler(int) {
    ReportBacktrace("abort() (SIGABRT)", true);
    LibcRunFailureReports_nid_no_patch();
}

void InvalidParameterHandler(const wchar_t*, const wchar_t*, const wchar_t*, unsigned, std::uintptr_t) {
    ReportBacktrace("UCRT invalid parameter", true);
    LibcRunFailureReports_nid_no_patch();
}

// Static destruction runs on the thread that ends the process (ExitProcess -> DLL_PROCESS_DETACH),
// so its stack names the exit's caller when no libc exit/abort path was taken.
struct ExitReporter {
    ~ExitReporter() {
        if (std::getenv("APS5_TRACE_EXIT") != nullptr) ReportBacktrace("process exit (static destruction)", false);
    }
} g_exitReporter;

const bool g_crashReportInstalled = [] {
    ApplyDemonsSoulsPreset();
    g_sse4aEmulation = !IsEnvironmentSet("APS5_NO_SSE4A_EMULATION");
    g_sse4aTrace = IsEnvironmentSet("APS5_TRACE_SSE4A");
    AddVectoredExceptionHandler(1, ReportCrash);
    std::signal(SIGABRT, AbortSignalHandler);
    _set_invalid_parameter_handler(InvalidParameterHandler);
    InstallWatch();
    InstallJobIdleSleep();
    if (const char* hang = std::getenv("APS5_HANG_DUMP_SECS")) {
        unsigned long long seconds = 0;
        if (hang[0] >= '0' && hang[0] <= '9') {
            char* end = nullptr;
            const auto value = std::strtoull(hang, &end, 10);
            if (end && *end == 0) seconds = value;
        }
        if (seconds > 0) CreateThread(nullptr, 0, HangWatchdog, reinterpret_cast<LPVOID>(static_cast<std::uintptr_t>(seconds)), 0, nullptr);
    }
    return true;
}();

}
#endif
