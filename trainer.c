/*
 * Exanima Heal Trainer (64-bit)
 *
 * Pointer chain:
 *   [module + STRUCT_PTR]  ->  character struct (64-bit ptr)
 *   struct + YEL_OFFSET*   ->  yellow stamina  (three copies, max ~0.25)
 *   struct + RED_OFFSET    ->  red health remaining (max ~0.25, 0.0 = dead)
 *   struct + BLU_CURRENT   ->  blue focus current  (max 1.0)
 *   struct + BLU_CAP       ->  blue bar capacity   (max 1.0, binding spells reduce)
 *
 * Instead of a hard lock, each bar regenerates at a chosen speed (units/second),
 * applied using real elapsed time so the rate is independent of poll jitter.
 * The top option ("Lock") snaps straight to max every tick = effective god mode.
 *
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <windows.h>
#include <psapi.h>

/* ── Offsets ───────────────────────────────────────────────────────────── */
#define STRUCT_PTR    0x4E0660 /* [module+this] 64-bit -> character struct      */
/* STRUCT_PTR is the only module-level offset — it shifts on game updates. It is
 * auto-located at startup by AOB scan (resolve_struct_ptr); the #define above is
 * the fallback if the scan fails. The struct-internal offsets below are stable
 * across updates and stay hardcoded. */
#define YEL_OFFSET    0x0D58   /* yellow stamina remaining  (max ~0.25)         */
#define YEL_OFFSET2   0x0D54   /* yellow stamina copy                           */
#define YEL_OFFSET3   0x0D40   /* yellow stamina copy — combat/knockout value   */
#define RED_OFFSET    0x0D44   /* red health remaining (0.25=healthy, 0.0=dead) */
#define BLU_CURRENT   0x0D5C   /* blue focus current (drained by active spells) */
#define BLU_CAP       0x0D60   /* blue bar max capacity (binding spells reduce)  */

#define YEL_MAX   0.25f
#define RED_MAX   0.25f
#define BLU_MAX   1.0f

#define POLL_MS  10

/*
 * Red health doesn't regenerate naturally in Exanima, so the multiply-natural
 * approach can't heal it. Red instead uses *additive* regen (force-add over real
 * time), gated on a heartbeat so it still won't heal while paused / in a
 * menu. We watch a block of live ragdoll physics (positions/velocities that
 * always micro-jitter while the sim runs); static for HB_STALE_MS => paused.
 */
#define HB_OFFSET   0x0C30
#define HB_LEN      0x40
#define HB_STALE_MS 250

/*
 * Regen speeds in units-per-second for each bar. Index 0 = off, last = lock.
 * Yellow/red are on a 0.25 scale, blue on a 1.0 scale, so the numbers differ
 * to give a comparable "time to refill" feel.
 *
 * The special LOCK means "snap to max instantly" (effective god mode).
 */
#define LOCK  (-1.0f)

/*
 * Each option is a MULTIPLIER on the game's own natural regen.
 * We only act when the game itself raises the bar this tick, then scale
 * that increase. This is automatically pause-safe: paused => no natural regen
 * => no delta => we do nothing. The final option locks to max (manual god mode).
 *
 * Caveat: a bar that doesn't regen naturally (e.g. deep red-health wounds barely
 * recover on their own) won't speed up much by multiplying — use Lock for those.
 */
/* Yellow stamina & Blue focus — shared multiplier ladder on natural regen */
static const float MULTS[] = { 0.0f, 2.0f, 4.0f, 8.0f, 16.0f, 32.0f, LOCK };
static const char *SPEED_LABELS[] = {
    "Off",
    "2x natural regen",
    "4x natural regen",
    "8x natural regen",
    "16x natural regen",
    "32x natural regen",
    "Lock to max (demigod mode)"
};
#define N_SPEEDS 7

/*
 * Red is additive (units/sec) since it has no natural regen to multiply.
 */
static const float RED_RATES[] = { 0.0f, 0.25f/120, 0.25f/60, 0.25f/30, 0.25f/10, 0.25f/5, LOCK };

static const char *RED_LABELS[] = {
    "Off",
    "Very slow (~120s to full)",
    "Slow      (~60s to full)",
    "Medium    (~30s to full)",
    "Fast      (~10s to full)",
    "Fastest   (~5s to full)",
    "Lock to max (demigod mode)"
};
#define N_RED 7

/* ── Process helpers ───────────────────────────────────────────────────── */

static HANDLE find_process(const char *name, uintptr_t *out_base)
{
    DWORD pids[1024], bytes;
    if (!EnumProcesses(pids, sizeof(pids), &bytes)) return NULL;
    int count = (int)(bytes / sizeof(DWORD));
    for (int i = 0; i < count; i++) {
        HANDLE h = OpenProcess(PROCESS_VM_READ | PROCESS_VM_WRITE |
                               PROCESS_VM_OPERATION | PROCESS_QUERY_INFORMATION,
                               FALSE, pids[i]);
        if (!h) continue;
        char buf[MAX_PATH]; HMODULE mods[1]; DWORD needed;
        if (EnumProcessModules(h, mods, sizeof(mods), &needed)) {
            GetModuleBaseNameA(h, mods[0], buf, sizeof(buf));
            if (_stricmp(buf, name) == 0) {
                *out_base = (uintptr_t)mods[0];
                return h;
            }
        }
        CloseHandle(h);
    }
    return NULL;
}

static int rpm8(HANDLE proc, uintptr_t addr, uint64_t *out)
{
    SIZE_T n;
    return ReadProcessMemory(proc, (LPCVOID)addr, out, 8, &n) && n == 8;
}

static int rpm4f(HANDLE proc, uintptr_t addr, float *out)
{
    SIZE_T n;
    return ReadProcessMemory(proc, (LPCVOID)addr, out, 4, &n) && n == 4;
}

static int rpm(HANDLE proc, uintptr_t addr, void *out, size_t len)
{
    SIZE_T n;
    return ReadProcessMemory(proc, (LPCVOID)addr, out, len, &n) && n == len;
}

static void wpm4f(HANDLE proc, uintptr_t addr, float val)
{
    SIZE_T n; DWORD old;
    VirtualProtectEx(proc, (LPVOID)addr, 4, PAGE_EXECUTE_READWRITE, &old);
    WriteProcessMemory(proc, (LPVOID)addr, &val, 4, &n);
    VirtualProtectEx(proc, (LPVOID)addr, 4, old, &old);
}

/* Module-relative offset of the struct pointer. Defaults to the hardcoded
 * value; replaced at startup by the AOB scan if it succeeds. */
static uintptr_t g_struct_ptr = STRUCT_PTR;

/*
 * AOB (array-of-bytes) signature scan over the module's executable image.
 * mask: 'x' = byte must match pat, '?' = wildcard. Returns the VA of the first
 * match, or 0. Lets us locate code by its (stable) opcodes instead of hardcoding
 * data addresses that move every game update.
 */
static uintptr_t aob_scan(HANDLE proc, uintptr_t base,
                          const uint8_t *pat, const char *mask, size_t len)
{
    MEMORY_BASIC_INFORMATION mbi;
    uint8_t *buf = NULL; size_t cap = 0;
    uintptr_t addr = base, found = 0;

    while (!found && VirtualQueryEx(proc, (LPCVOID)addr, &mbi, sizeof(mbi)) == sizeof(mbi)) {
        if (mbi.State == MEM_COMMIT && mbi.Type == MEM_IMAGE &&
            (uintptr_t)mbi.AllocationBase == base &&
            (mbi.Protect & (PAGE_EXECUTE | PAGE_EXECUTE_READ |
                            PAGE_EXECUTE_READWRITE | PAGE_EXECUTE_WRITECOPY))) {
            if (mbi.RegionSize > cap) {
                free(buf); buf = (uint8_t *)malloc(mbi.RegionSize);
                cap = buf ? mbi.RegionSize : 0;
            }
            SIZE_T n;
            if (buf && ReadProcessMemory(proc, mbi.BaseAddress, buf, mbi.RegionSize, &n)) {
                for (size_t i = 0; i + len <= n; i++) {
                    size_t j = 0;
                    while (j < len && (mask[j] == '?' || buf[i + j] == pat[j])) j++;
                    if (j == len) { found = (uintptr_t)mbi.BaseAddress + i; break; }
                }
            }
        }
        uintptr_t next = (uintptr_t)mbi.BaseAddress + mbi.RegionSize;
        if (next <= addr) break;
        addr = next;
    }
    free(buf);
    return found;
}

/*
 * Resolve the RIP-relative target of an instruction located by an AOB match.
 *   sig_at    - address the signature matched
 *   instr_off - offset of the target instruction within the signature
 *   instr_len - full length of that instruction
 *   disp_off  - offset of the rel32 displacement within the instruction
 * Returns the absolute target VA, or 0 on read failure. (x64 RIP-relative: the
 * displacement is signed and relative to the address of the NEXT instruction.)
 */
static uintptr_t rip_target(HANDLE proc, uintptr_t sig_at,
                            size_t instr_off, size_t instr_len, size_t disp_off)
{
    uintptr_t instr = sig_at + instr_off;
    int32_t disp; SIZE_T n;
    if (!ReadProcessMemory(proc, (LPCVOID)(instr + disp_off), &disp, 4, &n) || n != 4)
        return 0;
    return instr + instr_len + (intptr_t)disp;
}

/*
 * Locate the struct-pointer load and read its RIP-relative displacement to
 * compute STRUCT_PTR for the running build. Anchor:
 *   48 8B 05 ?? ?? ?? ??   mov rax,[rip+disp]   ; loads the struct pointer
 *   8B 80 58 0D 00 00      mov eax,[rax+0xD58]  ; yellow offset (makes it unique)
 * Returns the module-relative offset, or 0 if not found.
 */
static uintptr_t resolve_struct_ptr(HANDLE proc, uintptr_t base)
{
    static const uint8_t pat[]  = {0x48,0x8B,0x05,0,0,0,0,0x8B,0x80,0x58,0x0D,0x00,0x00};
    static const char    mask[] = "xxx????xxxxxx";
    uintptr_t at = aob_scan(proc, base, pat, mask, sizeof(pat));
    if (!at) return 0;

    /* the mov rax,[rip+disp] is at the start of the match: 7 bytes, rel32 @ +3 */
    uintptr_t target = rip_target(proc, at, 0, 7, 3);
    if (!target) return 0;
    return target - base;                         /* module-relative offset */
}

static uintptr_t get_struct(HANDLE proc, uintptr_t base)
{
    uint64_t ptr = 0;
    if (!rpm8(proc, base + g_struct_ptr, &ptr) || !ptr) return 0;
    return (uintptr_t)ptr;
}

/*
 * Amplify the game's own natural regen for one bar.
 *  *old   tracks the value we last observed/wrote (-1 = uninitialised).
 *  mult   0 = off, LOCK = lock to max, else multiplier on natural increase.
 * Returns the value the bar should now hold (or -1 if unreadable).
 *
 * Only acts when the game raised the bar since last tick (cur > *old). Drain or
 * no-change just resyncs *old, so we never fight damage and never move a bar the
 * game isn't already regenerating — which is what makes it pause-safe.
 */
static float amplify(HANDLE proc, uintptr_t addr, float *old, float mult, float max)
{
    float cur;
    if (!rpm4f(proc, addr, &cur)) return -1.0f;

    if (mult == LOCK) {
        if (cur < max) { wpm4f(proc, addr, max); cur = max; }
        *old = cur;
        return cur;
    }

    if (*old < 0.0f) { *old = cur; return cur; }   /* first observation */

    if (mult != 0.0f && cur > *old && cur < max) {
        float boosted = *old + (cur - *old) * mult;
        if (boosted > max) boosted = max;
        wpm4f(proc, addr, boosted);
        cur = boosted;
    }
    *old = cur;
    return cur;
}

/* ── Menu helper ───────────────────────────────────────────────────────── */

static int pick(const char *title, const char **labels, int n)
{
    printf("\n%s\n", title);
    for (int i = 0; i < n; i++)
        printf("  %d - %s\n", i + 1, labels[i]);
    printf("Choice: "); fflush(stdout);
    for (;;) {
        int c = getchar();
        if (c == EOF) return -1;
        if (c >= '1' && c < '1' + n) return c - '1';
    }
}

/* ── Entry point ───────────────────────────────────────────────────────── */

int main(void)
{
    printf("=== Exanima Heal Trainer ===\n");
    printf("Looking for Exanima.exe...\n");

    uintptr_t base;
    HANDLE proc = find_process("Exanima.exe", &base);
    if (!proc) {
        fprintf(stderr, "Process not found. Is Exanima running?\n");
        printf("Press Enter to exit...\n"); getchar();
        return 1;
    }
    printf("Found! Module base: 0x%llX\n", (unsigned long long)base);

    /* Auto-locate the struct pointer so the trainer survives game updates that
     * shift the static offset. Falls back to the hardcoded value. */
    uintptr_t aob = resolve_struct_ptr(proc, base);
    if (aob) {
        g_struct_ptr = aob;
        printf("Struct pointer located via AOB: module+0x%llX\n\n",
               (unsigned long long)g_struct_ptr);
    } else {
        printf("AOB scan failed — using built-in offset 0x%X "
               "(may be wrong after a game update)\n\n", STRUCT_PTR);
    }

    uintptr_t hs = get_struct(proc, base);
    if (!hs) {
        fprintf(stderr, "Cannot read struct pointer — load a save first.\n");
        getchar(); return 1;
    }

    float cur_yel = 0.0f, cur_red = 0.0f, cur_blu = 0.0f, cur_cap = 0.0f;
    rpm4f(proc, hs + YEL_OFFSET,  &cur_yel);
    rpm4f(proc, hs + RED_OFFSET,  &cur_red);
    rpm4f(proc, hs + BLU_CURRENT, &cur_blu);
    rpm4f(proc, hs + BLU_CAP,     &cur_cap);
    printf("Yellow stamina:    %.4f (max ~%.2f)\n", cur_yel, YEL_MAX);
    printf("Red health:        %.4f (max ~%.2f, 0.0=dead)\n", cur_red, RED_MAX);
    printf("Blue focus:        %.4f\n", cur_blu);
    printf("Blue bar capacity: %.4f\n", cur_cap);

    printf("(Yellow/Blue multiply the game's own regen; Red adds health directly\n");
    printf(" since it doesn't recover naturally. All halt when paused.)\n");

    int yel = pick("Yellow stamina regen:", SPEED_LABELS, N_SPEEDS);
    if (yel < 0) return 0;
    int red = pick("Red health regen:", RED_LABELS, N_RED);
    if (red < 0) return 0;
    int blu = pick("Blue focus regen:", SPEED_LABELS, N_SPEEDS);
    if (blu < 0) return 0;

    static const char *cap_labels[] = {
        "Off (binding spells reduce the bar normally)",
        "Restore (lock capacity to full - binding cost removed)"
    };
    int cap = pick("Blue bar capacity (binding spells):", cap_labels, 2);
    if (cap < 0) return 0;

    printf("\nRunning. Press Ctrl+C to exit.\n");

    /* Per-bar last-observed values for natural-regen amplification */
    float old_yel = -1.0f, old_blu = -1.0f;

    /* Heartbeat state for the additive red regen */
    uint8_t hb[HB_LEN], hb_prev[HB_LEN];
    memset(hb_prev, 0, HB_LEN);
    DWORD last_change = GetTickCount();
    DWORD last_tick   = GetTickCount();

    while (1) {
        hs = get_struct(proc, base);
        if (!hs) { Sleep(200); old_yel = old_blu = -1.0f; continue; }

        /* Yellow — amplify natural regen, mirror result to all three copies */
        if (MULTS[yel] != 0.0f) {
            float v = amplify(proc, hs + YEL_OFFSET, &old_yel, MULTS[yel], YEL_MAX);
            if (v >= 0.0f) {
                wpm4f(proc, hs + YEL_OFFSET2, v);
                wpm4f(proc, hs + YEL_OFFSET3, v);
            }
        }

        /* Blue focus — amplify natural regen */
        if (MULTS[blu] != 0.0f)
            amplify(proc, hs + BLU_CURRENT, &old_blu, MULTS[blu], BLU_MAX);

        /* Red health — additive, gated on the physics heartbeat (pause-safe) */
        if (RED_RATES[red] != 0.0f) {
            DWORD now_tick = GetTickCount();
            float dt = (float)(now_tick - last_tick) / 1000.0f;
            last_tick = now_tick;

            int live = 0;
            if (rpm(proc, hs + HB_OFFSET, hb, HB_LEN)) {
                if (memcmp(hb, hb_prev, HB_LEN) != 0) {
                    memcpy(hb_prev, hb, HB_LEN);
                    last_change = now_tick;
                }
                live = (now_tick - last_change) < HB_STALE_MS;
            }

            float cur;
            if (live && rpm4f(proc, hs + RED_OFFSET, &cur)) {
                if (RED_RATES[red] == LOCK) {
                    if (cur < RED_MAX) wpm4f(proc, hs + RED_OFFSET, RED_MAX);
                } else if (cur < RED_MAX) {
                    float v = cur + RED_RATES[red] * dt;
                    if (v > RED_MAX) v = RED_MAX;
                    wpm4f(proc, hs + RED_OFFSET, v);
                }
            }
        }

        /* Blue capacity — lock exactly to max (clamps binding over/undershoot) */
        if (cap == 1)
            wpm4f(proc, hs + BLU_CAP, BLU_MAX);

        Sleep(POLL_MS);
    }

    CloseHandle(proc);
    return 0;
}
