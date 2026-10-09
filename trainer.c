/* Exanima Heal Trainer (64-bit). Finds the player in memory, then boosts
 * health and focus recovery. Unknown game layouts are never written to. */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <windows.h>
#include <psapi.h>

/* The scan finds the player pointer and a yellow stamina field. The other fields
 * come from a known layout. Zero means we have not confirmed that field. */
typedef struct {
    uint32_t yellow_read, yellow, yellow_copy, yellow_combat;
    uint32_t red, blue, blue_cap, health_max, heartbeat;
    const char *name;
} Layout;

static const Layout layouts[] = {
    {.yellow_read = 0xE80, .yellow = 0xE80, .yellow_copy = 0xE7C,
     .yellow_combat = 0xE68, .red = 0xE6C, .blue = 0xE84,
     .blue_cap = 0xE88, .heartbeat = 0xD58,
     .name = "0.9.5.2c (verified 2026-09-19)"},
    {.yellow_read = 0xD70, .yellow = 0xD58, .red = 0xD5C,
     .blue = 0xD74, .blue_cap = 0xD78, .health_max = 0x103C,
     .heartbeat = 0xC48,
     .name = "reported D58/D74 layout"}
};
static const Layout *g_layout;

#define YEL_MAX   0.25f
#define RED_MAX   0.25f
#define BLU_MAX   1.0f

#define POLL_MS  10

/* Red health needs its own timer. We stop it when the game's physics data
 * stops changing, which happens while the game is paused. */
#define HB_LEN      0x40
#define HB_STALE_MS 250

#define LOCK  (-1.0f)

/* Yellow and blue follow the game's natural recovery. */
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

/* Red has no natural recovery, so these are amounts added per second. */
static const float RED_RATES[] = { 0.0f, 0.25f/600, 0.25f/120, 0.25f/60, 0.25f/30, 0.25f/10, 0.25f/5, LOCK };

static const char *RED_LABELS[] = {
    "Off",
    "Trickle   (~10m to full)",
    "Very slow (~2m to full)",
    "Slow      (~60s to full)",
    "Medium    (~30s to full)",
    "Fast      (~10s to full)",
    "Fastest   (~5s to full)",
    "Lock to max (demigod mode)"
};
#define N_RED 8

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

static int wpm4f(HANDLE proc, uintptr_t addr, float val)
{
    SIZE_T n = 0;
    DWORD old, ignored;
    if (!VirtualProtectEx(proc, (LPVOID)addr, 4, PAGE_READWRITE, &old)) return 0;
    int ok = WriteProcessMemory(proc, (LPVOID)addr, &val, 4, &n) && n == 4;
    VirtualProtectEx(proc, (LPVOID)addr, 4, old, &ignored);
    return ok;
}

static uintptr_t g_player_slot;

typedef struct {
    unsigned code_matches;
    unsigned known_fields;
    unsigned readable_players;
    unsigned valid_players;
    int ambiguous;
} ScanReport;

/* The pointer's address is stored relative to the next instruction. */
static uintptr_t pointer_slot(HANDLE proc, uintptr_t instr)
{
    int32_t distance;
    if (!rpm(proc, instr + 3, &distance, sizeof(distance))) return 0;
    return instr + 7 + (intptr_t)distance;
}

/* Check that the pointer leads to plausible health and focus values. */
static int valid_layout(HANDLE proc, uintptr_t player, const Layout *layout)
{
    MEMORY_BASIC_INFORMATION mbi;
    float y, b, cap, max;
    if (VirtualQueryEx(proc, (LPCVOID)player, &mbi, sizeof(mbi)) != sizeof(mbi) ||
        mbi.State != MEM_COMMIT || mbi.Protect == PAGE_NOACCESS ||
        (mbi.Protect & PAGE_GUARD)) return 0;
    if (!rpm4f(proc, player + layout->yellow, &y) ||
        !rpm4f(proc, player + layout->blue, &b) ||
        !rpm4f(proc, player + layout->blue_cap, &cap)) return 0;
    if (!isfinite(y) || y < 0.0f || y > 0.30f ||
        !isfinite(b) || b < 0.0f || b > 1.05f ||
        !isfinite(cap) || cap < 0.0f || cap > 1.05f || b > cap + 0.05f)
        return 0;
    if (layout->health_max) {
        if (!rpm4f(proc, player + layout->health_max, &max) ||
            !isfinite(max) || max < 0.20f || max > 0.30f) return 0;
    }
    if (layout->red) {
        if (!rpm4f(proc, player + layout->red, &max) ||
            !isfinite(max) || max < 0.0f || max > 0.30f) return 0;
    }
    return 1;
}

/* Check one matching instruction against the known layouts. */
static int consider_match(HANDLE proc, uintptr_t base, uintptr_t end, uintptr_t at,
                          uintptr_t *found_slot, const Layout **found_layout,
                          ScanReport *report)
{
    uint32_t field;
    if (!rpm(proc, at + 9, &field, sizeof(field))) return 0;
    const Layout *layout = NULL;
    for (size_t i = 0; i < sizeof(layouts) / sizeof(layouts[0]); i++)
        if (layouts[i].yellow_read == field ||
            layouts[i].yellow == field) { layout = &layouts[i]; break; }
    if (!layout) return 0;
    report->known_fields++;

    uintptr_t slot = pointer_slot(proc, at);
    uint64_t player;
    if (!slot || slot < base || slot >= end || end - slot < sizeof(player) ||
        !rpm8(proc, slot, &player) || !player) return 0;
    report->readable_players++;
    if (!valid_layout(proc, (uintptr_t)player, layout)) return 0;
    report->valid_players++;

    if (*found_slot && (*found_slot != slot || *found_layout != layout)) return -1;
    *found_slot = slot;
    *found_layout = layout;
    return 1;
}

static int resolve_layout(HANDLE proc, uintptr_t base, ScanReport *report)
{
    /* Ignore address and field bytes that change between game builds. */
    static const uint8_t pat[] = {0x48,0x8B,0x05,0,0,0,0,0x8B,0x80,0,0,0,0};
    static const char mask[] = "xxx????xx????";
    MEMORY_BASIC_INFORMATION mbi;
    uint8_t *buf = NULL; size_t cap = 0;
    uintptr_t addr = base, found_slot = 0;
    const Layout *found_layout = NULL;
    memset(report, 0, sizeof(*report));
    MODULEINFO info;
    if (!GetModuleInformation(proc, (HMODULE)base, &info, sizeof(info)) ||
        !info.SizeOfImage) return 0;
    uintptr_t end = base + info.SizeOfImage;
    if (end < base) return 0;

    while (addr < end &&
           VirtualQueryEx(proc, (LPCVOID)addr, &mbi, sizeof(mbi)) == sizeof(mbi)) {
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
                for (size_t i = 0; i + sizeof(pat) <= n; i++) {
                    size_t j = 0;
                    while (j < sizeof(pat) && (mask[j] == '?' || buf[i + j] == pat[j])) j++;
                    if (j == sizeof(pat)) {
                        report->code_matches++;
                        if (consider_match(proc, base, end,
                                           (uintptr_t)mbi.BaseAddress + i,
                                           &found_slot, &found_layout, report) < 0)
                            report->ambiguous = 1;
                    }
                }
            }
        }
        uintptr_t next = (uintptr_t)mbi.BaseAddress + mbi.RegionSize;
        if (next <= addr) break;
        addr = next;
    }
    free(buf);
    if (report->ambiguous || !found_slot) return 0;
    g_player_slot = found_slot - base;
    g_layout = found_layout;
    return 1;
}

static uintptr_t get_player(HANDLE proc, uintptr_t base)
{
    uint64_t ptr = 0;
    if (!rpm8(proc, base + g_player_slot, &ptr) || !ptr) return 0;
    return (uintptr_t)ptr;
}

/* Boost only recovery the game already started. Damage and pauses leave the
 * bar alone. Return -1 if it cannot be read. */
static float amplify(HANDLE proc, uintptr_t addr, float *old, float mult, float max)
{
    float cur;
    if (!rpm4f(proc, addr, &cur)) return -1.0f;

    if (mult == LOCK) {
        if (cur < max && wpm4f(proc, addr, max)) cur = max;
        *old = cur;
        return cur;
    }

    if (*old < 0.0f) { *old = cur; return cur; }

    if (mult != 0.0f && cur > *old && cur < max) {
        float boosted = *old + (cur - *old) * mult;
        if (boosted > max) boosted = max;
        if (wpm4f(proc, addr, boosted)) cur = boosted;
    }
    *old = cur;
    return cur;
}

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

static int startup_error(HANDLE proc, const char *message)
{
    fprintf(stderr, "\n%s\n", message);
    if (proc) CloseHandle(proc);
    printf("Press Enter to close...\n");
    fflush(stdout);
    getchar();
    return 1;
}

int main(void)
{
    printf("=== Exanima Heal Trainer ===\n");
    printf("Looking for Exanima.exe...\n");

    uintptr_t base;
    HANDLE proc = find_process("Exanima.exe", &base);
    if (!proc) return startup_error(NULL, "Exanima.exe was not found. Start the game and load a save first.");
    printf("Found! Module base: 0x%llX\n", (unsigned long long)base);

    ScanReport scan;
    if (!resolve_layout(proc, base, &scan)) {
        const char *reason = scan.ambiguous ? "More than one player matched." :
            !scan.code_matches ? "The game code no longer matches the scan." :
            !scan.known_fields ? "The health offsets have moved." :
            !scan.readable_players ? "The player pointer could not be read. Load a save first." :
            "The health values did not match a known layout.";
        char message[512];
        snprintf(message, sizeof(message),
                 "%s\nScan: %u code matches, %u known fields, %u readable players, %u valid players.",
                 reason, scan.code_matches, scan.known_fields,
                 scan.readable_players, scan.valid_players);
        return startup_error(proc, message);
    }
    printf("Player pointer: module+0x%llX; layout: %s\n",
           (unsigned long long)g_player_slot, g_layout->name);

    uintptr_t player = get_player(proc, base);
    if (!player) return startup_error(proc, "Cannot read the player pointer. Load a save first.");

    float cur_yel = 0.0f, cur_red = 0.0f, cur_blu = 0.0f, cur_cap = 0.0f;
    rpm4f(proc, player + g_layout->yellow, &cur_yel);
    if (g_layout->red) rpm4f(proc, player + g_layout->red, &cur_red);
    rpm4f(proc, player + g_layout->blue, &cur_blu);
    rpm4f(proc, player + g_layout->blue_cap, &cur_cap);
    printf("Yellow stamina:    %.4f (max ~%.2f)\n", cur_yel, YEL_MAX);
    if (g_layout->red) printf("Red health:        %.4f (max ~%.2f, 0.0=dead)\n", cur_red, RED_MAX);
    else printf("Red health:        not ready for this game version\n");
    printf("Blue focus:        %.4f\n", cur_blu);
    printf("Blue bar capacity: %.4f\n", cur_cap);

    printf("(Yellow/Blue multiply the game's own regen. ");
    if (g_layout->red) printf("Red adds health directly. ");
    printf("Natural regen halts when paused.)\n");

    if (!g_layout->yellow_combat)
        printf("Yellow lock is off until the combat value is confirmed.\n");
    int yel = pick("Yellow stamina regen:", SPEED_LABELS,
                   g_layout->yellow_combat ? N_SPEEDS : N_SPEEDS - 1);
    if (yel < 0) return 0;
    int red = 0;
    if (g_layout->red && g_layout->heartbeat) {
        red = pick("Red health regen:", RED_LABELS, N_RED);
        if (red < 0) return 0;
    }
    int blu = pick("Blue focus regen:", SPEED_LABELS, N_SPEEDS);
    if (blu < 0) return 0;

    static const char *cap_labels[] = {
        "Off (binding spells reduce the bar normally)",
        "Restore (lock capacity to full - binding cost removed)"
    };
    int cap = pick("Blue bar capacity (binding spells):", cap_labels, 2);
    if (cap < 0) return 0;

    printf("\nRunning. Press Ctrl+C to exit.\n");

    float old_yel = -1.0f, old_blu = -1.0f;

    uint8_t hb[HB_LEN], hb_prev[HB_LEN];
    int have_hb = 0, seen_change = 0;
    DWORD last_change = GetTickCount();
    DWORD last_tick   = GetTickCount();
    uintptr_t previous_player = player;

    while (1) {
        player = get_player(proc, base);
        if (!player || !valid_layout(proc, player, g_layout)) {
            Sleep(200); old_yel = old_blu = -1.0f; previous_player = 0; continue;
        }
        if (player != previous_player) {
            old_yel = old_blu = -1.0f;
            have_hb = seen_change = 0;
            last_change = last_tick = GetTickCount();
            previous_player = player;
        }

        if (MULTS[yel] != 0.0f) {
            float v = amplify(proc, player + g_layout->yellow, &old_yel, MULTS[yel], YEL_MAX);
            if (v >= 0.0f) {
                if (g_layout->yellow_copy) wpm4f(proc, player + g_layout->yellow_copy, v);
                if (g_layout->yellow_combat) wpm4f(proc, player + g_layout->yellow_combat, v);
            }
        }

        if (MULTS[blu] != 0.0f)
            amplify(proc, player + g_layout->blue, &old_blu, MULTS[blu], BLU_MAX);

        if (RED_RATES[red] != 0.0f) {
            DWORD now_tick = GetTickCount();
            float dt = (float)(now_tick - last_tick) / 1000.0f;
            last_tick = now_tick;

            int live = 0;
            if (rpm(proc, player + g_layout->heartbeat, hb, HB_LEN)) {
                if (!have_hb) {
                    memcpy(hb_prev, hb, HB_LEN);
                    have_hb = 1;
                } else if (memcmp(hb, hb_prev, HB_LEN) != 0) {
                    memcpy(hb_prev, hb, HB_LEN);
                    last_change = now_tick;
                    seen_change = 1;
                }
                live = seen_change && (now_tick - last_change) < HB_STALE_MS;
            }

            float cur;
            if (live && rpm4f(proc, player + g_layout->red, &cur)) {
                if (RED_RATES[red] == LOCK) {
                    if (cur < RED_MAX) wpm4f(proc, player + g_layout->red, RED_MAX);
                } else if (cur < RED_MAX) {
                    float v = cur + RED_RATES[red] * dt;
                    if (v > RED_MAX) v = RED_MAX;
                    wpm4f(proc, player + g_layout->red, v);
                }
            }
        }

        if (cap == 1)
            wpm4f(proc, player + g_layout->blue_cap, BLU_MAX);

        Sleep(POLL_MS);
    }

    CloseHandle(proc);
    return 0;
}
