// Reduced FTO (one centre orbit + 11 edges, "B U" edge fixed) -- complete disk-based BFS.
//
// Architecture follows the Puppet SSD BFS: a two-bit distance-mod-3 table split into sector
// files, destination-owned updates, symmetry-reduced sectors, durable per-sector commits and
// layer manifests.  Puzzle model:
//   * The fixed-edge puzzle is lifted to the physical one: 12 centre slots, 12 edge slots
//     (slot 11 = the B U edge) and the eight plain face turns.  A state of the fixed-edge
//     puzzle is a physical configuration modulo the 12 whole-puzzle rotations.
//   * K = rotations (12) x piece relabelings (12) x mirror (2) = 288 acts on configurations;
//     K-orbits are exactly the classes of fixed-edge states under the puzzle's 24 symmetries.
//   * Sector = K-class of the centre arrangement (369600 arrangements -> NCLASS classes).
//     Entry  = even permutation of the 12 edges (12!/2 = 239,500,800), two bits each.
//   * Each marked entry of a sector whose representative has stabiliser size k stands for
//     24/k ... precisely: (entries * 24) / k fixed-edge states.
// Convention: applying a move m to an array gives new[i] = old[m[i]].
#define NOMINMAX
#include <windows.h>
#include <immintrin.h>
#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <mutex>
#include <random>
#include <string>
#include <thread>
#include <vector>
#include <array>
#include <set>

typedef uint8_t u8; typedef uint16_t u16; typedef uint32_t u32; typedef uint64_t u64;

[[noreturn]] static void die(const char* fmt, ...) {
    va_list ap; va_start(ap, fmt); fprintf(stderr, "ERROR: "); vfprintf(stderr, fmt, ap); fprintf(stderr, "\n"); va_end(ap);
    fflush(stderr); exit(2);
}
#define CHECK(c) do { if (!(c)) die("check failed: %s (line %d)", #c, __LINE__); } while (0)

// ------------------------------------------------------------------ definition file (verbatim)
static const char* DEF_NAMES[8] = {"F", "Fw", "D", "Dw", "L", "BR", "BL", "R"};
static const u8 DEF_C[8][12] = {
    {6,1,3,4,5,2,7,8,9,10,11,12}, {6,1,3,5,10,2,7,8,9,4,11,12}, {1,4,3,7,6,8,2,5,9,10,11,12}, {9,4,1,7,6,8,2,5,3,10,11,12},
    {11,2,3,1,5,10,7,8,6,9,4,12}, {1,2,5,4,7,6,3,8,9,10,11,12}, {1,2,3,9,5,6,7,4,8,10,11,12}, {5,3,10,4,12,6,7,8,9,2,11,1}};
static const u8 DEF_E[8][11] = {
    {6,1,3,4,5,2,7,8,9,10,11}, {6,1,3,5,10,2,11,8,7,4,9}, {1,4,3,7,5,6,2,8,9,10,11}, {9,4,1,7,6,8,2,5,3,10,11},
    {1,2,3,4,5,10,7,8,6,9,11}, {1,2,5,4,7,6,3,8,9,10,11}, {1,2,3,9,5,6,7,4,8,10,11}, {5,2,3,4,11,6,7,8,9,10,1}};
static const u8 SOLVED_COL[12] = {0,0,1,2,1,0,1,2,2,3,3,3};

// ------------------------------------------------------------------ physical model (derive.py)
struct P24 { u8 c[12], e[12]; };
static const char* FACE_NAMES[8] = {"F", "B", "D", "U", "L", "BR", "BL", "R"};
static const P24 FACE[8] = {
    {{5,0,2,3,4,1,6,7,8,9,10,11}, {5,0,2,3,4,1,6,7,8,9,10,11}},
    {{0,1,7,3,4,5,8,10,11,9,2,6}, {0,1,7,3,4,5,6,11,8,9,10,2}},
    {{0,3,2,6,5,7,1,4,8,9,10,11}, {0,3,2,6,4,5,1,7,8,9,10,11}},
    {{0,1,2,3,4,5,6,7,8,11,9,10}, {0,1,2,3,4,5,6,7,8,10,11,9}},
    {{10,1,2,0,4,9,6,7,5,8,3,11}, {0,1,2,3,4,9,6,7,5,8,10,11}},
    {{0,1,4,3,6,5,2,7,8,9,10,11}, {0,1,4,3,6,5,2,7,8,9,10,11}},
    {{0,1,2,8,4,5,6,3,7,9,10,11}, {0,1,2,8,4,5,6,3,7,9,10,11}},
    {{4,2,9,3,11,5,6,7,8,1,10,0}, {4,1,2,3,10,5,6,7,8,9,0,11}}};
static const P24 ROTGEN[2] = {
    {{8,3,0,6,5,7,1,4,2,10,11,9}, {8,3,0,6,5,7,1,4,2,11,9,10}},
    {{5,0,10,4,9,1,11,2,6,3,7,8}, {5,0,11,4,9,1,10,2,6,3,8,7}}};
static const P24 MIRROR = {{0,5,8,4,3,1,7,6,2,9,11,10}, {5,1,7,6,8,0,3,2,4,10,9,11}};

// A symmetry / move in pull form:  cc'[i] = col[cc[sc[i]]],  p'[i] = rp[p[se[i]]]
struct Sym {
    u8 sc[12], se[12], col[4], rp[12];
    bool operator<(const Sym& o) const { return memcmp(this, &o, sizeof(Sym)) < 0; }
    bool operator==(const Sym& o) const { return memcmp(this, &o, sizeof(Sym)) == 0; }
};
static Sym symId() { Sym s; for (int i = 0; i < 12; i++) s.sc[i] = s.se[i] = s.rp[i] = (u8)i; for (int i = 0; i < 4; i++) s.col[i] = (u8)i; return s; }
static Sym compose(const Sym& a, const Sym& b) {  // a then b
    Sym r;
    for (int i = 0; i < 12; i++) { r.sc[i] = a.sc[b.sc[i]]; r.se[i] = a.se[b.se[i]]; r.rp[i] = b.rp[a.rp[i]]; }
    for (int i = 0; i < 4; i++) r.col[i] = b.col[a.col[i]];
    return r;
}
static Sym inverse(const Sym& a) {
    Sym r;
    for (int i = 0; i < 12; i++) { r.sc[a.sc[i]] = (u8)i; r.se[a.se[i]] = (u8)i; r.rp[a.rp[i]] = (u8)i; }
    for (int i = 0; i < 4; i++) r.col[a.col[i]] = (u8)i;
    return r;
}
static Sym slotSym(const P24& p) { Sym s = symId(); memcpy(s.sc, p.c, 12); memcpy(s.se, p.e, 12); return s; }
static Sym relabelSym(const P24& t) {
    Sym s = symId(); int seen[4] = {-1, -1, -1, -1};
    for (int i = 0; i < 12; i++) {
        int a = SOLVED_COL[i], b = SOLVED_COL[t.c[i]];
        CHECK(seen[a] < 0 || seen[a] == b); seen[a] = b; s.col[a] = (u8)b; s.rp[i] = t.e[i];
    }
    return s;
}
static Sym mirrorSym() {
    Sym s = symId();
    for (int i = 0; i < 12; i++) { s.sc[MIRROR.c[i]] = (u8)i; s.se[MIRROR.e[i]] = (u8)i; s.rp[i] = MIRROR.e[i]; s.col[SOLVED_COL[i]] = SOLVED_COL[MIRROR.c[i]]; }
    return s;
}
struct Config { u8 cc[12]; u8 p[12]; };
static Config applySym(const Sym& s, const Config& x) {
    Config r;
    for (int i = 0; i < 12; i++) { r.cc[i] = s.col[x.cc[s.sc[i]]]; r.p[i] = s.rp[x.p[s.se[i]]]; }
    return r;
}
static u32 packC(const u8* cc) { u32 v = 0; for (int i = 0; i < 12; i++) v |= (u32)cc[i] << (2 * i); return v; }
static void unpackC(u32 v, u8* cc) { for (int i = 0; i < 12; i++) cc[i] = (v >> (2 * i)) & 3; }

// ------------------------------------------------------------------ edge indexing (A12)
static const u32 CAP = 239500800u;                // 12!/2 entries per sector
static const u32 SECTOR_BYTES = CAP / 4;          // 59,875,200
static const u32 CHUNK = 65536;
static const u32 NCHUNK = (SECTOR_BYTES + CHUNK - 1) / CHUNK;   // 914
static const u32 SECTOR_FILE = NCHUNK * CHUNK;
static const u32 BM_WORDS = CAP / 64;             // exact
static const u32 BM_BYTES = BM_WORDS * 8;
static const u64 TOTAL_STATES = 7376624640000ull; // 12!/3!^4 * 11!/2

static inline u32 rank12(const u8* p) {
    u32 used = 0, idx = 0;
    for (int k = 0; k < 10; k++) {
        u32 v = p[k];
        u32 d = v - (u32)_mm_popcnt_u32(used & ((1u << v) - 1));
        idx = idx * (u32)(12 - k) + d; used |= 1u << v;
    }
    return idx;
}
static u16 LO_TAB[360];
static void initLoTab() {
    for (u32 lo = 0; lo < 360; lo++) {
        u32 d9 = lo % 3, d8 = (lo / 3) % 4, d7 = (lo / 12) % 5, d6 = lo / 60;
        LO_TAB[lo] = (u16)(d6 | d7 << 3 | d8 << 6 | d9 << 8 | ((d6 + d7 + d8 + d9) & 1) << 10);
    }
}
struct Unranker { u32 lastHi = 0xffffffffu, avail = 0, par = 0; u8 pre[6]; };
static inline __m128i unrank12(u32 idx, Unranker& s) {
    u32 hi = idx / 360, lo = idx - hi * 360;
    if (hi != s.lastHi) {
        s.lastHi = hi;
        u32 d[6]; d[5] = hi % 7; hi /= 7; d[4] = hi % 8; hi /= 8; d[3] = hi % 9; hi /= 9; d[2] = hi % 10; hi /= 10; d[1] = hi % 11; d[0] = hi / 11;
        u32 av = 0xFFF, par = 0;
        for (int k = 0; k < 6; k++) { u32 bit = _pdep_u32(1u << d[k], av); s.pre[k] = (u8)_tzcnt_u32(bit); av ^= bit; par += d[k]; }
        s.avail = av; s.par = par & 1;
    }
    alignas(16) u8 p[16] = {0};
    memcpy(p, s.pre, 6);
    u32 t = LO_TAB[lo], av = s.avail, bit;
    bit = _pdep_u32(1u << (t & 7), av); p[6] = (u8)_tzcnt_u32(bit); av ^= bit;
    bit = _pdep_u32(1u << ((t >> 3) & 7), av); p[7] = (u8)_tzcnt_u32(bit); av ^= bit;
    bit = _pdep_u32(1u << ((t >> 6) & 3), av); p[8] = (u8)_tzcnt_u32(bit); av ^= bit;
    bit = _pdep_u32(1u << ((t >> 8) & 3), av); p[9] = (u8)_tzcnt_u32(bit); av ^= bit;
    u32 a = _tzcnt_u32(av), b = _tzcnt_u32(av & (av - 1));
    if ((s.par ^ (t >> 10)) & 1) { p[10] = (u8)b; p[11] = (u8)a; } else { p[10] = (u8)a; p[11] = (u8)b; }
    return _mm_load_si128((const __m128i*)p);
}
// ---- fast path used by the kernels -------------------------------------------------------------
// An index is hi*360+lo: hi fixes the pieces in slots 0..5, lo arranges the other six in slots 6..11.
// For one hi block, `rem` = [6 fixed pieces | 6 remaining pieces ascending]; every entry of the block
// is rem shuffled by LOSHUF[parity][lo].  A pair's slot map L and relabel R fold into the tables, so
// mapping an entry costs one byte shuffle plus a rank.
static __m128i LOSHUF[2][360];
static void initLoShuf() {
    for (int par = 0; par < 2; par++) for (u32 lo = 0; lo < 360; lo++) {
        u32 t = LO_TAB[lo], d[4] = {t & 7, (t >> 3) & 7, (t >> 6) & 3, (t >> 8) & 3};
        alignas(16) u8 s[16]; for (int i = 0; i < 6; i++) s[i] = (u8)i; for (int i = 12; i < 16; i++) s[i] = 0x80;
        u8 pool[6] = {0, 1, 2, 3, 4, 5}; int n = 6;
        for (int k = 0; k < 4; k++) { s[6 + k] = (u8)(6 + pool[d[k]]); for (int j = d[k]; j < n - 1; j++) pool[j] = pool[j + 1]; n--; }
        if ((par ^ (t >> 10)) & 1) { s[10] = (u8)(6 + pool[1]); s[11] = (u8)(6 + pool[0]); } else { s[10] = (u8)(6 + pool[0]); s[11] = (u8)(6 + pool[1]); }
        LOSHUF[par][lo] = _mm_load_si128((const __m128i*)s);
    }
}
struct PairTab { __m128i SL[2][360]; __m128i R; };
static void buildPairTab(PairTab& pt, const u8* L16, const u8* R16) {
    const __m128i L = _mm_loadu_si128((const __m128i*)L16); pt.R = _mm_loadu_si128((const __m128i*)R16);
    for (int par = 0; par < 2; par++) for (int lo = 0; lo < 360; lo++) pt.SL[par][lo] = _mm_shuffle_epi8(LOSHUF[par][lo], L);
}
// per-block setup: relabelled rem vector and parity of the hi digits
static inline __m128i blockRem(u32 hi, const __m128i R, u32& par) {
    u32 d[6]; d[5] = hi % 7; hi /= 7; d[4] = hi % 8; hi /= 8; d[3] = hi % 9; hi /= 9; d[2] = hi % 10; hi /= 10; d[1] = hi % 11; d[0] = hi / 11;
    alignas(16) u8 t[16] = {0}; u32 av = 0xFFF, ps = 0;
    for (int k = 0; k < 6; k++) { u32 bit = _pdep_u32(1u << d[k], av); t[k] = (u8)_tzcnt_u32(bit); av ^= bit; ps += d[k]; }
    for (int k = 6; k < 12; k++) { t[k] = (u8)_tzcnt_u32(av); av &= av - 1; }
    par = ps & 1;
    return _mm_shuffle_epi8(R, _mm_load_si128((const __m128i*)t));
}
static inline u32 rank12f(const u8* p) {
    static const u32 W[10] = {19958400, 1814400, 181440, 20160, 2520, 360, 60, 12, 3, 1};
    u32 used = 0, a = 0, b = 0;
    for (int k = 0; k < 10; k += 2) {
        u32 v0 = p[k], v1 = p[k + 1];
        u32 u1 = used | (1u << v0);
        a += (v0 - (u32)_mm_popcnt_u32(used & ((1u << v0) - 1))) * W[k];
        b += (v1 - (u32)_mm_popcnt_u32(u1 & ((1u << v1) - 1))) * W[k + 1];
        used = u1 | (1u << v1);
    }
    return a + b;
}
static void unrankTo(u32 idx, u8* out12) { Unranker u; alignas(16) u8 t[16]; _mm_store_si128((__m128i*)t, unrank12(idx, u)); memcpy(out12, t, 12); }

// ------------------------------------------------------------------ model tables
static Sym MOVE[16];                 // 0..7 face turns, 8..15 their inverses
static std::vector<Sym> K;           // 288
static std::vector<int> ROTS;        // indices in K of the 12 pure rotations
static u32 NCLASS = 0;
static std::vector<u32> REP;         // packed representative centre arrangement per class
static std::vector<u32> STAB;        // stabiliser size in K
struct Pair { u32 src; u8 L[16]; u8 R[16]; };
static std::vector<Pair> PAIRS;      // NCLASS*16: dest class D, move m
static std::map<u32, std::pair<u32, u32>> CENTRE;   // packed arrangement -> (class, K index with K[k]*rep = arrangement)

static std::vector<int> SYM24;       // one K element per distinct relabeling: the 24 symmetries of fixed-edge states
static void buildModel() {
    initLoTab(); initLoShuf();
    for (int i = 0; i < 8; i++) { MOVE[i] = slotSym(FACE[i]); MOVE[i + 8] = inverse(MOVE[i]); CHECK(compose(compose(MOVE[i], MOVE[i]), MOVE[i]) == symId()); }
    std::vector<Sym> gens = {slotSym(ROTGEN[0]), slotSym(ROTGEN[1]), relabelSym(ROTGEN[0]), relabelSym(ROTGEN[1]), mirrorSym()};
    std::set<Sym> seen; seen.insert(symId()); K.push_back(symId());
    for (size_t i = 0; i < K.size(); i++) for (auto& g : gens) { Sym y = compose(K[i], g); if (seen.insert(y).second) { K.push_back(y); CHECK(K.size() <= 288); } }
    CHECK(K.size() == 288);
    Sym id = symId();
    for (int i = 0; i < 288; i++) if (!memcmp(K[i].col, id.col, 4) && !memcmp(K[i].rp, id.rp, 12)) ROTS.push_back(i);
    CHECK(ROTS.size() == 12);
    { std::set<std::array<u8, 16>> lab; for (int i = 0; i < 288; i++) { std::array<u8, 16> a; memcpy(a.data(), K[i].col, 4); memcpy(a.data() + 4, K[i].rp, 12); if (lab.insert(a).second) SYM24.push_back(i); } }
    CHECK(SYM24.size() == 24);
    // every K element is a graph automorphism: conjugation permutes the 16 moves; and it preserves the solved set
    Config solved; memcpy(solved.cc, SOLVED_COL, 12); for (int i = 0; i < 12; i++) solved.p[i] = (u8)i;
    std::set<std::pair<u32, u32>> solvedSet;
    for (int r : ROTS) { Config c = applySym(K[r], solved); solvedSet.insert({packC(c.cc), rank12(c.p)}); }
    CHECK(solvedSet.size() == 12);
    for (auto& k : K) {
        Sym ki = inverse(k);
        for (int m = 0; m < 16; m++) { Sym c = compose(compose(ki, MOVE[m]), k); bool f = false; for (int j = 0; j < 16; j++) f |= (c == MOVE[j]); CHECK(f); }
        Config c = applySym(k, solved); CHECK(solvedSet.count({packC(c.cc), rank12(c.p)}));
    }
    // centre classes
    std::vector<u32> all; u8 cc[12]; int left[4] = {3, 3, 3, 3};
    auto rec = [&](auto&& self, int i) -> void {
        if (i == 12) { all.push_back(packC(cc)); return; }
        for (int c = 0; c < 4; c++) if (left[c]) { left[c]--; cc[i] = (u8)c; self(self, i + 1); left[c]++; }
    };
    rec(rec, 0);
    CHECK(all.size() == 369600);
    std::sort(all.begin(), all.end());
    for (u32 a : all) {
        if (CENTRE.count(a)) continue;
        u32 cls = NCLASS++; REP.push_back(a); u32 orbit = 0;
        Config x; unpackC(a, x.cc); memset(x.p, 0, 12);
        for (u32 k = 0; k < 288; k++) { Config y = applySym(K[k], x); if (CENTRE.insert({packC(y.cc), {cls, k}}).second) orbit++; }
        CHECK(288 % orbit == 0); STAB.push_back(288 / orbit);
    }
    CHECK(CENTRE.size() == 369600);
    u64 tot = 0; for (u32 c = 0; c < NCLASS; c++) { CHECK(((u64)CAP * 24) % STAB[c] == 0); tot += (u64)CAP * 24 / STAB[c]; }
    CHECK(tot == TOTAL_STATES);
    // pair table
    PAIRS.resize((size_t)NCLASS * 16);
    for (u32 D = 0; D < NCLASS; D++) for (int m = 0; m < 16; m++) {
        Config c0; unpackC(REP[D], c0.cc); memset(c0.p, 0, 12);
        Config cs = applySym(MOVE[m ^ 8], c0);                       // undo m
        Config back = applySym(MOVE[m], cs); CHECK(packC(back.cc) == REP[D]);
        auto [r, k] = CENTRE.at(packC(cs.cc));
        Pair& pr = PAIRS[(size_t)D * 16 + m]; pr.src = r; memset(pr.L, 0x80, 16); memset(pr.R, 0, 16);
        for (int i = 0; i < 12; i++) { pr.L[i] = K[k].se[MOVE[m].se[i]]; pr.R[i] = K[k].rp[i]; }
    }
}
static u64 hashBytes(const void* data, size_t n) {
    const u8* p = (const u8*)data; u64 h = 0x9E3779B97F4A7C15ull ^ n; size_t i = 0;
    for (; i + 8 <= n; i += 8) { u64 w; memcpy(&w, p + i, 8); h = (h ^ w) * 0xff51afd7ed558ccdULL; h = (h << 29) | (h >> 35); }
    for (; i < n; i++) { h = (h ^ p[i]) * 0x100000001b3ull; }
    return h ^ (h >> 31);
}
static u64 modelFingerprint() {
    u64 h = hashBytes(PAIRS.data(), PAIRS.size() * sizeof(Pair));
    h ^= hashBytes(REP.data(), REP.size() * 4) * 3; h ^= hashBytes(STAB.data(), STAB.size() * 4) * 5;
    return h + 2;   // + on-disk format version
}
// bring the B U edge piece (11) back to slot 11 by a whole-puzzle rotation -> fixed-edge state
static Config normalize(const Config& x) {
    int j = 0; while (x.p[j] != 11) j++;
    for (int r : ROTS) if (K[r].se[11] == j) return applySym(K[r], x);
    die("normalize");
}
static u64 packState(const Config& n) {   // normalised state -> 64-bit key (centres 24 bits + edges 0..9, 4 bits each)
    u64 v = packC(n.cc); for (int i = 0; i < 10; i++) v |= (u64)n.p[i] << (24 + 4 * i); return v;
}
static void printState(FILE* f, const Config& n) {
    for (int i = 0; i < 12; i++) fprintf(f, "%d ", n.cc[i] + 1);
    fprintf(f, "/");
    for (int i = 0; i < 11; i++) fprintf(f, " %d", n.p[i] + 1);
    fprintf(f, "\n");
}

// ------------------------------------------------------------------ independent reference BFS
// Uses only the definition-file tables (fixed-edge model, 8 moves and their squares).
static u32 rank11(const u8* p) { u32 idx = 0; for (int i = 0; i < 11; i++) { u32 d = 0; for (int j = i + 1; j < 11; j++) d += p[j] < p[i]; idx = idx * (11 - i) + d; } return idx; }
static void unrank11(u32 idx, u8* p) {
    u8 d[11]; for (int i = 10; i >= 0; i--) { d[i] = idx % (11 - i); idx /= (11 - i); }
    u8 pool[11]; for (int i = 0; i < 11; i++) pool[i] = (u8)i;
    for (int i = 0; i < 11; i++) { p[i] = pool[d[i]]; for (int j = d[i]; j < 10 - i; j++) pool[j] = pool[j + 1]; }
}
static std::vector<u64> refBfs(int maxDepth) {
    auto apply = [](u64 key, int m, int times) {
        u8 cc[12], e[11], t[12]; unpackC((u32)(key >> 26), cc); unrank11((u32)(key & ((1u << 26) - 1)), e);
        for (int r = 0; r < times; r++) {
            for (int i = 0; i < 12; i++) t[i] = cc[DEF_C[m][i] - 1]; memcpy(cc, t, 12);
            for (int i = 0; i < 11; i++) t[i] = e[DEF_E[m][i] - 1]; memcpy(e, t, 11);
        }
        return ((u64)packC(cc) << 26) | rank11(e);
    };
    u8 e0[11]; for (int i = 0; i < 11; i++) e0[i] = (u8)i;
    std::vector<u64> prev, cur = {((u64)packC(SOLVED_COL) << 26) | rank11(e0)}, counts = {1};
    for (int d = 1; d <= maxDepth; d++) {
        std::vector<u64> next;
        const size_t CH = 2000000;
        for (size_t lo = 0; lo < cur.size(); lo += CH) {
            size_t hi = std::min(cur.size(), lo + CH);
            std::vector<u64> cand; cand.reserve((hi - lo) * 16);
            for (size_t i = lo; i < hi; i++) for (int m = 0; m < 8; m++) { cand.push_back(apply(cur[i], m, 1)); cand.push_back(apply(cur[i], m, 2)); }
            std::sort(cand.begin(), cand.end()); cand.erase(std::unique(cand.begin(), cand.end()), cand.end());
            std::vector<u64> a, b;
            std::set_difference(cand.begin(), cand.end(), cur.begin(), cur.end(), std::back_inserter(a));
            std::set_difference(a.begin(), a.end(), prev.begin(), prev.end(), std::back_inserter(b));
            std::vector<u64> merged; merged.reserve(next.size() + b.size());
            std::set_union(next.begin(), next.end(), b.begin(), b.end(), std::back_inserter(merged));
            next.swap(merged);
        }
        counts.push_back(next.size());
        // direct symmetry check: each of the 24 maps (relabel pieces and colours, turn the puzzle so the
        // B U piece is home again) must send every depth-d state to a state that is also at depth d
        std::atomic<u64> missing{0}, moved{0}; std::vector<std::thread> th; const int NT = 24;
        for (int t = 0; t < NT; t++) th.emplace_back([&, t]() {
            u64 miss = 0, mv = 0;
            for (size_t i = t; i < next.size(); i += NT) {
                Config x; unpackC((u32)(next[i] >> 26), x.cc); unrank11((u32)(next[i] & ((1u << 26) - 1)), x.p); x.p[11] = 11;
                for (int k : SYM24) {
                    Config y = normalize(applySym(K[k], x)); u64 key = ((u64)packC(y.cc) << 26) | rank11(y.p);
                    if (!std::binary_search(next.begin(), next.end(), key)) miss++;
                    if (key != next[i]) mv++;
                }
            }
            missing += miss; moved += mv;
        });
        for (auto& x : th) x.join();
        printf("ref depth %d: %llu positions; 24 symmetry images of each: %llu missing from this depth (%llu of %llu images differ from their source)\n", d,
               (unsigned long long)next.size(), (unsigned long long)missing.load(), (unsigned long long)moved.load(), (unsigned long long)next.size() * 24); fflush(stdout);
        CHECK(missing.load() == 0);
        prev.swap(cur); cur.swap(next);
    }
    return counts;
}

// ------------------------------------------------------------------ files
static std::string DIR;
static std::string pathOf(const char* fmt, ...) { char b[512]; va_list ap; va_start(ap, fmt); vsnprintf(b, sizeof b, fmt, ap); va_end(ap); return DIR + "\\" + b; }
static bool fileExists(const std::string& p) { DWORD a = GetFileAttributesA(p.c_str()); return a != INVALID_FILE_ATTRIBUTES; }
static void writeAtomic(const std::string& path, const std::string& text) {
    std::string tmp = path + ".tmp";
    HANDLE h = CreateFileA(tmp.c_str(), GENERIC_WRITE, 0, 0, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, 0);
    if (h == INVALID_HANDLE_VALUE) die("cannot write %s", tmp.c_str());
    DWORD w; if (!WriteFile(h, text.data(), (DWORD)text.size(), &w, 0) || w != text.size()) die("write %s", tmp.c_str());
    FlushFileBuffers(h); CloseHandle(h);
    if (!MoveFileExA(tmp.c_str(), path.c_str(), MOVEFILE_REPLACE_EXISTING | MOVEFILE_WRITE_THROUGH)) die("rename %s", path.c_str());
}
static void readAt(HANDLE h, u64 off, void* buf, u64 n, const char* what) {
    u8* p = (u8*)buf;
    while (n) {
        OVERLAPPED ov = {}; ov.Offset = (DWORD)off; ov.OffsetHigh = (DWORD)(off >> 32);
        DWORD want = (DWORD)std::min<u64>(n, 1u << 26), got = 0;
        if (!ReadFile(h, p, want, &got, &ov) || got == 0) die("read failed (%s), error %lu", what, GetLastError());
        p += got; off += got; n -= got;
    }
}
static void writeAt(HANDLE h, u64 off, const void* buf, u64 n, const char* what) {
    const u8* p = (const u8*)buf;
    while (n) {
        OVERLAPPED ov = {}; ov.Offset = (DWORD)off; ov.OffsetHigh = (DWORD)(off >> 32);
        DWORD want = (DWORD)std::min<u64>(n, 1u << 26), got = 0;
        if (!WriteFile(h, p, want, &got, &ov) || got == 0) die("write failed (%s), error %lu -- is the drive full?", what, GetLastError());
        p += got; off += got; n -= got;
    }
}
static u64 fileSize(HANDLE h) { LARGE_INTEGER s; GetFileSizeEx(h, &s); return (u64)s.QuadPart; }

// set files -- frontier_NN.bin (entries at depth NN) and unvisited_NN.bin (entries still unvisited after
// depth NN): a sequence of records [4 KiB header block][payload padded to 4 KiB], so that the heavy
// traffic (appends and blob reads) bypasses the Windows file cache.
// payload formats: 0 = sorted u32 list, 1 = bitmap, 2 = gap bytes (gap < 255: one byte, else 255 + u32)
struct RecHdr { u32 magic, sector, fmt, pad; u64 count, bytes, sum; };
static const u32 REC_MAGIC = 0x46544F48;
static const u64 BLK = 4096;
static inline u64 padBlk(u64 n) { return (n + BLK - 1) / BLK * BLK; }
struct Rec { u64 off = 0, bytes = 0, count = 0; u32 fmt = 0; bool present = false; };
struct SetFile {
    char kind = 'f'; int depth = -1; HANDLE h = INVALID_HANDLE_VALUE, hw = INVALID_HANDLE_VALUE; u64 size = 0; std::vector<Rec> idx; std::vector<u8> cache; bool cached = false, open = false;
    void close() {
        if (h != INVALID_HANDLE_VALUE) CloseHandle(h); if (hw != INVALID_HANDLE_VALUE) CloseHandle(hw);
        h = hw = INVALID_HANDLE_VALUE; cache.clear(); cache.shrink_to_fit(); cached = false; open = false; idx.assign(NCLASS, Rec()); size = 0;
    }
};
static std::string FDIR;   // where the set files live (defaults to the search directory)
static std::string setPath(char kind, int d) { char b[64]; snprintf(b, sizeof b, "\\%s_%02d.bin", kind == 'f' ? "frontier" : "unvisited", d); return FDIR + b; }
// scan a set file; validate payload checksums when `validate`; truncate a torn tail.
// h is a cached handle for scans and small reads; hw (forAppend) is an unbuffered read/write handle.
static bool openSet(SetFile& f, char kind, int depth, bool create, bool validate, bool forAppend) {
    f.close(); f.kind = kind; f.depth = depth;
    std::string p = setPath(kind, depth);
    f.h = CreateFileA(p.c_str(), GENERIC_READ | GENERIC_WRITE, FILE_SHARE_READ | FILE_SHARE_WRITE, 0, create ? OPEN_ALWAYS : OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, 0);
    if (f.h == INVALID_HANDLE_VALUE) { if (!create && GetLastError() == ERROR_FILE_NOT_FOUND) return false; die("cannot open %s (error %lu)", p.c_str(), GetLastError()); }
    u64 sz = fileSize(f.h), off = 0; std::vector<u8> buf;
    while (off + BLK <= sz) {
        RecHdr hd; readAt(f.h, off, &hd, sizeof hd, "set header");
        if (hd.magic != REC_MAGIC || hd.sector >= NCLASS || hd.bytes > BM_BYTES || off + BLK + padBlk(hd.bytes) > sz) break;
        if (validate) { buf.resize(hd.bytes); readAt(f.h, off + BLK, buf.data(), hd.bytes, "set payload"); if (hashBytes(buf.data(), hd.bytes) != hd.sum) break; }
        Rec& r = f.idx[hd.sector]; CHECK(!r.present);
        r.off = off + BLK; r.bytes = hd.bytes; r.count = hd.count; r.fmt = hd.fmt; r.present = true;
        off += BLK + padBlk(hd.bytes);
    }
    if (off != sz) {
        if (!validate) die("%s is damaged (bad record at offset %llu)", p.c_str(), (unsigned long long)off);
        printf("  discarding %llu torn bytes at the end of %s\n", (unsigned long long)(sz - off), p.c_str());
        LARGE_INTEGER li; li.QuadPart = (LONGLONG)off; SetFilePointerEx(f.h, li, 0, FILE_BEGIN); SetEndOfFile(f.h); FlushFileBuffers(f.h);
    }
    f.size = off; f.open = true;
    if (forAppend) {
        f.hw = CreateFileA(p.c_str(), GENERIC_READ | GENERIC_WRITE, FILE_SHARE_READ | FILE_SHARE_WRITE, 0, OPEN_EXISTING, FILE_FLAG_NO_BUFFERING | FILE_FLAG_WRITE_THROUGH, 0);
        if (f.hw == INVALID_HANDLE_VALUE) die("cannot open %s for appending (error %lu)", p.c_str(), GetLastError());
    }
    return true;
}

// ------------------------------------------------------------------ search state
static int CUR = -1;                               // deepest complete depth
static bool COMPLETE = false;
static bool MATERIALIZED = false;                  // the two-bit table exists and holds every depth <= CUR
static std::vector<u64> DIST_CANON, DIST_PHYS;
static std::vector<u32> VISITED;                   // per sector, through depth CUR
static u64 FINGERPRINT = 0;

static void saveState() {
    std::string s = "fto-bfs-state 3\n";
    char b[256];
    snprintf(b, sizeof b, "fingerprint %016llx\ncur %d\ncomplete %d\nmaterialized %d\n", (unsigned long long)FINGERPRINT, CUR, COMPLETE ? 1 : 0, MATERIALIZED ? 1 : 0); s += b;
    s += "frontier_dir " + (FDIR == DIR ? std::string(".") : FDIR) + "\n";   // "." = the search directory itself, so the folder can be renamed or moved
    for (size_t d = 0; d < DIST_CANON.size(); d++) { snprintf(b, sizeof b, "dist %zu %llu %llu\n", d, (unsigned long long)DIST_CANON[d], (unsigned long long)DIST_PHYS[d]); s += b; }
    for (u32 c = 0; c < NCLASS; c++) if (VISITED[c]) { snprintf(b, sizeof b, "visited %u %u\n", c, VISITED[c]); s += b; }
    writeAtomic(pathOf("state.txt"), s);
    std::string t = "depth\tcanonical_orbits\tpositions\n"; u64 tot = 0;
    for (size_t d = 0; d < DIST_CANON.size(); d++) { snprintf(b, sizeof b, "%zu\t%llu\t%llu\n", d, (unsigned long long)DIST_CANON[d], (unsigned long long)DIST_PHYS[d]); t += b; tot += DIST_PHYS[d]; }
    snprintf(b, sizeof b, "total\t\t%llu\nexpected\t\t%llu\nstatus\t\t%s\n", (unsigned long long)tot, (unsigned long long)TOTAL_STATES,
             COMPLETE ? (tot == TOTAL_STATES ? "complete, total verified" : "COMPLETE BUT TOTAL MISMATCH") : "in progress"); t += b;
    writeAtomic(pathOf("distribution.tsv"), t);
}
static bool loadState() {
    FILE* f = fopen(pathOf("state.txt").c_str(), "r"); if (!f) return false;
    char line[1024]; VISITED.assign(NCLASS, 0); DIST_CANON.clear(); DIST_PHYS.clear();
    if (!fgets(line, sizeof line, f) || strncmp(line, "fto-bfs-state 3", 15)) die("state.txt was written by a different version");
    while (fgets(line, sizeof line, f)) {
        unsigned long long a, b2; unsigned d, c, v; int i;
        if (sscanf(line, "fingerprint %llx", &a) == 1) { if (a != FINGERPRINT) die("state.txt belongs to a different model/version"); }
        else if (sscanf(line, "cur %d", &i) == 1) CUR = i;
        else if (sscanf(line, "complete %d", &i) == 1) COMPLETE = i != 0;
        else if (sscanf(line, "materialized %d", &i) == 1) MATERIALIZED = i != 0;
        else if (!strncmp(line, "frontier_dir ", 13)) { FDIR = line + 13; while (!FDIR.empty() && (FDIR.back() == '\n' || FDIR.back() == '\r')) FDIR.pop_back(); if (FDIR == ".") FDIR = DIR; }
        else if (sscanf(line, "dist %u %llu %llu", &d, &a, &b2) == 3) { CHECK(d == DIST_CANON.size()); DIST_CANON.push_back(a); DIST_PHYS.push_back(b2); }
        else if (sscanf(line, "visited %u %u", &c, &v) == 2) { CHECK(c < NCLASS); VISITED[c] = v; }
    }
    fclose(f); return true;
}

// ------------------------------------------------------------------ engine
static std::atomic<bool> STOP{false};
static BOOL WINAPI ctrlHandler(DWORD) { STOP = true; fprintf(stderr, "\nStop requested: pausing at the next safe point (rerun with `resume` to continue)...\n"); return TRUE; }

struct Options { int threads = 24; int stopDepth = -1; u64 listMax = BM_BYTES; u64 cacheBytes = 1ull << 30; double maxSeconds = 0;
                 double backFactor = 4.0; int forceBackMod = 0; int materializeAt = -1; bool forceU = false; };
static Options OPT;
static SetFile FCUR, FPREV, FNEXT, UPREV, UNEXT;
static std::vector<SetFile> ALLF;
static std::mutex MFRONT, MDONE;
static FILE* DONELOG = nullptr;
static std::atomic<u64> A_edges{0}, A_new{0}, A_tasks{0}, A_rd{0}, A_wr{0}, A_back{0};
static u8 CODE_NEXT = 0;
static const u64 M55 = 0x5555555555555555ull;
// 32 two-bit entries -> 32-bit mask of the entries equal to the code whose pattern is `pat`
static inline u32 eq32(u64 w, u64 pat) { u64 x = w ^ pat; return (u32)_pext_u64(~(x | (x >> 1)) & M55, M55); }

static const u32 BK_SHIFT = 20, BK_N = (CAP >> BK_SHIFT) + 1, BK_CAP = 16384;
struct Worker {
    u8* dest; u64* nb; u8* blob; u64* srcbm; u8* hdr; HANDLE hs[3] = {INVALID_HANDLE_VALUE, INVALID_HANDLE_VALUE, INVALID_HANDLE_VALUE};
    std::vector<u8> dirty; bool fileExists = false;
    PairTab* pt = (PairTab*)_aligned_malloc(sizeof(PairTab), 64);
    u32* bk = nullptr; u32 bn[BK_N] = {0};        // write-combining buckets for markPair (table-free layers only)
    void needBuckets() { if (!bk) { bk = (u32*)VirtualAlloc(0, (size_t)BK_N * BK_CAP * 4, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE); if (!bk) die("out of memory (buckets)"); } }
    void freeBuckets() { if (bk) VirtualFree(bk, 0, MEM_RELEASE); bk = nullptr; }
    inline void drain(u32 b) { const u32* a = bk + (size_t)b * BK_CAP; u32 n = bn[b]; for (u32 i = 0; i < n; i++) nb[a[i] >> 6] |= 1ull << (a[i] & 63); bn[b] = 0; }
    Worker() {
        dest = (u8*)VirtualAlloc(0, SECTOR_FILE, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
        nb = (u64*)VirtualAlloc(0, BM_BYTES, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
        blob = (u8*)VirtualAlloc(0, BM_BYTES + 4096, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
        srcbm = (u64*)VirtualAlloc(0, BM_BYTES, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
        hdr = (u8*)VirtualAlloc(0, BLK, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
        if (!dest || !nb || !blob || !srcbm || !hdr) die("out of memory allocating worker buffers");
        dirty.assign(NCHUNK, 0);
    }
    void openRead(int slot, const SetFile& f) {
        if (hs[slot] != INVALID_HANDLE_VALUE) CloseHandle(hs[slot]); hs[slot] = INVALID_HANDLE_VALUE;
        if (!f.open || f.cached) return;
        hs[slot] = CreateFileA(setPath(f.kind, f.depth).c_str(), GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE, 0, OPEN_EXISTING, FILE_FLAG_NO_BUFFERING, 0);
        if (hs[slot] == INVALID_HANDLE_VALUE) die("cannot open %s for reading", setPath(f.kind, f.depth).c_str());
    }
};
static std::string sectorPath(u32 s) { return pathOf("sectors\\%04u.bin", s); }
static void loadSector(Worker& w, u32 s) {
    HANDLE h = CreateFileA(sectorPath(s).c_str(), GENERIC_READ, FILE_SHARE_READ, 0, OPEN_EXISTING, FILE_FLAG_NO_BUFFERING | FILE_FLAG_SEQUENTIAL_SCAN, 0);
    if (h == INVALID_HANDLE_VALUE) {
        if (GetLastError() != ERROR_FILE_NOT_FOUND) die("cannot open sector %u (error %lu)", s, GetLastError());
        if (VISITED[s]) die("sector %u file is missing but the state says it holds %u entries", s, VISITED[s]);
        memset(w.dest, 0, SECTOR_FILE); w.fileExists = false;
    } else { if (fileSize(h) != SECTOR_FILE) die("sector %u file has the wrong size", s); readAt(h, 0, w.dest, SECTOR_FILE, "sector"); CloseHandle(h); w.fileExists = true; A_rd += SECTOR_FILE; }
    std::fill(w.dirty.begin(), w.dirty.end(), 0);
}
static void storeSector(Worker& w, u32 s) {
    HANDLE h = CreateFileA(sectorPath(s).c_str(), GENERIC_WRITE, FILE_SHARE_READ, 0, OPEN_ALWAYS, FILE_FLAG_NO_BUFFERING | FILE_FLAG_WRITE_THROUGH, 0);
    if (h == INVALID_HANDLE_VALUE) die("cannot write sector %u (error %lu)", s, GetLastError());
    if (!w.fileExists) { writeAt(h, 0, w.dest, SECTOR_FILE, "sector"); A_wr += SECTOR_FILE; }
    else for (u32 c = 0; c < NCHUNK;) {
        if (!w.dirty[c]) { c++; continue; }
        u32 e = c; while (e < NCHUNK && w.dirty[e]) e++;
        writeAt(h, (u64)c * CHUNK, w.dest + (u64)c * CHUNK, (u64)(e - c) * CHUNK, "sector"); A_wr += (u64)(e - c) * CHUNK; c = e;
    }
    CloseHandle(h);
}
// payload of one record: a pointer into the RAM cache, or read (unbuffered) into w.blob
static const u8* getBlob(const SetFile& f, const Rec& r, Worker& w, int slot) {
    if (f.cached) return f.cache.data() + r.off;
    readAt(w.hs[slot], r.off, w.blob, padBlk(r.bytes), "set blob"); A_rd += r.bytes; return w.blob;
}
template <class F> static inline void forEachEntry(const u8* blob, const Rec& r, F&& fn) {
    if (r.fmt == 0) { const u32* a = (const u32*)blob; for (u64 i = 0; i < r.count; i++) fn(a[i]); }
    else if (r.fmt == 1) { const u64* b = (const u64*)blob; for (u32 wd = 0; wd < BM_WORDS; wd++) { u64 x = b[wd]; while (x) { fn(wd * 64 + (u32)_tzcnt_u64(x)); x &= x - 1; } } }
    else { const u8* p = blob; const u8* end = blob + r.bytes; u32 prev = 0xffffffffu; while (p < end) { u32 g = *p++; if (g == 255) { memcpy(&g, p, 4); p += 4; } prev += g; fn(prev); } }
}
static const u64* toBitmap(const u8* blob, const Rec& r, u64* scratch) {
    if (r.fmt == 1) return (const u64*)blob;
    memset(scratch, 0, BM_BYTES); forEachEntry(blob, r, [&](u32 e) { scratch[e >> 6] |= 1ull << (e & 63); }); return scratch;
}
// choose the smallest encoding of the set bits of bm; returns the payload (bm itself or `out`)
static const u8* encodeSet(const u64* bm, u64 cnt, u8* out, u32& fmt, u64& bytes) {
    if (cnt > OPT.listMax || cnt >= BM_BYTES - 4096) { fmt = 1; bytes = BM_BYTES; return (const u8*)bm; }
    if (cnt <= CAP / 300) {
        u32* o = (u32*)out; u64 k = 0;
        for (u32 wd = 0; wd < BM_WORDS; wd++) { u64 x = bm[wd]; while (x) { o[k++] = wd * 64 + (u32)_tzcnt_u64(x); x &= x - 1; } }
        CHECK(k == cnt); fmt = 0; bytes = cnt * 4;
    } else {
        u8* o = out; u8* lim = out + BM_BYTES - 4096; u32 prev = 0xffffffffu; u64 k = 0;
        for (u32 wd = 0; wd < BM_WORDS; wd++) {
            u64 x = bm[wd];
            while (x) { u32 e = wd * 64 + (u32)_tzcnt_u64(x); x &= x - 1; u32 g = e - prev; prev = e; k++; if (g < 255) *o++ = (u8)g; else { *o++ = 255; memcpy(o, &g, 4); o += 4; } }
            if (o > lim) { fmt = 1; bytes = BM_BYTES; return (const u8*)bm; }
        }
        CHECK(k == cnt); fmt = 2; bytes = (u64)(o - out);
    }
    memset(out + bytes, 0, padBlk(bytes) - bytes);
    return out;
}
static void appendRecord(SetFile& f, Worker& w, u32 s, u64 cnt, u32 fmt, u64 bytes, const u8* payload) {
    RecHdr hd = {}; hd.magic = REC_MAGIC; hd.sector = s; hd.count = cnt; hd.fmt = fmt; hd.bytes = bytes; hd.sum = hashBytes(payload, bytes);
    memset(w.hdr, 0, BLK); memcpy(w.hdr, &hd, sizeof hd);
    std::lock_guard<std::mutex> g(MFRONT);
    CHECK(!f.idx[s].present);
    writeAt(f.hw, f.size, w.hdr, BLK, "set file"); if (bytes) writeAt(f.hw, f.size + BLK, payload, padBlk(bytes), "set file");
    if (!FlushFileBuffers(f.hw)) die("flush of set file failed");
    Rec& r = f.idx[s]; r.off = f.size + BLK; r.bytes = bytes; r.count = cnt; r.fmt = fmt; r.present = true;
    f.size += BLK + padBlk(bytes); A_wr += BLK + padBlk(bytes);
}

// ---- kernels.  A (dest sector, move) pair maps every entry of the source sector to one dest entry.
// forward into the two-bit table: unvisited targets get this layer's code
static u64 pullPair(Worker& w, const Pair& pr, const u8* blob, const Rec& r) {
    PairTab& pt = *w.pt; buildPairTab(pt, pr.L, pr.R);
    u8* dest = w.dest; u8* dirty = w.dirty.data(); const u8 code = CODE_NEXT;
    u32 di[64]; int n = 0; u64 found = 0; u32 curHi = 0xffffffffu, par = 0; __m128i rem = _mm_setzero_si128();
    auto flush = [&]() {
        for (int i = 0; i < n; i++) {
            u32 d = di[i]; u8& b = dest[d >> 2]; int sh = (d & 3) * 2;
            if (!((b >> sh) & 3)) { b |= (u8)(code << sh); dirty[d >> 18] = 1; found++; }
        }
        n = 0;
    };
    forEachEntry(blob, r, [&](u32 si) {
        u32 hi = si / 360, lo = si - hi * 360;
        if (hi != curHi) { curHi = hi; rem = blockRem(hi, pt.R, par); }
        alignas(16) u8 t[16]; _mm_store_si128((__m128i*)t, _mm_shuffle_epi8(rem, pt.SL[par][lo]));
        u32 d = rank12f(t); di[n++] = d;
        _mm_prefetch((const char*)(dest + (d >> 2)), _MM_HINT_T0);
        if (n == 64) flush();
    });
    flush();
    return found;
}
// forward into a candidate bitmap (table-free layers)
static void markPair(Worker& w, const Pair& pr, const u8* blob, const Rec& r) {
    PairTab& pt = *w.pt; buildPairTab(pt, pr.L, pr.R);
    // Targets are scattered over the 30 MB bitmap, and one cache line per lookup saturates this machine's
    // memory bandwidth.  So targets are first appended to one of 229 buckets (128 KiB of bitmap each) and a
    // full bucket is applied in one go, while its slice of the bitmap sits in the L2 cache.
    u32 curHi = 0xffffffffu, par = 0; __m128i rem = _mm_setzero_si128(); u32* bk = w.bk; u32* bn = w.bn;
    forEachEntry(blob, r, [&](u32 si) {
        u32 hi = si / 360, lo = si - hi * 360;
        if (hi != curHi) { curHi = hi; rem = blockRem(hi, pt.R, par); }
        alignas(16) u8 t[16]; _mm_store_si128((__m128i*)t, _mm_shuffle_epi8(rem, pt.SL[par][lo]));
        u32 d = rank12f(t), b = d >> BK_SHIFT;
        bk[(size_t)b * BK_CAP + bn[b]] = d;
        if (++bn[b] == BK_CAP) w.drain(b);
    });
}
// reverse: every still-unvisited dest entry looks up its one predecessor under this move in a bitmap of
// the source sector (frontier bitmap, or with invert=1 the "still unvisited" bitmap)
static u64 pushPair(Worker& w, const Pair& pr, const u64* src, u64& probes, u32 invert) {
    u8 li[16], ri[16]; memset(li, 0x80, 16); memset(ri, 0, 16);
    for (int i = 0; i < 12; i++) { li[pr.L[i]] = (u8)i; ri[pr.R[i]] = (u8)i; }
    PairTab& pt = *w.pt; buildPairTab(pt, li, ri);
    u8* dest = w.dest; u8* dirty = w.dirty.data(); const u8 code = CODE_NEXT; const u64* d64 = (const u64*)dest;
    u32 de[64], si[64]; int n = 0; u64 found = 0, pr_ = 0; u32 curHi = 0xffffffffu, par = 0; __m128i rem = _mm_setzero_si128();
    auto flush = [&]() {
        for (int i = 0; i < n; i++) {   // branch-free: the hit bit is close to a coin flip in the dense layers
            u32 hit = ((u32)(src[si[i] >> 6] >> (si[i] & 63)) & 1) ^ invert, d = de[i];
            dest[d >> 2] |= (u8)((code & (0u - hit)) << ((d & 3) * 2)); dirty[d >> 18] |= (u8)hit; found += hit;
        }
        pr_ += n; n = 0;
    };
    for (u32 wi = 0; wi < SECTOR_BYTES / 8; wi++) {
        u64 x = d64[wi]; u64 z = ~(x | (x >> 1)) & M55;
        while (z) {
            u32 d = wi * 32 + ((u32)_tzcnt_u64(z) >> 1); z &= z - 1;
            u32 hi = d / 360, lo = d - hi * 360;
            if (hi != curHi) { curHi = hi; rem = blockRem(hi, pt.R, par); }
            alignas(16) u8 t[16]; _mm_store_si128((__m128i*)t, _mm_shuffle_epi8(rem, pt.SL[par][lo]));
            u32 s = rank12f(t); de[n] = d; si[n++] = s;
            _mm_prefetch((const char*)(src + (s >> 6)), _MM_HINT_T0);
            if (n == 64) flush();
        }
    }
    flush(); probes += pr_;
    return found;
}
static void logDone(u32 s) { std::lock_guard<std::mutex> g(MDONE); fwrite(&s, 4, 1, DONELOG); fflush(DONELOG); }

// kind 2: table-free layer.  new(s) = neighbours of frontier(n-1), minus frontier(n-1)(s), minus frontier(n-2)(s)
static void taskFrontierOnly(Worker& w, u32 s) {
    memset(w.nb, 0, BM_BYTES); w.needBuckets(); memset(w.bn, 0, sizeof w.bn);
    for (int m = 0; m < 16; m++) {
        if (STOP) return;
        const Pair& pr = PAIRS[(size_t)s * 16 + m]; const Rec& r = FCUR.idx[pr.src];
        if (!r.present || !r.count) continue;
        markPair(w, pr, getBlob(FCUR, r, w, 0), r); A_edges += r.count;
    }
    for (u32 b = 0; b < BK_N; b++) w.drain(b);
    for (int k = 0; k < 2; k++) {
        const SetFile& f = k ? FPREV : FCUR; if (!f.open) continue;
        const Rec& r = f.idx[s]; if (!r.present || !r.count) continue;
        const u8* blob = getBlob(f, r, w, k);
        if (r.fmt == 1) { const u64* b = (const u64*)blob; for (u32 i = 0; i < BM_WORDS; i++) w.nb[i] &= ~b[i]; }
        else forEachEntry(blob, r, [&](u32 e) { w.nb[e >> 6] &= ~(1ull << (e & 63)); });
    }
    if (STOP) return;
    u64 cnt = 0; for (u32 i = 0; i < BM_WORDS; i++) cnt += (u64)_mm_popcnt_u64(w.nb[i]);
    if (cnt) { u32 fmt; u64 bytes; const u8* payload = encodeSet(w.nb, cnt, w.blob, fmt, bytes); appendRecord(FNEXT, w, s, cnt, fmt, bytes, payload); }
    logDone(s); A_new += cnt; A_tasks++;
}
// kind 3: build one table sector from every frontier file written so far
static void taskMaterialize(Worker& w, u32 s) {
    memset(w.dest, 0, SECTOR_FILE); u64* d64 = (u64*)w.dest;
    for (int d = 0; d <= CUR; d++) {
        const SetFile& f = ALLF[d]; const Rec& r = f.idx[s]; if (!r.present || !r.count) continue;
        readAt(f.h, r.off, w.blob, r.bytes, "frontier record"); A_rd += r.bytes;
        const u64 code = (u64)(d % 3 + 1);
        if (r.fmt == 1) { const u32* b = (const u32*)w.blob; for (u32 wi = 0; wi < SECTOR_BYTES / 8; wi++) d64[wi] |= _pdep_u64(b[wi], M55) * code; }
        else forEachEntry(w.blob, r, [&](u32 e) { w.dest[e >> 2] |= (u8)(code << ((e & 3) * 2)); });
    }
    u64 unv = 0; for (u32 wi = 0; wi < SECTOR_BYTES / 8; wi++) unv += (u32)_mm_popcnt_u32(eq32(d64[wi], 0));
    if ((u64)CAP - unv != VISITED[s]) die("materialised sector %u holds %llu entries, expected %u", s, (unsigned long long)(CAP - unv), VISITED[s]);
    if (VISITED[s]) { w.fileExists = false; storeSector(w, s); }
    logDone(s); A_tasks++;
}
// kind 0: compute the new entries of table sector s;  kind 1: re-apply an already durable frontier record
static void taskTable(Worker& w, u32 s, int kind) {
    if (kind == 1) {
        const Rec& r = FNEXT.idx[s];
        { std::lock_guard<std::mutex> g(MFRONT); readAt(FNEXT.hw, r.off, w.blob, padBlk(r.bytes), "frontier record"); }
        loadSector(w, s);
        forEachEntry(w.blob, r, [&](u32 d) {
            u8& b = w.dest[d >> 2]; int sh = (d & 3) * 2; u8 v = (b >> sh) & 3;
            if (v != CODE_NEXT) { if (v) die("re-apply conflict in sector %u", s); b |= (u8)(CODE_NEXT << sh); w.dirty[d >> 18] = 1; }
        });
        storeSector(w, s); logDone(s); A_new += r.count; A_tasks++; return;
    }
    loadSector(w, s);
    // remember which entries already carry this layer's code (they are from three depths back)
    const u64 pat = (u64)CODE_NEXT * M55; u64* d64 = (u64*)w.dest; u32* nb32 = (u32*)w.nb; const u32 NW = SECTOR_BYTES / 8;
    for (u32 wi = 0; wi < NW; wi++) nb32[wi] = eq32(d64[wi], pat);
    // per source: 0 nothing, 1 test membership in frontier(n-1), 2 test non-membership in unvisited(n-1), 3 source fully visited
    int mode[16]; double dens[16]; u64 cnt = 0, sum = 0; const u64 room = (u64)CAP - VISITED[s];
    for (int m = 0; m < 16; m++) {
        u32 src = PAIRS[(size_t)s * 16 + m].src; const Rec& f = FCUR.idx[src]; mode[m] = 0; dens[m] = 0;
        if (f.present && f.count) { sum += f.count; mode[m] = 1; dens[m] = (double)f.count / CAP; }
        if (VISITED[src] == CAP) { mode[m] = 3; dens[m] = 2; }
        else if (UPREV.open && UPREV.idx[src].present && (mode[m] == 0 || OPT.forceU || UPREV.idx[src].bytes < f.bytes)) { mode[m] = 2; dens[m] = 1.0 - (double)UPREV.idx[src].count / CAP; }
    }
    bool back = OPT.backFactor * (double)room < (double)sum;
    if (OPT.forceBackMod) back = (s % OPT.forceBackMod) == 0;
    if (back) A_back++;
    int order[16]; for (int m = 0; m < 16; m++) order[m] = m;
    if (back) std::stable_sort(order, order + 16, [&](int a, int b) { return dens[a] > dens[b]; });   // likeliest hits first
    for (int mi = 0; mi < 16 && cnt < room; mi++) {
        if (STOP) return;
        const int m = order[mi]; const Pair& pr = PAIRS[(size_t)s * 16 + m];
        if (!back) {
            const Rec& r = FCUR.idx[pr.src]; if (!r.present || !r.count) continue;
            cnt += pullPair(w, pr, getBlob(FCUR, r, w, 0), r); A_edges += r.count; continue;
        }
        if (mode[m] == 0) continue;
        if (mode[m] == 3) {   // every neighbour through this move is visited: all remaining entries are new
            for (u32 wi = 0; wi < NW; wi++) { u64 x = d64[wi], z = ~(x | (x >> 1)) & M55; if (z) { d64[wi] = x | z * CODE_NEXT; w.dirty[wi >> 13] = 1; cnt += (u64)_mm_popcnt_u64(z); } }
            continue;
        }
        const SetFile& f = mode[m] == 1 ? FCUR : UPREV; const Rec& r = f.idx[pr.src];
        const u64* src = toBitmap(getBlob(f, r, w, mode[m] == 1 ? 0 : 2), r, w.srcbm);
        u64 probes = 0; cnt += pushPair(w, pr, src, probes, mode[m] == 2); A_edges += probes;
    }
    if (STOP) return;
    u64 k = 0, unv = 0;
    for (u32 wi = 0; wi < NW; wi++) { u32 nw = eq32(d64[wi], pat) & ~nb32[wi]; nb32[wi] = nw; k += (u32)_mm_popcnt_u32(nw); }
    CHECK(k == cnt && cnt <= room); unv = room - cnt;
    // unvisited(n) record first (the next layer may test against it), then the frontier record, then the sector
    if (unv && (unv < cnt || OPT.forceU) && !UNEXT.idx[s].present) {
        u32* u32p = (u32*)w.srcbm; for (u32 wi = 0; wi < NW; wi++) u32p[wi] = eq32(d64[wi], 0);
        u32 fmt; u64 bytes; const u8* payload = encodeSet(w.srcbm, unv, w.blob, fmt, bytes); appendRecord(UNEXT, w, s, unv, fmt, bytes, payload);
    }
    if (cnt) {
        u32 fmt; u64 bytes; const u8* payload = encodeSet(w.nb, cnt, w.blob, fmt, bytes); appendRecord(FNEXT, w, s, cnt, fmt, bytes, payload);
        storeSector(w, s);
    }
    logDone(s); A_new += cnt; A_tasks++;
}

static void writeProgress(const char* phase, int layer, u64 tasksTotal, double elapsed, double layerSec) {
    u64 phys = 0; for (u64 x : DIST_PHYS) phys += x;
    char b[1024];
    snprintf(b, sizeof b, "{\n  \"phase\":\"%s\",\n  \"building_depth\":%d,\n  \"sector_tasks_done\":%llu,\n  \"sector_tasks_total\":%llu,\n  \"new_canonical_this_layer\":%llu,\n"
             "  \"positions_through_previous_depth\":%llu,\n  \"total_positions\":%llu,\n  \"percent_through_previous_depth\":%.4f,\n  \"threads\":%d,\n"
             "  \"elapsed_seconds_this_run\":%.1f,\n  \"layer_seconds\":%.1f,\n  \"read_bytes_this_run\":%llu,\n  \"write_bytes_this_run\":%llu\n}\n",
             phase, layer, (unsigned long long)A_tasks.load(), (unsigned long long)tasksTotal, (unsigned long long)A_new.load(), (unsigned long long)phys,
             (unsigned long long)TOTAL_STATES, 100.0 * phys / TOTAL_STATES, OPT.threads, elapsed, layerSec, (unsigned long long)A_rd.load(), (unsigned long long)A_wr.load());
    writeAtomic(pathOf("progress.json"), b);
}
static double now() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }

// run `tasks` on the worker pool; returns false if a stop was requested
static bool runPool(std::vector<Worker*>& workers, const std::vector<std::pair<u32, int>>& tasks, const char* what, int n, double t0) {
    A_tasks = 0; A_new = 0; A_edges = 0; A_back = 0;
    std::atomic<size_t> next{0}; double tl = now(); std::atomic<int> running{OPT.threads};
    std::vector<std::thread> th;
    for (int t = 0; t < OPT.threads; t++) th.emplace_back([&, t]() {
        while (!STOP) {
            size_t i = next++; if (i >= tasks.size()) break;
            Worker& w = *workers[t]; u32 s = tasks[i].first; int kind = tasks[i].second;
            if (kind == 2) taskFrontierOnly(w, s); else if (kind == 3) taskMaterialize(w, s); else taskTable(w, s, kind);
        }
        running--;
    });
    double lastPrint = now();
    while (running.load() > 0) {
        Sleep(100);
        if (OPT.maxSeconds > 0 && now() - t0 > OPT.maxSeconds) STOP = true;
        if (now() - lastPrint >= 15) {
            lastPrint = now();
            printf("  %s %d: %llu/%zu sectors (%llu reverse), %.3e lookups (%.0f M/s), %llu new canonical, read %.0f GB, written %.0f GB, layer %.0fs, run %.0fs\n", what, n,
                   (unsigned long long)A_tasks.load(), tasks.size(), (unsigned long long)A_back.load(), (double)A_edges.load(), A_edges.load() / 1e6 / (now() - tl),
                   (unsigned long long)A_new.load(), A_rd.load() / 1e9, A_wr.load() / 1e9, now() - tl, now() - t0); fflush(stdout);
            writeProgress(what, n, tasks.size(), now() - t0, now() - tl);
        }
    }
    for (auto& x : th) x.join();
    return !STOP;
}

static int cmdRun(bool fresh, const std::string& frontierDirArg) {
    CreateDirectoryA(DIR.c_str(), 0); CreateDirectoryA(pathOf("sectors").c_str(), 0);
    HANDLE lock = CreateFileA(pathOf(".lock").c_str(), GENERIC_WRITE, 0, 0, OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, 0);
    if (lock == INVALID_HANDLE_VALUE) die("another fto_bfs process is using %s", DIR.c_str());
    FINGERPRINT = modelFingerprint();
    bool have = loadState();
    if (!have) {
        FDIR = frontierDirArg.empty() ? DIR : frontierDirArg; CreateDirectoryA(FDIR.c_str(), 0);
        ULARGE_INTEGER freeB, freeF; GetDiskFreeSpaceExA(DIR.c_str(), &freeB, 0, 0); GetDiskFreeSpaceExA(FDIR.c_str(), &freeF, 0, 0);
        double tableGB = (double)NCLASS * SECTOR_FILE / 1e9, frontGB = 3.6 * NCLASS * BM_BYTES / 1e9 + 10;
        bool same = toupper(DIR[0]) == toupper(FDIR[0]);
        printf("Planned peak disk use: table %.0f GB in %s, frontier files up to about %.0f GB in %s. Free: %.0f GB / %.0f GB\n", tableGB, DIR.c_str(), frontGB, FDIR.c_str(), freeB.QuadPart / 1e9, freeF.QuadPart / 1e9);
        if (same ? freeB.QuadPart / 1e9 < tableGB + frontGB : (freeB.QuadPart / 1e9 < tableGB + 5 || freeF.QuadPart / 1e9 < frontGB)) die("not enough free space");
        // depth 0: the solved position
        Config solved; memcpy(solved.cc, SOLVED_COL, 12); for (int i = 0; i < 12; i++) solved.p[i] = (u8)i;
        std::vector<std::pair<u32, u32>> init;
        for (int r : ROTS) { Config c = applySym(K[r], solved); auto [cls, k] = CENTRE.at(packC(c.cc)); if (packC(c.cc) == REP[cls]) init.push_back({cls, rank12(c.p)}); }
        CHECK(init.size() == 1 && STAB[init[0].first] == 24);
        VISITED.assign(NCLASS, 0); COMPLETE = false; MATERIALIZED = false;
        SetFile f; openSet(f, 'f', 0, true, true, false);
        if (f.size == 0) { RecHdr hd = {}; hd.magic = REC_MAGIC; hd.sector = init[0].first; hd.count = 1; hd.fmt = 0; hd.bytes = 4; u32 e = init[0].second; hd.sum = hashBytes(&e, 4);
            std::vector<u8> blk(2 * BLK, 0); memcpy(blk.data(), &hd, sizeof hd); memcpy(blk.data() + BLK, &e, 4);
            writeAt(f.h, 0, blk.data(), blk.size(), "frontier"); FlushFileBuffers(f.h); }
        f.close(); CUR = 0; DIST_CANON = {1}; DIST_PHYS = {1}; VISITED[init[0].first] = 1; saveState();
    } else if (fresh) die("%s already holds a search; use `resume`", DIR.c_str());
    else if (!frontierDirArg.empty() && frontierDirArg != FDIR) die("this search keeps its frontier files in %s; do not pass a different --frontier-dir", FDIR.c_str());
    if (COMPLETE) { printf("Search already complete (maximum depth %d). See distribution.tsv.\n", CUR); return 0; }
    MEMORYSTATUSEX ms; ms.dwLength = sizeof ms; GlobalMemoryStatusEx(&ms);
    double perThread = (SECTOR_FILE + 3.0 * BM_BYTES + 8192) / 1048576.0;
    printf("Model: %u sectors x %u entries (%.1f GB table), %zu symmetries. Threads %d (%.0f MiB buffers), frontier RAM cache %.1f GiB, available RAM %.1f GiB\n",
           NCLASS, CAP, (double)NCLASS * SECTOR_FILE / 1e9, K.size(), OPT.threads, perThread * OPT.threads, OPT.cacheBytes / 1073741824.0, ms.ullAvailPhys / 1073741824.0);
    if (perThread * OPT.threads * 1048576.0 + OPT.cacheBytes > ms.ullAvailPhys * 0.9) printf("WARNING: buffers may exceed available RAM; consider fewer --threads or a smaller --cache-mib\n");
    std::vector<Worker*> workers; for (int t = 0; t < OPT.threads; t++) workers.push_back(new Worker());
    SetConsoleCtrlHandler(ctrlHandler, TRUE);
    double t0 = now();
    auto readDone = [&](const std::string& path) { std::vector<u8> done(NCLASS, 0); if (FILE* f = fopen(path.c_str(), "rb")) { u32 s; while (fread(&s, 4, 1, f) == 1) if (s < NCLASS) done[s] = 1; fclose(f); } return done; };
    while (true) {
        int n = CUR + 1; CODE_NEXT = (u8)(n % 3 + 1);
        if (OPT.stopDepth >= 0 && CUR >= OPT.stopDepth) { printf("Reached --stop-depth %d; paused.\n", OPT.stopDepth); return 0; }
        // ---- switch from table-free layers to the two-bit table once reverse lookups pay off
        if (!MATERIALIZED) {
            u64 vis = 0; for (u32 v : VISITED) vis += v;
            double unvisited = (double)NCLASS * CAP - (double)vis;
            bool sw = 16.0 * (double)DIST_CANON[CUR] > OPT.backFactor * unvisited;
            if (OPT.materializeAt >= 0) sw = CUR >= OPT.materializeAt;
            if (sw) {
                printf("Building the two-bit table from frontier files 0..%d\n", CUR); fflush(stdout);
                ALLF.clear(); ALLF.resize(CUR + 1);
                for (int d = 0; d <= CUR; d++) { if (!openSet(ALLF[d], 'f', d, false, false, false)) die("frontier_%02d is missing", d); u64 c = 0; for (auto& r : ALLF[d].idx) c += r.count; CHECK(c == DIST_CANON[d]); }
                std::string dl = pathOf("materialize.done"); std::vector<u8> done = readDone(dl);
                DONELOG = fopen(dl.c_str(), "ab"); if (!DONELOG) die("cannot open %s", dl.c_str());
                std::vector<std::pair<u32, int>> tasks; for (u32 s = 0; s < NCLASS; s++) if (!done[s]) tasks.push_back({s, 3});
                double tl = now(); bool ok = runPool(workers, tasks, "table build after depth", CUR, t0);
                fclose(DONELOG); DONELOG = nullptr; for (auto& f : ALLF) f.close(); ALLF.clear();
                if (!ok) { printf("Paused safely during the table build. Run `resume` to continue.\n"); return 0; }
                MATERIALIZED = true; saveState(); DeleteFileA(dl.c_str()); for (auto w : workers) w->freeBuckets();
                for (int d = 0; d <= CUR - 2; d++) DeleteFileA(setPath('f', d).c_str());
                printf("Table built (%.1fs)\n", now() - tl); fflush(stdout);
            }
        }
        if (!openSet(FCUR, 'f', CUR, false, false, false)) die("frontier_%02d is missing", CUR);
        { u64 c = 0; for (auto& r : FCUR.idx) c += r.count; if (c != DIST_CANON[CUR]) die("frontier_%02d does not match the recorded count", CUR); }
        FPREV.close(); UPREV.close(); UNEXT.close();
        if (!MATERIALIZED) { if (CUR >= 1 && !openSet(FPREV, 'f', CUR - 1, false, false, false)) die("frontier_%02d is missing", CUR - 1); }
        else { openSet(UPREV, 'u', CUR, false, false, false); openSet(UNEXT, 'u', n, true, true, true); }
        u64 budget = OPT.cacheBytes;
        for (SetFile* f : {&FCUR, &FPREV, &UPREV}) if (f->open && f->size <= budget) { f->cache.resize(f->size); if (f->size) readAt(f->h, 0, f->cache.data(), f->size, "set cache"); f->cached = true; budget -= f->size; }
        for (auto w : workers) { w->openRead(0, FCUR); w->openRead(1, FPREV); w->openRead(2, UPREV); }
        openSet(FNEXT, 'f', n, true, true, true);
        std::string dl = pathOf("layer_%02d.done", n); std::vector<u8> done = readDone(dl);
        DONELOG = fopen(dl.c_str(), "ab"); if (!DONELOG) die("cannot open %s", dl.c_str());
        std::vector<std::pair<u32, int>> tasks; u64 already = 0;
        for (u32 s = 0; s < NCLASS; s++) {
            if (done[s]) { already++; continue; }
            if (FNEXT.idx[s].present) { if (MATERIALIZED) tasks.push_back({s, 1}); continue; }
            if (VISITED[s] == CAP) continue;
            bool act = false; for (int m = 0; m < 16; m++) { const Rec& r = FCUR.idx[PAIRS[(size_t)s * 16 + m].src]; act |= r.present && r.count; }
            if (act) tasks.push_back({s, MATERIALIZED ? 0 : 2});
        }
        printf("Depth %d (%s): %zu sector tasks (%llu already committed), frontier %llu canonical\n", n, MATERIALIZED ? "table" : "table-free", tasks.size(), (unsigned long long)already, (unsigned long long)DIST_CANON[CUR]); fflush(stdout);
        double tl = now(); bool ok = runPool(workers, tasks, "depth", n, t0);
        fclose(DONELOG); DONELOG = nullptr;
        for (auto w : workers) for (int k = 0; k < 3; k++) if (w->hs[k] != INVALID_HANDLE_VALUE) { CloseHandle(w->hs[k]); w->hs[k] = INVALID_HANDLE_VALUE; }
        if (!ok) { writeProgress("paused", n, tasks.size(), now() - t0, now() - tl); printf("Paused safely during depth %d. Run `resume` to continue.\n", n); return 0; }
        // layer complete: counts, closure check, manifest
        u64 canon = 0, phys = 0;
        for (u32 s = 0; s < NCLASS; s++) if (FNEXT.idx[s].present) {
            u64 c = FNEXT.idx[s].count; canon += c;
            if ((c * 24) % STAB[s]) die("symmetry closure check failed in sector %u at depth %d", s, n);
            phys += c * 24 / STAB[s]; VISITED[s] += (u32)c; CHECK(VISITED[s] <= CAP);
        }
        FNEXT.close(); FCUR.close(); FPREV.close(); UPREV.close(); UNEXT.close();
        if (canon == 0) { COMPLETE = true; DeleteFileA(setPath('f', n).c_str()); DeleteFileA(setPath('u', n).c_str()); }
        else { DIST_CANON.push_back(canon); DIST_PHYS.push_back(phys); CUR = n; }
        saveState(); DeleteFileA(dl.c_str());
        if (MATERIALIZED) { DeleteFileA(setPath('u', n - 1).c_str()); if (!COMPLETE && n >= 2) DeleteFileA(setPath('f', n - 2).c_str()); }
        printf("Depth %d complete: %llu canonical, %llu positions (%.1fs, run %.0fs)\n", n, (unsigned long long)canon, (unsigned long long)phys, now() - tl, now() - t0); fflush(stdout);
        writeProgress(COMPLETE ? "search_complete" : "searching", n, tasks.size(), now() - t0, now() - tl);
        if (COMPLETE) {
            u64 tot = 0; for (u64 x : DIST_PHYS) tot += x;
            printf("\nSEARCH COMPLETE. Maximum depth (God's number for this puzzle) = %d\nTotal positions %llu, expected %llu: %s\n", CUR, (unsigned long long)tot,
                   (unsigned long long)TOTAL_STATES, tot == TOTAL_STATES ? "VERIFIED" : "MISMATCH");
            printf("Next: fto_bfs export --dir %s   (writes the final-depth positions)\n", DIR.c_str());
            return tot == TOTAL_STATES ? 0 : 3;
        }
    }
}

// ------------------------------------------------------------------ export / status / verify
static int cmdStatus() {
    FINGERPRINT = modelFingerprint(); if (!loadState()) die("no search in %s", DIR.c_str());
    printf("deepest complete depth: %d   complete: %s\n", CUR, COMPLETE ? "yes" : "no"); u64 tot = 0;
    printf("depth\tcanonical_orbits\tpositions\n");
    for (size_t d = 0; d < DIST_CANON.size(); d++) { printf("%zu\t%llu\t%llu\n", d, (unsigned long long)DIST_CANON[d], (unsigned long long)DIST_PHYS[d]); tot += DIST_PHYS[d]; }
    printf("positions so far %llu of %llu (%.4f%%)\n", (unsigned long long)tot, (unsigned long long)TOTAL_STATES, 100.0 * tot / TOTAL_STATES);
    return 0;
}
// write positions of one depth as fixed-edge states ("centres / edges", definition-file numbering)
static void exportDepth(int depth, u64 limit, const std::string& out) {
    SetFile f; if (!openSet(f, 'f', depth, false, false, false)) die("frontier_%02d is not on disk (only the last two depths are kept)", depth);
    u64 canon = DIST_CANON[depth], phys = DIST_PHYS[depth];
    bool all = (limit == 0);
    std::vector<u64> keys; std::vector<u8> buf;
    u64 stride = all ? 1 : std::max<u64>(1, canon / limit), seen = 0;
    for (u32 s = 0; s < NCLASS; s++) {
        const Rec& r = f.idx[s]; if (!r.present) continue;
        buf.resize(r.bytes); readAt(f.h, r.off, buf.data(), r.bytes, "frontier record");
        Config x; unpackC(REP[s], x.cc);
        forEachEntry(buf.data(), r, [&](u32 e) {
            if (!all && (seen++ % stride)) return;
            unrankTo(e, x.p);
            if (all) for (auto& k : K) keys.push_back(packState(normalize(applySym(k, x))));
            else keys.push_back(packState(normalize(x)));
        });
        if (all && keys.size() > 400000000) { std::sort(keys.begin(), keys.end()); keys.erase(std::unique(keys.begin(), keys.end()), keys.end()); }
    }
    std::sort(keys.begin(), keys.end()); keys.erase(std::unique(keys.begin(), keys.end()), keys.end());
    if (all && keys.size() != phys) die("export of depth %d produced %zu positions, expected %llu", depth, keys.size(), (unsigned long long)phys);
    if (!all && keys.size() > limit) keys.resize(limit);
    FILE* o = fopen(out.c_str(), "w"); if (!o) die("cannot write %s", out.c_str());
    fprintf(o, "# reduced FTO, depth %d: %zu of %llu positions (%llu classes under the 24 symmetries)\n", depth, keys.size(), (unsigned long long)phys, (unsigned long long)canon);
    fprintf(o, "# each line: CENTERS (12 colours, 1-4) / EDGES (11 pieces), same numbering and convention as the definition file's Solved block\n");
    for (u64 v : keys) {
        Config n; unpackC((u32)(v & 0xFFFFFF), n.cc); u32 used = 0;
        for (int i = 0; i < 10; i++) { n.p[i] = (v >> (24 + 4 * i)) & 15; used |= 1u << n.p[i]; }
        n.p[10] = (u8)_tzcnt_u32(~used & 0x7FF); n.p[11] = 11; printState(o, n);
    }
    fclose(o); printf("wrote %zu positions of depth %d to %s\n", keys.size(), depth, out.c_str());
}
static int cmdExport(int depthArg, long long limitArg, const std::string& outArg) {
    FINGERPRINT = modelFingerprint(); if (!loadState()) die("no search in %s", DIR.c_str());
    if (depthArg >= 0) { CHECK(depthArg <= CUR); exportDepth(depthArg, limitArg < 0 ? 0 : (u64)limitArg, outArg.empty() ? pathOf("positions_depth_%02d.txt", depthArg) : outArg); return 0; }
    if (!COMPLETE) die("search not complete; use --depth N to export a finished depth");
    exportDepth(CUR, 0, pathOf("positions_depth_%02d_all.txt", CUR));
    u64 lim = std::min<u64>(100000, DIST_PHYS[CUR - 1]);
    if (lim == DIST_PHYS[CUR - 1]) exportDepth(CUR - 1, 0, pathOf("positions_depth_%02d_all.txt", CUR - 1));
    else exportDepth(CUR - 1, lim, pathOf("positions_depth_%02d_sample_%llu.txt", CUR - 1, (unsigned long long)lim));
    return 0;
}
// spot check of the stored table: every sampled visited entry (other than solved) has a neighbour one step closer;
// when the search is complete every neighbour is visited.
static int cmdVerify(int nsectors, u64 samples) {
    FINGERPRINT = modelFingerprint(); if (!loadState()) die("no search in %s", DIR.c_str());
    if (!MATERIALIZED) die("the two-bit table has not been built yet (it is built just before the dense layers)");
    std::mt19937_64 rng(12345); Worker w; u64 checked = 0, bad = 0;
    std::vector<u8*> nbuf(16); for (auto& p : nbuf) p = (u8*)VirtualAlloc(0, SECTOR_FILE, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
    for (int it = 0; it < nsectors; it++) {
        u32 D = (u32)(rng() % NCLASS); if (!VISITED[D]) { continue; }
        loadSector(w, D); u8* dest = w.dest;
        u8 Li[16][16], Ri[16][16];
        for (int m = 0; m < 16; m++) {
            const Pair& pr = PAIRS[(size_t)D * 16 + m];
            w.dest = nbuf[m]; loadSector(w, pr.src); w.dest = dest;
            memset(Li[m], 0x80, 16); memset(Ri[m], 0, 16);
            for (int i = 0; i < 12; i++) { Li[m][pr.L[i]] = (u8)i; Ri[m][pr.R[i]] = (u8)i; }
        }
        for (u64 k = 0; k < samples; k++) {
            u32 d = (u32)(rng() % CAP); u8 v = (dest[d >> 2] >> ((d & 3) * 2)) & 3; if (!v) continue;
            Unranker un; __m128i p = unrank12(d, un); bool pred = false, unv = false; u8 want = (u8)((v + 1) % 3 + 1);   // code of depth-1
            for (int m = 0; m < 16; m++) {
                __m128i q = _mm_shuffle_epi8(_mm_loadu_si128((const __m128i*)Ri[m]), _mm_shuffle_epi8(p, _mm_loadu_si128((const __m128i*)Li[m])));
                alignas(16) u8 t[16]; _mm_store_si128((__m128i*)t, q); u32 si = rank12(t);
                u8 sv = (nbuf[m][si >> 2] >> ((si & 3) * 2)) & 3; pred |= (sv == want); unv |= (sv == 0);
            }
            checked++;
            bool isSolved = false;
            if (!pred) { Config x; unpackC(REP[D], x.cc); unrankTo(d, x.p); Config nrm = normalize(x); isSolved = v == 1 && packC(nrm.cc) == packC(SOLVED_COL) && rank12(nrm.p) == 0; }
            if ((!pred && !isSolved) || (COMPLETE && unv)) bad++;
        }
        printf("sector %u: cumulative %llu entries checked, %llu bad\n", D, (unsigned long long)checked, (unsigned long long)bad); fflush(stdout);
    }
    printf(bad ? "VERIFY FAILED\n" : "verify ok\n"); return bad ? 3 : 0;
}

// ---- optimal solutions from the finished table
static Config defMove(const Config& x, int m, int times) {   // definition-file move, exactly as written there
    Config y = x;
    for (int r = 0; r < times; r++) { Config t = y; for (int j = 0; j < 12; j++) y.cc[j] = t.cc[DEF_C[m][j] - 1]; for (int j = 0; j < 11; j++) y.p[j] = t.p[DEF_E[m][j] - 1]; y.p[11] = 11; }
    return y;
}
static int tableCode(const Config& x) {                       // two-bit entry of a fixed-edge state (0 = unvisited)
    auto [cls, k] = CENTRE.at(packC(x.cc)); Config y = applySym(inverse(K[k]), x); CHECK(packC(y.cc) == REP[cls]);
    u32 idx = rank12(y.p);
    HANDLE h = CreateFileA(sectorPath(cls).c_str(), GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE, 0, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, 0);
    if (h == INVALID_HANDLE_VALUE) die("cannot open sector %u", cls);
    u8 b; readAt(h, idx >> 2, &b, 1, "sector byte"); CloseHandle(h);
    return (b >> ((idx & 3) * 2)) & 3;
}
static int cmdSolve(const std::string& inArg, const std::string& outArg) {
    FINGERPRINT = modelFingerprint(); if (!loadState()) die("no search in %s", DIR.c_str());
    if (!COMPLETE || !MATERIALIZED) die("solve needs the finished table");
    std::string in = inArg.empty() ? pathOf("positions_depth_%02d_all.txt", CUR) : inArg, out = outArg.empty() ? pathOf("solutions_depth_%02d.txt", CUR) : outArg;
    FILE* fi = fopen(in.c_str(), "r"); if (!fi) die("cannot read %s", in.c_str());
    FILE* fo = fopen(out.c_str(), "w"); if (!fo) die("cannot write %s", out.c_str());
    fprintf(fo, "# optimal solutions, one position per line:  CENTERS / EDGES | length | solution (apply to the position to solve it) | scramble (apply to solved to get the position)\n");
    fprintf(fo, "# moves are the definition file's F Fw D Dw L BR BL R; X' is X applied twice. Every solution was replayed with the definition file's permutations (new[i] = old[move[i]]).\n");
    Config solved; memcpy(solved.cc, SOLVED_COL, 12); for (int i = 0; i < 12; i++) solved.p[i] = (u8)i;
    char line[512]; int n = 0, maxLen = 0; std::map<int, int> hist;
    while (fgets(line, sizeof line, fi)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        int v[23]; int got = sscanf(line, "%d %d %d %d %d %d %d %d %d %d %d %d / %d %d %d %d %d %d %d %d %d %d %d", v, v+1, v+2, v+3, v+4, v+5, v+6, v+7, v+8, v+9, v+10, v+11, v+12, v+13, v+14, v+15, v+16, v+17, v+18, v+19, v+20, v+21, v+22);
        if (got != 23) die("bad line in %s: %s", in.c_str(), line);
        Config x; for (int i = 0; i < 12; i++) x.cc[i] = (u8)(v[i] - 1); for (int i = 0; i < 11; i++) x.p[i] = (u8)(v[12 + i] - 1); x.p[11] = 11;
        const Config start = x; std::vector<std::pair<int, int>> sol; int code = tableCode(x); CHECK(code != 0);
        while (memcmp(&x, &solved, sizeof x)) {
            int want = (code + 1) % 3 + 1; bool stepped = false;     // code of one depth less
            for (int m = 0; m < 8 && !stepped; m++) for (int t = 1; t <= 2 && !stepped; t++) {
                Config y = defMove(x, m, t);
                if (tableCode(y) == want) { x = y; code = want; sol.push_back({m, t}); stepped = true; }
            }
            if (!stepped) die("no closer neighbour found (position %d)", n + 1);
            if (sol.size() > 40) die("descent did not terminate (position %d)", n + 1);
        }
        // independent replay: solution from the position reaches solved, scramble from solved reaches the position
        Config r = start; for (auto [m, t] : sol) r = defMove(r, m, t); CHECK(!memcmp(&r, &solved, sizeof r));
        Config s2 = solved; for (size_t i = sol.size(); i-- > 0;) s2 = defMove(s2, sol[i].first, 3 - sol[i].second); CHECK(!memcmp(&s2, &start, sizeof s2));
        for (int i = 0; i < 12; i++) fprintf(fo, "%d ", start.cc[i] + 1); fprintf(fo, "/"); for (int i = 0; i < 11; i++) fprintf(fo, " %d", start.p[i] + 1);
        fprintf(fo, " | %zu |", sol.size());
        for (auto [m, t] : sol) fprintf(fo, " %s%s", DEF_NAMES[m], t == 2 ? "'" : "");
        fprintf(fo, " |");
        for (size_t i = sol.size(); i-- > 0;) fprintf(fo, " %s%s", DEF_NAMES[sol[i].first], sol[i].second == 1 ? "'" : "");
        fprintf(fo, "\n"); n++; hist[(int)sol.size()]++; maxLen = std::max(maxLen, (int)sol.size());
    }
    fclose(fi); fclose(fo);
    for (auto [len, c] : hist) printf("%d positions solved in %d moves\n", c, len);
    printf("wrote %d verified solutions to %s\n", n, out.c_str());
    return 0;
}

// Several different solutions per position, for the joint phase-1/phase-2 argument: `count` random optimal
// ones (random choice among the moves that go one step closer) and `count` that are one move longer (one
// sideways step at a random point).  Output: the position line, then one solution per line prefixed by its length.
static int cmdOptimals(const std::string& inArg, const std::string& outArg, int count) {
    FINGERPRINT = modelFingerprint(); if (!loadState()) die("no search in %s", DIR.c_str());
    if (!COMPLETE || !MATERIALIZED) die("needs the finished table");
    std::string in = inArg.empty() ? pathOf("positions_depth_%02d_all.txt", CUR) : inArg, out = outArg.empty() ? pathOf("solutions_many_depth_%02d.txt", CUR) : outArg;
    FILE* fi = fopen(in.c_str(), "r"); if (!fi) die("cannot read %s", in.c_str());
    FILE* fo = fopen(out.c_str(), "w"); if (!fo) die("cannot write %s", out.c_str());
    Config solved; memcpy(solved.cc, SOLVED_COL, 12); for (int i = 0; i < 12; i++) solved.p[i] = (u8)i;
    std::mt19937_64 rng(2026); char line[512]; int n = 0; u64 total = 0;
    while (fgets(line, sizeof line, fi)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        int v[23]; int got = sscanf(line, "%d %d %d %d %d %d %d %d %d %d %d %d / %d %d %d %d %d %d %d %d %d %d %d", v, v+1, v+2, v+3, v+4, v+5, v+6, v+7, v+8, v+9, v+10, v+11, v+12, v+13, v+14, v+15, v+16, v+17, v+18, v+19, v+20, v+21, v+22);
        if (got != 23) die("bad line in %s: %s", in.c_str(), line);
        Config start; for (int i = 0; i < 12; i++) start.cc[i] = (u8)(v[i] - 1); for (int i = 0; i < 11; i++) start.p[i] = (u8)(v[12 + i] - 1); start.p[11] = 11;
        const int code0 = tableCode(start); CHECK(code0 != 0);
        std::set<std::string> sols;
        for (int extra = 0; extra <= 1; extra++) for (int tries = 0; tries < count * 4 && (int)sols.size() < count * (extra + 1); tries++) {
            Config x = start; int code = code0; std::string s; int len = 0; bool ok = true, side = extra == 0; int sideAt = extra ? (int)(rng() % 12) : -1;
            while (memcmp(&x, &solved, sizeof x)) {
                int want = (code + 1) % 3 + 1; bool wantSide = !side && len >= sideAt; if (wantSide) want = code;
                int cand[16], nc = 0; Config ys[16];
                for (int m = 0; m < 8; m++) for (int t = 1; t <= 2; t++) { Config y = defMove(x, m, t); if (tableCode(y) == want) { ys[nc] = y; cand[nc++] = m * 2 + (t - 1); } }
                if (!nc) { if (wantSide) { sideAt = len + 1; if (sideAt > 13) { ok = false; break; } continue; } ok = false; break; }
                int k = (int)(rng() % nc); x = ys[k]; if (wantSide) side = true; else code = want;
                s += " "; s += DEF_NAMES[cand[k] / 2]; if (cand[k] & 1) s += "'"; len++;
                if (len > 40) { ok = false; break; }
            }
            if (ok && side) sols.insert((len < 10 ? " " : "") + std::to_string(len) + s);
        }
        fprintf(fo, "P %s", line); for (auto& s : sols) fprintf(fo, "%s\n", s.c_str());
        n++; total += sols.size(); if (n % 50 == 0) { printf("%d positions, %llu solutions\n", n, (unsigned long long)total); fflush(stdout); }
    }
    fclose(fi); fclose(fo); printf("wrote %llu solutions for %d positions to %s\n", (unsigned long long)total, n, out.c_str());
    return 0;
}

// kernel throughput without any disk I/O: synthetic frontier bitmaps of a given density
static int cmdBench(double density) {
    FCUR.idx.assign(NCLASS, Rec()); CODE_NEXT = 1;
    for (int mode = 0; mode < 2; mode++) {
        std::atomic<u64> ops{0}, hits{0}; std::atomic<int> ready{0}; std::atomic<bool> go{false}; std::vector<std::thread> th;
        for (int t = 0; t < OPT.threads; t++) th.emplace_back([&, t]() {
            Worker w; std::mt19937_64 rng(t + 1); u64 thr = (u64)(density * 18446744073709551615.0);
            for (u32 i = 0; i < BM_WORDS; i++) { u64 x = 0; for (int b = 0; b < 64; b++) x |= (u64)(rng() < thr) << b; w.srcbm[i] = x; }
            memset(w.dest, 0, SECTOR_FILE); Rec r; r.fmt = 1; r.present = true; r.count = 0; for (u32 i = 0; i < BM_WORDS; i++) r.count += _mm_popcnt_u64(w.srcbm[i]);
            const Pair& pr = PAIRS[(size_t)(t * 53 + 7) * 16 + 5]; u64 probes = 0, f;
            ready++; while (!go) Sleep(1);
            if (mode == 0) { f = pullPair(w, pr, (const u8*)w.srcbm, r); probes = r.count; } else f = pushPair(w, pr, w.srcbm, probes, 0);
            ops += probes; hits += f;
        });
        while (ready.load() < OPT.threads) Sleep(5);
        double t0 = now(); go = true;
        for (auto& x : th) x.join();
        double dt = now() - t0;
        printf("%s: %d threads, density %.2f: %.3e lookups, %.3e hits, %.2fs -> %.0f M lookups/s (%.1f ns per lookup per thread)\n", mode ? "reverse (push)" : "forward (pull)", OPT.threads, density,
               (double)ops.load(), (double)hits.load(), dt, ops.load() / dt / 1e6, dt * OPT.threads / ops.load() * 1e9);
    }
    return 0;
}

static int cmdSelftest(int refDepth) {
    printf("symmetries: %zu, rotations: %zu, sectors (centre classes): %u\n", K.size(), ROTS.size(), NCLASS);
    std::map<u32, u32> hist; for (u32 s : STAB) hist[s]++;
    for (auto [k, c] : hist) printf("  stabiliser %u: %u sectors\n", k, c);
    printf("canonical entries: %llu  (table %.2f GB at 2 bits)\n", (unsigned long long)NCLASS * CAP, (double)NCLASS * SECTOR_FILE / 1e9);
    printf("weighted capacity == 12!/3!^4 * 11!/2 == %llu: ok\n", (unsigned long long)TOTAL_STATES);
    std::mt19937_64 rng(1); Unranker un;
    for (int i = 0; i < 3000000; i++) { u32 x = (u32)(rng() % CAP); alignas(16) u8 t[16]; _mm_store_si128((__m128i*)t, unrank12(x, un)); CHECK(rank12(t) == x);
        u32 inv = 0, used = 0; for (int a = 0; a < 12; a++) { used |= 1u << t[a]; for (int b = a + 1; b < 12; b++) inv += t[b] < t[a]; } CHECK(used == 0xFFF && inv % 2 == 0); }
    for (u32 x = 0; x < 2000000; x++) { alignas(16) u8 t[16]; _mm_store_si128((__m128i*)t, unrank12(x, un)); CHECK(rank12(t) == x); }
    printf("edge rank/unrank round trip (even permutations of 12): ok\n");
    // pair maps are bijections of even permutations, and commute with the definition file:
    // lift a fixed-edge state, apply a definition move, compare with face turn + renormalisation.
    for (int i = 0; i < 200000; i++) {
        u32 D = (u32)(rng() % NCLASS); int m = (int)(rng() % 16); const Pair& pr = PAIRS[(size_t)D * 16 + m];
        u32 x = (u32)(rng() % CAP); __m128i p = unrank12(x, un), q = _mm_shuffle_epi8(_mm_loadu_si128((const __m128i*)pr.R), _mm_shuffle_epi8(p, _mm_loadu_si128((const __m128i*)pr.L)));
        alignas(16) u8 t[16]; _mm_store_si128((__m128i*)t, q); u32 inv = 0; for (int a = 0; a < 12; a++) for (int b = a + 1; b < 12; b++) inv += t[b] < t[a]; CHECK(inv % 2 == 0);
    }
    {   // fast kernel path == straightforward unrank / shuffle / rank
        PairTab* pt = (PairTab*)_aligned_malloc(sizeof(PairTab), 64);
        for (int i = 0; i < 3000; i++) {
            const Pair& pr = PAIRS[rng() % PAIRS.size()]; buildPairTab(*pt, pr.L, pr.R);
            for (int j = 0; j < 300; j++) {
                u32 x = (u32)(rng() % CAP), hi = x / 360, lo = x % 360, par;
                __m128i rem = blockRem(hi, pt->R, par); alignas(16) u8 a[16], b[16];
                _mm_store_si128((__m128i*)a, _mm_shuffle_epi8(rem, pt->SL[par][lo]));
                Unranker u2; _mm_store_si128((__m128i*)b, _mm_shuffle_epi8(_mm_loadu_si128((const __m128i*)pr.R), _mm_shuffle_epi8(unrank12(x, u2), _mm_loadu_si128((const __m128i*)pr.L))));
                CHECK(!memcmp(a, b, 12) && rank12f(a) == rank12(b));
            }
        }
        _aligned_free(pt); printf("fast kernel tables == reference index maths (900000 random maps): ok\n");
    }
    static const int DEF2FACE[8] = {0, 1, 2, 3, 4, 5, 6, 7};  // F,Fw(=B),D,Dw(=U),L,BR,BL,R
    for (int i = 0; i < 200000; i++) {
        Config x; unpackC(REP[rng() % NCLASS], x.cc); unrankTo((u32)(rng() % CAP), x.p); x = normalize(applySym(K[rng() % 288], x));
        for (int m = 0; m < 8; m++) {
            Config y; for (int j = 0; j < 12; j++) y.cc[j] = x.cc[DEF_C[m][j] - 1]; for (int j = 0; j < 11; j++) y.p[j] = x.p[DEF_E[m][j] - 1]; y.p[11] = 11;
            Config a = normalize(applySym(MOVE[DEF2FACE[m]], x)), b = normalize(applySym(MOVE[DEF2FACE[m] + 8], x));
            bool ok = (!memcmp(&a, &y, sizeof y)) || (!memcmp(&b, &y, sizeof y)); CHECK(ok);
        }
    }
    printf("definition-file moves == plain face turns modulo rotation (200000 random states x 8 moves): ok\n");
    if (refDepth > 0) refBfs(refDepth);
    return 0;
}

int main(int argc, char** argv) {
    setvbuf(stdout, 0, _IOLBF, 1 << 12);
    if (argc < 2) { printf("usage: fto_bfs start|resume|status|export|verify|selftest [--dir D] [--threads N] [--stop-depth N] [--cache-mib N] [--max-seconds S]\n"
                           "       export [--depth N [--limit K] [--out FILE]]   verify [--sectors N] [--samples K]   selftest [--ref-depth N]\n"); return 1; }
    std::string cmd = argv[1], out, fdir, inFile; int depth = -1, refDepth = 0, vsec = 3; long long limit = -1; u64 vsamp = 200000; double density = 0.4;
    for (int i = 2; i < argc; i++) {
        std::string a = argv[i]; auto val = [&]() { if (i + 1 >= argc) die("missing value for %s", a.c_str()); return std::string(argv[++i]); };
        if (a == "--dir") DIR = val(); else if (a == "--threads") OPT.threads = atoi(val().c_str()); else if (a == "--stop-depth") OPT.stopDepth = atoi(val().c_str());
        else if (a == "--cache-mib") OPT.cacheBytes = (u64)atoll(val().c_str()) << 20; else if (a == "--list-max") OPT.listMax = (u64)atoll(val().c_str());
        else if (a == "--max-seconds") OPT.maxSeconds = atof(val().c_str()); else if (a == "--depth") depth = atoi(val().c_str()); else if (a == "--limit") limit = atoll(val().c_str());
        else if (a == "--out") out = val(); else if (a == "--ref-depth") refDepth = atoi(val().c_str()); else if (a == "--sectors") vsec = atoi(val().c_str());
        else if (a == "--samples") vsamp = (u64)atoll(val().c_str()); else if (a == "--back-factor") OPT.backFactor = atof(val().c_str());
        else if (a == "--force-back-mod") OPT.forceBackMod = atoi(val().c_str()); else if (a == "--density") density = atof(val().c_str());
        else if (a == "--force-u") OPT.forceU = true; else if (a == "--in") inFile = val();
        else if (a == "--frontier-dir") fdir = val(); else if (a == "--materialize-at") OPT.materializeAt = atoi(val().c_str()); else die("unknown option %s", a.c_str());
    }
    CHECK(OPT.threads >= 1 && OPT.threads <= 64);
    buildModel();
    if (cmd == "selftest") return cmdSelftest(refDepth);
    if (cmd == "bench") return cmdBench(density);
    if (DIR.empty()) die("--dir is required");
    if (cmd == "start") return cmdRun(true, fdir);
    if (cmd == "resume") return cmdRun(false, fdir);
    if (cmd == "status") return cmdStatus();
    if (cmd == "export") return cmdExport(depth, limit, out);
    if (cmd == "verify") return cmdVerify(vsec, vsamp);
    if (cmd == "solve") return cmdSolve(inFile, out);
    if (cmd == "optimals") return cmdOptimals(inFile, out, limit > 0 ? (int)limit : 32);
    die("unknown command %s", cmd.c_str());
}
