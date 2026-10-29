// FTO phase-2 upper bounds: BFS of the FULL puzzle with ordinary single face turns, restricted to positions
// whose CENTERS+EDGES part (the phase-1 state) is within R moves of solved.
//
// In the frame where the B U edge is home, a full position is a pair (phase-1 state p, phase-2 state f):
//   p = EDGES permutation + CENTERS colouring,   f = corner state (11520) x CENTERS2 colouring (369600),
// and every face turn acts on p and on f independently (U and B carry a fixed whole-puzzle rotation).
// The search keeps p inside the ball of radius R (1 / 17 / 201 / 2249 states for R = 0..3).  The depth at which
// (solved p, f) is reached is a proven upper bound on the optimal solution length of the phase-2 position f,
// and is exact whenever some optimal solution stays within R moves of phase-1-solved.
//
// No visited table: in a BFS, new(d+1) = neighbours(frontier d) - frontier d - frontier d-1, per phase-1 node.
// A face turn maps one corner row (369600 bits = 46 KB) onto another, so the kernel stays inside the L2 cache.
#define NOMINMAX
#include <windows.h>
#include <immintrin.h>
#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <random>
#include <mutex>
#include <string>
#include <functional>
#include <thread>
#include <unordered_map>
#include <vector>
#include "full_tables.h"
typedef uint8_t u8; typedef uint16_t u16; typedef uint32_t u32; typedef uint64_t u64;
[[noreturn]] static void die(const char* fmt, ...) { va_list ap; va_start(ap, fmt); fprintf(stderr, "ERROR: "); vfprintf(stderr, fmt, ap); fprintf(stderr, "\n"); va_end(ap); exit(2); }
#define CHECK(c) do { if (!(c)) die("check failed: %s (line %d)", #c, __LINE__); } while (0)
typedef std::array<u8, 60> St;
struct H60 { size_t operator()(const St& a) const { u64 h = 1469598103934665603ull; for (size_t i = 0; i + 8 <= 60; i += 4) { u64 w; memcpy(&w, a.data() + i, 8); h = (h ^ w) * 0x9E3779B97F4A7C15ull; h ^= h >> 29; } return (size_t)h; } };
static const u32 NC2 = 369600, ROWW = NC2 / 64;      // one corner row = 5775 words exactly
static u32 NCO = 0; static u64 NF = 0, NWORDS = 0;
static u8 MN[16][60];                               // normalised moves: face turn, then the rotation that brings B U home
static std::vector<u16> CM; static std::vector<u32> C2M;   // [m][corner], [m][colouring]
static std::vector<std::array<u8, 24>> NODEKEY; static std::vector<int> PT;   // phase-1 ball and its move table (-1 = leaves the ball)
static std::vector<int> NODEDEPTH;
static int THREADS = 24, MAXDEPTH = -1; static std::string DIR; static u64 SPARSE_LIMIT = 5000000; static int TARGET = -1; static bool CHUNK_FORCE = false, LIST_OFF = false; static int BWORKERS = 3, KEEPDEPTH = 0;   // files of phase-1 classes this close to solved are kept for every layer
static std::map<std::array<u8, 24>, u32> CIDX; static std::vector<std::array<u8, 24>> CS; static std::vector<u32> COLS, COLIDX;

// ---- symmetry-reduced phase-1 ball.  A transformation of positions in pull form: new[i] = la[old[pi[i]]].
// K = whole-puzzle rotations x piece relabelings x mirror (288); the 24 symmetries of fixed-edge positions are
// the elements of K that leave the B U edge home.  With --sym 0, K is just the identity.
typedef std::array<u8, 24> PKey;                 // EDGES permutation (12) + CENTERS colours (12)
struct Sym { u8 pi[60], la[60]; bool operator<(const Sym& o) const { return memcmp(this, &o, sizeof(Sym)) < 0; } };
static Sym symId() { Sym s; for (int i = 0; i < 60; i++) s.pi[i] = s.la[i] = (u8)i; return s; }
static Sym symMul(const Sym& a, const Sym& b) { Sym r; for (int i = 0; i < 60; i++) { r.pi[i] = a.pi[b.pi[i]]; r.la[i] = b.la[a.la[i]]; } return r; }   // a then b
static std::vector<Sym> KSYM;
struct Edge { int src; Sym t; int mv = -1; };   // mv: the move this edge ends with                 // f(dest) receives t applied to f(source)
static std::vector<PKey> NREP; static std::vector<int> NDEPTH; static std::vector<u32> NORBIT; static std::vector<std::vector<Edge>> EDGES;
static PKey applyP(const Sym& k, const PKey& p) {
    PKey r; u8 lc[4]; for (int j = 0; j < 12; j++) lc[FULL_COL1[j]] = FULL_COL1[k.la[36 + j] - 36];
    for (int i = 0; i < 12; i++) { r[i] = k.la[p[k.pi[i]]]; r[12 + i] = lc[p[12 + k.pi[36 + i] - 36]]; }
    return r;
}
static void buildSym(int R, bool useSym) {
    KSYM.clear(); KSYM.push_back(symId());
    if (useSym) {
        std::vector<Sym> gens;
        auto inv60 = [](const u8* p, u8* q) { for (int i = 0; i < 60; i++) q[p[i]] = (u8)i; };
        for (int r = 0; r < 12; r++) { Sym a = symId(); memcpy(a.pi, FULL_ROT[r], 60); gens.push_back(a); Sym b = symId(); inv60(FULL_ROT[r], b.la); gens.push_back(b); }
        { Sym m; memcpy(m.pi, FULL_MIRROR, 60); inv60(FULL_MIRROR, m.la); gens.push_back(m); }
        std::map<Sym, int> seen; seen[KSYM[0]] = 0;
        for (size_t i = 0; i < KSYM.size(); i++) for (auto& g : gens) { Sym y = symMul(KSYM[i], g); if (seen.insert({y, 0}).second) { KSYM.push_back(y); CHECK(KSYM.size() <= 288); } }
        CHECK(KSYM.size() == 288);
        for (auto& k : KSYM) {      // every element must map colour classes to colour classes in both centre sets
            for (int base : {36, 48}) { const u8* col = base == 36 ? FULL_COL1 : FULL_COL2; int cm[4] = {-1, -1, -1, -1};
                for (int j = 0; j < 12; j++) { int a = col[j], b = col[k.la[base + j] - base]; CHECK(cm[a] < 0 || cm[a] == b); cm[a] = b; } }
        }
    }
    auto canon = [&](const PKey& p, u32* orbit) { PKey best = p; std::vector<PKey> imgs;
        for (auto& k : KSYM) { PKey q = applyP(k, p); if (q[10] != 10) continue; imgs.push_back(q); if (q < best) best = q; }
        if (orbit) { std::sort(imgs.begin(), imgs.end()); *orbit = (u32)(std::unique(imgs.begin(), imgs.end()) - imgs.begin()); }
        return best; };
    PKey p0; for (int i = 0; i < 12; i++) { p0[i] = (u8)i; p0[12 + i] = FULL_COL1[i]; }
    std::map<PKey, int> nidx; u32 orb; CHECK(canon(p0, &orb) == p0);
    NREP = {p0}; NDEPTH = {0}; NORBIT = {orb}; nidx[p0] = 0;
    Sym mv[16], mvinv[16]; for (int m = 0; m < 16; m++) { mv[m] = symId(); memcpy(mv[m].pi, MN[m], 60); mvinv[m] = symId(); for (int i = 0; i < 60; i++) mvinv[m].pi[MN[m][i]] = (u8)i; }
    for (size_t i = 0; i < NREP.size(); i++) if (NDEPTH[i] < R) for (int m = 0; m < 16; m++) {
        PKey t = canon(applyP(mv[m], NREP[i]), &orb);
        if (nidx.insert({t, (int)NREP.size()}).second) { NREP.push_back(t); NDEPTH.push_back(NDEPTH[i] + 1); NORBIT.push_back(orb); }
    }
    EDGES.assign(NREP.size(), {});
    for (size_t q = 0; q < NREP.size(); q++) for (int m = 0; m < 16; m++) {
        PKey p = applyP(mvinv[m], NREP[q]); CHECK(p[10] == 10 && applyP(mv[m], p) == NREP[q]);
        auto it = nidx.find(canon(p, nullptr)); if (it == nidx.end()) continue;      // predecessor lies outside the ball
        const PKey& rep = NREP[it->second]; bool found = false;
        for (auto& k : KSYM) if (applyP(k, rep) == p) { Edge e; e.src = it->second; e.t = symMul(k, mv[m]); e.mv = m; CHECK(applyP(e.t, rep) == NREP[q]); EDGES[q].push_back(e); found = true; break; }
        CHECK(found);
    }
}
// index maps of one edge on the two phase-2 coordinates
static void buildMaps(const Sym& t, std::vector<u16>& cmap, std::vector<u32>& c2map, int nth) {
    const int THREADS = nth;
    cmap.resize(NCO); c2map.resize(NC2);
    u8 lc[4]; for (int j = 0; j < 12; j++) lc[FULL_COL2[j]] = FULL_COL2[t.la[48 + j] - 48];
    std::vector<std::thread> th;
    for (int w = 0; w < THREADS; w++) th.emplace_back([&, w]() {
        for (u32 i = (u32)((u64)NCO * w / THREADS); i < (u32)((u64)NCO * (w + 1) / THREADS); i++) { std::array<u8, 24> c; for (int j = 0; j < 24; j++) c[j] = t.la[CS[i][t.pi[12 + j] - 12]]; auto it = CIDX.find(c); if (it == CIDX.end()) die("symmetry leaves the corner set"); cmap[i] = (u16)it->second; }
        for (u32 i = (u32)((u64)NC2 * w / THREADS); i < (u32)((u64)NC2 * (w + 1) / THREADS); i++) { u32 v = 0; for (int j = 0; j < 12; j++) v |= (u32)lc[(COLS[i] >> (2 * (t.pi[48 + j] - 48))) & 3] << (2 * j); u32 x = COLIDX[v]; if (x == 0xffffffffu) die("bad colouring"); c2map[i] = x; }
    });
    for (auto& x : th) x.join();
}
static double now() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }

static void buildModel(int R) {
    u8 mv[16][60];
    for (int m = 0; m < 8; m++) for (int i = 0; i < 60; i++) mv[m][i] = FULL_MOVE[m][i];
    for (int m = 0; m < 8; m++) for (int i = 0; i < 60; i++) mv[m + 8][i] = mv[m][mv[m][i]];
    for (int m = 0; m < 16; m++) { int r = 0; for (; r < 12; r++) if (mv[m][FULL_ROT[r][10]] == 10) break; CHECK(r < 12); for (int i = 0; i < 60; i++) MN[m][i] = mv[m][FULL_ROT[r][i]]; }
    // corner coordinate
    auto& cidx = CIDX; auto& cs = CS; std::array<u8, 24> c0; for (int i = 0; i < 24; i++) c0[i] = (u8)(12 + i);
    cs.push_back(c0); cidx[c0] = 0;
    for (size_t i = 0; i < cs.size(); i++) for (int m = 0; m < 16; m++) { std::array<u8, 24> t; for (int j = 0; j < 24; j++) t[j] = cs[i][MN[m][12 + j] - 12]; if (cidx.insert({t, (u32)cs.size()}).second) cs.push_back(t); }
    NCO = (u32)cs.size(); CHECK(NCO == 11520);
    CM.resize(16 * (size_t)NCO);
    for (u32 i = 0; i < NCO; i++) for (int m = 0; m < 16; m++) { std::array<u8, 24> t; for (int j = 0; j < 24; j++) t[j] = cs[i][MN[m][12 + j] - 12]; CM[(size_t)m * NCO + i] = (u16)cidx.at(t); }
    // CENTERS2 colouring coordinate
    std::vector<u32> cols; { u8 c[12]; int left[4] = {3, 3, 3, 3};
        auto rec = [&](auto&& self, int i) -> void { if (i == 12) { u32 v = 0; for (int k = 0; k < 12; k++) v |= (u32)c[k] << (2 * k); cols.push_back(v); return; } for (int k = 0; k < 4; k++) if (left[k]) { left[k]--; c[i] = (u8)k; self(self, i + 1); left[k]++; } };
        rec(rec, 0); }
    std::sort(cols.begin(), cols.end()); CHECK(cols.size() == NC2);
    COLS = cols; COLIDX.assign(1u << 24, 0xffffffffu); for (u32 i = 0; i < NC2; i++) COLIDX[cols[i]] = i;
    C2M.resize(16 * (size_t)NC2);
    for (u32 i = 0; i < NC2; i++) for (int m = 0; m < 16; m++) { u32 v = 0; for (int k = 0; k < 12; k++) v |= ((cols[i] >> (2 * (MN[m][48 + k] - 48))) & 3) << (2 * k);
        auto it = std::lower_bound(cols.begin(), cols.end(), v); CHECK(it != cols.end() && *it == v); C2M[(size_t)m * NC2 + i] = (u32)(it - cols.begin()); }
    NF = (u64)NCO * NC2; NWORDS = NF / 64; CHECK(NF % 64 == 0 && NF < (1ull << 32));
    // phase-1 ball: key = EDGES permutation (12) + CENTERS colours (12)
    std::map<std::array<u8, 24>, int> pidx; std::array<u8, 24> p0; for (int i = 0; i < 12; i++) { p0[i] = (u8)i; p0[12 + i] = FULL_COL1[i]; }
    NODEKEY.push_back(p0); NODEDEPTH.push_back(0); pidx[p0] = 0;
    auto pmove = [&](const std::array<u8, 24>& a, int m) { std::array<u8, 24> t; for (int j = 0; j < 12; j++) { t[j] = a[MN[m][j]]; t[12 + j] = a[12 + MN[m][36 + j] - 36]; } return t; };
    for (size_t i = 0; i < NODEKEY.size(); i++) if (NODEDEPTH[i] < R) for (int m = 0; m < 16; m++) { auto t = pmove(NODEKEY[i], m); if (pidx.insert({t, (int)NODEKEY.size()}).second) { NODEKEY.push_back(t); NODEDEPTH.push_back(NODEDEPTH[i] + 1); } }
    PT.assign(NODEKEY.size() * 16, -1);
    for (size_t i = 0; i < NODEKEY.size(); i++) for (int m = 0; m < 16; m++) { auto it = pidx.find(pmove(NODEKEY[i], m)); if (it != pidx.end()) PT[i * 16 + m] = it->second; }
    // sanity: the solved phase-2 state is corner 0 with the solved colouring; moves have order 3
    for (int m = 0; m < 8; m++) for (u32 i = 0; i < NCO; i += 97) CHECK(CM[(size_t)m * NCO + CM[(size_t)m * NCO + CM[(size_t)m * NCO + i]]] == i || (m == 1 || m == 3));
}
static u32 solvedC2() {   // index of the solved colouring
    std::vector<u32> cols; { u8 c[12]; int left[4] = {3, 3, 3, 3};
        auto rec = [&](auto&& self, int i) -> void { if (i == 12) { u32 v = 0; for (int k = 0; k < 12; k++) v |= (u32)c[k] << (2 * k); cols.push_back(v); return; } for (int k = 0; k < 4; k++) if (left[k]) { left[k]--; c[i] = (u8)k; self(self, i + 1); left[k]++; } };
        rec(rec, 0); }
    std::sort(cols.begin(), cols.end()); u32 v = 0; for (int k = 0; k < 12; k++) v |= (u32)FULL_COL2[k] << (2 * k);
    return (u32)(std::lower_bound(cols.begin(), cols.end(), v) - cols.begin());
}

// ---- frontier files: [u64 count][u32 fmt][u32 pad] + sorted u32 list (fmt 0) or bitmap (fmt 1)
struct Set { u64 count = 0; u32 fmt = 0; std::vector<u32> list; u64* bm = nullptr; };
static std::string fpath(int depth, int node) { char b[64]; snprintf(b, sizeof b, "\\f_%02d_%04d.bin", depth, node); return DIR + b; }
static void ioAll(HANDLE h, void* buf, u64 n, bool wr) { u8* p = (u8*)buf; while (n) { DWORD w = (DWORD)std::min<u64>(n, 1u << 26), got = 0; if (!(wr ? WriteFile(h, p, w, &got, 0) : ReadFile(h, p, w, &got, 0)) || !got) die("%s failed (error %lu)", wr ? "write" : "read", GetLastError()); p += got; n -= got; } }
static std::atomic<u64> IO_R{0}, IO_W{0};
static bool headerOf(int depth, int node, u64& count, u32& fmt) {
    HANDLE h = CreateFileA(fpath(depth, node).c_str(), GENERIC_READ, FILE_SHARE_READ, 0, OPEN_EXISTING, 0, 0); if (h == INVALID_HANDLE_VALUE) return false;
    u64 hd[2]; ioAll(h, hd, 16, false); CloseHandle(h); count = hd[0]; fmt = (u32)(hd[1] & 0xff); if (fmt == 3) fmt = 1; return true;   // 2 (gap bytes) loads as a list, 3 (chunked gaps) as a bitmap
}
static const u32 CHR = 48;   // rows per chunk in format 3: every chunk decodes on its own, so threads can share the work
// load into s; a bitmap goes into `bmbuf`
static void loadSet(int depth, int node, Set& s, u64* bmbuf) {
    HANDLE h = CreateFileA(fpath(depth, node).c_str(), GENERIC_READ, FILE_SHARE_READ, 0, OPEN_EXISTING, FILE_FLAG_SEQUENTIAL_SCAN, 0); if (h == INVALID_HANDLE_VALUE) die("missing %s", fpath(depth, node).c_str());
    u64 hd[2]; ioAll(h, hd, 16, false); s.count = hd[0]; s.fmt = (u32)(hd[1] & 0xff); s.list.clear(); s.bm = nullptr;
    if (s.fmt == 0) { s.list.resize(s.count); if (s.count) ioAll(h, s.list.data(), s.count * 4, false); IO_R += s.count * 4; }
    else if (s.fmt == 2) {   // gap bytes: gap < 255 in one byte, else 255 + u32
        u64 bytes = hd[1] >> 8; std::vector<u8> raw(bytes); ioAll(h, raw.data(), bytes, false); IO_R += bytes;
        s.list.resize(s.count); const u8* p = raw.data(); const u8* end = p + bytes; u32 prev = 0xffffffffu; u64 k = 0;
        while (p < end) { u32 g = *p++; if (g == 255) { memcpy(&g, p, 4); p += 4; } prev += g; s.list[k++] = prev; }
        CHECK(k == s.count); s.fmt = 0;
    }
    else if (s.fmt == 3) {   // gap bytes in independent chunks of CHR rows -> bitmap
        CHECK(bmbuf); const u32 NCH = NCO / CHR; std::vector<u64> offs(NCH + 1); ioAll(h, offs.data(), (NCH + 1) * 8, false);
        std::vector<u8> raw(offs[NCH]); ioAll(h, raw.data(), raw.size(), false); IO_R += raw.size();
        std::atomic<u32> next{0}; std::atomic<u64> got{0}; std::vector<std::thread> th;
        for (int t = 0; t < THREADS; t++) th.emplace_back([&]() { u64 k = 0;
            for (;;) { u32 c = next++; if (c >= NCH) break; u64 w0 = (u64)c * CHR * ROWW, w1 = w0 + (u64)CHR * ROWW; memset(bmbuf + w0, 0, (w1 - w0) * 8);
                const u8* p = raw.data() + offs[c]; const u8* end = raw.data() + offs[c + 1]; u32 prev = (u32)(w0 * 64) - 1;
                while (p < end) { u32 g = *p++; if (g == 255) { memcpy(&g, p, 4); p += 4; } prev += g; bmbuf[prev >> 6] |= 1ull << (prev & 63); k++; } }
            got += k; });
        for (auto& x : th) x.join();
        CHECK(got.load() == s.count); s.fmt = 1; s.bm = bmbuf;
    }
    else { CHECK(bmbuf); ioAll(h, bmbuf, NWORDS * 8, false); s.bm = bmbuf; IO_R += NWORDS * 8; }
    CloseHandle(h);
}
// bitmap -> chunked gap bytes (format 3); used when that is clearly smaller than the raw bitmap
static void saveSetChunked(int depth, int node, u64 count, const u64* bm) {
    const u32 NCH = NCO / CHR; std::vector<std::vector<u8>> part(NCH); std::atomic<u32> next{0}; std::vector<std::thread> th;
    for (int t = 0; t < THREADS; t++) th.emplace_back([&]() {
        for (;;) { u32 c = next++; if (c >= NCH) break; u64 w0 = (u64)c * CHR * ROWW, w1 = w0 + (u64)CHR * ROWW; std::vector<u8>& o = part[c]; u32 prev = (u32)(w0 * 64) - 1;
            for (u64 w = w0; w < w1; w++) { u64 x = bm[w]; while (x) { u32 e = (u32)(w * 64 + _tzcnt_u64(x)); x &= x - 1; u32 g = e - prev; prev = e; if (g < 255) o.push_back((u8)g); else { o.push_back(255); u8 b4[4]; memcpy(b4, &g, 4); o.insert(o.end(), b4, b4 + 4); } } } } });
    for (auto& x : th) x.join();
    std::vector<u64> offs(NCH + 1, 0); for (u32 c = 0; c < NCH; c++) offs[c + 1] = offs[c] + part[c].size();
    std::string p = fpath(depth, node), tmp = p + ".tmp";
    HANDLE h = CreateFileA(tmp.c_str(), GENERIC_WRITE, 0, 0, CREATE_ALWAYS, FILE_FLAG_SEQUENTIAL_SCAN, 0); if (h == INVALID_HANDLE_VALUE) die("cannot write %s", tmp.c_str());
    u64 hd[2] = {count, 3 | (offs[NCH] << 8)}; ioAll(h, hd, 16, true); ioAll(h, offs.data(), (NCH + 1) * 8, true);
    for (u32 c = 0; c < NCH; c++) if (!part[c].empty()) ioAll(h, part[c].data(), part[c].size(), true);
    IO_W += offs[NCH]; CloseHandle(h);
    if (!MoveFileExA(tmp.c_str(), p.c_str(), MOVEFILE_REPLACE_EXISTING)) die("rename %s", p.c_str());
}
static void saveSet(int depth, int node, u64 count, const std::vector<u32>* list, const u64* bm) {
    std::string p = fpath(depth, node), tmp = p + ".tmp";
    HANDLE h = CreateFileA(tmp.c_str(), GENERIC_WRITE, 0, 0, CREATE_ALWAYS, FILE_FLAG_SEQUENTIAL_SCAN, 0); if (h == INVALID_HANDLE_VALUE) die("cannot write %s", tmp.c_str());
    if (list && count > 100000) {   // dense enough that gaps mostly fit one byte
        std::vector<u8> raw; raw.reserve(count + count / 8 + 64); u32 prev = 0xffffffffu;
        for (u32 e : *list) { u32 g = e - prev; prev = e; if (g < 255) raw.push_back((u8)g); else { raw.push_back(255); u8 b4[4]; memcpy(b4, &g, 4); raw.insert(raw.end(), b4, b4 + 4); } }
        u64 hd[2] = {count, 2 | ((u64)raw.size() << 8)}; ioAll(h, hd, 16, true); ioAll(h, raw.data(), raw.size(), true); IO_W += raw.size();
    } else {
    u64 hd[2] = {count, (u64)(list ? 0 : 1)}; ioAll(h, hd, 16, true);
    if (list) { if (count) ioAll(h, (void*)list->data(), count * 4, true); IO_W += count * 4; } else { ioAll(h, (void*)bm, NWORDS * 8, true); IO_W += NWORDS * 8; }
    }
    CloseHandle(h);
    if (!MoveFileExA(tmp.c_str(), p.c_str(), MOVEFILE_REPLACE_EXISTING)) die("rename %s", p.c_str());
}
template <class F> static void parallel(u64 n, F&& fn) {   // fn(thread, lo, hi) over [0,n) in THREADS contiguous chunks
    std::vector<std::thread> th; for (int t = 0; t < THREADS; t++) th.emplace_back([&, t]() { fn(t, n * t / THREADS, n * (t + 1) / THREADS); }); for (auto& x : th) x.join();
}
template <class F> static void parallelRows(F&& fn) {      // fn(row) for every corner row, dynamic
    std::atomic<u32> next{0}; std::vector<std::thread> th;
    for (int t = 0; t < THREADS; t++) th.emplace_back([&]() { for (;;) { u32 lo = next.fetch_add(16); if (lo >= NCO) break; for (u32 r = lo; r < std::min(NCO, lo + 16); r++) fn(r); } });
    for (auto& x : th) x.join();
}

static int cmdRun(int R) {
    CreateDirectoryA(DIR.c_str(), 0);
    const int NN = (int)NREP.size(); const u32 SOLC2 = solvedC2(); u64 physNodes = 0; for (u32 o : NORBIT) physNodes += o;
    std::vector<u16> cmv; std::vector<u32> c2v;
    printf("phase-1 ball: %llu states in %d symmetry classes (%zu symmetries)\n", (unsigned long long)physNodes, NN, KSYM.size() == 288 ? (size_t)24 : (size_t)1);
    printf("radius %d: %d phase-1 states x %llu phase-2 states = %.3e positions; up to %.0f GB per layer of frontier files\n", R, NN, (unsigned long long)NF, (double)NN * NF, NN * (NWORDS * 8.0) / 1e9);
    // sources of each node
    std::vector<std::vector<std::pair<int, int>>> src(NN);
    u64 edges = 0; for (auto& v : EDGES) edges += v.size(); printf("moves that stay inside the ball: %llu of %d\n", (unsigned long long)edges, NN * 16);
    // resume point
    int depth = 0; std::vector<u64> totals, node0;
    { FILE* f = fopen((DIR + "\\state.txt").c_str(), "r"); char line[256]; int r = -1;
      if (f) { while (fgets(line, sizeof line, f)) { int d; unsigned long long a, b; if (sscanf(line, "radius %d", &d) == 1) r = d; else if (sscanf(line, "target %d", &d) == 1) { if (d != TARGET) die("%s was started with --target %d", DIR.c_str(), d); } else if (sscanf(line, "layer %d %llu %llu", &d, &a, &b) == 3) { CHECK(d == (int)totals.size()); totals.push_back(a); node0.push_back(b); } } fclose(f);
          if (r != R) die("%s holds a search of radius %d", DIR.c_str(), r); depth = (int)totals.size() - 1; } }
    auto saveState = [&](bool complete) { std::string s = "fto-tube 1\nradius " + std::to_string(R) + "\ntarget " + std::to_string(TARGET) + "\n"; char b[128]; for (size_t d = 0; d < totals.size(); d++) { snprintf(b, sizeof b, "layer %zu %llu %llu\n", d, (unsigned long long)totals[d], (unsigned long long)node0[d]); s += b; } if (complete) s += "complete\n";
        std::string p = DIR + "\\state.txt", t = p + ".tmp"; FILE* f = fopen(t.c_str(), "w"); CHECK(f); fputs(s.c_str(), f); fclose(f); MoveFileExA(t.c_str(), p.c_str(), MOVEFILE_REPLACE_EXISTING); };
    if (totals.empty()) {   // depth 0: the solved position
        std::vector<u32> one = {SOLC2}; saveSet(0, 0, 1, &one, nullptr); std::vector<u32> none; for (int q = 1; q < NN; q++) saveSet(0, q, 0, &none, nullptr);
        totals.push_back(1); node0.push_back(1); saveState(false); depth = 0;
    }
    u64* cand = (u64*)VirtualAlloc(0, NWORDS * 8, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE); u64* buf = (u64*)VirtualAlloc(0, NWORDS * 8, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
    if (!cand || !buf) die("out of memory");
    double t0 = now(); const u64 SPARSE = SPARSE_LIMIT, PREVMAX = 8000000, CHUNKMAX = CHUNK_FORCE ? ~0ull : NF / 10;
    struct Ctx { u64* cand = nullptr; u64* buf = nullptr; u64* cand2 = nullptr; u64* buf2 = nullptr; std::vector<u16> cmv; std::vector<u32> c2v; Set s; int inner = 1; };
    u64* cand2 = nullptr; u64* buf2 = nullptr; std::vector<u64*> wb;   // extra buffer pairs for concurrent big destinations
    if (TARGET >= 0) { cand2 = (u64*)VirtualAlloc(0, NWORDS * 8, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE); buf2 = (u64*)VirtualAlloc(0, NWORDS * 8, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE); if (!cand2 || !buf2) die("out of memory"); }
    auto saveMarker = [&](int d, int q) { std::string p = fpath(d, q), tmp = p + ".tmp"; HANDLE h = CreateFileA(tmp.c_str(), GENERIC_WRITE, 0, 0, CREATE_ALWAYS, 0, 0); if (h == INVALID_HANDLE_VALUE) die("cannot write %s", tmp.c_str());
        u64 hd[2] = {0, 9}; ioAll(h, hd, 16, true); CloseHandle(h); if (!MoveFileExA(tmp.c_str(), p.c_str(), MOVEFILE_REPLACE_EXISTING)) die("rename %s", p.c_str()); };
    for (;; depth++) {
        if (MAXDEPTH >= 0 && depth >= MAXDEPTH) { printf("paused at --max-depth %d; run again to continue\n", MAXDEPTH); return 0; }
        if (TARGET >= 0 && depth >= TARGET) break;
        double tl = now(); std::atomic<u64> tot{0}, n0{0}, lookups{0};
        std::vector<u64> cnt(NN, 0); std::vector<u32> fm(NN, 0); for (int p = 0; p < NN; p++) if (!headerOf(depth, p, cnt[p], fm[p])) die("missing frontier file for depth %d node %d", depth, p);
        // candidate bitmap of node q for layer d+1: neighbours of the frontiers at layer d, minus this node's own
        // frontiers d and d-1.  Each source row lands in exactly one target row, so threads never collide.
        // A source whose layer was not stored (marker) is recomputed here from layer d-1 into the second buffers.
        std::function<void(int, int, u64*, u64*, Ctx&, bool)> markInto = [&](int q, int d, u64* target, u64* scratch, Ctx& cx, bool top) {
            Set& s = cx.s;
            parallel(NWORDS, [&](int, u64 lo, u64 hi) { memset(target + lo, 0, (hi - lo) * 8); });
            for (auto& E : EDGES[q]) {
                u64 c; u32 f; if (!headerOf(d, E.src, c, f)) die("missing frontier file for depth %d node %d", d, E.src);
                const u64* sbm = nullptr;
                if (f == 9) { CHECK(top && cx.cand2); markInto(E.src, d - 1, cx.cand2, cx.buf2, cx, false); sbm = cx.cand2; }
                else { if (!c) continue; loadSet(d, E.src, s, scratch); if (s.fmt == 1) sbm = s.bm; }
                buildMaps(E.t, cx.cmv, cx.c2v, cx.inner); const u16* cm = cx.cmv.data(); const u32* c2 = cx.c2v.data();
                if (sbm) parallelRows([&](u32 ci) { const u64* sr = sbm + (u64)ci * ROWW; u64* tr = target + (u64)cm[ci] * ROWW;
                    for (u32 w = 0; w < ROWW; w++) { u64 x = sr[w]; while (x) { u32 t = c2[w * 64 + (u32)_tzcnt_u64(x)]; tr[t >> 6] |= 1ull << (t & 63); x &= x - 1; } } });
                else { // list source: split at row boundaries so threads own whole rows
                    std::vector<size_t> cut(THREADS + 1); for (int t = 0; t <= THREADS; t++) { size_t i = s.list.size() * t / THREADS; while (i > 0 && i < s.list.size() && s.list[i] / NC2 == s.list[i - 1] / NC2) i++; cut[t] = i; }
                    std::vector<std::thread> th; for (int t = 0; t < THREADS; t++) th.emplace_back([&, t]() { for (size_t i = cut[t]; i < cut[t + 1]; i++) { u32 e = s.list[i], ci = e / NC2, k = e - ci * NC2; u64 tb = (u64)cm[ci] * NC2 + c2[k]; target[tb >> 6] |= 1ull << (tb & 63); } });
                    for (auto& x : th) x.join(); }
            }
            for (int back = 0; back < 2 && d - back >= 0; back++) { u64 c; u32 f; if (!headerOf(d - back, q, c, f) || !c) continue; CHECK(f != 9); loadSet(d - back, q, s, scratch);
                if (s.fmt == 1) parallel(NWORDS, [&](int, u64 lo, u64 hi) { for (u64 w = lo; w < hi; w++) target[w] &= ~s.bm[w]; });
                else for (u32 e : s.list) target[e >> 6] &= ~(1ull << (e & 63)); }
        };
        // one destination class.  Returns false if it needs the big buffers and this context has none.
        auto doDest = [&](int q, Ctx& cx) -> bool {
            u64 c; u32 f; if (headerOf(depth + 1, q, c, f)) { tot += c * NORBIT[q]; if (q == 0) n0 = c; return true; }   // already done (resume)
            u64 work = 0; for (auto& E : EDGES[q]) work += fm[E.src] == 9 ? SPARSE + 1 : cnt[E.src];
            std::vector<u32> out; u64 newc = 0; bool outBitmap = false;
            // with a target T, a position over a phase-1 state k moves from solved is useless after step T - k
            if (work == 0 || (TARGET >= 0 && depth + 1 + NDEPTH[q] > TARGET)) { saveSet(depth + 1, q, 0, &out, nullptr); return true; }
            // the outermost states' last useful layer is the biggest one and is read only once: do not store it,
            // leave a marker and let the next layer recompute it on the fly
            if (TARGET >= 0 && R >= 1 && NDEPTH[q] == R && depth + 1 + R == TARGET) { saveMarker(depth + 1, q); return true; }
            u64 pc[2] = {0, 0}; u32 pf[2] = {0, 0}; for (int back = 0; back < 2 && depth - back >= 0; back++) headerOf(depth - back, q, pc[back], pf[back]);
            bool srcBitmap = false; for (auto& E : EDGES[q]) if (cnt[E.src] && fm[E.src] == 1) srcBitmap = true;   // includes the chunked format, which decodes to a bitmap
            if (!cx.cand && (work > SPARSE || pc[0] > PREVMAX || pc[1] > PREVMAX || pf[0] == 1 || pf[1] == 1 || srcBitmap)) return false;
            Set& s = cx.s; lookups += work;
            if (work <= SPARSE && !srcBitmap) {
                // sparse: collect, sort, subtract the two previous frontiers of this node
                std::vector<u32> cv; cv.reserve(work);
                for (auto& E : EDGES[q]) if (cnt[E.src]) { loadSet(depth, E.src, s, cx.buf); CHECK(s.fmt == 0); buildMaps(E.t, cx.cmv, cx.c2v, cx.inner); const u16* cm = cx.cmv.data(); const u32* c2 = cx.c2v.data();
                    for (u32 e : s.list) { u32 ci = e / NC2, k = e - ci * NC2; cv.push_back((u32)cm[ci] * NC2 + c2[k]); } }
                std::sort(cv.begin(), cv.end()); cv.erase(std::unique(cv.begin(), cv.end()), cv.end());
                for (int back = 0; back < 2 && depth - back >= 0; back++) { if (!pc[back]) continue; loadSet(depth - back, q, s, cx.buf);
                    std::vector<u32> keep; keep.reserve(cv.size());
                    if (s.fmt == 0) std::set_difference(cv.begin(), cv.end(), s.list.begin(), s.list.end(), std::back_inserter(keep));
                    else for (u32 e : cv) if (!((s.bm[e >> 6] >> (e & 63)) & 1)) keep.push_back(e);
                    cv.swap(keep); }
                out.swap(cv); newc = out.size();
            } else {
                // dense: mark a candidate bitmap row by row (each source row lands in exactly one target row)
                u64* cand = cx.cand;
                markInto(q, depth, cand, cx.buf, cx, true);
                std::vector<u64> pcn(THREADS, 0); parallel(NWORDS, [&](int t, u64 lo, u64 hi) { u64 c2 = 0; for (u64 w = lo; w < hi; w++) c2 += (u64)_mm_popcnt_u64(cand[w]); pcn[t] = c2; });
                for (u64 x : pcn) newc += x;
                if (newc <= 2000000 && !LIST_OFF) { out.resize(newc);   /* larger sets go out as chunked gaps, which encode and decode on all cores */ std::vector<u64> off(THREADS + 1, 0); for (int t = 0; t < THREADS; t++) off[t + 1] = off[t] + pcn[t];
                    parallel(NWORDS, [&](int t, u64 lo, u64 hi) { u64 k = off[t]; for (u64 w = lo; w < hi; w++) { u64 x = cand[w]; while (x) { out[k++] = (u32)(w * 64 + _tzcnt_u64(x)); x &= x - 1; } } });
                } else outBitmap = true;
            }
            if (outBitmap && newc <= CHUNKMAX) saveSetChunked(depth + 1, q, newc, cx.cand);    // about a byte per entry: smaller than the bitmap below ~10% full
            else if (outBitmap) saveSet(depth + 1, q, newc, nullptr, cx.cand); else saveSet(depth + 1, q, newc, &out, nullptr);
            tot += newc * NORBIT[q]; if (q == 0) n0 = newc;
            return true;
        };
        // pass A: small destinations, many at once; pass B: the rest one at a time with all threads inside
        std::vector<u8> deferred(NN, 0); { std::atomic<int> next{0}; std::vector<std::thread> th;
            for (int t = 0; t < THREADS; t++) th.emplace_back([&]() { Ctx cx; for (;;) { int q = next++; if (q >= NN) break; if (!doDest(q, cx)) deferred[q] = 1; } });
            for (auto& x : th) x.join(); }
        {   // big destinations: a few at a time (each needs ~1 GB of buffers and has serial stretches), except in the
            // layer that recomputes unstored sources, which needs the second pair of buffers
            bool anyMarker = false; for (u32 f : fm) anyMarker |= f == 9;
            MEMORYSTATUSEX ms; ms.dwLength = sizeof ms; GlobalMemoryStatusEx(&ms);
            int W = anyMarker ? 1 : std::max(1, std::min(BWORKERS, (int)(ms.ullAvailPhys / (3ull << 30))));
            while ((int)wb.size() < 2 * (W - 1)) { u64* p = (u64*)VirtualAlloc(0, NWORDS * 8, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE); if (!p) { W = 1 + (int)wb.size() / 2; break; } wb.push_back(p); }
            std::atomic<int> next{0}; std::vector<std::thread> th;
            for (int t = 0; t < W; t++) th.emplace_back([&, t]() { Ctx cx; cx.inner = THREADS;
                if (t == 0) { cx.cand = cand; cx.buf = buf; cx.cand2 = cand2; cx.buf2 = buf2; } else { cx.cand = wb[2 * (t - 1)]; cx.buf = wb[2 * (t - 1) + 1]; }
                for (;;) { int q = next++; if (q >= NN) break; if (deferred[q]) CHECK(doDest(q, cx)); } });
            for (auto& x : th) x.join();
        }
        if (tot == 0) { for (int q = 0; q < NN; q++) DeleteFileA(fpath(depth + 1, q).c_str()); break; }
        totals.push_back(tot); node0.push_back(n0); saveState(false);
        // drop layers no longer needed (node 0 files are the result: keep them all).  The layer after an unstored
        // one still needs the two layers before it, so nothing is dropped right after writing markers.
        if (!(TARGET >= 0 && depth + 1 + R == TARGET)) for (int dd = std::max(0, depth - 2); dd <= depth - 1; dd++) for (int q = 1; q < NN; q++) if (NDEPTH[q] > KEEPDEPTH) DeleteFileA(fpath(dd, q).c_str());
        u64 dsk = 0; { WIN32_FIND_DATAA fd; HANDLE h = FindFirstFileA((DIR + "\\f_*.bin").c_str(), &fd); if (h != INVALID_HANDLE_VALUE) { do dsk += ((u64)fd.nFileSizeHigh << 32) | fd.nFileSizeLow; while (FindNextFileA(h, &fd)); FindClose(h); } }
        printf("depth %d: %llu positions, %llu with phase 1 solved  (%.3e lookups, layer %.0fs, run %.0fs, read %.0f GB, written %.0f GB, on disk %.0f GB)\n", depth + 1, (unsigned long long)tot.load(), (unsigned long long)n0.load(), (double)lookups.load(), now() - tl, now() - t0, IO_R.load() / 1e9, IO_W.load() / 1e9, dsk / 1e9); fflush(stdout);
    }
    saveState(true);
    u64 all = 0, a0 = 0; for (u64 x : totals) all += x; for (u64 x : node0) a0 += x;
    printf("\nCOMPLETE. positions reached %llu of %llu; phase-2 positions reached %llu of %llu\n", (unsigned long long)all, (unsigned long long)(physNodes * NF), (unsigned long long)a0, (unsigned long long)NF);
    if (TARGET >= 0) printf("target %d: %llu phase-2 positions have a solution of at most %d moves; %llu do not (within radius %d)\n", TARGET, (unsigned long long)a0, TARGET, (unsigned long long)(NF - a0), R);
    printf("phase-2 upper bounds (radius %d):\ndepth\tpositions\n", R); for (size_t d = 0; d < node0.size(); d++) if (node0[d]) printf("%zu\t%llu\n", d, (unsigned long long)node0[d]);
    return 0;
}
// independent reference: unrestricted BFS of the full puzzle on explicit states (both centre sets as colours)
static int cmdRef(int maxDepth) {
    std::unordered_map<St, u8, H60> seen; St id; for (int i = 0; i < 60; i++) id[i] = (u8)i; for (int i = 0; i < 12; i++) { id[36 + i] = FULL_COL1[i]; id[48 + i] = FULL_COL2[i]; }
    std::vector<St> cur = {id}; seen[id] = 0; printf("ref depth 0: 1 positions, 1 with phase 1 solved\n");
    for (int d = 1; d <= maxDepth; d++) { std::vector<St> next; u64 n0 = 0;
        for (auto& c : cur) for (int m = 0; m < 16; m++) { St t; for (int j = 0; j < 60; j++) t[j] = c[MN[m][j]]; if (seen.emplace(t, (u8)d).second) { next.push_back(t); bool p1 = true; for (int j = 0; j < 12; j++) p1 &= t[j] == j && t[36 + j] == FULL_COL1[j]; n0 += p1; } }
        printf("ref depth %d: %zu positions, %llu with phase 1 solved\n", d, next.size(), (unsigned long long)n0); fflush(stdout); cur.swap(next); }
    return 0;
}
// write phase-2 positions of one bound value as text.  Default: the deepest ones (all of them) and
// min(100000, count) of the next value down, like the phase-1 export.
static void exportDepth(int d, u64 limit, const std::string& out) {
    Set s; u64* bm = (u64*)VirtualAlloc(0, NWORDS * 8, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE); CHECK(bm); loadSet(d, 0, s, bm);
    FILE* f = fopen(out.c_str(), "w"); if (!f) die("cannot write %s", out.c_str());
    u64 n = limit ? std::min(limit, s.count) : s.count, stride = std::max<u64>(1, s.count / n), seen = 0, wrote = 0;
    fprintf(f, "# FTO phase 2 (CENTERS and EDGES solved): %llu of %llu positions whose shortest solution within 3 moves of phase 1 has %d moves\n", (unsigned long long)n, (unsigned long long)s.count, d);
    fprintf(f, "# each line: C4RNER permutation (6) | C4RNER orientation (6) / CENTERS2 (12 colours), numbered as in the definition file's Solved block\n");
    auto emit = [&](u32 e) {
        if ((seen++ % stride) || wrote >= n) return; wrote++;
        u32 ci = e / NC2, k = e - ci * NC2; const auto& c = CS[ci];
        for (int i = 0; i < 6; i++) fprintf(f, "%d ", (c[i * 4] - 12) / 4 + 1);
        fprintf(f, "|"); for (int i = 0; i < 6; i++) fprintf(f, " %d", (4 - (c[i * 4] - 12) % 4) % 4);
        fprintf(f, " /"); for (int j = 0; j < 12; j++) fprintf(f, " %d", ((COLS[k] >> (2 * j)) & 3) + 1);
        fprintf(f, "\n"); };
    if (s.fmt == 0) for (u32 e : s.list) emit(e); else for (u64 w = 0; w < NWORDS; w++) { u64 x = bm[w]; while (x) { emit((u32)(w * 64 + _tzcnt_u64(x))); x &= x - 1; } }
    fclose(f); VirtualFree(bm, 0, MEM_RELEASE); printf("wrote %llu positions with bound %d to %s\n", (unsigned long long)wrote, d, out.c_str());
}
// Positions the target run did not reach, and a sweep over them with a list of loops (macros) that restore
// phase 1: if a loop of length a takes holdout f to a position with bound b and a + b <= target, f is solved.
static int cmdHoldouts(const std::string& macroFile, int target) {
    u8* dist = (u8*)malloc(NF); CHECK(dist); memset(dist, 255, NF);
    u64* bm = (u64*)VirtualAlloc(0, NWORDS * 8, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE); CHECK(bm);
    u64 known = 0;
    for (int d = 0; d <= target; d++) { u64 c; u32 f; if (!headerOf(d, 0, c, f) || !c) continue; Set s; loadSet(d, 0, s, bm); known += s.count;
        if (s.fmt == 0) for (u32 e : s.list) { CHECK(dist[e] == 255); dist[e] = (u8)d; }
        else for (u64 w = 0; w < NWORDS; w++) { u64 x = bm[w]; while (x) { u64 e = w * 64 + _tzcnt_u64(x); x &= x - 1; CHECK(dist[e] == 255); dist[e] = (u8)d; } } }
    std::vector<u32> hold; for (u64 e = 0; e < NF; e++) if (dist[e] == 255) hold.push_back((u32)e);
    printf("positions with a bound of at most %d: %llu; holdouts: %zu\n", target, (unsigned long long)known, hold.size());
    CHECK(known + hold.size() == NF);
    if (hold.size() > 1000000) { printf("too many holdouts for a sweep\n"); return 1; }
    std::vector<std::array<u8, 37>> mac; { FILE* f = fopen(macroFile.c_str(), "rb"); if (!f) die("cannot read %s", macroFile.c_str()); std::array<u8, 37> r; while (fread(r.data(), 1, 37, f) == 37) mac.push_back(r); fclose(f); }
    printf("macros: %zu\n", mac.size());
    auto apply = [&](u32 e, const u8* t) -> u64 {          // f' = f o T on corner stickers and CENTERS2 slots
        u32 ci = e / NC2, k = e - ci * NC2; std::array<u8, 24> c; for (int j = 0; j < 24; j++) c[j] = CS[ci][t[j]];
        auto it = CIDX.find(c); if (it == CIDX.end()) return ~0ull;
        u32 v = 0; for (int j = 0; j < 12; j++) v |= ((COLS[k] >> (2 * (t[24 + j] - 24))) & 3) << (2 * j);
        u32 x = COLIDX[v]; if (x == 0xffffffffu) return ~0ull; return (u64)it->second * NC2 + x; };
    // sanity of the macro action: a loop of length a from solved must land on a position with bound <= a,
    // and for short loops (which stay inside radius 4) the bound obeys the triangle inequality from sampled positions
    const u32 SOL = solvedC2(); u64 bad = 0, checked = 0;
    u64 bad1 = 0; for (auto& m : mac) { u64 y = apply(SOL, m.data()); if (y == ~0ull) bad++; else if (m[36] <= 8 && dist[y] > m[36]) bad++; else if (dist[y] > m[36]) bad1++; }
    printf("loops of length 9-10 that leave radius 4 and beat the stored bound of where they land: %llu\n", (unsigned long long)bad1);
    for (u64 e = 12345; e < NF; e += 40000003) if (dist[e] != 255) for (auto& m : mac) if (m[36] <= 8 && dist[e] + m[36] <= target) { u64 y = apply((u32)e, m.data()); checked++; if (y == ~0ull || dist[y] > dist[e] + m[36]) bad++; }
    printf("macro action checks: %llu sampled applications, %llu violations\n", (unsigned long long)(checked + mac.size()), (unsigned long long)bad); CHECK(bad == 0);
    // a position that is itself the effect of one loop is solved by that loop: tighten the table with those
    { u64 imp = 0; for (auto& m : mac) { u64 y = apply(SOL, m.data()); if (y != ~0ull && dist[y] > m[36]) { dist[y] = m[36]; imp++; } } printf("bounds tightened by single loops: %llu\n", (unsigned long long)imp); }
    FILE* fo = fopen((DIR + "\\holdouts.txt").c_str(), "w"); CHECK(fo);
    fprintf(fo, "# phase-2 positions with no solution of at most %d moves inside the search radius; then the best route found by the macro sweep\n", target);
    fprintf(fo, "# C4RNER permutation (6) | orientation (6) / CENTERS2 (12)  ->  best total = loop length + bound of the position it lands on\n");
    int unsolved = 0; std::map<int, int> hist;
    for (u32 h : hold) {
        std::vector<int> best(THREADS, 999), bestA(THREADS, 0); std::vector<std::thread> th;
        for (int t = 0; t < THREADS; t++) th.emplace_back([&, t]() { for (size_t i = t; i < mac.size(); i += THREADS) { u64 y = apply(h, mac[i].data()); if (y == ~0ull || dist[y] == 255) continue; int tot = mac[i][36] + dist[y]; if (tot < best[t]) { best[t] = tot; bestA[t] = mac[i][36]; } } });
        for (auto& x : th) x.join();
        int b = 999, a = 0; for (int t = 0; t < THREADS; t++) if (best[t] < b) { b = best[t]; a = bestA[t]; }
        u32 ci = h / NC2, k = h - ci * NC2; const auto& c = CS[ci];
        for (int i = 0; i < 6; i++) fprintf(fo, "%d ", (c[i * 4] - 12) / 4 + 1); fprintf(fo, "|"); for (int i = 0; i < 6; i++) fprintf(fo, " %d", (4 - (c[i * 4] - 12) % 4) % 4);
        fprintf(fo, " /"); for (int j = 0; j < 12; j++) fprintf(fo, " %d", ((COLS[k] >> (2 * j)) & 3) + 1);
        if (b == 999) fprintf(fo, "  ->  no route found\n"); else fprintf(fo, "  ->  %d = loop of %d + %d\n", b, a, b - a);
        hist[b]++; if (b > target) unsolved++;
    }
    fclose(fo);
    for (auto [b, n] : hist) { if (b == 999) printf("%d holdouts: no route found\n", n); else printf("%d holdouts: best route %d moves\n", n, b); }
    printf("%s\n", unsolved ? "NOT all holdouts are within the target" : "every holdout has a route within the target"); printf("details in %s\\holdouts.txt\n", DIR.c_str());
    // routes made of two loops only (holdout --loop 1--> g, and g is what loop 2 makes from solved), so that
    // explicit move sequences can be written and replayed: saved for fto_macros to turn into words
    if (hold.size() <= 100)
    { std::unordered_map<u32, std::pair<u8, u32>> one; one.reserve(mac.size() * 2); one[SOL] = {0, 0xffffffffu};
      for (u32 i = 0; i < mac.size(); i++) { u64 y = apply(SOL, mac[i].data()); if (y == ~0ull) continue; auto it = one.find((u32)y); if (it == one.end()) one[(u32)y] = {mac[i][36], i}; else if (mac[i][36] < it->second.first) it->second = {mac[i][36], i}; }
      FILE* fc = fopen((DIR + "\\holdouts_cert.bin").c_str(), "wb"); CHECK(fc); int worst = 0;
      for (u32 h : hold) { int best = 999; u32 b1 = 0, b2 = 0;
          for (u32 i = 0; i < mac.size(); i++) { u64 y = apply(h, mac[i].data()); if (y == ~0ull) continue; auto it = one.find((u32)y); if (it == one.end()) continue; int tot = mac[i][36] + it->second.first; if (tot < best) { best = tot; b1 = i; b2 = it->second.second; } }
          CHECK(best != 999); worst = std::max(worst, best);
          u32 ci = h / NC2, k = h - ci * NC2; u8 col[12]; for (int j = 0; j < 12; j++) col[j] = (COLS[k] >> (2 * j)) & 3;
          u8 idm[37]; for (int j = 0; j < 36; j++) idm[j] = (u8)j; idm[36] = 0;
          fwrite(CS[ci].data(), 1, 24, fc); fwrite(col, 1, 12, fc); fwrite(mac[b1].data(), 1, 37, fc); fwrite(b2 == 0xffffffffu ? idm : mac[b2].data(), 1, 37, fc);
          printf("  two-loop route: %d = %d + %d\n", best, mac[b1][36], best - mac[b1][36]); }
      fclose(fc); printf("worst two-loop route %d; wrote %s\\holdouts_cert.bin\n", worst, DIR.c_str()); }
    return unsolved ? 1 : 0;
}
static std::vector<std::pair<u32, u8>> SWEEP;
// Joint argument over the deepest phase-1 positions.  A full position (p, f) with p one of those needs more
// than T moves only if EVERY known solution w of p leaves phase 2 at a position whose bound is too high:
// |w| + bound(w applied to f) > T.  For each p this checks every f that fails with the first solution
// against all the other solutions (optimal ones and ones a move longer).
// phase-2 bound for every position: the radius-4 search (through 23), then the results of the loop sweeps
static u8* loadBounds() {
    u8* dist = (u8*)malloc(NF); CHECK(dist); memset(dist, 255, NF);
    u64* bm = (u64*)VirtualAlloc(0, NWORDS * 8, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE); CHECK(bm);
    auto loadUpTo = [&](int dmax) { for (int d = 0; d <= dmax; d++) { u64 c; u32 f; if (!headerOf(d, 0, c, f) || !c) continue; Set s; loadSet(d, 0, s, bm);
        if (s.fmt == 0) for (u32 e : s.list) dist[e] = (u8)d; else for (u64 w = 0; w < NWORDS; w++) { u64 x = bm[w]; while (x) { dist[w * 64 + _tzcnt_u64(x)] = (u8)d; x &= x - 1; } } } };
    // sweep results are listed in ascending position order of whatever the search had not reached by that depth
    auto applySweep = [&](const char* name, int upTo) { FILE* f = fopen((DIR + "\\" + name).c_str(), "r"); if (!f) { printf("(no %s)\n", name); return; }
        memset(dist, 255, NF); loadUpTo(upTo); std::vector<u32> hold; for (u64 e = 0; e < NF; e++) if (dist[e] == 255) hold.push_back((u32)e);
        std::vector<int> best; char line[512]; while (fgets(line, sizeof line, f)) { if (line[0] == '#') continue; const char* a = strstr(line, "->"); if (!a) continue; int b; best.push_back(sscanf(a + 2, " %d", &b) == 1 ? b : 255); }
        fclose(f); if (best.size() != hold.size()) die("%s has %zu entries, expected %zu", name, best.size(), hold.size());
        for (size_t i = 0; i < hold.size(); i++) SWEEP.push_back({hold[i], (u8)std::min(best[i], 255)}); printf("%s: %zu sweep results\n", name, hold.size()); };
    applySweep("holdouts_target23.txt", 23); applySweep("holdouts.txt", 22);
    memset(dist, 255, NF); loadUpTo(23); for (auto& sw : SWEEP) if (sw.second < dist[sw.first]) dist[sw.first] = sw.second;
    { std::vector<u64> h(256, 0); for (u64 e = 0; e < NF; e++) h[dist[e]]++; printf("phase-2 bounds in use:"); for (int d = 18; d < 256; d++) if (h[d]) printf("  %d: %llu", d, (unsigned long long)h[d]); printf("\n"); CHECK(h[255] == 0); }
    VirtualFree(bm, 0, MEM_RELEASE); return dist;
}
// One step back.  For a phase-2 position b and a move m, z = m applied to (phase-1 solved, b) is a full position
// one move out of phase 1.  A loop T that starts with m gives z a solution of length |T| - 1 + bound(b after T).
// For every b with bound exactly `level` this looks for, per move, a loop with |T| + bound <= level + 1, i.e. it
// shows that no neighbour of b is further from solved than `level`.
static int cmdStepBack(const std::string& macroFile, int level) {
    u8* dist = loadBounds();
    std::vector<std::array<u8, 52>> mac; { FILE* f = fopen(macroFile.c_str(), "rb"); if (!f) die("cannot read %s", macroFile.c_str()); std::array<u8, 52> r; while (fread(r.data(), 1, 52, f) == 52) mac.push_back(r); fclose(f); }
    std::sort(mac.begin(), mac.end(), [](const std::array<u8, 52>& a, const std::array<u8, 52>& b) { return *std::min_element(a.begin() + 36, a.end()) < *std::min_element(b.begin() + 36, b.end()); });
    std::vector<u32> lev; for (u64 e = 0; e < NF; e++) if (dist[e] == level) lev.push_back((u32)e);
    printf("loops with first-move data: %zu; positions with bound %d: %zu\n", mac.size(), level, lev.size());
    auto apply = [&](u32 e, const u8* t) -> u64 { u32 ci = e / NC2, k = e - ci * NC2; std::array<u8, 24> c; for (int j = 0; j < 24; j++) c[j] = CS[ci][t[j]];
        auto it = CIDX.find(c); if (it == CIDX.end()) return ~0ull; u32 v = 0; for (int j = 0; j < 12; j++) v |= ((COLS[k] >> (2 * (t[24 + j] - 24))) & 3) << (2 * j);
        u32 x = COLIDX[v]; return x == 0xffffffffu ? ~0ull : (u64)it->second * NC2 + x; };
    std::atomic<size_t> next{0}; std::atomic<u64> failPairs{0}, failPos{0}, tests{0}; std::vector<std::thread> th; std::mutex mu; std::vector<std::pair<u32, u16>> fails;
    for (int t = 0; t < THREADS; t++) th.emplace_back([&]() { u64 tt = 0;
        for (;;) { size_t i = next++; if (i >= lev.size()) break; u32 b = lev[i]; u16 need = 0xffff;
            for (size_t k = 0; k < mac.size() && need; k++) { const u8* m = mac[k].data(); u16 can = 0; for (int mv = 0; mv < 16; mv++) if ((need >> mv & 1) && m[36 + mv] != 255) can |= (u16)(1u << mv); if (!can) continue;
                u64 y = apply(b, m); tt++; if (y == ~0ull) continue; int d = dist[y];
                for (int mv = 0; mv < 16; mv++) if ((can >> mv & 1) && m[36 + mv] + d <= level + 1) need &= (u16)~(1u << mv); }
            if (need) { failPos++; failPairs += (u64)_mm_popcnt_u32(need); std::lock_guard<std::mutex> g(mu); if (fails.size() < 100000) fails.push_back({b, need}); } }
        tests += tt; });
    for (auto& x : th) x.join();
    printf("level %d: %zu positions x 16 moves; neighbours not shown to be within %d: %llu (over %llu positions); %.3e loop applications\n", level, lev.size(), level, (unsigned long long)failPairs.load(), (unsigned long long)failPos.load(), (double)tests.load());
    FILE* fo = fopen((DIR + "\\stepback_fail_" + std::to_string(level) + ".txt").c_str(), "w"); if (fo) { for (auto& f : fails) fprintf(fo, "%u %04x\n", f.first, f.second); fclose(fo); }
    return failPairs ? 1 : 0;
}
static int cmdJoint(const std::string& solFile, const std::string& macroFile, int T, int p1max) {
    u8* dist = loadBounds();
    int p2max = 0; for (u64 e = 0; e < NF; e++) p2max = std::max(p2max, (int)dist[e]);
    printf("phase-2 maximum %d; positions whose phase-1 part needs at most %d are within %d\n", p2max, p1max - 1, p1max - 1 + p2max);
    // definition-file move names -> normalised moves here (Fw is B with a rotation, Dw is U with a rotation; direction found by replay)
    static const char* DN[8] = {"F", "Fw", "D", "Dw", "L", "BR", "BL", "R"};
    struct Sol { int len; std::vector<int> mv; }; struct Pos { PKey key; std::vector<Sol> sols; }; std::vector<Pos> pos;
    { FILE* f = fopen(solFile.c_str(), "r"); if (!f) die("cannot read %s", solFile.c_str()); char line[1024];
      while (fgets(line, sizeof line, f)) {
          if (line[0] == 'P') { int v[23]; CHECK(sscanf(line + 1, "%d %d %d %d %d %d %d %d %d %d %d %d / %d %d %d %d %d %d %d %d %d %d %d", v, v+1, v+2, v+3, v+4, v+5, v+6, v+7, v+8, v+9, v+10, v+11, v+12, v+13, v+14, v+15, v+16, v+17, v+18, v+19, v+20, v+21, v+22) == 23);
              Pos p; auto fp = [](int d) { return (u8)(d < 10 ? d : 11); }; for (int i = 0; i < 10; i++) p.key[i] = fp(v[12 + i] - 1); p.key[10] = 10; p.key[11] = fp(v[22] - 1); for (int i = 0; i < 12; i++) p.key[12 + i] = (u8)(v[i] - 1); pos.push_back(p); }
          else { Sol s; char* tok = strtok(line, " \r\n"); if (!tok) continue; s.len = atoi(tok); while ((tok = strtok(nullptr, " \r\n"))) { std::string t = tok; bool inv = t.back() == '\''; if (inv) t.pop_back(); int m = -1; for (int k = 0; k < 8; k++) if (t == DN[k]) m = k; CHECK(m >= 0); s.mv.push_back(m + (inv ? 8 : 0)); }
              CHECK((int)s.mv.size() == s.len); pos.back().sols.push_back(s); } }
      fclose(f); }
    auto pmove = [&](const PKey& a, int m) { PKey t; for (int j = 0; j < 12; j++) { t[j] = a[MN[m][j]]; t[12 + j] = a[12 + MN[m][36 + j] - 36]; } return t; };
    PKey p0; for (int i = 0; i < 12; i++) { p0[i] = (u8)i; p0[12 + i] = FULL_COL1[i]; }
    int flipB = -1, flipU = -1;
    for (int fb = 0; fb < 2 && flipB < 0; fb++) for (int fu = 0; fu < 2 && flipB < 0; fu++) { bool ok = true;
        for (size_t i = 0; i < pos.size() && ok; i += 37) for (auto& s : pos[i].sols) { PKey x = pos[i].key; for (int m : s.mv) { int mm = m; if ((m & 7) == 1 && fb) mm ^= 8; if ((m & 7) == 3 && fu) mm ^= 8; x = pmove(x, mm); } if (!(x == p0)) { ok = false; break; } }
        if (ok) { flipB = fb; flipU = fu; } }
    if (flipB < 0) die("could not match the definition-file moves to this model");
    u64 nsol = 0; for (auto& p : pos) for (auto& s : p.sols) { for (int& m : s.mv) { if ((m & 7) == 1 && flipB) m ^= 8; if ((m & 7) == 3 && flipU) m ^= 8; } PKey x = p.key; for (int m : s.mv) x = pmove(x, m); CHECK(x == p0); nsol++; }
    printf("%zu phase-1 positions, %llu solutions, all replayed to phase-1-solved\n", pos.size(), (unsigned long long)nsol);
    std::vector<u32> B; const int thr = T - p1max; for (u64 e = 0; e < NF; e++) if (dist[e] > thr) B.push_back((u32)e);
    printf("target %d: phase-2 positions with bound above %d: %zu\n", T, thr, B.size());
    u64 leftover = 0; int worstP = 0; FILE* fl = fopen((DIR + "\\joint_leftovers.txt").c_str(), "w"); CHECK(fl);
    for (size_t pi = 0; pi < pos.size(); pi++) { auto& P = pos[pi]; int S = (int)P.sols.size(); CHECK(S >= 1);
        std::sort(P.sols.begin(), P.sols.end(), [](const Sol& a, const Sol& b) { return a.len < b.len; }); CHECK(P.sols[0].len == p1max);
        std::vector<std::vector<u16>> cm(S, std::vector<u16>(NCO)); std::vector<std::vector<u32>> km(S, std::vector<u32>(NC2));
        parallel((u64)S, [&](int, u64 lo, u64 hi) { for (u64 s = lo; s < hi; s++) { for (u32 i = 0; i < NCO; i++) { u32 x = i; for (int m : P.sols[s].mv) x = CM[(size_t)m * NCO + x]; cm[s][i] = (u16)x; } for (u32 i = 0; i < NC2; i++) { u32 x = i; for (int m : P.sols[s].mv) x = C2M[(size_t)m * NC2 + x]; km[s][i] = x; } } });
        std::vector<u16> ci(NCO); std::vector<u32> ki(NC2); for (u32 i = 0; i < NCO; i++) ci[cm[0][i]] = (u16)i; for (u32 i = 0; i < NC2; i++) ki[km[0][i]] = i;
        std::vector<u64> bad(THREADS, 0); std::vector<std::vector<u32>> badList(THREADS);
        parallel(B.size(), [&](int t, u64 lo, u64 hi) { for (u64 b = lo; b < hi; b++) { u32 g = B[b], gc = g / NC2, gk = g - gc * NC2, fc = ci[gc], fk = ki[gk]; bool ok = false;
            for (int s = 1; s < S && !ok; s++) ok = P.sols[s].len + dist[(u64)cm[s][fc] * NC2 + km[s][fk]] <= T;
            if (!ok) { bad[t]++; if (badList[t].size() < 100) badList[t].push_back(fc * NC2 + fk); } } });
        u64 nb = 0; for (u64 x : bad) nb += x; leftover += nb; if (nb) { worstP++; for (auto& bl : badList) for (u32 f : bl) fprintf(fl, "%zu %u\n", pi, f); }
        if ((pi + 1) % 50 == 0 || pi + 1 == pos.size()) { printf("  %zu of %zu phase-1 positions checked, %llu pairs left over so far\n", pi + 1, pos.size(), (unsigned long long)leftover); fflush(stdout); }
    }
    fclose(fl);
    printf("target %d: %llu (phase-1 position, phase-2 position) pairs not covered, in %d of %zu phase-1 positions\n", T, (unsigned long long)leftover, worstP, pos.size());
    int rest = p1max - 1 + p2max;
    if (!leftover && rest <= T) printf("=> every position of the puzzle is within %d moves\n", T);
    else if (!leftover) printf("=> the deepest phase-1 positions are within %d, but the others are only within %d\n", T, rest);
    return leftover ? 1 : 0;
}
static int cmdExport(int depthArg, long long limitArg) {
    std::vector<u64> node0; bool complete = false; FILE* f = fopen((DIR + "\\state.txt").c_str(), "r"); if (!f) die("no search in %s", DIR.c_str());
    char line[256]; while (fgets(line, sizeof line, f)) { int d; unsigned long long a, b; if (sscanf(line, "layer %d %llu %llu", &d, &a, &b) == 3) node0.push_back(b); else if (!strncmp(line, "complete", 8)) complete = true; } fclose(f);
    char b[96];
    if (depthArg >= 0) { snprintf(b, sizeof b, "\\phase2_bound_%02d.txt", depthArg); exportDepth(depthArg, limitArg > 0 ? (u64)limitArg : 0, DIR + b); return 0; }
    if (!complete) die("search not complete; use --depth N to export a finished depth");
    int top = (int)node0.size() - 1; while (top > 0 && !node0[top]) top--; int second = top - 1; while (second > 0 && !node0[second]) second--;
    snprintf(b, sizeof b, "\\phase2_bound_%02d_all.txt", top); exportDepth(top, 0, DIR + b);
    if (node0[second] <= 100000) { snprintf(b, sizeof b, "\\phase2_bound_%02d_all.txt", second); exportDepth(second, 0, DIR + b); }
    else { snprintf(b, sizeof b, "\\phase2_bound_%02d_sample_100000.txt", second); exportDepth(second, 100000, DIR + b); }
    return 0;
}
int main(int argc, char** argv) {
    if (argc < 2) { printf("usage: fto_tube run | export | holdouts | stepback | joint | ref  (see README.md for the full command lines)\n"); return 1; }
    std::string cmd = argv[1], macroFile = "macros_len10.bin", solFile, boundsDir; int R = 3, depth = 5, expDepth = -1; long long limit = 0; bool useSym = true;
    for (int i = 2; i + 1 < argc; i += 2) { std::string a = argv[i]; if (a == "--dir") DIR = argv[i + 1]; else if (a == "--radius") R = atoi(argv[i + 1]); else if (a == "--threads") THREADS = atoi(argv[i + 1]); else if (a == "--depth") { depth = atoi(argv[i + 1]); expDepth = depth; } else if (a == "--limit") limit = atoll(argv[i + 1]); else if (a == "--max-depth") MAXDEPTH = atoi(argv[i + 1]); else if (a == "--sym") useSym = atoi(argv[i + 1]) != 0; else if (a == "--target") TARGET = atoi(argv[i + 1]); else if (a == "--big-workers") BWORKERS = atoi(argv[i + 1]); else if (a == "--keep-depth") KEEPDEPTH = atoi(argv[i + 1]); else if (a == "--bounds-dir") boundsDir = argv[i + 1]; else if (a == "--macros") macroFile = argv[i + 1]; else if (a == "--solutions") solFile = argv[i + 1]; else if (a == "--test-chunked") { CHUNK_FORCE = LIST_OFF = atoi(argv[i + 1]) != 0; } else if (a == "--sparse") SPARSE_LIMIT = strtoull(argv[i + 1], 0, 10); else die("unknown option %s", a.c_str()); }
    buildModel(cmd == "ref" ? 0 : R);
    if (cmd == "ref") return cmdRef(depth);
    if (cmd == "export") { if (DIR.empty()) die("--dir is required"); return cmdExport(expDepth, limit); }
    if (cmd == "stepback") { if (DIR.empty() || TARGET < 0) die("--dir and --target (the bound level) are required"); return cmdStepBack(macroFile, TARGET); }
    if (cmd == "joint") { if (DIR.empty() || TARGET < 0) die("--dir and --target are required"); return cmdJoint(solFile, macroFile, TARGET, 15); }
    if (cmd == "holdouts") { if (DIR.empty() || TARGET < 0) die("--dir and --target are required"); return cmdHoldouts(macroFile, TARGET); }
    if (cmd == "run") { if (DIR.empty()) die("--dir is required"); buildSym(R, useSym); return cmdRun(R); }
    die("unknown command");
}
