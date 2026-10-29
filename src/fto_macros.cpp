// Macros for FTO phase 2: every face-turn sequence of length <= 2k that returns CENTERS + EDGES to solved
// (up to whole-puzzle rotation), as a transformation of corners + CENTERS2.
// Method: enumerate all elements of the full puzzle within k moves of solved (kept in the frame where the
// B U edge is home), group them by their CENTERS/EDGES state, and combine every pair (u, v) in a group:
// "do u, then undo v" is a closed loop of length |u| + |v|.  Any loop of length <= 2k splits this way.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <unordered_map>
#include <vector>
#include "full_tables.h"
typedef uint8_t u8; typedef uint16_t u16; typedef uint32_t u32; typedef uint64_t u64;
#define CHECK(c) do { if (!(c)) { fprintf(stderr, "check failed: %s (line %d)\n", #c, __LINE__); exit(2); } } while (0)
typedef std::array<u8, 60> St;      // slot -> piece point; CENTERS entries hold colours (identical pieces)
typedef std::array<u8, 36> Mac;     // slot map on corner stickers (0-23) and CENTERS2 (24-35)
template <size_t N> struct H { size_t operator()(const std::array<u8, N>& a) const { u64 h = 1469598103934665603ull; for (size_t i = 0; i + 8 <= N; i += 4) { u64 w; memcpy(&w, a.data() + i, 8); h = (h ^ w) * 0x9E3779B97F4A7C15ull; h ^= h >> 29; } return (size_t)h; } };
static u8 MV[16][60];
static St normalize(const St& s) {
    for (int r = 0; r < 12; r++) if (s[FULL_ROT[r][10]] == 10) { St n; for (int i = 0; i < 60; i++) n[i] = s[FULL_ROT[r][i]]; return n; }
    fprintf(stderr, "normalize failed\n"); exit(2);
}
int main(int argc, char** argv) {
    int k = argc > 1 ? atoi(argv[1]) : 5; const char* out = argc > 2 ? argv[2] : nullptr; u64 pairCap = argc > 3 ? strtoull(argv[3], 0, 10) : 4000000000ull;
    for (int m = 0; m < 8; m++) for (int i = 0; i < 60; i++) { MV[m][i] = FULL_MOVE[m][i]; }
    for (int m = 0; m < 8; m++) for (int i = 0; i < 60; i++) MV[m + 8][i] = MV[m][MV[m][i]];
    St id; for (int i = 0; i < 60; i++) id[i] = (u8)i; for (int i = 0; i < 12; i++) id[36 + i] = FULL_COL1[i];
    std::unordered_map<St, u32, H<60>> seen; std::vector<St> all = {id}; std::vector<u8> dep = {0}; seen[id] = 0;
    std::vector<u32> par = {0}; std::vector<u8> pmv = {0};
    // over ALL shortest paths to an element: which moves can come first, and which can come last
    std::vector<u16> firstMask = {0}, lastMask = {0};
    const bool withFirst = out && strstr(out, "first");
    size_t lo = 0; auto t0 = std::chrono::steady_clock::now();
    for (int d = 1; d <= k; d++) {
        size_t hi = all.size();
        for (size_t i = lo; i < hi; i++) for (int m = 0; m < 16; m++) {
            St s; const St cur = all[i]; for (int j = 0; j < 60; j++) s[j] = cur[MV[m][j]];
            St n = normalize(s);
            auto ins = seen.emplace(n, (u32)all.size()); u16 fmk = i == 0 ? (u16)(1u << m) : firstMask[i];
            if (ins.second) { all.push_back(n); dep.push_back((u8)d); par.push_back((u32)i); pmv.push_back((u8)m); firstMask.push_back(fmk); lastMask.push_back((u16)(1u << m)); }
            else if (dep[ins.first->second] == d) { firstMask[ins.first->second] |= fmk; lastMask[ins.first->second] |= (u16)(1u << m); }
        }
        printf("depth %d: %zu elements (ball %zu)\n", d, all.size() - hi, all.size()); fflush(stdout); lo = hi;
    }
    seen.clear();
    // group by phase-1 state (edges 0-11 and centre colours 36-47)
    std::vector<u32> ord(all.size()); for (u32 i = 0; i < ord.size(); i++) ord[i] = i;
    auto key = [&](u32 i, u8* kk) { memcpy(kk, all[i].data(), 12); memcpy(kk + 12, all[i].data() + 36, 12); };
    std::sort(ord.begin(), ord.end(), [&](u32 a, u32 b) { u8 ka[24], kb[24]; key(a, ka); key(b, kb); int c = memcmp(ka, kb, 24); return c ? c < 0 : dep[a] < dep[b]; });
    u64 pairs = 0, groups = 0, big = 0;
    for (size_t i = 0; i < ord.size();) { size_t j = i; u8 ka[24], kb[24]; key(ord[i], ka); while (j < ord.size()) { key(ord[j], kb); if (memcmp(ka, kb, 24)) break; j++; } u64 g = j - i; pairs += g * (g - 1); groups++; big = std::max(big, g); i = j; }
    printf("phase-1 states within %d moves: %llu; largest group %llu; ordered pairs to combine: %llu\n", k, (unsigned long long)groups, (unsigned long long)big, (unsigned long long)pairs); fflush(stdout);
    if (pairs > pairCap) { printf("too many pairs for this run (cap %llu)\n", (unsigned long long)pairCap); return 1; }
    std::unordered_map<Mac, u8, H<36>> mac; u64 tested = 0, replayed = 0; int shown = 0, lastShown = -1;
    u64 firstChecked = 0;
    struct FArr { u8 c[16] = {0}; }; std::unordered_map<Mac, FArr, H<36>> macF;   // per effect: shortest loop length for each possible first move
    // certificate mode: positions with a two-loop route (from fto_tube holdouts); find a pair for each loop
    struct Want { u8 cost; int a = -1, b = -1; }; std::unordered_map<Mac, Want, H<36>> wanted;
    struct CertRec { u8 corner[24], col[12], t1[37], t2[37]; }; std::vector<CertRec> cert;
    if (argc > 4) { FILE* f = fopen(argv[4], "rb"); CHECK(f); CertRec r; while (fread(&r, 1, sizeof r, f) == sizeof r) cert.push_back(r); fclose(f);
        for (auto& r : cert) for (const u8* t : {r.t1, r.t2}) if (t[36]) { Mac m; memcpy(m.data(), t, 36); Want w; w.cost = t[36]; wanted.emplace(m, w); }
        printf("certificate mode: %zu positions, %zu loops to find\n", cert.size(), wanted.size()); }
    for (size_t i = 0; i < ord.size();) {
        size_t j = i; u8 ka[24], kb[24]; key(ord[i], ka); while (j < ord.size()) { key(ord[j], kb); if (memcmp(ka, kb, 24)) break; j++; }
        for (size_t b = i; b < j; b++) {
            const St& B = all[ord[b]]; u8 binv[60]; for (int x = 12; x < 36; x++) binv[B[x]] = (u8)x; for (int x = 48; x < 60; x++) binv[B[x]] = (u8)x;
            for (size_t a = i; a < j; a++) if (a != b) {
                const St& A = all[ord[a]]; Mac t; bool isId = true;
                for (int x = 12; x < 36; x++) { t[x - 12] = (u8)(A[binv[x]] - 12); isId &= t[x - 12] == x - 12; }
                for (int x = 48; x < 60; x++) { t[x - 24] = (u8)(A[binv[x]] - 24); isId &= t[x - 24] == x - 24; }
                if (isId) continue;
                u8 cost = (u8)(dep[ord[a]] + dep[ord[b]]); auto it = mac.find(t);
                if (it == mac.end()) mac.emplace(t, cost); else if (cost < it->second) it->second = cost;
                if (withFirst) {   // the loop "u then v backwards" can start with any first move of u, or, if u is empty, with the inverse of any last move of v
                    u16 fmk = dep[ord[a]] ? firstMask[ord[a]] : 0; if (!dep[ord[a]]) for (int m = 0; m < 16; m++) if (lastMask[ord[b]] >> m & 1) fmk |= (u16)(1u << (m ^ 8));
                    auto& arr = macF.try_emplace(t, FArr{}).first->second; if (arr.c[0] == 0 && arr.c[1] == 0) memset(arr.c, 255, 16);
                    for (int m = 0; m < 16; m++) if ((fmk >> m & 1) && cost < arr.c[m]) arr.c[m] = cost; }
                if (!wanted.empty()) { auto w = wanted.find(t); if (w != wanted.end() && cost == w->second.cost && w->second.a < 0) { w->second.a = (int)ord[a]; w->second.b = (int)ord[b]; } }
                // end-to-end check on a sample: write the loop as plain face turns, replay it on the real puzzle
                if ((++tested % 997) == 1 || cost <= 5) {
                    typedef std::array<u8, 60> P; P I; for (int x = 0; x < 60; x++) I[x] = (u8)x;
                    auto comp = [](const P& X, const P& Y) { P r; for (int x = 0; x < 60; x++) r[x] = X[Y[x]]; return r; };
                    auto inv = [](const P& X) { P r; for (int x = 0; x < 60; x++) r[X[x]] = (u8)x; return r; };
                    auto mvp = [&](int m) { P r; memcpy(r.data(), MV[m], 60); return r; };
                    auto faceOf = [&](const P& q) { for (int m = 0; m < 16; m++) if (!memcmp(q.data(), MV[m], 60)) return m; fprintf(stderr, "not a face turn\n"); exit(2); };
                    auto walk = [&](u32 e, std::vector<int>& faces, P& S, P& rho) {      // physical word of element e
                        std::vector<int> mv; for (u32 x = e; x; x = par[x]) mv.push_back(pmv[x]); std::reverse(mv.begin(), mv.end());
                        S = I; rho = I;
                        for (int m : mv) { int f = faceOf(comp(comp(rho, mvp(m)), inv(rho))); faces.push_back(f); S = comp(S, mvp(f));
                            P N = comp(S, rho); int r = 0; for (; r < 12; r++) if (N[FULL_ROT[r][10]] == 10) break; CHECK(r < 12); P rr; memcpy(rr.data(), FULL_ROT[r], 60); rho = comp(rho, rr); }
                    };
                    std::vector<int> fu, fv; P Su, ru, Sv, rv; walk(ord[a], fu, Su, ru); walk(ord[b], fv, Sv, rv);
                    P sig = comp(ru, inv(rv)); std::vector<int> W = fu;
                    for (size_t x = fv.size(); x-- > 0;) W.push_back(faceOf(comp(comp(sig, mvp(fv[x] ^ 8)), inv(sig))));
                    CHECK((int)W.size() == cost);
                    { // the first face turn of the replayed loop must be one of the first moves recorded for this pair
                      u16 fmk2 = dep[ord[a]] ? firstMask[ord[a]] : 0; if (!dep[ord[a]]) for (int m = 0; m < 16; m++) if (lastMask[ord[b]] >> m & 1) fmk2 |= (u16)(1u << (m ^ 8));
                      CHECK(fmk2 >> W[0] & 1); firstChecked++; }
                    P S = I; for (int f : W) S = comp(S, mvp(f));
                    P N = comp(S, sig);
                    for (int x = 0; x < 12; x++) { CHECK(N[x] == x); CHECK(FULL_COL1[N[36 + x] - 36] == FULL_COL1[x]); }
                    for (int x = 12; x < 36; x++) CHECK(N[x] - 12 == t[x - 12]);
                    for (int x = 48; x < 60; x++) CHECK(N[x] - 24 == t[x - 24]);
                    if (shown < 6 && cost <= 6 && (cost != lastShown)) { shown++; lastShown = cost; printf("  example, length %d:", cost); for (int f : W) printf(" %s%s", FULL_NAMES[f & 7], f >= 8 ? "'" : ""); printf("\n"); }
                    replayed++;
                }
            }
        }
        i = j;
    }
    printf("replayed %llu sampled loops as plain face turns on the full puzzle: all restore CENTERS and EDGES and match their macro\n", (unsigned long long)replayed);
    if (!cert.empty()) {
        typedef std::array<u8, 60> P; P I; for (int x = 0; x < 60; x++) I[x] = (u8)x;
        auto comp = [](const P& X, const P& Y) { P r; for (int x = 0; x < 60; x++) r[x] = X[Y[x]]; return r; };
        auto inv = [](const P& X) { P r; for (int x = 0; x < 60; x++) r[X[x]] = (u8)x; return r; };
        auto mvp = [&](int m) { P r; memcpy(r.data(), MV[m], 60); return r; };
        auto faceOf = [&](const P& q) { for (int m = 0; m < 16; m++) if (!memcmp(q.data(), MV[m], 60)) return m; fprintf(stderr, "not a face turn\n"); exit(2); };
        auto walk = [&](u32 e, std::vector<int>& faces, P& S, P& rho) {
            std::vector<int> mv; for (u32 x = e; x; x = par[x]) mv.push_back(pmv[x]); std::reverse(mv.begin(), mv.end()); S = I; rho = I;
            for (int m : mv) { int f = faceOf(comp(comp(rho, mvp(m)), inv(rho))); faces.push_back(f); S = comp(S, mvp(f));
                P N = comp(S, rho); int r = 0; for (; r < 12; r++) if (N[FULL_ROT[r][10]] == 10) break; CHECK(r < 12); P rr; memcpy(rr.data(), FULL_ROT[r], 60); rho = comp(rho, rr); } };
        auto loopWord = [&](const u8* t, std::vector<int>& W, P& sig) {      // plain face turns of one loop, and the rotation it ends in
            W.clear(); sig = I; if (!t[36]) return; Mac m; memcpy(m.data(), t, 36); const Want& w = wanted.at(m); CHECK(w.a >= 0);
            std::vector<int> fu, fv; P Su, ru, Sv, rv; walk((u32)w.a, fu, Su, ru); walk((u32)w.b, fv, Sv, rv); sig = comp(ru, inv(rv)); W = fu;
            for (size_t x = fv.size(); x-- > 0;) W.push_back(faceOf(comp(comp(sig, mvp(fv[x] ^ 8)), inv(sig)))); CHECK((int)W.size() == t[36]); };
        FILE* fo = fopen(argc > 5 ? argv[5] : "holdout_solutions.txt", "w"); CHECK(fo);
        fprintf(fo, "# explicit solutions for the phase-2 positions the radius-4 search left above 23 moves\n");
        fprintf(fo, "# position: C4RNER permutation (6) | orientation (6) / CENTERS2 (12)   | length | solution in the ground-truth file's move names (X' = X twice)\n");
        fprintf(fo, "# each was replayed on the full puzzle (all four piece sets): it ends solved up to whole-puzzle rotation\n");
        int worst = 0;
        for (auto& r : cert) {
            std::vector<int> W1, W2; P s1, s2; loopWord(r.t1, W1, s1); loopWord(r.t2, W2, s2);
            P rho = comp(s1, inv(s2)); std::vector<int> sol = W1; for (size_t x = W2.size(); x-- > 0;) sol.push_back(faceOf(comp(comp(rho, mvp(W2[x] ^ 8)), inv(rho))));
            P X = I; for (int j = 0; j < 24; j++) X[12 + j] = r.corner[j];
            { bool used[12] = {false}; for (int j = 0; j < 12; j++) { int k = 0; while (used[k] || FULL_COL2[k] != r.col[j]) { k++; CHECK(k < 12); } used[k] = true; X[48 + j] = (u8)(48 + k); } }
            for (int f : sol) X = comp(X, mvp(f));
            int rr = 0; for (; rr < 12; rr++) if (X[FULL_ROT[rr][10]] == 10) break; CHECK(rr < 12); P R; memcpy(R.data(), FULL_ROT[rr], 60); P N = comp(X, R);
            bool ok = true; for (int x = 0; x < 36; x++) ok &= N[x] == x; for (int x = 0; x < 12; x++) ok &= FULL_COL1[N[36 + x] - 36] == FULL_COL1[x] && FULL_COL2[N[48 + x] - 48] == FULL_COL2[x];
            if (!ok) { fprintf(stderr, "replay FAILED for a holdout\n"); return 3; }
            for (int i = 0; i < 6; i++) fprintf(fo, "%d ", (r.corner[i * 4] - 12) / 4 + 1); fprintf(fo, "|"); for (int i = 0; i < 6; i++) fprintf(fo, " %d", (4 - (r.corner[i * 4] - 12) % 4) % 4);
            fprintf(fo, " /"); for (int j = 0; j < 12; j++) fprintf(fo, " %d", r.col[j] + 1);
            fprintf(fo, " | %zu |", sol.size()); for (int f : sol) fprintf(fo, " %s%s", FULL_NAMES[f & 7], f >= 8 ? "'" : ""); fprintf(fo, "\n");
            worst = std::max(worst, (int)sol.size());
        }
        fclose(fo); printf("certificate: %zu positions solved and replayed, longest solution %d moves\n", cert.size(), worst);
    }
    std::vector<u64> byCost(64, 0); for (auto& kv : mac) byCost[kv.second]++;
    u64 cum = 0; printf("distinct non-trivial macros by shortest length (complete through length %d):\n", 2 * k);
    for (int c = 0; c <= 2 * k; c++) if (byCost[c]) { cum += byCost[c]; printf("  length %2d: %llu  (cumulative %llu)\n", c, (unsigned long long)byCost[c], (unsigned long long)cum); }
    printf("%.0fs\n", std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count());
    if (withFirst) { FILE* f = fopen(out, "wb"); CHECK(f); for (auto& kv : macF) { fwrite(kv.first.data(), 1, 36, f); fwrite(kv.second.c, 1, 16, f); } fclose(f); printf("wrote %s (%zu macros, 52 bytes each: effect + shortest length per first move)\n", out, macF.size()); return 0; }
    if (out) { FILE* f = fopen(out, "wb"); CHECK(f); for (auto& kv : mac) { fwrite(kv.first.data(), 1, 36, f); fwrite(&kv.second, 1, 1, f); } fclose(f); printf("wrote %s (%zu macros, 37 bytes each)\n", out, mac.size()); }
    return 0;
}
