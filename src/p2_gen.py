"""Emit p2_tables.h for the corner + CENTERS2 lower-bound BFS: move data from the ground-truth file and
the 12 rotated copies of the solved state, derived geometrically from the face lists in the file's comments.
Reading of the file (as twsearch does): new[i] = old[P[i]], and the twist listed at position j is added to
the piece that leaves position j."""
from itertools import permutations, product
CORNER_FACES = [l.split() for l in ["F D L BL", "F U L R", "F D BR R", "B U L BL", "B D BR BL", "B U BR R"]]
C2_FACES = [l.split() for l in ["F D BR", "F L BL", "D BR BL", "B BR BL", "B U BR", "F U R", "F BR R", "U L BL", "F D BL", "B U BL", "U BR R", "F U L"]]
EDGE_FACES = [l.split() for l in ["F R", "F D", "B BR", "D BL", "BR R", "F L", "D BR", "B BL", "L BL", "U L", "B U", "U R"]]
COL2 = [1,2,1,3,3,4,4,2,1,3,4,2]
MV = {  # corner perm, corner twist, centers2 perm
 'F':  ([3,1,2,4,5,6],[3,3,2,0,0,0],[6,1,3,4,5,2,12,8,7,10,11,9]),
 'B':  ([1,2,3,6,4,5],[0,0,0,3,3,2],[1,2,3,10,4,6,7,8,9,5,11,12]),
 'D':  ([5,2,1,4,3,6],[0,0,0,0,0,0],[9,2,1,4,5,6,7,8,3,10,11,12]),
 'U':  ([1,6,3,2,5,4],[0,0,0,0,0,0],[1,2,3,4,8,5,7,6,9,12,10,11]),
 'L':  ([2,4,3,1,5,6],[3,3,0,2,0,0],[1,12,3,4,5,6,7,2,9,10,11,8]),
 'BR': ([1,2,5,4,6,3],[0,0,3,0,2,3],[4,2,5,11,7,6,3,8,9,10,1,12]),
 'BL': ([4,2,3,5,1,6],[2,0,0,3,3,0],[1,10,2,9,5,6,7,4,8,3,11,12]),
 'R':  ([1,3,6,4,5,2],[0,2,3,0,0,3],[1,2,3,4,5,7,11,8,9,10,6,12]),
}
FACES = ['F','B','D','U','L','BR','BL','R']
# octahedron faces = cube vertices; two faces share an edge iff they differ in one coordinate
adj = {f: set() for f in FACES}
for a, b in EDGE_FACES: adj[a].add(b); adj[b].add(a)
assert all(len(v) == 3 for v in adj.values())
verts = list(product((1, -1), repeat=3))
emb = None
for perm in permutations(verts):
    m = dict(zip(FACES, perm))
    if all((sum(x != y for x, y in zip(m[a], m[b])) == 1) == (b in adj[a]) for a in FACES for b in FACES if a != b):
        emb = m; break
assert emb
inv_emb = {v: k for k, v in emb.items()}
# The comment lists a corner's four faces in name order, not in the order they sit around the corner.
# Orientation counts quarter-steps around the corner, so put each list in cyclic order (same handedness
# everywhere, seen from outside), starting from the first listed face.
import math
def cyclic(fl):
    vs = [emb[f] for f in fl]
    k = [i for i in range(3) if len({v[i] for v in vs}) == 1][0]; sgn = vs[0][k]
    a, b = [i for i in range(3) if i != k]
    if (k, a, b) not in ((0, 1, 2), (1, 2, 0), (2, 0, 1)): a, b = b, a
    ang = lambda f: (sgn * math.atan2(emb[f][b], emb[f][a])) % (2 * math.pi)
    order = sorted(fl, key=ang); i0 = order.index(fl[0])
    return order[i0:] + order[:i0]
CORNER_FACES = [cyclic(fl) for fl in CORNER_FACES]
# rotations of the cube: signed permutation matrices with determinant +1
def det_sign(p, s):
    inv = sum(1 for i in range(3) for j in range(i+1, 3) if p[i] > p[j])
    return (-1)**inv * s[0]*s[1]*s[2]
rots = []
for p in permutations(range(3)):
    for s in product((1, -1), repeat=3):
        if det_sign(p, s) != 1: continue
        phi = {f: inv_emb[tuple(s[i]*emb[f][p[i]] for i in range(3))] for f in FACES}
        rots.append(phi)
assert len(rots) == 24
tetrad = {'F', 'BR', 'BL', 'U'}                      # faces carrying the CENTERS colours
rots12 = [r for r in rots if {r[f] for f in tetrad} == tetrad]
assert len(rots12) == 12

# ---- check the sticker reading on every face turn: a turn of face X is a rotation phi about X, and the model
# says sticker (slot P[i], index a) lands on (slot i, index a + s*t[P[i]]).  Find the sign s that fits all moves.
def corner_slot(faces):
    for j, fl in enumerate(CORNER_FACES):
        if set(fl) == set(faces): return j
    raise KeyError(faces)
def c2_slot(faces):
    for j, fl in enumerate(C2_FACES):
        if set(fl) == set(faces): return j
    raise KeyError(faces)
# each face turn as a geometric rotation, identified from its CENTERS2 action alone
turn = {}
for name, (P, T, C2) in MV.items():
    ok = [r for r in rots if r[name] == name and all(c2_slot([r[f] for f in C2_FACES[C2[i]-1]]) == i for i in range(12) if C2[i]-1 != i)
          and any(r[f] != f for f in FACES)]
    assert len(ok) == 1, (name, len(ok))
    turn[name] = ok[0]
# corner stickers: slot i, index a sits on face CORNER_FACES[i][(a*sign + off[i]) % 4]; find sign and offsets
def consistent(sign, off):
    for name, (P, T, C2) in MV.items():
        r = turn[name]
        for i in range(6):
            src = P[i]-1
            if src == i: continue        # corner not in this face's layer
            for a in range(4):
                f_from = CORNER_FACES[src][(a*sign + off[src]) % 4]
                f_to = CORNER_FACES[i][((a + T[src])*sign + off[i]) % 4]
                if r[f_from] != f_to: return False
    return True
fitsl = [(s, off) for s in (1, -1) for off in product(range(4), repeat=6) if consistent(s, off)]
print("consistent (sign, per-slot reference offsets):", len(fitsl), fitsl[:4])
assert fitsl
sign, off = fitsl[0]
CORNER_FACES = [[fl[(a*sign + off[i]) % 4] for a in range(4)] for i, fl in enumerate(CORNER_FACES)]
sign = 1
# ---- the 12 rotated solved states: slot j = phi(slot i) holds piece i; its orientation is the index shift
starts = []
for r in rots12:
    perm = [0]*6; ori = [0]*6
    for i in range(6):
        j = corner_slot([r[f] for f in CORNER_FACES[i]])
        b = CORNER_FACES[j].index(r[CORNER_FACES[i][0]])     # where the piece's sticker 0 sits
        perm[j] = i; ori[j] = (sign * b) % 4
    col = [0]*12
    for i in range(12): col[c2_slot([r[f] for f in C2_FACES[i]])] = COL2[i]
    starts.append((perm, ori, col))
assert sum(1 for p, o, c in starts if p == list(range(6)) and o == [0]*6 and c == COL2) == 1
with open("p2_tables.h", "w") as f:
    f.write("// generated by p2_gen.py\n")
    f.write("static const char* P2_NAMES[8] = {" + ",".join('"%s"' % n for n in MV) + "};\n")
    f.write("static const unsigned char P2_CP[8][6] = {" + ",".join("{" + ",".join(str(x-1) for x in v[0]) + "}" for v in MV.values()) + "};\n")
    f.write("static const unsigned char P2_CT[8][6] = {" + ",".join("{" + ",".join(str(x) for x in v[1]) + "}" for v in MV.values()) + "};\n")
    f.write("static const unsigned char P2_C2[8][12] = {" + ",".join("{" + ",".join(str(x-1) for x in v[2]) + "}" for v in MV.values()) + "};\n")
    f.write("static const unsigned char P2_COL[12] = {" + ",".join(str(x-1) for x in COL2) + "};\n")
    f.write("static const unsigned char P2_START_PERM[12][6] = {" + ",".join("{" + ",".join(map(str, s[0])) + "}" for s in starts) + "};\n")
    f.write("static const unsigned char P2_START_ORI[12][6] = {" + ",".join("{" + ",".join(map(str, s[1])) + "}" for s in starts) + "};\n")
    f.write("static const unsigned char P2_START_COL[12][12] = {" + ",".join("{" + ",".join(str(x-1) for x in s[2]) + "}" for s in starts) + "};\n")
print("wrote p2_tables.h with", len(starts), "rotated solved states")

# ---- full 60-point model for the macro search: 0-11 edges, 12-35 corner stickers, 36-47 CENTERS, 48-59 CENTERS2
CEN_FACES = [l.split() for l in ["F L R","F D R","B BR R","D L BL","D BR R","F D L","B D BR","B D BL","B L BL","U L R","B U L","B U R"]]
CEN_P = {'F':[6,1,3,4,5,2,7,8,9,10,11,12],'B':[1,2,8,4,5,6,9,11,12,10,3,7],'D':[1,4,3,7,6,8,2,5,9,10,11,12],'U':[1,2,3,4,5,6,7,8,9,12,10,11],
         'L':[11,2,3,1,5,10,7,8,6,9,4,12],'BR':[1,2,5,4,7,6,3,8,9,10,11,12],'BL':[1,2,3,9,5,6,7,4,8,10,11,12],'R':[5,3,10,4,12,6,7,8,9,2,11,1]}
EDG_P = {'F':[6,1,3,4,5,2,7,8,9,10,11,12],'B':[1,2,8,4,5,6,7,11,9,10,3,12],'D':[1,4,3,7,5,6,2,8,9,10,11,12],'U':[1,2,3,4,5,6,7,8,9,12,10,11],
         'L':[1,2,3,4,5,10,7,8,6,9,11,12],'BR':[1,2,5,4,7,6,3,8,9,10,11,12],'BL':[1,2,3,9,5,6,7,4,8,10,11,12],'R':[5,2,3,4,12,6,7,8,9,10,11,1]}
COL1 = [1,1,2,3,2,1,2,3,3,4,4,4]
def slot_of(lst, faces):
    for j, fl in enumerate(lst):
        if set(fl) == set(faces): return j
    raise KeyError(faces)
def move60(n):
    P, T, C2 = MV[n]; p = [0]*60
    for i in range(12): p[i] = EDG_P[n][i]-1
    for i in range(6):
        for a in range(4): p[12+i*4+a] = 12 + (P[i]-1)*4 + (a - T[P[i]-1]) % 4
    for i in range(12): p[36+i] = 36 + CEN_P[n][i]-1; p[48+i] = 48 + C2[i]-1
    assert sorted(p) == list(range(60)); return p
def rot60(r):      # whole-puzzle rotation as a pull permutation: new[r(x)] = old[x]
    p = [0]*60
    for i in range(12): p[slot_of(EDGE_FACES, [r[f] for f in EDGE_FACES[i]])] = i
    for i in range(6):
        j = corner_slot([r[f] for f in CORNER_FACES[i]])
        for a in range(4): p[12 + j*4 + CORNER_FACES[j].index(r[CORNER_FACES[i][a]])] = 12 + i*4 + a
    for i in range(12): p[36 + slot_of(CEN_FACES, [r[f] for f in CEN_FACES[i]])] = 36 + i
    for i in range(12): p[48 + c2_slot([r[f] for f in C2_FACES[i]])] = 48 + i
    assert sorted(p) == list(range(60)); return p
def mul(a, b): return [a[x] for x in b]
def inv(a):
    r = [0]*60
    for i, x in enumerate(a): r[x] = i
    return r
m60 = {n: move60(n) for n in MV}; r60 = [rot60(r) for r in rots12]
plain = [m60[n] for n in MV]
for rho in r60:                       # a rotation must carry every face turn to a face turn of the same handedness
    for n in MV: assert mul(mul(inv(rho), m60[n]), rho) in plain, n
    for base, col in ((36, COL1), (48, COL2)):   # and colour classes to colour classes
        cm = {}
        for i in range(12): assert cm.setdefault(col[rho[base+i]-base], col[i]) == col[i]
print("rotations conjugate face turns to face turns: ok")
with open("full_tables.h", "w") as f:
    f.write("// generated by p2_gen.py: 0-11 edges, 12-35 corner stickers, 36-47 CENTERS, 48-59 CENTERS2; new[i] = old[m[i]]\n")
    f.write("static const char* FULL_NAMES[8] = {" + ",".join('"%s"' % n for n in MV) + "};\n")
    f.write("static const unsigned char FULL_MOVE[8][60] = {" + ",".join("{" + ",".join(map(str, m60[n])) + "}" for n in MV) + "};\n")
    f.write("static const unsigned char FULL_ROT[12][60] = {" + ",".join("{" + ",".join(map(str, p)) + "}" for p in r60) + "};\n")
    f.write("static const unsigned char FULL_COL1[12] = {" + ",".join(str(x-1) for x in COL1) + "};\n")
    f.write("static const unsigned char FULL_COL2[12] = {" + ",".join(str(x-1) for x in COL2) + "};\n")
print("wrote full_tables.h")

# ---- one mirror (a reflection of the octahedron that keeps the F/BR/BL/U tetrad) as a point map
mirrors = []
for p in permutations(range(3)):
    for s in product((1, -1), repeat=3):
        if det_sign(p, s) != -1: continue
        phi = {f: inv_emb[tuple(s[i]*emb[f][p[i]] for i in range(3))] for f in FACES}
        if {phi[f] for f in tetrad} == tetrad: mirrors.append(phi)
assert len(mirrors) == 12
mu = rot60(mirrors[0])
allm = plain + [mul(m, m) for m in plain]
for n in MV: assert mul(mul(inv(mu), m60[n]), mu) in [mul(m, m) for m in plain], n     # a mirror turns each face turn into an inverse turn
with open("full_tables.h", "a") as f:
    f.write("static const unsigned char FULL_MIRROR[60] = {" + ",".join(map(str, mu)) + "};\n")
print("mirror conjugates face turns to inverse face turns: ok")
