# Face-Turning Octahedron: God's number is at most 36

Every position of the Face-Turning Octahedron (FTO) can be solved in **36 moves or fewer**, counting
each face turn as one move (either direction; FTO faces are triangles, so a turn is 120° and the two
directions are the only ones).

The proof is a two-phase argument made exact by computer search. This repository holds the programs,
the results they produced, and the argument that turns those results into the bound.

## The puzzle and how positions are written

The FTO has 6 corners, 12 edges and 24 triangular centres. The centres split into two separate sets
of 12 that never mix:

- **CENTERS**: one set of 12 centres, coloured 4 colours × 3 each,
- **CENTERS2**: the other set of 12, also 4 colours × 3.

Centres of the same colour are interchangeable, so a centre set is described by its colouring
(12!/3!⁴ = 369,600 colourings).

The FTO has no fixed centre piece, so the same physical position can be held in 12 orientations. To get
one description per position, we always hold the puzzle so that the edge between faces **B** and **U**
is in its home slot, the right way round. A move is a face turn followed, when needed, by the
whole-puzzle rotation that puts that edge back home. In this frame the definition file names the moves
**F, Fw, D, Dw, L, BR, BL, R**: Fw and Dw are B and U turns re-expressed in the fixed frame. Each move
with or without `'` is one move.

A position splits into two independent parts:

| part | pieces | states |
|---|---|---|
| **phase 1** | EDGES (11 free, one fixed by the frame) + CENTERS | 11!/2 × 12!/3!⁴ = 7,376,624,640,000 |
| **phase 2** | corners + CENTERS2 | 11,520 × 369,600 = 4,257,792,000 |

Every move acts on each part separately, so applying a move sequence to a position applies it to both
parts independently.

## Terms

- **Phase-1 distance** `d1(p)`: the fewest moves that solve the phase-1 part p (edges and CENTERS),
  ignoring everything else.
- **Phase-1 solved**: edges and CENTERS solved. **Phase-2 position**: a full position that is phase-1
  solved, described by its corners + CENTERS2 state f.
- **Phase-2 bound** `B(f)`: a proven upper bound on the moves needed to solve the phase-2 position f
  completely, never leaving the puzzle in a different phase-1 state at the end. The intermediate moves
  may disturb edges and CENTERS freely, as long as they are restored by the end.
- **Radius**: how far the search lets phase 1 wander. The phase-2 search below only visits full positions
  whose phase-1 part is within **4** moves of phase-1 solved. "Radius 4" therefore means: routes that
  may scramble edges and CENTERS, but never more than 4 moves' worth.
- **Loop**: a move sequence that starts and ends with phase 1 solved. It changes only corners and
  CENTERS2, so it acts like one big phase-2 move. Example: `U' BL U BL'` (4 moves) restores edges and
  CENTERS but cycles three corners. If a loop T of length a takes f to f', then `B(f) ≤ a + B(f')`: do
  T, then the route for f'.
- **Holdout**: a phase-2 position the radius-4 search did not reach within a given number of moves.
- **Symmetry class**: positions that are images of each other under the puzzle's 24 symmetries that
  keep the B U edge home (whole-puzzle rotations combined with recolouring, and mirror images). They all
  need the same number of moves, so the searches store one representative per class.
- **2-bit table**: the phase-1 search stores, for every position, its distance mod 3 in 2 bits. That is
  enough to walk down to solved: from distance d, some move reaches d − 1.

## The results the proof uses

**R1. Phase 1 needs at most 15 moves** (`results/phase1_distribution.tsv`). A complete breadth-first
search of all 7,376,624,640,000 phase-1 states, with every depth counted and the total checked against
the group order:

| depth | 0–11 | 12 | 13 | 14 | 15 |
|---|---|---|---|---|---|
| positions | (see file) | 2,737,029,747,682 | 4,126,276,081,604 | 91,762,964,330 | **411** |

The 411 depth-15 states are in `results/phase1_depth15_positions.txt`.

**R2. Radius-4 phase-2 bounds** (`results/phase2_bounds_radius4.tsv`). A breadth-first search of the
full puzzle restricted to radius 4, run to depth 23. A phase-2 position first reached at depth t gets
`B(f) = t`. It reached 4,257,791,986 of the 4,257,792,000 phase-2 positions by depth 23; 11,625,577 of
them at 22 and 13,595 at 23.

**R3. The 14 holdouts have explicit solutions of 20 to 23 moves** (`results/holdout_solutions.txt`).
Each is written as a plain move sequence and replayed on the whole puzzle (all four piece sets),
ending solved. So `B(f) ≤ 23` for every phase-2 position.

**R4. Loop sweep: all but 3 drop to 22 or less** (`results/phase2_sweep_bound23.txt`). Take the 13,609
positions without a bound of 22 or less after R2 (the 13,595 at 23 plus the 14 holdouts). For each one,
try every loop of length ≤ 12: there are 11,568,601 distinct loop effects, found by meet-in-the-middle
over all move sequences of length ≤ 6. Each gives a route of loop length + R2 bound of the landing
position. All but 3 get a route of 22 or less. The 3 that don't are three of the holdouts from R3, with
23-move solutions. So `B(f) ≤ 22` for all phase-2 positions except a set E of 3, where `B = 23`.

**R5. Step-back check** (`results/log_stepback.txt`). For each b in E and each of the 16 moves m, the
full position "m applied to (phase-1 solved, b)" can be solved in at most 23 moves. This is shown by a
loop T of length a that **starts with m** and takes b to some f' with `a − 1 + B(f') ≤ 23`: after the
first move of T, the remaining a − 1 moves and then the route for f' solve it.

**R6. Joint check on the 411 depth-15 states** (`results/log_joint.txt`). For each of the 411 states p,
take 24 different 15-move solutions and 24 different 16-move solutions of p (19,728 in all,
`results/phase1_depth15_solutions.txt`, each replayed to phase-1 solved). Every phase-2 part f is
covered: some solution w of p sends f to an f' with `|w| + B(f') ≤ 36`.

## The proof

Take any position P = (p, f) and let d = d1(p) ≤ 15 (R1). Solve phase 1 with an optimal sequence w
of d moves. That leaves a phase-2 position f'.

- **d ≤ 13:** `B(f') ≤ 23` (R3), so P is solved in at most 13 + 23 = 36.
- **d = 14 and f' not in E:** `B(f') ≤ 22` (R4), so P is solved in at most 14 + 22 = 36.
- **d = 14 and f' in E:** write w = w'·m, where m is the last move. After the 13 moves of w', the puzzle
  is at the position that m takes to (phase-1 solved, f'). That position is "m⁻¹ applied to
  (phase-1 solved, f')", and R5 solves it in at most 23 (it covers all 16 moves). Total at most 13 + 23 = 36.
- **d = 15:** p is one of the 411 states, and R6 gives a solution of at most 36 for every f.

Every case is at most 36, so **God's number for the FTO is at most 36**.

## Built-in checks

- **Phase 1 (`fto_bfs selftest`)**: all 24 symmetries are verified as automorphisms of the move graph.
  The definition-file moves are checked against plain face turns on 200,000 random states. An
  independent plain BFS (no symmetry) matches the engine through depth 7, and the engine's different
  code paths agree through depth 11, including interrupted and resumed runs. Every layer is checked for
  symmetry closure, and the final total equals 7,376,624,640,000.
- **Radius search**: three independent radius-4 runs, with different storage paths, gave identical
  counts at every depth. A radius-0 reference BFS (`fto_tube ref`) matches the engine at small depths.
- **Loops**: sampled loops are replayed as plain face turns on the full puzzle; all restore edges and
  CENTERS and have the recorded effect. Loops of length ≤ 8, which stay inside radius 4, never beat the
  R2 bound, as the triangle inequality requires. Loops with a recorded first move are checked to start
  with that move.
- **Explicit solutions**: the 14 holdout solutions in R3 are replayed on the whole puzzle, and so are
  all 19,728 phase-1 solutions used in R6.

## Programs (`src/`)

| program | what it computes |
|---|---|
| `fto_bfs.cpp` | R1: complete phase-1 BFS on SSD (2-bit table, 24 symmetries, resumable); exports the depth-15 states and their optimal and near-optimal solutions |
| `fto_tube.cpp` | R2 `run`, R4 `holdouts`, R5 `stepback`, R6 `joint` |
| `fto_macros.cpp` | the loop lists (all loops up to length 12) and the explicit holdout solutions of R3 |
| `full_tables.h`, `p2_gen.py` | the move tables of the whole puzzle, generated from the definition file |

Build with g++ 13 or newer (MSYS2 UCRT64 on Windows):

```
g++ -std=c++20 -O3 -march=native -static src/fto_bfs.cpp    -o fto_bfs.exe
g++ -std=c++20 -O3 -march=native -static src/fto_tube.cpp   -o fto_tube.exe
g++ -std=c++20 -O3 -march=native -static src/fto_macros.cpp -o fto_macros.exe
```

The programs use the Windows file API.

## Reproducing

The two large searches need an NVMe SSD. Phase 1 uses an 84 GB table plus up to about 160 GB of
frontier files. The radius-4 search peaks at a few hundred GB. Both ran on a laptop with 16 GB of RAM.

```
# R1: phase 1
fto_bfs start  --dir P1 --threads 24          # resume with: fto_bfs resume --dir P1
fto_bfs export --dir P1                        # depth-15 states
fto_bfs optimals --dir P1 --limit 24           # 24 solutions of 15 and 24 of 16 moves per depth-15 state

# loops up to length 12 (plain, and with first-move data)
fto_macros 6 macros_len12.bin
fto_macros 6 macros_first12.bin

# R2: radius-4 search to depth 23
fto_tube run --dir R4 --radius 4 --target 23 --threads 24

# R3: the 14 holdouts, then explicit sequences for them
fto_tube holdouts --dir R4 --radius 4 --target 23 --macros macros_len12.bin   # -> R4\holdouts.txt, R4\holdouts_cert.bin
rename R4\holdouts.txt holdouts_target23.txt
fto_macros 6 x.bin 4000000000 R4\holdouts_cert.bin holdout_solutions.txt

# R4: sweep of everything above 22
fto_tube holdouts --dir R4 --radius 4 --target 22 --macros macros_len12.bin   # -> R4\holdouts.txt

# R5, R6
fto_tube stepback --dir R4 --radius 4 --target 23 --macros macros_first12.bin
fto_tube joint    --dir R4 --radius 4 --target 36 --solutions P1\solutions_many_depth_15.txt
```

`stepback` and `joint` read the R2 layers together with both sweep files from the R4 folder.

## Result files (`results/`)

| file | contents |
|---|---|
| `phase1_distribution.tsv` | R1: positions and symmetry classes at each phase-1 depth |
| `phase1_depth15_positions.txt` | the 411 depth-15 phase-1 states (CENTERS colours / EDGES) |
| `phase1_depth15_solutions.txt` | 24 solutions of 15 moves and 24 of 16 moves for each of them |
| `phase2_bounds_radius4.tsv` | R2: number of phase-2 positions at each bound |
| `phase2_holdouts_radius4.txt` | R3: the 14 positions not reached within 23, with their best loop route |
| `holdout_solutions.txt` | R3: explicit solutions (20–23 moves) for those 14 |
| `phase2_sweep_bound23.txt` | R4: best loop route for each of the 13,609 positions above 22 |
| `log_stepback.txt`, `log_joint.txt` | R5, R6: program output (0 failures, 0 leftovers) |

The last line of `log_joint.txt` ("the others are only within 37") is the program's simple 14 + 23
estimate. It doesn't know about R5, which closes that case as shown in the proof above.

Phase-2 positions are written as corner permutation (6) | corner orientation (6) / CENTERS2 colours (12).
