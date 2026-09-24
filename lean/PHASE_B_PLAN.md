# Phase B plan (Memnar #1535 / GTD #538) — Pick's + Platonic

Survey date: 2026-09-24 (America/New_York).  
Mathlib pin: `09a9e06e4e5ccd5b783f25e52ad3ebecfb1e2d68` (Lean `v4.35.0-rc1`).

## Mathlib survey (Pick / Platonic)

| Item | In Mathlib? | Notes |
|---|---|---|
| Pick's theorem | **No** | LeanEval leaderboard + Stuttgart `PicksTheorem2025` (lemma ≠ full geometric thm); no Mathlib port |
| Lattice polygon / interior–boundary lattice counts | **No** | Geometry-of-numbers has Minkowski/Blichfeldt, not Pick |
| Planar-graph Euler / triangulation API | **No** usable for Pick | `SimpleGraph` has trees/Eulerian paths; no faces/planarity |
| Regular / Platonic / Schläfli | **No** | LeanEval Schläfli challenge is `sorry`; no Mathlib datatype |
| Polygon area / shoelace | Partial | Euclidean Hausdorff volume exists; no lattice-triangle area=1/2 API ready for Pick |

Existing eulers-gem substrate (`Euler_Poincare_full`, 3D `V−E+F=2`) is the Euler input; Pick/Platonic are **combinatorial consequences**, matching Poly100 stubs.

## Platonic solids (what README/ROADMAP mean)

From `isabelle/Poly100.thy` § Platonic + notes:

1. **Number:** combinatorial classification — if faces are regular `s`-gons, `m` meet at each vertex (`s,m≥3`), double-counting `sF=2E`, `mV=2E`, and Euler `V−E+F=2`, then
   `(s,m) ∈ {(3,3),(3,4),(3,5),(4,3),(5,3)}`.
2. **Constructions:** Euler bookkeeping for the five Schläfli types (explicit `V,E,F`); geometric regular embeddings still open (Poly100 also left constructions TODO).

**Lean plan:** `EulersGem/Platonic.lean` — integer identity `(s−2)(m−2)<4`, enumerate five pairs, construct five `(V,E,F)` witnesses; claim in `Results.lean`.

## Pick's theorem (Funkenbusch / Euler route)

From Poly100 notes + Funkenbusch Monthly 1974:

1. Triangulate lattice polygon → planar graph with `V=I+B`, outer face + `T` triangles (`F=T+1`).
2. Edge theorem / handshaking: `2E = 3T + B` (equiv. Funkenbusch `E = 3I + 2B − 3` via Euler).
3. Primitive triangles have area `1/2` ⇒ `A = T/2 = (F−1)/2`.
4. Plug into Euler ⇒ `A = I + B/2 − 1`.

**Lean plan:** `EulersGem/Picks.lean`

- Prove algebraic Pick from Euler + Funkenbusch + `A=(F−1)/2` (Poly100 `pick's_theorem`).
- Prove triangulation identities: `2E = 3T + B` + Euler + `V=I+B` ⇒ Funkenbusch edge count and Pick.
- **Scope narrowing (honest):** full geometric lattice triangulation + primitive-triangle area `1/2` remain open (Mathlib gap); we land the Euler→Pick combinatorial core that Poly100 already sketched.

## Deliverables

- Green `lake build`; Results claims only proved statements
- Unpark README/ROADMAP/site; update prove2 milestones
- Incremental green commits on `main`
