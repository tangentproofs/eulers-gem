# Platonic lane — Claude honesty audit

Companion to `PICKS_CLAUDE_AUDIT.md`, for the Platonic half of `UNIFIED_SPINE.md`.
Question this file answers: **what exactly is proved, and what is still hypothesis, in the
chain Euler–Poincaré → Platonic?**

## The chain as it now stands

```
Euler_Poincare_full                     (Embed.lean)          geometric, H+V-rep polytope
  └─► euler_relation_convex_3polytope   (Embed.lean)          V − E + F = 2, geometric
        └─► Platonic.regular_polytope_counts                  (PlatonicOfEuler.lean)
              ├── s·F = 2·E, m·V = 2·E  ← proved by double counting over face incidence
              └── V − E + F = 2         ← discharged from EP, NOT a hypothesis
                └─► Platonic.schlafli_pair_mem_of_regular_polytope
                      (s,m) ∈ {(3,3),(3,4),(3,5),(4,3),(5,3)}
                        └─► Simplex.tetrahedron_platonic       (GeometricPlatonic.lean)
                              a geometric tetrahedron, everything discharged
```

No theorem in this chain takes a bare `hEuler : V − E + F = 2`. The old
`Platonic.RegularNumbers` structure still has such a field, but it is now *constructed*
from EP inside `schlafli_pair_mem_of_regular_polytope`, never assumed at the top.

## Proved (no hypothesis)

| Fact | Where | Note |
|---|---|---|
| `V − E + F = 2` for a convex 3-polytope | `Embed.euler_relation_convex_3polytope` | root; H+V-rep, `affDim p = 3` |
| `s·F = 2·E`, `m·V = 2·E` | `PlatonicOfEuler.regular_polytope_counts` | double counting over `e ⊆ f` incidence, via `ncard_mul_eq_ncard_mul` (Mathlib `Finset.card_mul_eq_card_mul`) |
| `0 < E` | `PlatonicOfEuler.pos_edges_of_euler` | derived from `s,m ≥ 3` + double counting + Euler; no longer assumed |
| face-set finiteness per dimension | `PolytopeFaces.facesOfDim_finite_of_isPolytope` | from `face_eq_convexHull_inter`: a face of `convexHull ℝ V` is `convexHull ℝ (V ∩ F)`, so `F ↦ V ∩ F` is injective on faces |
| `(s,m)` in the five pairs | `Platonic.schlafli_pair_mem` | unchanged combinatorial argument |
| simplex face lattice | `SimplexFaces.lean` | faces ↔ vertex subsets; `affDim (face b S) = S.card − 1`; H-representation from barycentric coordinates + Riesz |
| tetrahedron `V=4, E=6, F=4` | `GeometricPlatonic.tetrahedron_face_counts` | *geometric* face counts (`IsFaceOf` + `affDim`) |
| tetrahedron `V − E + F = 2` | `GeometricPlatonic.tetrahedron_euler_relation` | from EP, for any tetrahedron in any 3-dim inner product space |
| tetrahedron incidence counts | `GeometricPlatonic.tetrahedron_incidence` | all four, from the face lattice |
| tetrahedron is `{3,3}` | `GeometricPlatonic.tetrahedron_platonic` | double counting + Euler + Schläfli membership |
| cross-polytope H-rep | `Octahedron.body_eq_iInter_closedHalfspace` | padding trick; lets EP apply to the octahedron |
| cross-polytope face lattice | `Octahedron.lean` | faces = partial sign assignments (`face b c`) plus the body; `eq_face_or_eq_body` |
| octahedron `V=6, E=12, F=8` | `Octahedron.octahedron_face_counts` | geometric face counts |
| octahedron `V − E + F = 2` | `Octahedron.octahedron_euler_relation` | from EP; `6 − 12 + 8 = 2` is a cross-check, not an input |
| octahedron incidence counts | `Octahedron.octahedron_incidence` | all four, from the face lattice |
| octahedron is `{3,4}` | `Octahedron.octahedron_platonic` | double counting + Euler + Schläfli membership |
| supporting-hyperplane face tool | `PolytopeFaces.isFaceOf_convexHull_argmax` | face lattice recipe for any explicit V-polytope |
| cube V-rep = Minkowski sum | `Cube.body_eq_sum_segment` | `∑ᵢ [-bᵢ, bᵢ]`; makes the H-rep easy both ways |
| cube H-rep | `Cube.body_eq_iInter_closedHalfspace` | `2n` halfspaces; lets EP apply to the cube |
| cube faces are subcubes | `Cube.eq_face_of_isFaceOf` | coordinate transfer: a face containing two corners contains the transferred corner, since the midpoints coincide |
| cube face dimension | `Cube.affDim_face` | `n − |supp c|`; direction = span of the free basis vectors |
| cube `V=8, E=12, F=6` | `Cube.cube_face_counts` | geometric face counts |
| cube `V − E + F = 2` | `Cube.cube_euler_relation` | from EP; `8 − 12 + 6 = 2` is a cross-check |
| cube incidence counts | `Cube.cube_incidence` | all four, from the face lattice |
| cube is `{4,3}` | `Cube.cube_platonic` | double counting + Euler + Schläfli membership |
| geometric simplex face counts | `Simplex.geometric_simplex_euler_poincare` | `C(n+1,d+1)` geometric `d`-faces in every dimension, and alternating sum `1` |
| every edge has two vertices | `EdgeVertices.ncard_vertices_of_edge` | a 1-dimensional face is a segment: a supporting functional along its direction is *injective* on it, so the extreme points are its argmin and argmax, and they differ |

Axiom check: run `lean/scripts/audit-axioms.sh`, which `#print axioms`-es every declaration in
`Results.lean` and fails on a `native_decide` axiom or `sorryAx`. Every Platonic-lane
declaration passes with `[propext, Classical.choice, Quot.sound]` — no `sorry`, no
`native_decide` axiom (three `native_decide`s were removed from the EP root,
`card_schlafliPairs` and two Results Platonic-count theorems for exactly this reason).

## Still hypothesis (and honestly labelled as such)

`schlafli_pair_mem_of_regular_polytope` takes three incidence counts. Two are the
*regularity* input and belong there:

* `hface_edges` — every 2-face has exactly `s` edges (it is an `s`-gon);
* `hvert_edges` — exactly `m` edges meet at every vertex.

One is a *polytope fact* that is assumed rather than derived from `IsPolytope`:

* `hedge_faces` — every edge lies in exactly two 2-faces (the **diamond property**).

**It is not vacuous.** The incidence theorems for all three geometric solids
(`tetrahedron_incidence`, `octahedron_incidence`, `cube_incidence`) prove it, so the theorem
has geometric models. Deriving the diamond property in general needs the quotient-polytope
(vertex-figure) theory of face lattices, which is not formalized here.

The fourth count, "every edge has exactly two 0-faces", **used to be assumed and is now
proved** in general: `EdgeVertices.ncard_vertices_of_edge`.

## Open

1. **The other two solids.** Three of five are geometric: the tetrahedron `{3,3}`
   (`SimplexFaces` + `GeometricPlatonic`), the octahedron `{3,4}` (`Octahedron.lean`) and the
   cube `{4,3}` (`Cube.lean`). The dodecahedron `{5,3}` and icosahedron `{3,5}` still exist
   only as `Platonic.RegularNumbers` witnesses (Euler bookkeeping, `(V,E,F)` integers) —
   those are explicitly **not** geometric constructions. They need golden-ratio coordinates,
   where the face lattice cannot be settled by `decide`, and are not attempted here.
2. **Regularity itself.** `hface_edges`/`hvert_edges` state *combinatorial* regularity of
   the face lattice. Metric regularity (congruent regular faces, equal solid angles, the
   symmetry group acting transitively on flags) is not formalized anywhere here, and no
   theorem in this repo should be read as classifying *metrically* regular polyhedra.
3. **Uniqueness.** "Exactly five" in the sense of *five Schläfli pairs* is proved; "exactly
   five solids up to similarity" is not — that needs uniqueness of the realization for each
   pair, which is not attempted.

## Verdict for Results.lean naming

Safe to name a Results theorem for:

* geometric Euler–Poincaré / `V − E + F = 2` for convex 3-polytopes;
* Schläfli classification **of combinatorially regular convex 3-polytopes**, provided the
  docstring says the two polytope-fact incidence hypotheses are assumed;
* the geometric tetrahedron, octahedron and cube statements, which are fully discharged.

Not safe to name:

* "the five Platonic solids" as a classification of geometric solids — two of the five
  have no geometric construction here;
* anything suggesting metric regularity or uniqueness up to similarity.
