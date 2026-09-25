# Results honesty notes (for full Claude audit)

Policy (2026-09-24): Claude double-check applies to **every** Results theorem,
README/site row, ROADMAP checkbox, and theorem-naming docstring — not only Pick.

## Pick-related (already FAIL once — see `PICKS_CLAUDE_AUDIT.md`)

| Export | Classical name? | Honest status |
|--------|-----------------|---------------|
| `results_funkenbusch_identity` | No | Count identity only |
| `results_triangulation_count_identity` | No | Count identity only; handshaking **assumed** |
| `results_shoelace_pick_form_of_primitive_triangulation_witness` | No (name avoids classical Pick) | Witness + `hEuler_planar` (EP-spine hyp, discharge open) + handshaking |
| (none) | classical Pick | **Not claimed** |

EP-spine constraint: `hEuler_planar` must eventually come from `Euler_Poincare_full` / planar EP — not free bare-ℤ Euler; no Ehrhart bypass.

`LatticeTriangle.lean`: shoelace/`|det|=1` + Cramer + closed-triangle emptiness; **not** Haar.
`LatticePolygon.lean` / `PicksTriangulation.lean`: geometric I/B + witness; not classical Pick.

## Platonic / Schläfli

| Export | Hedge |
|--------|-------|
| `results_platonic_schlafli_classification` | Combinatorial Schläfli pairs under Euler + double-counting — **not** geometric regular solids in `ℝ³` |
| `results_platonic_schlafli_card` | Card of the five pairs finset |
| `results_platonic_five_constructions` | Existential `(V,E,F)` witnesses — **not** geometric embeddings |

## Simplex / binomial

| Export | Hedge |
|--------|-------|
| `results_eulerChar_simplex` | Binomial alternating sum = 0 |
| `results_card_combinatorialFaces` | `powersetCard` identity |
| `results_tetrahedron_polyhedron_numbers` | Abstract 3-simplex binomial counts — **not** embedded tetrahedron |
| `results_polyhedron_formula_of_eulerChar` | Pure ℤ bookkeeping from Euler char hypothesis |
| `results_faceEulerSum_simplex_faceCount` | Binomial face-sum = 1 |

## Geometric Euler–Poincaré (`EulersGem` substrate)

| Export | Hedge |
|--------|-------|
| `results_euler_relation_of_faceEulerSum` | Bookkeeping from `faceEulerSum=1` + face ncard hyps — does not discharge geometric hyps alone |
| `results_faceEulerSum_of_height_one` | Needs height-1 / homogenize / dual-open hypotheses (Paulson slice setup) |
| `results_Euler_Poincare_full` | Full-dim H+V-rep in `EulersGem` API — Mathlib lacks native polytope faces |
| `results_euler_relation_convex_3polytope` | Same substrate; classical “all convex 3-polytopes” only insofar as `IsPolytope` + H-rep match |

Auditor should verify each geometric theorem’s hypotheses match the informal claim on README/site.
