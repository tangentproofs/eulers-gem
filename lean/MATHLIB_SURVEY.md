# Mathlib survey vs Paulson AFP (`Euler_Polyhedron_Formula`)

Survey date: 2026-09-24 (America/New_York).  
Mathlib pin: `09a9e06e4e5ccd5b783f25e52ad3ebecfb1e2d68` (Lean `v4.35.0-rc1`).  
AFP reference: [Euler's Polyhedron Formula](https://isa-afp.org/entries/Euler_Polyhedron_Formula.html)
(theory `Euler_Formula`; HOL Light / Jim Lawrence → Paulson).

Goal of this note: map Paulson's development onto Mathlib and list **gaps we must
port ourselves** under `lean/EulersGem/`.

## Paulson outline (what we need)

| AFP notion | Role |
|---|---|
| `hyperplane_side (a,b) x = sgn (a · x − b)` | trichotomy relative to one affine hyperplane |
| `hyperplane_equiv A` | equivalence: same side of every hyperplane in arrangement `A` |
| `hyperplane_cell A C` | cells = equivalence classes |
| `hyperplane_cellcomplex A S` | unions of cells |
| `Euler_characteristic A S` | `∑_{C cell, C ⊆ S} (−1)^{aff_dim C}` |
| invariance under refining `A` | key lemma before cones |
| `Euler_polyhedral_cone` | full-dim proper polyhedral cones |
| `Euler_Poincare_full` | full-dim convex polytopes |
| `Euler_relation` | dim-3 specialisation `V − E + F = 2` |

Uses Isabelle `HOL-Analysis`: `polyhedron`, `polytope`, `face_of`, `aff_dim`,
`rel_interior`, halfspace openness/convexity, cones, supporting hyperplanes.

## What Mathlib already has (usable substrate)

### Half-spaces / hyperplanes (set-level convexity)

- `Mathlib.Analysis.Convex.Basic`:
  - `convex_halfSpace_le / ge / lt / gt`
  - `convex_hyperplane`
  - all take an `IsLinearMap` functional + threshold.
- Complex special cases: `convex_halfSpace_re_*`, `convex_halfSpace_im_*`.
- Manifold model: `EuclideanHalfSpace` (charts with boundary) — **not** the
  combinatorial arrangement notion.
- Separation: `Analysis.LocallyConvex.Separation` (`iInter_halfSpaces_eq`).
- Inner-product linear forms: `innerSL ℝ a : E →L[ℝ] ℝ` so
  `⟪a, ·⟫` is immediately an `IsLinearMap`.

**Gap:** no bundled “affine hyperplane = `(a,b)`” type, no `hyperplane_side` /
arrangement / cell API.

### Affine dimension

- `AffineSubspace.dim` / `AffineSubspace.finDim` (`WithBot Cardinal` / `WithBot ℕ`)
  in `LinearAlgebra.AffineSpace.Dimension`.
- Empty subspace → `⊥` (Isabelle `aff_dim = -1`).

**Gap:** Paulson applies `aff_dim` to arbitrary *sets* (via affine hull). Mathlib
has the subspace API; we need a thin wrapper `affDim (s : Set E) : ℤ` (or
`WithBot ℕ`) matching Isabelle conventions for Euler sums.

### Faces / extreme / exposed sets

- `IsExtreme`, `Set.extremePoints` (`Analysis.Convex.Extreme`).
- `IsExposed`, exposed points; `eq_inter_halfSpace` (`Analysis.Convex.Exposed`).
- Cone faces: `PointedCone.IsFaceOf` (`Geometry.Convex.Cone.Face`) — cone-specific,
  not general polytope `face_of`.

**Gap:** no Isabelle-style `face_of` for convex polytopes/polyhedra; no face lattice
of a polytope; docs in `Exposed.lean` explicitly note this as future work.

### Polyhedra / polytopes

- **No** `IsPolyhedron` / `IsPolytope` predicates, no H-description /
  V-description API comparable to `HOL-Analysis.Polytope`.
- Informal mentions only (Coxeter, intercalation of a “convex polytope” in
  neighborhood arguments).
- Cones: `ProperCone`, dual / finitely generated dual cones (`DualFG` = finite
  intersection of halfspaces) — useful later for the cone step, not a substitute
  for polytope faces.

**Gap:** entire polyhedron/polytope layer must be ported or redefined (H-rep as
finite intersection of closed halfspaces; polytope = bounded polyhedron / convex
hull of finite set).

### Cell complexes / Euler characteristic

- Algebraic topology: `Topology.CWComplex`, `AlgebraicTopology.RelativeCellComplex`,
  simplicial sets / singular homology.
- Homological `eulerChar` (`Algebra.Homology.EulerCharacteristic`) — chain complexes,
  not combinatorial cells of a hyperplane arrangement.
- Poset `eulerChar` in incidence algebras — different notion.
- Simplicial complexes: `Analysis.Convex.SimplicialComplex` (geometric) and
  `AlgebraicTopology.SimplicialComplex`.

**Gap:** Paulson's *hyperplane cell complex* and its combinatorial
`Euler_characteristic` (sum over arrangement cells by affine dimension) are
**absent**. CW / relative cell complexes do not give the invariance-under-refining
proof.

### Simplices (already used in this repo)

- `Affine.Simplex`, face constructions, centroids — good for the combinatorial
  simplex special case already proved in `EulersGem.SimplexEuler`.

## Gap summary (port priority)

| Priority | Missing in Mathlib | Paulson name | Lean home (planned) |
|---|---|---|---|
| P0 | Hyperplane side / equiv / cells | `hyperplane_side`, `hyperplane_cell` | `EulersGem.Hyperplane` |
| P0 | Cell complexes (unions of cells) | `hyperplane_cellcomplex` | `EulersGem.Hyperplane` / `CellComplex` |
| P1 | Combinatorial Euler char of a complex | `Euler_characteristic` | `EulersGem.EulerChar` |
| P1 | Invariance under refining arrangements | `Euler_characterstic_invariant` | same |
| P2 | Polyhedron / polytope + `face_of` | HOL-Analysis `Polytope` | `EulersGem.Polytope` (later) |
| P2 | Set-level `affDim` wrapper | `aff_dim` | small util next to Euler char |
| P3 | Cone Euler relation → full Euler–Poincaré | `Euler_polyhedral_cone`, `Euler_Poincare_full` | after P1–P2 |

## Design choices for the Lean port

1. **Stay close to Paulson.** Prefer `(a, b) : E × ℝ` hyperplanes and `SignType`
   sides over inventing a different cell language, so AFP cross-checks stay easy.
2. **Reuse Mathlib** for convexity of halfspaces/hyperplanes, inner products,
   finiteness of powersets, and (later) `AffineSubspace.finDim`.
3. **Do not** route through CW complexes or homological Euler char for the main
   theorem — wrong abstraction for Lawrence's proof.
4. **Results.lean discipline:** only export proved theorems; substrate lemmas may
   live in `EulersGem.*` long before they are claimed in `Results.lean`.

## Status after this session

- Survey written (this file).
- `EulersGem.Hyperplane`: sides, equiv, cells, complexes, Un/Inter/mono, finiteness.
- `EulersGem.AffDim`: set-level `affDim` (`∅ ↦ -1`).
- `EulersGem.CellGeometry`: open∩affine, relative interior, halfspace affDim
  preservation, **and** proper hyperplane-slice affDim drop-by-1
  (`affDim_affine_inter_hyperplane` / `affDim_cell_inter_hyperplane`).
- `EulersGem.EulerChar`: combinatorial `eulerCharacteristic`, cell/Un additivity,
  empty-arrangement evaluation; **full refinement invariance**
  (`eulerCharacteristic_insert`, `eulerCharacteristic_invariant`) via cut-into-three
  sign identity. Not yet exported in `Results.lean`.
