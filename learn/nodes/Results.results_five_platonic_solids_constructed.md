---
id: Results.results_five_platonic_solids_constructed
title: "The five Platonic solids, built in ℝ³ and proved regular"
summary: "Five explicit convex hulls in `EuclideanSpace ℝ (Fin 3)`, coordinates in `ℤ[φ]` (`φ = Real.goldenRatio`). Each is proved to be a regular polyhedron — a 3-dimensional polytope whose isometries act transitively on flags — with the classical `V`, `E`, `F` and face type `{s, m}`."
review: draft
authors: ["Grok Bot (for @tangentstorm)"]
caveats:
  - "**\"Regular\" means flag-transitive** (`IsRegularPolyhedron`: Coxeter, McMullen–Schulte), not Euclid's \"congruent regular faces, the same number at each vertex\". The two are classically equivalent for convex polyhedra; that equivalence is **not** formalized here."
  - "**This is existence, not uniqueness.** It says these five sets are regular. It does not say every regular polyhedron is one of them — for that see [`results_regular_polyhedron_face_data`](#/node/Results.results_regular_polyhedron_face_data), which is conditional."
  - "The face lattices are settled by kernel computation (`decide +kernel`) over exact `ℤ[φ]` arithmetic, from certificates produced by `lean/scripts/platonic_gen.py`. The script is untrusted; the kernel re-checks every certificate. No `native_decide`."
widgets:
  - type: polyhedron
    title: "The five — all of them now built in the Lean"
    config:
      preset: dodecahedron
      presets: [tetrahedron, cube, octahedron, dodecahedron, icosahedron]
      show: [counts, incidence]
quiz:
  - q: "What does `IsRegularPolyhedron P` require, besides `IsPolytope P` and `affDim P = 3`?"
    type: choice
    choices:
      - "for any two flags (vertex ⊆ edge ⊆ facet) there is an isometry of ℝ³ mapping `P` onto itself and the first flag onto the second"
      - "all edges have the same length and all faces are congruent regular polygons"
      - "the same number of faces meets at every vertex"
      - "the vertices lie on a sphere"
    answer: 0
    explain: "`RegularPolyhedron.lean`: `∀ v e f v' e' f', IsFlag P v e f → IsFlag P v' e' f' → ∃ g : R3 ≃ᵃⁱ[ℝ] R3, g '' P = P ∧ g '' v = v' ∧ g '' e = e' ∧ g '' f = f'`. Nothing about lengths or angles is assumed — those become consequences."
  - q: "What are `V`, `E`, `F` for `Platonic3.icosahedron` in this theorem?"
    type: choice
    choices: ["12, 30, 20", "20, 30, 12", "6, 12, 8", "12, 30, 12"]
    answer: 0
    explain: "`HasFaceData icosahedron 12 30 20 3 5`: 12 vertices, 30 edges, 20 triangular facets, five edges at every vertex. The dodecahedron has the dual numbers `20 30 12 5 3`."
  - q: "How is it shown that the icosahedron has exactly 20 facets (and no other 2-faces)?"
    type: choice
    choices:
      - "the kernel checks, for every triple of vertices, that their plane either separates the vertices or cuts out a listed facet — exact `ℤ[φ]` arithmetic, so the face lattice is computed, not assumed"
      - "it is assumed as a hypothesis"
      - "by floating-point computation"
      - "by `native_decide`"
    answer: 0
    explain: "`Explicit.Data.face_cases` turns `checkAll = true` into: every face is ∅, the body, a vertex, a listed edge or a listed facet. It rests on `IsPolytope.exposed_of_isFaceOf` (every face of a polytope is cut out by a supporting plane). The checks are `decide +kernel`."
  - q: "Does this theorem prove that every regular polyhedron is similar to one of these five?"
    type: choice
    choices:
      - "no — it is existence only; uniqueness is stated elsewhere and still rests on two unproved gaps"
      - "yes"
      - "yes, but only up to isometry"
    answer: 0
    explain: "The statement is a conjunction of five `IsRegularPolyhedron _ ∧ HasFaceData _ …` facts about five specific sets. The converse direction is `PlatonicGaps.regular_polyhedron_classification`, outside `Results`, which depends on `sorryAx`."
  - q: "Which number is `φ` in the coordinates?"
    type: choice
    choices: ["`Real.goldenRatio = (1 + √5)/2`", "`π`", "`√2`", "`1/2`"]
    answer: 0
    explain: "The icosahedron's vertices are `(0, ±1, ±φ)` and cyclic permutations; the dodecahedron's are `(±1, ±1, ±1)` and `(0, ±φ⁻¹, ±φ)` cyclic. `ZPhi.lean` does exact arithmetic in `ℤ[φ]` using `φ² = φ + 1`."
---

## Plain English

The statement is five facts, one per solid:

```lean
(IsRegularPolyhedron Platonic3.tetrahedron  ∧ HasFaceData Platonic3.tetrahedron   4  6  4 3 3) ∧
(IsRegularPolyhedron Platonic3.cube         ∧ HasFaceData Platonic3.cube          8 12  6 4 3) ∧
(IsRegularPolyhedron Platonic3.octahedron   ∧ HasFaceData Platonic3.octahedron    6 12  8 3 4) ∧
(IsRegularPolyhedron Platonic3.dodecahedron ∧ HasFaceData Platonic3.dodecahedron 20 30 12 5 3) ∧
(IsRegularPolyhedron Platonic3.icosahedron  ∧ HasFaceData Platonic3.icosahedron  12 30 20 3 5)
```

Each solid is a concrete subset of `EuclideanSpace ℝ (Fin 3)`: the convex hull of a list of points.
`HasFaceData P V E F s m` says `P` has `V` vertices, `E` edges and `F` facets — the faces
([`IsFaceOf`](#/node/IsFaceOf)) of affine dimension 0, 1, 2, counted with `Set.ncard` — and that every
facet has `s` edges, every edge lies in two facets, and every vertex lies on `m` edges.

`IsRegularPolyhedron P` says `P` is a convex polytope of dimension 3 and that its symmetry group is
*flag-transitive*: any vertex-in-edge-in-facet can be moved to any other by an isometry of ℝ³ that
maps `P` onto itself. The isometries are found explicitly: three reflections per solid, with each of
the 24, 48, 48, 120, 120 flags reached by a word in them.

### In one breath

The Greeks' five solids are now real objects in the Lean, not just lists of numbers: the computer
builds each one from coordinates — the golden ratio for the two hard ones — and checks every face
and every symmetry exactly.

## What this does and does not prove

**It does prove:**

- **Existence of all five**, as genuine convex polytopes in ℝ³, including the dodecahedron and the
  icosahedron that [`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids) only
  has as number records.
- **Regularity in the strong modern sense**: flag-transitivity under the full isometry group.
- **The face lattice, computed**: the counts and incidences are about the actual face sets.

**It does not prove:**

- **Uniqueness.** Nothing here says a regular polyhedron must be one of these. The conditional
  result is [`results_regular_polyhedron_face_data`](#/node/Results.results_regular_polyhedron_face_data).
- **Euclid's definition.** "Congruent regular faces, the same number at each vertex" is not the
  definition used, and its equivalence with flag-transitivity is not formalized.
- Anything about the specific size or position: these are particular representatives; any similar
  copy is equally Platonic.

### Where it sits

- Restates `Platonic3.five_platonic_solids_exist` (`EulersGem/PlatonicSolids.lean`).
- Built on `ExposedFaces.lean`, `ZPhi.lean`, `ExplicitPolyhedron.lean`, `ExplicitRegular.lean` and the
  five generated modules in `EulersGem/PlatonicSolids/`.
- [Trust](#/trust) has the one-row summary.
