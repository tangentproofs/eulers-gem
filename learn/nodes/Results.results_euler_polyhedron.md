---
id: Results.results_euler_polyhedron
title: "Euler's polyhedron formula in ℝ³, with two hypotheses"
summary: "In `EuclideanSpace ℝ (Fin 3)`: a finite convex hull of affine dimension 3 satisfies `V − E + F = 2`. The whole repository in one line."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "No stronger than [results_euler_relation_dimension_three](#/node/Results.results_euler_relation_dimension_three), which holds in any 3-dimensional real inner product space. This is the ℝ³ reading, so that the statement can be read with no type-class hypotheses in it."
  - "`affDim p = 3` is load-bearing: `IsPolytope` alone admits `∅`, points, segments and flat polygons."
widgets:
  - type: polyhedron
    title: "Turn it. Both hypotheses hold for seven of these."
    config:
      preset: cube
      show: [counts, incidence, truncate]
quiz:
  - q: "List the hypotheses of `results_euler_polyhedron`."
    type: choice
    choices:
      - "`EulersGem.IsPolytope p` and `EulersGem.affDim p = 3`"
      - "`IsPolytope p`, `affDim p = 3`, and a finite halfspace presentation of `p`"
      - "`IsPolyhedron p` and `affDim p = 3`"
      - "`IsPolytope p`, `affDim p = 3` and finiteness of each face set"
    answer: 0
    explain: "Exactly two: `theorem results_euler_polyhedron {p : Set (EuclideanSpace ℝ (Fin 3))} (hP : EulersGem.IsPolytope p) (hdim : EulersGem.affDim p = 3)`. The halfspace presentation is derived by [IsPolytope.isPolyhedron](#/node/IsPolytope.isPolyhedron) and the face finiteness by [facesOfDim_finite_of_isPolytope](#/node/facesOfDim_finite_of_isPolytope) — both theorems, not hypotheses."
  - q: "What is `EuclideanSpace ℝ (Fin 3)`?"
    type: choice
    choices:
      - "ℝ³ with the standard inner product"
      - "the three-element type"
      - "an abstract 3-dimensional vector space with no inner product"
      - "the unit cube"
    answer: 0
    explain: "Mathlib's `EuclideanSpace ℝ (Fin 3)` is `PiLp 2 fun _ : Fin 3 => ℝ`: functions `Fin 3 → ℝ` with the L² inner product. Ordinary three-space. `finrank_euclideanSpace_fin` gives its dimension as 3, which is how the general theorem's third hypothesis is discharged by `simp`."
  - q: "`p = ∅`. Both `IsPolytope p` and the conclusion?"
    type: choice
    choices:
      - "`IsPolytope ∅` holds, but `affDim ∅ = -1 ≠ 3`, so the theorem does not apply"
      - "`IsPolytope ∅` fails"
      - "the theorem applies and the conclusion is `0 = 2`, a contradiction"
    answer: 0
    explain: "`IsPolytope ∅` holds with `V = ∅`. `affDim_empty : affDim ∅ = -1`, so `hdim` fails and no conclusion is drawn. This is exactly the role of the dimension hypothesis."
  - q: "Count for a dodecahedron: `V = 20`, `E = 30`, `F = 12`. Does the theorem apply to it?"
    type: choice
    choices:
      - "yes if someone constructs one in ℝ³ — and this repository does not"
      - "yes, and the repository constructs it"
      - "no, dodecahedra are not polytopes"
    answer: 0
    explain: "The theorem would apply, since a geometric dodecahedron is a 3-dimensional convex hull of 20 points. But nothing in this repository builds one: `Platonic.dodecahedron` is a `RegularNumbers` record holding `(20, 30, 12, 5, 3)`. The tetrahedron, octahedron and cube *are* built (`GeometricPlatonic.lean`, `Octahedron.lean`, `Cube.lean`)."
  - q: "True or false: `results_euler_polyhedron` is Euler's polyhedron formula."
    type: choice
    choices:
      - "True, for convex polyhedra, which is what Euler's formula is about"
      - "False: it only proves the characteristic is 1"
      - "False: the counts are combinatorial, not geometric"
    answer: 0
    explain: "True, with the qualifier stated. The conclusion is literally `V − E + F = 2` with `V`, `E`, `F` the cardinalities of the geometric face sets, and the only hypotheses are convex-hull-of-a-finite-set and dimension 3. Non-convex polyhedra are a different claim and are not proved here (nor are they true in this form)."
---

## Plain English

```lean
theorem results_euler_polyhedron {p : Set (EuclideanSpace ℝ (Fin 3))}
    (hP : EulersGem.IsPolytope p) (hdim : EulersGem.affDim p = 3) :
    ({f | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 0}.ncard : ℤ) -
    ({f | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 1}.ncard : ℤ) +
    ({f | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 2}.ncard : ℤ) = 2
```

**Take any set in ordinary three-dimensional space that is the convex hull of finitely many points
and that is genuinely three-dimensional. Then corners minus edges plus flat sides equals two.**

This is the headline result. Two hypotheses, both about the shape itself, both checkable; and a
conclusion in which `V`, `E`, `F` are the honest geometric face counts.

### In one breath

A die has eight corners, twelve edges and six faces, and eight minus twelve plus six is two. So
does every other solid you could carve out of a block of wood with straight cuts and no hollowing:
pyramids, prisms, gemstones, geodesic domes. Two, every single time. That is the whole theorem, and
it is the oldest result in topology.

## What this does and does not prove

**It does prove:**

- Euler's polyhedron formula for convex polyhedra in ℝ³, with only `IsPolytope` and `affDim = 3`
  assumed. Nothing is handed to the theorem — not a presentation, not a face count, not a
  triangulation, not Euler's relation itself.
- `V`, `E` and `F` really are the counts of faces of affine dimension 0, 1 and 2 — single points,
  segments and flat patches, defined by [`IsFaceOf`](#/node/IsFaceOf) and
  [`affDim`](#/node/affDim). They are counts, not `ncard`-of-possibly-infinite artefacts, because
  [`facesOfDim_finite_of_isPolytope`](#/node/facesOfDim_finite_of_isPolytope) is proved.

**It does not prove:**

- Euler's formula for **non-convex** polyhedra. `IsPolytope` is a convex hull. The toroidal picture
  frame has `V − E + F = 0`; the widget above has it as a preset precisely so that this is visible.
- Anything about **polyhedra with holes**, **polyhedral surfaces** or **genus**.
- Anything about **graphs**, **maps** or **planar graphs**. Those require Steinitz's theorem or an
  equivalent to connect to polytopes, and there is none here.
- Anything in **other dimensions**. Use
  [`results_euler_characteristic`](#/node/Results.results_euler_characteristic) for those, where
  the answer is 1, not 2.
- Any **converse**. A solid with `V − E + F = 2` need not be convex.

### How it is proved

```
Euler_Poincare_of_isPolytope        faceEulerSum p (finrank ℝ E) = 1
  └─► euler_relation_of_isPolytope  V − E + F = 2, any 3-dim inner product space
        └─► euler_polyhedron        the same, in EuclideanSpace ℝ (Fin 3)
              └─► results_euler_polyhedron
```

The real work is below the first line: hyperplane arrangements, cell complexes, invariance of a
cell count under refinement, the cone case (where the answer is `0`), and a cone-slice
correspondence that shifts every dimension by one and so flips every sign. See the walkthrough on
[`Euler_Poincare_of_isPolytope`](#/node/Euler_Poincare_of_isPolytope).

### Where it sits

The focal node of this site's [graph](#/). From here,
[`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids) and the
[Pick lane](#/node/Results.results_picks_theorem) descend — read [Trust](#/trust) for how far each
descent actually reaches.
