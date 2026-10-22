---
id: Results.results_euler_characteristic
title: "Euler–Poincaré: the characteristic of a convex polytope is 1"
summary: "The paper-facing form of the root theorem: a full-dimensional convex polytope in a finite-dimensional real inner product space has `faceEulerSum = 1`."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "The docstring's closing line, \"In dimension 3 this is `V − E + F = 2`\", is a pointer to a *different* theorem ([results_euler_relation_dimension_three](#/node/Results.results_euler_relation_dimension_three)), not part of this statement. This one concludes `= 1`."
  - "Full-dimensionality (`affDim p = Module.finrank ℝ E`) is a genuine hypothesis. A square in ℝ³ is not covered as stated."
  - "This is a restatement: the proof is `EulersGem.Euler_Poincare_of_isPolytope hP hdim hn`, one term."
widgets:
  - type: face-lattice
    title: "The alternating sum, for the two families whose counts are exact"
    config:
      n: 4
quiz:
  - q: "What does the theorem conclude?"
    type: choice
    choices:
      - "`faceEulerSum p (Module.finrank ℝ E) = 1`"
      - "`V − E + F = 2`"
      - "`faceEulerSum p 3 = 2`"
      - "`faceEulerSum p (Module.finrank ℝ E) = 0`"
    answer: 0
    explain: "`theorem results_euler_characteristic … : EulersGem.faceEulerSum p (Module.finrank ℝ E) = 1`. The `2` is a different theorem; the `0` is the *cone* result (`Euler_polyhedral_cone`) that the proof passes through."
  - q: "`p` is a square in `EuclideanSpace ℝ (Fin 3)`. Does the theorem apply?"
    type: choice
    choices:
      - "yes"
      - "no: `affDim p = 2` and `Module.finrank ℝ E = 3`, so `hdim` fails"
      - "no: a square is not an `IsPolytope`"
    answer: 1
    explain: "`hdim : EulersGem.affDim p = Module.finrank ℝ E` is full-dimensionality. The square's characteristic is still 1 (apply the theorem in the plane it spans), but this statement does not reach it."
  - q: "For the 4-dimensional cube (tesseract): `f₀ = 16`, `f₁ = 32`, `f₂ = 24`, `f₃ = 8`, `f₄ = 1`. What does `faceEulerSum` come to?"
    type: number
    answer: 1
    explain: "`16 − 32 + 24 − 8 + 1 = 1`. The value is 1 in every dimension — that is the content of the theorem, and the reason the repository treats `= 1` rather than `= 2` as the root claim."
  - q: "Which hypothesis excludes the ambient space being zero-dimensional?"
    type: choice
    choices: ["`hP`", "`hdim`", "`hn : 1 ≤ Module.finrank ℝ E`", "none of them"]
    answer: 2
    explain: "`hn : 1 ≤ Module.finrank ℝ E`. The proof route homogenizes `p` into `E × ℝ` and slices a cone, which needs a dimension to work in."
  - q: "True or false: this theorem proves Euler's formula for every polyhedron in ℝ³."
    type: choice
    choices: ["True", "False — only for convex ones, and only via the dimension-3 corollary"]
    answer: 1
    explain: "False twice over. `IsPolytope` is \"convex hull of a finite set\", so non-convex polyhedra are excluded (the toroidal picture frame has `V − E + F = 0`). And this statement concludes `= 1`; the `V − E + F = 2` reading is [results_euler_relation_dimension_three](#/node/Results.results_euler_relation_dimension_three)."
---

## Plain English

```lean
theorem results_euler_characteristic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {p : Set E}
    (hP : EulersGem.IsPolytope p)
    (hdim : EulersGem.affDim p = Module.finrank ℝ E)
    (hn : 1 ≤ Module.finrank ℝ E) :
    EulersGem.faceEulerSum p (Module.finrank ℝ E) = 1
```

**The Euler–Poincaré characteristic of a convex polytope is 1.** Take any shape that is the convex
hull of finitely many points, filling up the space it lives in. Count its faces of each dimension,
add them with alternating signs, counting the shape itself at the top. You get 1.

This is the paper-facing restatement of
[`Euler_Poincare_of_isPolytope`](#/node/Euler_Poincare_of_isPolytope). The proof is a single term.

### In one breath

Corners minus edges plus flat sides minus the solid itself: one. For a flat shape, corners minus
edges plus the shape: one. For a four-dimensional shape, the same alternating count: one. One is the
answer in every dimension, and that invariance is the actual theorem. Euler's famous two is what you
see in three dimensions when you forget to count the solid.

## What this does and does not prove

**It does prove:**

- Genuine Euler–Poincaré for convex polytopes, in arbitrary finite dimension, over any
  finite-dimensional real inner product space.
- With the counts being the real geometric ones: `{f | IsFaceOf p f ∧ affDim f = d}.ncard`, where
  [`IsFaceOf`](#/node/IsFaceOf) is extreme-plus-convex and [`affDim`](#/node/affDim) is the
  dimension of the affine span. No combinatorial stand-in.
- With no presentation assumed. The halfspace description the proof needs is derived from the
  vertex description by [`IsPolytope.isPolyhedron`](#/node/IsPolytope.isPolyhedron); the finiteness
  of each face set is derived by
  [`facesOfDim_finite_of_isPolytope`](#/node/facesOfDim_finite_of_isPolytope). Both are theorems in
  this repository, not hypotheses.

**It does not prove:**

- Anything about **non-convex** bodies. [`IsPolytope`](#/node/IsPolytope) is a convex hull, so
  convexity is not negotiable. The toroidal picture frame has `V − E + F = 0`.
- Anything about a polytope that does **not** fill its ambient space. `hdim` is used. (The fix is
  to apply the theorem inside `affineSpan ℝ p`; the theorem does not do it for you.)
- Anything about convex bodies that are not finite hulls — a ball, a disc, a cylinder.
- `V − E + F = 2`. That is the separate statement
  [`results_euler_relation_dimension_three`](#/node/Results.results_euler_relation_dimension_three),
  one bookkeeping step away.
- Anything about surfaces, genus, or the formula `V − E + F = 2 − 2g`. None of that is formalized
  anywhere in this repository.

### Where it sits

The root. Everything on the [graph](#/) hangs below it:
[`euler_relation_of_isPolytope`](#/node/euler_relation_of_isPolytope) in dimension 3, and from
there the [Platonic](#/node/Results.results_five_platonic_solids) and
[Pick](#/node/Results.results_picks_theorem) lanes. See [Trust](#/trust) for how much of each lane
really descends from here.
