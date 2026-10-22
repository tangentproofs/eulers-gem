---
id: closedHalfspace
title: "closedHalfspace: one linear inequality"
summary: "`closedHalfspace a b = {x | ⟪a, x⟫ ≤ b}` — everything on one side of a plane, boundary included. The brick that polyhedra are built from."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "The normal `a` may be `0`. Then the set is all of `E` if `0 ≤ b` and empty otherwise: a degenerate \"halfspace\" that is not half of anything. Nothing in the development rules this out, and nothing needs to."
  - "`⟪a, x⟫` is the real inner product, so this definition needs `[InnerProductSpace ℝ E]`. The functional-based alternative in `PolyhedralRepresentation.lean` (`IsPolyhedral`) does not, and works over any linearly ordered field."
widgets:
  - type: polyhedron
    title: "Each flat side of these is where one halfspace is tight"
    config:
      preset: octahedron
      show: [counts, incidence]
quiz:
  - q: "`closedHalfspace a b` is which set?"
    type: choice
    choices: ["`{x | ⟪a, x⟫ ≤ b}`", "`{x | ⟪a, x⟫ < b}`", "`{x | ⟪a, x⟫ = b}`", "`{x | ⟪x, x⟫ ≤ b}`"]
    answer: 0
    explain: "`def closedHalfspace (a : E) (b : ℝ) : Set E := {x | ⟪a, x⟫ ≤ b}` (Polytope.lean). Weak inequality, hence *closed*."
  - q: "Which lemma states that it is convex, and what does the proof use?"
    type: choice
    choices:
      - "`convex_closedHalfspace`, from Mathlib's `convex_halfSpace_le` applied to `isLinearMap_inner a`"
      - "it is not proved convex anywhere"
      - "`isConic_closedHalfspace_zero`"
      - "`convex_closedHalfspace`, by `simp`"
    answer: 0
    explain: "`lemma convex_closedHalfspace (a : E) (b : ℝ) : Convex ℝ (closedHalfspace a b) := convex_halfSpace_le (isLinearMap_inner a) b`. The content is that `x ↦ ⟪a, x⟫` is linear, which Mathlib supplies."
  - q: "What is `closedHalfspace 0 (-1)`?"
    type: choice
    choices: ["all of `E`", "the empty set", "a hyperplane through the origin", "a half of `E`"]
    answer: 1
    explain: "`⟪0, x⟫ = 0` for every `x`, and `0 ≤ -1` is false, so no point qualifies. With `b ≥ 0` instead you would get all of `E`. A zero normal gives a degenerate case, which the definition permits."
  - q: "`closedHalfspace a 0` for `a ≠ 0` — is it a cone (closed under scaling by non-negative reals)?"
    type: choice
    choices: ["yes, and the Lean proves it", "no", "only when `a = 0`"]
    answer: 0
    explain: "`lemma isConic_closedHalfspace_zero (a : E) : IsConic (closedHalfspace a 0)`. With `b = 0` the inequality `⟪a, c • x⟫ = c⟪a, x⟫ ≤ 0` survives multiplication by `c ≥ 0`. Homogeneous halfspaces are what the cone half of the Euler proof (`Cone.lean`, `ConeSlice.lean`) runs on."
---

## Plain English

```lean
def closedHalfspace (a : E) (b : ℝ) : Set E := {x | ⟪a, x⟫ ≤ b}
```

Pick a direction `a` and a number `b`. Measure every point `x` by how far it goes in direction
`a` — that is the inner product `⟪a, x⟫` — and keep the points whose measurement is at most `b`.
The result is one side of a flat wall, with the wall itself included. "Closed" is exactly that
`≤`: the boundary belongs.

Three or four of these intersected give a tetrahedron. Six give a cube.
[IsPolyhedron](#/node/IsPolyhedron) is "finitely many of these, intersected", and that is the
H-description a polytope is handed to the Euler machinery in.

### In one breath

One straight cut through space, and you keep one side of it, wall and all. That is the whole
idea. Everything else in this part of the proof is made by stacking these up.

### Two special cases worth knowing

- **`b = 0`.** Then the wall passes through the origin and the set is a *cone*: scaling a point by
  any non-negative number keeps it inside (`isConic_closedHalfspace_zero`). The Euler argument
  proves its core result about cones first (`Euler_polyhedral_cone`) and then descends to
  polytopes by slicing a cone one dimension up — that is what `ConeSlice.lean` and `Embed.lean`
  do. The homogeneity here is what makes that possible.
- **`a = 0`.** Then nothing is being measured, and the set is either everything or nothing
  depending on the sign of `b`. Degenerate, allowed, harmless.

### Where it sits

Used directly in [IsPolyhedron](#/node/IsPolyhedron) and `IsPolyhedralCone`, and therefore
everywhere underneath [`Euler_Poincare_of_isPolytope`](#/node/Euler_Poincare_of_isPolytope).
`isHyperplaneCellComplex_closedHalfspace_zero` is the lemma that turns one into a cell complex of
a one-element hyperplane arrangement, which is where the cell-counting argument starts.
