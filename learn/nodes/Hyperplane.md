---
id: Hyperplane
title: "Hyperplane: a normal and a constant, nothing more"
summary: "`abbrev Hyperplane (E : Type*) := E × ℝ` — a pair `(a, b)` standing for the equation `⟪a, x⟫ = b`. It is not a subspace, and it is degenerate when `a = 0`."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**It is an `abbrev` for a product type.** `Hyperplane E` and `E × ℝ` are the same type, and Lean will happily unfold one into the other. The name is documentation, not structure."
  - "`a = 0` is allowed and is degenerate: `⟪0, x⟫ = b` describes the whole space (if `b = 0`) or nothing. The docstring says this matches Paulson's treatment via `sgn`, and nothing downstream needs to exclude it."
  - "A `Hyperplane` is *data*, not a set. The sets it names are `closedHalfspace h.1 h.2` and the cell-complex machinery's `{x | ⟪h.1, x⟫ = h.2}`; the pair itself is just a label."
widgets:
  - type: polyhedron
    title: "A cube is six halfspaces; its faces are where they are tight"
    config:
      preset: cube
      show: [counts]
quiz:
  - q: "What is `Hyperplane E`?"
    type: choice
    choices:
      - "`abbrev Hyperplane (E : Type*) := E × ℝ`"
      - "a `structure` with a normal and a constant"
      - "`Submodule ℝ E` of codimension 1"
      - "`AffineSubspace ℝ E`"
    answer: 0
    explain: "`abbrev Hyperplane (E : Type*) := E × ℝ` (Hyperplane.lean), with the docstring \"An affine hyperplane given in H-description by `⟪a, x⟫ = b`\". A pair, by abbreviation."
  - q: "What set does the pair `(a, b)` name in `IsPolyhedron`?"
    type: choice
    choices:
      - "`closedHalfspace a b = {x | ⟪a, x⟫ ≤ b}`"
      - "`{x | ⟪a, x⟫ = b}`"
      - "`{x | ⟪a, x⟫ < b}`"
      - "`{a}`"
    answer: 0
    explain: "`IsPolyhedron S` is `∃ H : Set (Hyperplane E), H.Finite ∧ S = ⋂ h ∈ H, closedHalfspace h.1 h.2`. The *halfspace* is what gets intersected; the hyperplane equation is the boundary of it, and is what the cell-complex machinery in `Hyperplane.lean` and `EulerChar.lean` chops space with."
  - q: "`(0, 1) : Hyperplane E`. What does `closedHalfspace 0 1` come to?"
    type: choice
    choices: ["all of `E`, since `⟪0, x⟫ = 0 ≤ 1` always", "the empty set", "a hyperplane through the origin"]
    answer: 0
    explain: "The inequality is satisfied by every point. With `b < 0` instead it would be empty. Degenerate normals are permitted; the docstring notes this is deliberate, following Paulson."
  - q: "Why does the Euler proof need a set of hyperplanes rather than just the polytope?"
    type: choice
    choices:
      - "the proof is a cell-counting argument over the arrangement the hyperplanes cut space into, and invariance under refining that arrangement is its engine"
      - "to compute the volume"
      - "to decide convexity"
      - "it does not; the hyperplanes are decoration"
    answer: 0
    explain: "`HyperplaneEquiv`, the cells, `CellGeometry.lean` and the refinement-invariance results in `EulerChar.lean` all run on a finite `Set (Hyperplane E)`. [IsPolytope.isPolyhedron](#/node/IsPolytope.isPolyhedron) is what produces one from a finite vertex set."
---

## Plain English

```lean
abbrev Hyperplane (E : Type*) := E × ℝ
```

A pair: a vector `a` and a number `b`, standing for the equation `⟪a, x⟫ = b`. In ℝ³ that is an
ordinary flat plane; in the plane it is a line.

It is an `abbrev`, so `Hyperplane E` *is* `E × ℝ` as far as Lean is concerned. The pair carries no
proof that `a ≠ 0`, so a degenerate "hyperplane" with `a = 0` is allowed — the docstring notes this
matches Paulson's treatment, where it describes the whole space or nothing depending on the sign of
`b`.

The pair is data. The sets it names are:

- `{x | ⟪a, x⟫ = b}` — the plane itself, which the cell-complex machinery cuts space along;
- [`closedHalfspace a b = {x | ⟪a, x⟫ ≤ b}`](#/node/closedHalfspace) — one side of it, which
  [`IsPolyhedron`](#/node/IsPolyhedron) intersects finitely many of.

### In one breath

A direction and a distance. Together they pick out a flat wall: all the points that stick out
exactly that far in that direction. Give the Lean a direction and a number and it knows which wall
you mean.

### Where it sits

`Set (Hyperplane E)` is the "arrangement" the whole Euler proof is built on:
`HyperplaneEquiv` identifies points with the same sign pattern against a set of them, the
equivalence classes are the *cells*, and `EulerChar.lean`'s central result is that an alternating
count over cells does not change when you refine the arrangement. Everything in
`Hyperplane.lean`, `CellGeometry.lean`, `Cone.lean`, `ConeFaceCell.lean` and `Embed.lean` quantifies
over one.

Used in the statement of [`IsPolyhedron`](#/node/IsPolyhedron) and of
[`Platonic.regular_polytope_counts`](#/node/Platonic.regular_polytope_counts).
