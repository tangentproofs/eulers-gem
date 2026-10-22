---
id: IsPolytope.isPolyhedron
title: "Finitely many points, finitely many inequalities"
summary: "Every convex hull of a finite set is a finite intersection of closed halfspaces. Proving this is what let the public Euler results drop their halfspace-presentation hypothesis."
review: draft
authors: ["claude (for @tangentstorm)", "Kim Morrison (the Lean)"]
caveats:
  - "This is **one direction only**. The converse is false: an `IsPolyhedron` need not be bounded (a single halfspace is one), so it need not be a finite convex hull."
  - "It needs `[FiniteDimensional ℝ E]`. The functional-level work (`LinearInequalities.lean`, `PolyhedralRepresentation.lean`) is dimension-free and holds over any linearly ordered field; finite-dimensionality enters only to turn linear functionals into inner-product normals by Riesz representation."
  - "The docstring says it \"includes empty and lower-dimensional polytopes\", and that is worth taking literally: no nonemptiness or full-dimensionality hypothesis appears here. Those hypotheses live in the Euler theorems, not in the representation theorem."
  - "The Lean here (and in `LinearInequalities.lean`, `PolyhedralRepresentation.lean`, `PolytopeHalfspaces.lean`, `UnconditionalEuler.lean`) is Kim Morrison's, from PR #2; this explainer is not."
widgets:
  - type: outline
    title: "Three layers, bottom up"
    config:
      steps:
        - text: "LinearInequalities.lean: eliminate a variable from a finite system of linear inequalities"
          note: "Fourier–Motzkin style, over any linearly ordered field."
        - text: "PolyhedralRepresentation.lean: isPolyhedral_convexHull_of_finite — the hull of a finite set is cut out by finitely many inequalities on linear functionals"
          note: "Still field-generic; no inner product yet."
        - text: "PolytopeHalfspaces.lean: IsPolyhedral.isPolyhedron — replace each functional f by the vector normal f, with ⟪normal f, x⟫ = f x"
          note: "Finite-dimensional Riesz representation. This is the only place [FiniteDimensional ℝ E] is used."
          hard: true
        - text: "IsPolytope.isPolyhedron: compose the two"
          link: IsPolytope.isPolyhedron
quiz:
  - q: "What does `IsPolytope.isPolyhedron` state?"
    type: choice
    choices:
      - "`IsPolytope p → IsPolyhedron p`"
      - "`IsPolyhedron p → IsPolytope p`"
      - "`IsPolytope p ↔ IsPolyhedron p`"
      - "`IsPolytope p → Convex ℝ p`"
    answer: 0
    explain: "`theorem IsPolytope.isPolyhedron {p : Set E} (hp : IsPolytope p) : IsPolyhedron p` (PolytopeHalfspaces.lean), in a `[FiniteDimensional ℝ E]` section. The arrow goes V to H."
  - q: "Is the converse true?"
    type: choice
    choices:
      - "yes, by the same proof"
      - "no: polyhedra can be unbounded, polytopes cannot"
      - "yes, but only in dimension ≤ 3"
    answer: 1
    explain: "`closedHalfspace a 0` is an `IsPolyhedron` and is unbounded, while a finite convex hull is bounded. The full Weyl–Minkowski correspondence needs boundedness added on the H side; only the direction proved here is used."
  - q: "What role does Riesz representation play?"
    type: choice
    choices:
      - "it supplies the finitely many points"
      - "it turns the linear functionals of `IsPolyhedral` into the inner-product normals of `IsPolyhedron`"
      - "it proves the hull is convex"
      - "none; the proof is purely combinatorial"
    answer: 1
    explain: "`IsPolyhedral` (PolyhedralRepresentation.lean) describes a set by inequalities on linear functionals; `IsPolyhedron` uses `⟪a, x⟫ ≤ b`. The private `normal` in `PolytopeHalfspaces.lean` is `(InnerProductSpace.toDual ℝ E).symm`, and `normal_inner` is `⟪normal f, x⟫ = f x`. That is the bridge, and it is where finite-dimensionality is needed."
  - q: "What did the public Euler results look like before this theorem existed?"
    type: choice
    choices:
      - "they took a finite halfspace presentation `H` and `p = ⋂ h ∈ H, closedHalfspace h.1 h.2` as extra hypotheses"
      - "they were stated only for the cube"
      - "they assumed `V − E + F = 2`"
      - "they were unchanged"
    answer: 0
    explain: "Compare `Euler_Poincare_full hH hrep hp hdim hn` (Embed.lean), which still takes `hH : H.Finite` and `hrep`, with [`Euler_Poincare_of_isPolytope`](#/node/Euler_Poincare_of_isPolytope), which obtains both by `obtain ⟨H, hH, hrep⟩ := hp.isPolyhedron`. The git history calls this \"Discharge halfspace hypotheses from public Euler results\"."
---

## Plain English

**Theorem.** If `p` is the convex hull of finitely many points, then `p` is the intersection of
finitely many closed halfspaces.

```lean
theorem IsPolytope.isPolyhedron {p : Set E} (hp : IsPolytope p) : IsPolyhedron p
```

Two ways of describing a shape, and this says one implies the other. You hand over a list of
corners; the theorem hands back a list of inequalities whose solution set is exactly the same
shape. For a cube: in come eight points, out come six inequalities.

Half of the classical **Weyl–Minkowski** theorem, in the direction the Euler proof needs.

### In one breath

There are two ways to describe a crystal. You can name its corners, or you can name its faces —
"everything below this plane, and below that one, and below that one". Different descriptions, same
crystal. Going from corners to faces sounds obvious and is not: you have to find the planes, and
there is no formula for them. This theorem does it, for any number of corners in any number of
dimensions.

### Why it matters here

The Euler proof this repository follows — Jim Lawrence's, by way of Paulson's AFP entry — does not
work with corners. It works with **hyperplane arrangements**: it takes the finitely many planes
bounding the shape, uses them to chop all of space into cells, and shows that an alternating count
over cells cannot change when you refine the arrangement. You cannot start without a list of
planes.

So `Euler_Poincare_full` in `Embed.lean` asks for both descriptions at once:

```lean
Euler_Poincare_full (hH : H.Finite) (hrep : p = ⋂ h ∈ H, closedHalfspace h.1 h.2)
  (hp : IsPolytope p) (hdim : affDim p = Module.finrank ℝ E) (hn : 1 ≤ Module.finrank ℝ E)
```

That is honest but awkward: a *user* has a shape, not a presentation of it. This theorem makes
the presentation free, so [`Euler_Poincare_of_isPolytope`](#/node/Euler_Poincare_of_isPolytope)
opens with one line:

```lean
obtain ⟨H, hH, hrep⟩ := hp.isPolyhedron
exact Euler_Poincare_full hH hrep hp hdim hn
```

and [`results_euler_polyhedron`](#/node/Results.results_euler_polyhedron) ends up with exactly two
geometric hypotheses: `IsPolytope p` and `affDim p = 3`.

### How it is proved

In three layers, bottom up:

1. `LinearInequalities.lean` — Fourier–Motzkin-style elimination of variables from a finite system
   of linear inequalities, over any linearly ordered field.
2. `PolyhedralRepresentation.lean` — `isPolyhedral_convexHull_of_finite`: the hull of a finite set
   is cut out by finitely many inequalities on *linear functionals*. Still field-generic.
3. `PolytopeHalfspaces.lean` — `IsPolyhedral.isPolyhedron`: replace each functional `f` by the
   vector `normal f = (InnerProductSpace.toDual ℝ E).symm f`, so that `f x = ⟪normal f, x⟫`. This
   is where `[FiniteDimensional ℝ E]` is used, and it is the only place.

`isPolyhedron_iff_isPolyhedral` records that in finite dimensions the two presentation predicates
are interchangeable.

### Where it sits

Used by [`Euler_Poincare_of_isPolytope`](#/node/Euler_Poincare_of_isPolytope) and
[`euler_relation_of_isPolytope`](#/node/euler_relation_of_isPolytope), and through them by every
`Results` theorem on the Euler side —
[`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids) calls
`hP.isPolyhedron` directly as well, to get the `H` that
[`regular_polytope_counts`](#/node/Platonic.regular_polytope_counts) wants.
