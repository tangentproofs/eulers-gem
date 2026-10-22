---
id: IsPolyhedron
title: "IsPolyhedron: a finite intersection of closed halfspaces"
summary: "`IsPolyhedron S` says `S` is cut out by finitely many inequalities `⟪a, x⟫ ≤ b`. This is the H-description, and the Euler proof works with it internally — but it is no longer a hypothesis of the public results."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "`IsPolyhedron` does **not** imply bounded. The empty intersection is all of `E`; a single halfspace is a half of it. Every `IsPolytope` is an `IsPolyhedron`, but not conversely, and the word \"polyhedron\" here means the unbounded notion, following Paulson's `polyhedron`."
  - "The normals `h.1` are vectors of `E`, not abstract linear functionals, so the definition needs an inner product. `IsPolyhedral` (defined in `LinearInequalities.lean`) uses functionals instead and works over any linearly ordered field; `isPolyhedron_iff_isPolyhedral` identifies the two in finite dimensions, by Riesz representation."
  - "`Hyperplane E` is just `abbrev Hyperplane (E : Type*) := E × ℝ` (`Hyperplane.lean`): a pair of a normal and a constant. It is not a subspace, despite the name."
widgets:
  - type: polyhedron
    title: "Every convex preset here is also a finite intersection of halfspaces"
    config:
      preset: triangular-prism
      show: [counts, incidence]
quiz:
  - q: "Write out the definition of `IsPolyhedron S`."
    type: choice
    choices:
      - "`∃ V : Set E, V.Finite ∧ S = convexHull ℝ V`"
      - "`∃ H : Set (Hyperplane E), H.Finite ∧ S = ⋂ h ∈ H, closedHalfspace h.1 h.2`"
      - "`Convex ℝ S ∧ IsClosed S`"
      - "`∃ a b, S = closedHalfspace a b`"
    answer: 1
    explain: "`def IsPolyhedron (S : Set E) : Prop := ∃ H : Set (Hyperplane E), H.Finite ∧ S = ⋂ h ∈ H, closedHalfspace h.1 h.2` (Polytope.lean). The first choice is [IsPolytope](#/node/IsPolytope)."
  - q: "Is every `IsPolyhedron` bounded?"
    type: choice
    choices: ["yes", "no — a single halfspace is one, and so is all of `E` (take `H = ∅`)"]
    answer: 1
    explain: "An intersection over the empty finite set of halfspaces is `Set.univ`. One halfspace is an unbounded slab. So `IsPolyhedron` is strictly weaker than `IsPolytope`, which is why the implication goes one way only."
  - q: "Which direction is a theorem in this repository?"
    type: choice
    choices:
      - "`IsPolyhedron → IsPolytope`"
      - "`IsPolytope → IsPolyhedron`"
      - "both, as `isPolytope_iff_isPolyhedron`"
      - "neither; they are assumed to coincide"
    answer: 1
    explain: "[`IsPolytope.isPolyhedron`](#/node/IsPolytope.isPolyhedron), in `PolytopeHalfspaces.lean`: every convex hull of finitely many points is a finite intersection of closed halfspaces. The converse is false, since polyhedra can be unbounded."
  - q: "`closedHalfspace a b` is which set?"
    type: choice
    choices: ["`{x | ⟪a, x⟫ ≤ b}`", "`{x | ⟪a, x⟫ = b}`", "`{x | ⟪a, x⟫ < b}`", "`{x | ‖x - a‖ ≤ b}`"]
    answer: 0
    explain: "`def closedHalfspace (a : E) (b : ℝ) : Set E := {x | ⟪a, x⟫ ≤ b}` (Polytope.lean), with `convex_closedHalfspace` proving it convex. Closed and weak: `≤`, not `<`."
---

## Plain English

`IsPolyhedron S` means: **`S` is everything that satisfies a fixed finite list of linear
inequalities.**

```lean
def IsPolyhedron (S : Set E) : Prop :=
  ∃ H : Set (Hyperplane E), H.Finite ∧
    S = ⋂ h ∈ H, closedHalfspace h.1 h.2
```

A `Hyperplane E` is an `abbrev` for a pair `(a, b) : E × ℝ`, and
`closedHalfspace a b = {x | ⟪a, x⟫ ≤ b}` is the slab of points on one side of the plane
`⟪a, x⟫ = b`, boundary included. Intersect finitely many of those and you have a polyhedron.

The cube `[-1,1]³` is six inequalities: `x ≤ 1`, `-x ≤ 1`, `y ≤ 1`, and so on. The tetrahedron is
four. But so is the single inequality `z ≤ 0` — an infinite half of space — and so is the empty
list of inequalities, which is all of ℝ³. **Polyhedra need not be bounded.** That is the one place
the everyday word and the Lean word part company.

### In one breath

Think of a slab of stone and a saw. Each cut is straight and goes all the way through, and you
keep whichever side you like. Make finitely many cuts and whatever is left is a polyhedron. If you
cut enough times in enough directions you end up with something you could hold in your hand; if
you cut only once you are left with half the world, which is still a polyhedron in this sense.

### The two descriptions

| | you say | you get |
|---|---|---|
| [IsPolytope](#/node/IsPolytope) (V) | finitely many **points** | fill in between them |
| `IsPolyhedron` (H) | finitely many **inequalities** | keep what satisfies all of them |

The classical **Weyl–Minkowski** theorem says these describe the same bounded sets. Half of that —
the half the Euler proof needs — is a theorem here:
[`IsPolytope.isPolyhedron`](#/node/IsPolytope.isPolyhedron).

Why does the Euler proof need the H-description at all? Because Jim Lawrence's argument, as
Paulson formalized it, works with **hyperplane arrangements**: it takes the finitely many
hyperplanes bounding the polytope, chops space into cells by them, and shows the Euler
characteristic is invariant under refining the arrangement. You cannot start that without a list
of hyperplanes. The V-description is what a user naturally has; the H-description is what the
proof wants; the representation theorem bridges the two, and before it was proved the public
results had to carry the H-description as an extra hypothesis.

### Where it sits

- [`IsPolytope.isPolyhedron`](#/node/IsPolytope.isPolyhedron) produces one from a finite hull.
- [`Euler_Poincare_of_isPolytope`](#/node/Euler_Poincare_of_isPolytope) calls that, then hands the
  arrangement to `Euler_Poincare_full` in `Embed.lean`.
- `isPolyhedron_iff_isPolyhedral` relates it to the functional-based `IsPolyhedral` of
  `LinearInequalities.lean`, by finite-dimensional Riesz representation.
