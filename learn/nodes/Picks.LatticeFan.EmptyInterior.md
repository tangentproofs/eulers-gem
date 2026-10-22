---
id: Picks.LatticeFan.EmptyInterior
title: "EmptyInterior: I = 0, stated as a set equation"
summary: "`P.interiorLatticePoints = ∅` — no lattice point lies in the convex hull of the vertices other than the boundary points. The hypothesis that avoids needing a finite enumeration."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "Like [interiorLatticePoints](#/node/Picks.LatticePolygon.interiorLatticePoints), it is measured against the **convex hull of the vertex set**. Its docstring adds the right qualifier: \"Matches classical Pick `I = 0` when the polygon is convex (listed vertices extreme).\" For a non-convex polygon it is a stronger condition than \"nothing inside the shape\"."
  - "Being a statement that a `Set` is empty, it sidesteps the finiteness problem entirely: you do not need a `Finset` to say a set is empty. That is why [results_picks_of_empty_primitive_fan](#/node/Results.results_picks_of_empty_primitive_fan) has no un-discharged existence hypothesis and [results_picks_theorem](#/node/Results.results_picks_theorem) does."
widgets:
  - type: pick
    title: "EmptyInterior holds for some of these, not others"
    config:
      preset: primitive-triangle
      show: [counts, hypotheses, fan]
quiz:
  - q: "State the definition."
    type: choice
    choices:
      - "`P.interiorLatticePoints = ∅`"
      - "`P.B = P.nVertices`"
      - "`interior P.convexHullRegion = ∅`"
      - "`P.latticePointsInConvexHull = P.boundaryLatticePoints`"
    answer: 0
    explain: "`def EmptyInterior : Prop := P.interiorLatticePoints = ∅` (LatticeFan.lean). The third choice is a topological statement that would mean the polygon is degenerate; the fourth is equivalent but is not the definition."
  - q: "Why does this hypothesis remove the need for a `Finset S`?"
    type: choice
    choices:
      - "because \"this set is empty\" needs no enumeration, while \"this set has `n` elements\" does"
      - "because `∅` is a `Finset`"
      - "because `Set.ncard ∅ = 0`"
      - "it does not"
    answer: 0
    explain: "[results_picks_theorem](#/node/Results.results_picks_theorem) needs `S.card` as a number, which requires a `Finset`, which requires finiteness — not proved here. `results_picks_of_empty_primitive_fan` only needs the set to be empty, which is a `Prop` about the set itself. That is why it is the Pick result with no remaining gap."
  - q: "Which triangle satisfies both `PrimitiveEdges` and `EmptyInterior`?"
    type: choice
    choices:
      - "`(0,0), (1,0), (0,1)`"
      - "`(0,0), (2,1), (1,2)`"
      - "`(0,0), (3,0), (0,3)`"
      - "`(0,0), (4,0), (1,3)`"
    answer: 0
    explain: "The unit right triangle: all three edges primitive, area `1/2`, no lattice point inside. The second has `(1,1)` inside (its determinant is 3, so area `3/2`). The third has non-primitive edges and one interior point. The fourth has `I = 3`."
  - q: "A triangle with `|latticeDet| = 1` — does it satisfy `EmptyInterior`?"
    type: choice
    choices:
      - "yes: `LatticeTriangle`'s `|det| = 1 ⇒` only vertex lattice points"
      - "no"
      - "only if its edges are primitive"
    answer: 0
    explain: "`LatticeTriangle.lean` proves `|det| = 1` implies the *closed* triangle contains only the three vertices as lattice points (via Cramer's rule on the barycentric coordinates). `LatticeTriangleEmpty.lean` proves the converse for nondegenerate triangles, which is the direction `FanDetPrimitive_of_empty_fan_triangles` uses."
  - q: "`EmptyInterior` plus `StrictlyConvexCCW` plus `PrimitiveEdges` plus injectivity gives which chain?"
    type: choice
    choices:
      - "`FanTrianglesEmpty` → `FanDetPrimitive` → each fan triangle has area `1/2` → shoelace `= (n−2)/2 = B/2 − 1`"
      - "`V − E + F = 2` directly"
      - "finiteness of the interior points"
      - "`B = 2 * nVertices`"
    answer: 0
    explain: "`FanTrianglesEmpty_of_empty_interior` → `FanDetPrimitive_of_empty_fan_triangles` → `Triangle.shoelace_eq_half_of_isDetPrimitive` → `shoelace_eq_B_div_two_sub_one_of_empty_fan`. Four hypotheses, four links in the chain — one each."
---

## Plain English

```lean
def EmptyInterior : Prop := P.interiorLatticePoints = ∅
```

Nothing inside. No lattice point lies in the convex hull of the vertices except the ones on the
cyclic boundary.

This is the `I = 0` case of Pick's formula, and it has a quiet advantage: **you can say a set is
empty without enumerating it.** [`results_picks_theorem`](#/node/Results.results_picks_theorem) has
to be handed a `Finset S` of the interior points, because it needs their *number*, and the
finiteness that would produce one is not proved in this repository.
[`results_picks_of_empty_primitive_fan`](#/node/Results.results_picks_of_empty_primitive_fan) needs
no such thing. It is the one Pick result here with no un-met hypothesis.

### In one breath

Your shape is small enough that no grid crossing lands strictly inside it. Then the area formula
loses its first term and reads: half the number of crossings on the outline, minus one. The
smallest case is a triangle with three crossings and area a half, and you cannot draw a smaller
triangle on the grid than that.

### Why it comes with friends

In the Lean, `EmptyInterior` almost never appears alone. The chain it starts is:

```
EmptyInterior + PrimitiveEdges + VerticesExtreme + injective vertices
  └─► FanTrianglesEmpty           (no stray lattice point in any corner-fan triangle)
        └─► FanDetPrimitive        (each fan determinant is ±1)
              └─► each fan triangle has shoelace exactly 1/2
                    └─► P.shoelace = (n − 2)/2 = B/2 − 1
```

and `VerticesExtreme` is itself discharged from
[`StrictlyConvexCCW`](#/node/Picks.LatticeFan.StrictlyConvexCCW)
(`VerticesExtreme_of_strictlyConvexCCW`). Each hypothesis of
`results_picks_of_empty_primitive_fan` buys exactly one link.

The middle step is a genuinely pretty piece of number theory: a nondegenerate lattice triangle
containing no lattice points other than its vertices has `|det| = 1`
(`LatticeTriangleEmpty.lean`), and therefore area exactly `1/2`. That is the sense in which
primitive triangles are the atoms of lattice geometry.

### Where it sits

A hypothesis of
[`results_picks_of_empty_primitive_fan`](#/node/Results.results_picks_of_empty_primitive_fan).
Defined from [`interiorLatticePoints`](#/node/Picks.LatticePolygon.interiorLatticePoints). Its
`I = 1` analogue, `UniqueInterior`, drives `LatticeFanInterior.lean`.
