---
id: Picks.LatticeFan.ConvexCCW
title: "ConvexCCW: every vertex left of every edge"
summary: "`∀ i j, 0 ≤ latticeDet (vertex i) (vertex (nextIdx i)) (vertex j)` — a doubly-quantified sign condition that says \"convex and counterclockwise\" in one go."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "It is **weak** (`0 ≤`), so collinear listed vertices pass it. That is why [StrictlyConvexCCW](#/node/Picks.LatticeFan.StrictlyConvexCCW) pairs it with the strict `LocalCCWTurns`."
  - "It bundles convexity and orientation. A convex polygon listed clockwise fails it, even though the shape is convex — the condition is about the description, not only the shape."
  - "The quantification is over *all* pairs `(i, j)`, including `j = i` and `j = nextIdx i`, where the determinant is zero and `0 ≤` holds trivially."
widgets:
  - type: pick
    title: "The clockwise and non-convex presets fail this one"
    config:
      preset: clockwise
      show: [counts, hypotheses]
quiz:
  - q: "State the definition."
    type: choice
    choices:
      - "`∀ i j : Fin P.nVertices, 0 ≤ latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j)`"
      - "`∀ i, 0 < latticeDet (P.vertex (P.prevIdx i)) (P.vertex i) (P.vertex (P.nextIdx i))`"
      - "`Convex ℝ P.convexHullRegion`"
      - "`∀ i j, latticeDet (P.vertex i) (P.vertex j) (P.vertex (P.nextIdx j)) ≠ 0`"
    answer: 0
    explain: "Doubly quantified, weak inequality. The second choice is `LocalCCWTurns`; the third is trivially true of any convex hull and says nothing about the vertex list."
  - q: "Why is a *convex* polygon listed clockwise not `ConvexCCW`?"
    type: choice
    choices:
      - "reversing the cycle negates every determinant, so `0 ≤` becomes `0 ≥`"
      - "it is `ConvexCCW`; orientation is irrelevant"
      - "because clockwise polygons are not convex"
    answer: 0
    explain: "`latticeDet` is alternating, so the whole condition flips sign. The name says `CCW` for a reason. Reverse the list and it holds — the restriction is on the description."
  - q: "What is discharged from `ConvexCCW` alone in `LatticeFan.lean`?"
    type: choice
    choices:
      - "`FanDetsNonneg` — the corner-fan determinants are all `≥ 0`, so the fan triangles are consistently oriented"
      - "`FanDetsPos`"
      - "`PrimitiveEdges`"
      - "nothing"
    answer: 0
    explain: "`FanDetsNonneg_of_ConvexCCW`. The strict version `FanDetsPos` needs `StrictlyConvexCCW` *and* injective vertices (`FanDetsPos_of_strictlyConvexCCW`), because a degenerate fan triangle would have determinant zero."
  - q: "Does `ConvexCCW` imply the vertices are distinct?"
    type: choice
    choices:
      - "no — a repeated vertex gives zero determinants, which satisfy `0 ≤`"
      - "yes"
      - "yes, given `3 ≤ nVertices`"
    answer: 0
    explain: "Injectivity is a separate hypothesis everywhere it is needed. The `repeated-vertex` preset in the `pick` widget shows a polygon where this matters."
---

## Plain English

```lean
def ConvexCCW : Prop :=
  ∀ i j : Fin P.nVertices,
    0 ≤ latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j)
```

Walk the outline. For every edge you are standing on, *every* vertex of the polygon is weakly on
your left. [`latticeDet a b c`](#/node/Picks.LatticeTriangle.latticeDet) is positive exactly when
`c` is left of the ray `a → b`.

That one condition says two things at once:

- **convex** — if the shape bulged inward anywhere, some vertex would be strictly right of some
  edge;
- **counterclockwise** — if you listed it the other way round, every determinant would come out
  negative.

It is weak (`0 ≤`), so it tolerates collinear vertices. The strict partner `LocalCCWTurns` does not,
and [`StrictlyConvexCCW`](#/node/Picks.LatticeFan.StrictlyConvexCCW) is the conjunction.

### In one breath

Stand on each side of your shape in turn, facing the way you are walking. Every corner of the shape
should be on your left or straight ahead — never on your right. If that is true for every side, the
shape is convex and you are going anticlockwise.

### Where it sits

Half of [`StrictlyConvexCCW`](#/node/Picks.LatticeFan.StrictlyConvexCCW), and used on its own for
`FanDetsNonneg_of_ConvexCCW`, which is what
[`volume_convexHullRegion_eq_ofReal_shoelace`](#/node/Picks.LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace)
needs to know the fan triangles do not overlap.
