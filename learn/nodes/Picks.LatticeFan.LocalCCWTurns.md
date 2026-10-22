---
id: Picks.LatticeFan.LocalCCWTurns
title: "LocalCCWTurns: a strict left turn at every vertex"
summary: "`∀ i, 0 < latticeDet (vertex (prevIdx i)) (vertex i) (vertex (nextIdx i))` — no three consecutive listed vertices are collinear. Strict, and that strictness is a real restriction."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**The strictness is the trap.** A convex polygon listed with a redundant vertex in the middle of one side satisfies [ConvexCCW](#/node/Picks.LatticeFan.ConvexCCW) but fails this, so the Pick results do not apply to that *description* — even though they apply to the same region once the redundant vertex is dropped."
  - "It is a purely local condition: three consecutive vertices at a time. On its own it does not give convexity — a star-shaped polygon can turn left at every listed vertex. `ConvexCCW` supplies the global part."
widgets:
  - type: pick
    title: "The collinear-vertex preset: ConvexCCW holds, this fails"
    config:
      preset: collinear-vertex
      show: [counts, hypotheses, fan]
quiz:
  - q: "State the definition."
    type: choice
    choices:
      - "`∀ i : Fin P.nVertices, 0 < latticeDet (P.vertex (P.prevIdx i)) (P.vertex i) (P.vertex (P.nextIdx i))`"
      - "`∀ i j, 0 ≤ latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j)`"
      - "`∀ i, latticeDet … ≠ 0`"
      - "`∀ i, edgeGcd (P.edgePair i).1 (P.edgePair i).2 = 1`"
    answer: 0
    explain: "Strictly positive, one condition per vertex, involving that vertex and its two neighbours. The second choice is `ConvexCCW`; the fourth is `PrimitiveEdges`."
  - q: "A triangle listed `(0,0), (2,0), (4,0), (2,3)`. Does `LocalCCWTurns` hold?"
    type: choice
    choices:
      - "no — at `(2,0)` the three consecutive vertices are collinear, so the determinant is `0`, not `> 0`"
      - "yes"
      - "no, because `ConvexCCW` fails"
    answer: 0
    explain: "`latticeDet (0,0) (2,0) (4,0) = 0`. `ConvexCCW` still holds here (no vertex is strictly right of any edge). Drop `(2,0)` and both conditions hold, for the same region, with the same area, `I` and `B`. The `collinear-vertex` preset in the `pick` widget."
  - q: "Why is the condition strict rather than `0 ≤`?"
    type: choice
    choices:
      - "so that the corner-fan triangles are nondegenerate — a zero determinant would be a flat triangle with no area"
      - "to rule out non-convex polygons"
      - "for symmetry with `ConvexCCW`"
      - "no reason; `0 ≤` would do"
    answer: 0
    explain: "`FanDetsPos_of_strictlyConvexCCW` concludes `0 < fanDet i`, and the strictness has to come from somewhere. `FanDetPrimitive_of_empty_fan_triangles` then needs `fanDet ≠ 0` to apply the nondegenerate-empty-triangle lemma."
  - q: "Does `LocalCCWTurns` alone imply convexity?"
    type: choice
    choices:
      - "no — it is local; a self-overlapping star polygon can turn left at every listed vertex"
      - "yes"
      - "yes, with `3 ≤ nVertices`"
    answer: 0
    explain: "Three consecutive vertices say nothing about distant ones. `ConvexCCW`'s double quantifier is what makes the condition global, which is why `StrictlyConvexCCW` is the conjunction of both."
---

## Plain English

```lean
def LocalCCWTurns : Prop :=
  ∀ i : Fin P.nVertices,
    0 < latticeDet (P.vertex (P.prevIdx i)) (P.vertex i) (P.vertex (P.nextIdx i))
```

At every listed vertex, the path turns **strictly** left. Equivalently: no three consecutive listed
vertices are collinear.

### In one breath

Walk the outline. At every corner you wrote down, you must actually turn — and turn left. If at some
"corner" you carried straight on, it was not a corner, and this condition rejects your description
of the shape.

### Why strictness matters

Because it is the one Pick hypothesis that can fail for a perfectly ordinary convex polygon. Take
the triangle with corners `(0,0)`, `(4,0)`, `(2,3)` and write it down as

> `(0,0), (2,0), (4,0), (2,3)`

— the same region, with a redundant point listed on the base. Now
[`ConvexCCW`](#/node/Picks.LatticeFan.ConvexCCW) still holds, `B` and `I` and the area are all
unchanged, Pick's theorem is still *true* for the region — and
[`results_picks_theorem`](#/node/Results.results_picks_theorem) does not apply, because
`latticeDet (0,0) (2,0) (4,0) = 0`.

The fix is to re-list the polygon without the redundant vertex. Worth knowing before you conclude
the theorem is weaker than it is.

### What the strictness buys

`FanDetsPos_of_strictlyConvexCCW` concludes `0 < fanDet i` for every corner-fan triangle. Strictly
positive, not merely non-negative, because a flat fan triangle would have determinant zero and
`FanDetPrimitive_of_empty_fan_triangles` could not apply the `|det| = 1` lemma to it. One strict
inequality in, one strict inequality out.

### Where it sits

Half of [`StrictlyConvexCCW`](#/node/Picks.LatticeFan.StrictlyConvexCCW). Stated with
[`latticeDet`](#/node/Picks.LatticeTriangle.latticeDet) and the modular `prevIdx`/`nextIdx` of
[`LatticePolygon`](#/node/Picks.LatticePolygon).
