---
id: Picks.LatticePolygon.shoelaceSum
title: "shoelaceSum: the signed cyclic sum"
summary: "`∑ i, (xᵢ·yᵢ₊₁ − xᵢ₊₁·yᵢ)` over the cyclic edges, as an `ℤ`. Signed: positive for a counterclockwise simple polygon, negative for a clockwise one."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**It is signed, and the sign is information.** [shoelace](#/node/Picks.LatticePolygon.shoelace) throws it away with `Int.natAbs`. Lemmas about the corner fan work with the signed version, because the orientation is what tells you the fan triangles tile the polygon rather than cancelling."
  - "For a self-crossing vertex list it is the sum of signed loop areas, and can be zero for a non-degenerate path. The definition still computes; it just measures nothing."
  - "It is an `ℤ`, so it is exact. `shoelace` divides by 2 in `ℚ`, which is why areas come out as exact halves."
widgets:
  - type: pick
    title: "The shoelace sum, and the fan it splits into"
    config:
      preset: pentagon
      show: [counts, fan]
quiz:
  - q: "State the summand."
    type: choice
    choices:
      - "`e.1.1 * e.2.2 - e.2.1 * e.1.2` for `e = P.edgePair i`"
      - "`e.1.1 * e.2.1 + e.1.2 * e.2.2`"
      - "`|e.1.1 * e.2.2 - e.2.1 * e.1.2|`"
      - "`latticeDet (0,0) e.1 e.2`"
    answer: 0
    explain: "`def shoelaceSum : ℤ := ∑ i : Fin P.nVertices, let e := P.edgePair i; e.1.1 * e.2.2 - e.2.1 * e.1.2`. (The fourth choice is in fact numerically equal to the summand, since `latticeDet (0,0) p q = p.1*q.2 − p.2*q.1`, but it is not what the Lean writes.)"
  - q: "For the triangle `(0,0), (4,0), (1,3)`, compute it."
    type: number
    answer: 12
    explain: "`(0·0 − 4·0) + (4·3 − 1·0) + (1·0 − 0·3) = 0 + 12 + 0 = 12`. So the area is `6`, and `I + B/2 − 1 = 3 + 4 − 1 = 6`."
  - q: "Reverse the vertex list. What happens?"
    type: choice
    choices:
      - "the sum negates; `shoelace` is unchanged because it takes `natAbs`"
      - "nothing changes"
      - "it becomes zero"
      - "it doubles"
    answer: 0
    explain: "Each term `x·y' − x'·y` becomes its negative when the edge is traversed backwards. This is why `ConvexCCW` can detect a clockwise listing while `shoelace` cannot."
  - q: "Why does the Lean keep a signed version at all, if the area is the absolute value?"
    type: choice
    choices:
      - "because the corner-fan identity relates the signed fan determinants to the signed sum, and the signs are what prove the triangles do not overlap"
      - "for efficiency"
      - "it does not; `shoelaceSum` is unused"
      - "to allow negative areas"
    answer: 0
    explain: "`LatticeFan.lean`'s fan identity sums `fanDet i` over the fan and matches `shoelaceSum`. With all the determinants positive (`FanDetsPos`, discharged from `StrictlyConvexCCW`), the sum is a sum of *areas* rather than a cancelling combination — which is what `volume_convexHullRegion_eq_sum_volume_fanTriangleRegion` needs."
---

## Plain English

```lean
def shoelaceSum : ℤ :=
  ∑ i : Fin P.nVertices,
    let e := P.edgePair i
    e.1.1 * e.2.2 - e.2.1 * e.1.2
```

For each directed edge `(x, y) → (x', y')`, add `x·y' − x'·y`. Sum over the cycle.

Each term is twice the signed area of the triangle from the origin to that edge. Going round the
loop, the contributions outside the polygon cancel and what is left is twice the polygon's signed
area. Hence the name: lacing a shoe is the mnemonic for the crossing pattern of multiplications.

**The sign is kept here on purpose.** [`shoelace`](#/node/Picks.LatticePolygon.shoelace) is
`|shoelaceSum| / 2` and is orientation-blind; this one is not.

### In one breath

For each side of your shape, multiply the across of where you start by the up of where you finish,
then subtract the other way round, then add up all the sides. The answer is twice the area, with a
plus sign if you went anticlockwise and a minus sign if you went the other way.

### Why the sign is kept

`LatticeFan.lean` proves an algebraic identity: the signed determinants of the corner-fan triangles
`(v₀, vᵢ₊₁, vᵢ₊₂)` add up to `shoelaceSum`. Taken with signs, that identity is pure algebra and holds
for *any* vertex list. Taken as an identity between *areas*, it needs every determinant to have the
same sign — which is `FanDetsPos`, discharged from
[`StrictlyConvexCCW`](#/node/Picks.LatticeFan.StrictlyConvexCCW) plus injectivity. Then the fan
triangles genuinely tile the polygon, and
[`volume_convexHullRegion_eq_ofReal_shoelace`](#/node/Picks.LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace)
can add up their measures.

So: the signed sum is where the algebra lives; the unsigned one is where the geometry lands.

### Where it sits

[`shoelace`](#/node/Picks.LatticePolygon.shoelace) is `(Int.natAbs shoelaceSum : ℚ) / 2`. Both are
in `LatticePolygon.lean`, with the fan identity in `LatticeFan.lean`.
