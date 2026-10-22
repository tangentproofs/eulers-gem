---
id: Picks.LatticePolygon.shoelace
title: "shoelace: |∑ (xᵢyᵢ₊₁ − xᵢ₊₁yᵢ)| / 2"
summary: "The classical shoelace number of the cyclic vertex list, as a `ℚ`. Its equality with the Lebesgue measure of the convex hull is a separate theorem, not part of the definition."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**It is not an area until a theorem says so.** The docstring: \"Not identified with Haar/Lebesgue measure.\" That identification is [volume_convexHullRegion_eq_ofReal_shoelace](#/node/Picks.LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace), and it needs `StrictlyConvexCCW` and injective vertices."
  - "`shoelace` is `|shoelaceSum| / 2` — the absolute value is taken, so orientation is lost. `shoelaceSum` itself is signed, and positive exactly for a counterclockwise simple polygon. Lemmas that care about orientation (the fan determinants) use the signed version."
  - "For a self-crossing list, `shoelaceSum` is the sum of signed areas of the loops and can be anything, including zero. The definition still computes; it just measures nothing."
  - "`shoelace : ℚ` is exact — halves of integers, no floating point. That is why `A = T/2` and `A = I + B/2 − 1` can be equations rather than approximations."
widgets:
  - type: pick
    title: "The shoelace number, and I + B/2 − 1, side by side"
    config:
      preset: pentagon
      show: [counts, hypotheses, fan]
quiz:
  - q: "How is `shoelace` defined from `shoelaceSum`?"
    type: choice
    choices:
      - "`(Int.natAbs P.shoelaceSum : ℚ) / 2`"
      - "`(P.shoelaceSum : ℚ) / 2`"
      - "`(P.shoelaceSum : ℚ)`"
      - "`(Int.natAbs P.shoelaceSum : ℚ)`"
    answer: 0
    explain: "`def shoelace : ℚ := (Int.natAbs P.shoelaceSum : ℚ) / 2`. Absolute value then halve, so the result is non-negative and orientation-blind."
  - q: "For the triangle `(0,0), (4,0), (1,3)`, what is `shoelaceSum`?"
    type: number
    answer: 12
    explain: "`∑ (xᵢyᵢ₊₁ − xᵢ₊₁yᵢ)` = `(0·0 − 4·0) + (4·3 − 1·0) + (1·0 − 0·3)` = `0 + 12 + 0 = 12`. So `shoelace = 6`, and indeed `I + B/2 − 1 = 3 + 4 − 1 = 6`."
  - q: "Is `shoelace` the area of `convexHullRegion` by definition?"
    type: choice
    choices:
      - "no — that is the theorem `LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace`, which needs `StrictlyConvexCCW` and injective vertices"
      - "yes, by definition"
      - "yes, for convex polygons, by definition"
    answer: 0
    explain: "The definition is a sum of products of coordinates. Its docstring explicitly declines the identification. `LatticeArea.lean` is 1430 lines, most of which is proving that identification by cutting the hull into fan triangles and measuring each."
  - q: "What is `shoelaceSum` for the vertices listed clockwise instead of counterclockwise?"
    type: choice
    choices:
      - "the negative of the counterclockwise value; `shoelace` is unchanged, since it takes `natAbs`"
      - "the same"
      - "zero"
      - "undefined"
    answer: 0
    explain: "Reversing the cycle negates every term. `shoelace` cannot tell, but `ConvexCCW` can — the `clockwise` preset in the widget has the right shoelace and fails the convexity hypothesis."
  - q: "A det-primitive triangle has `|latticeDet| = 1`. What is its shoelace?"
    type: choice
    choices: ["`1/2`", "`1`", "`2`", "it depends on the vertices"]
    answer: 0
    explain: "`Triangle.shoelace_eq_half_of_isDetPrimitive`: `triangleShoelace a b c = |latticeDet a b c| / 2 = 1/2`. Every primitive lattice triangle has area exactly a half, and that is the fact Pick's proof multiplies by `T`."
---

## Plain English

```lean
def shoelaceSum : ℤ :=
  ∑ i : Fin P.nVertices,
    let e := P.edgePair i
    e.1.1 * e.2.2 - e.2.1 * e.1.2

def shoelace : ℚ := (Int.natAbs P.shoelaceSum : ℚ) / 2
```

The **shoelace formula**: walk the vertex list in order, and for each consecutive pair
`(x, y) → (x', y')` add `x·y' − x'·y`. Halve the absolute value of the total.

You learned it in school as a way to find the area of a polygon from its corners. It *is* that —
but in this development, saying so requires a theorem, and the definition is careful not to claim
it. `shoelace` is a number computed from coordinates. That it equals the Lebesgue measure of
[`convexHullRegion`](#/node/Picks.LatticePolygon.convexHullRegion) is
[`volume_convexHullRegion_eq_ofReal_shoelace`](#/node/Picks.LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace),
proved under `StrictlyConvexCCW` and injective vertices, in a 1430-line module.

### In one breath

Lay out the corners in order, and for each step multiply the across of where you are by the up of
where you are going, then subtract the other way round. Add all those up and halve it. The answer
is the area — and the reason it is the area is that each term is twice the signed area of the
triangle from the origin to that edge, and going round the loop the outside parts cancel. Lacing a
shoe is the mnemonic for the pattern of multiplications.

### Signed versus unsigned

`shoelaceSum` is **signed**: positive for a counterclockwise simple polygon, negative for a
clockwise one. `shoelace` takes the absolute value, so it is blind to orientation.

That split is used: lemmas about the corner fan work with signed determinants
(`fanDet`, `FanDetsPos`), because the orientation is what tells you the fan triangles do not
overlap and cover the polygon exactly once. The algebraic identity at the heart of it is
`LatticeFan`'s fan identity, which says the signed fan determinants sum to the signed shoelace.

### Where it sits

- Appears as `A` in [`results_pick_count_of_euler`](#/node/Results.results_pick_count_of_euler)
  when a caller instantiates it.
- `shoelace_eq_two_cardI_add_B_sub_two_div_two` (`PickFromEuler.lean`) proves
  `P.shoelace = (2·I + B − 2)/2` for a strictly convex polygon — the geometric heart of the Pick
  proof.
- [`volume_convexHullRegion_eq_ofReal_shoelace`](#/node/Picks.LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace)
  turns it into a measure, which is what
  [`results_picks_theorem`](#/node/Results.results_picks_theorem) concludes about.
