---
id: Picks.LatticePolygon.convexHullRegion
title: "convexHullRegion: the hull of the vertices, in ℝ × ℝ"
summary: "`convexHull ℝ (toReal '' vertexFinset)` — the convex hull of the listed vertices, embedded in the real plane. It is the set whose Lebesgue measure Pick's theorem computes."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**It is the hull of the vertices, not the region the polygon traces.** The docstring: \"For a **convex** lattice polygon this is the filled region; for non-convex simple polygons it is typically larger than the polygonal region.\" Every Pick result in `Results.lean` assumes [StrictlyConvexCCW](#/node/Picks.LatticeFan.StrictlyConvexCCW), which makes the two coincide."
  - "`vertexFinset` is `vertices.toFinset`, so duplicates in the list collapse and the *order* is lost. The hull does not care about the cyclic order at all — which is exactly why `B`, which does, has to be defined separately."
  - "The ambient space is `ℝ × ℝ` with its product measure, not `EuclideanSpace ℝ (Fin 2)`. `MeasureTheory.volume` on `ℝ × ℝ` is two-dimensional Lebesgue measure, which is what you want."
widgets:
  - type: pick
    title: "The hull is where I is measured. Try the non-convex preset."
    config:
      preset: non-convex
      show: [counts, hypotheses]
quiz:
  - q: "What is `convexHullRegion`?"
    type: choice
    choices:
      - "`convexHull ℝ (toReal '' (P.vertexFinset : Set (ℤ × ℤ)))`"
      - "the set of points enclosed by the cyclic edge path"
      - "`convexHull ℝ P.boundaryLatticePoints`"
      - "the interior of the polygon"
    answer: 0
    explain: "`def convexHullRegion : Set (ℝ × ℝ) := convexHull ℝ (toReal '' (P.vertexFinset : Set (ℤ × ℤ)))` (LatticePolygon.lean). The hull of the *vertex set*, with no reference to the cyclic order."
  - q: "For a non-convex polygon, how do `convexHullRegion` and the traced-out region compare?"
    type: choice
    choices:
      - "the hull is larger — it fills in the dents"
      - "they are equal"
      - "the hull is smaller"
      - "they are incomparable"
    answer: 0
    explain: "A hull is convex, so it contains the segment between any two points of the region; a dent is precisely where the region fails that. The docstring says \"typically larger\". Everything downstream carries `StrictlyConvexCCW` to rule this out."
  - q: "Does `convexHullRegion` depend on the cyclic order of the vertex list?"
    type: choice
    choices:
      - "no — it is built from `vertexFinset`, which forgets the order"
      - "yes, the order determines the edges"
      - "only up to reflection"
    answer: 0
    explain: "`vertexFinset = vertices.toFinset`. Shuffle the list and the hull is unchanged, while `B`, `shoelaceSum` and every convexity predicate *do* change. That is why a convex polygon listed in the wrong order has the right hull and fails `ConvexCCW`."
  - q: "`MeasureTheory.volume P.convexHullRegion` on `ℝ × ℝ` is what kind of quantity?"
    type: choice
    choices:
      - "two-dimensional Lebesgue measure — the area, as an `ℝ≥0∞`"
      - "the number of lattice points in the hull"
      - "the shoelace sum"
      - "one-dimensional measure of the boundary"
    answer: 0
    explain: "`volume` on a product of `ℝ`s is the product Lebesgue measure, valued in `ℝ≥0∞` — which is why the right-hand side of [results_picks_theorem](#/node/Results.results_picks_theorem) is wrapped in `ENNReal.ofReal`. The bridge to the shoelace number is [volume_convexHullRegion_eq_ofReal_shoelace](#/node/Picks.LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace)."
---

## Plain English

```lean
def convexHullRegion : Set (ℝ × ℝ) :=
  convexHull ℝ (toReal '' (P.vertexFinset : Set (ℤ × ℤ)))
```

Take the listed vertices, forget the order, move them from `ℤ × ℤ` into `ℝ × ℝ` (that is what
`toReal` does), and stretch a rubber band round them. The filled shape you get is
`convexHullRegion`.

This is the set whose **area** Pick's theorem computes — area meaning genuine Lebesgue measure, by
way of [`volume_convexHullRegion_eq_ofReal_shoelace`](#/node/Picks.LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace).

### In one breath

Mark the corners on graph paper, loop a rubber band round them all, and shade in what it encloses.
That shaded patch is what gets measured. Note what you did *not* do: you did not follow the outline
you intended. If your intended outline had a dent, the rubber band bridged it, and the patch is
bigger than your shape.

### The one thing to keep straight

| | depends on | for a strictly convex polygon |
|---|---|---|
| `convexHullRegion` | the vertex **set** | the filled polygon |
| [`B`](#/node/Picks.LatticePolygon.B) | the cyclic **order** | boundary lattice points of the hull |
| [`shoelaceSum`](#/node/Picks.LatticePolygon.shoelace) | the cyclic **order** | ± twice the hull's area |
| [`interiorLatticePoints`](#/node/Picks.LatticePolygon.interiorLatticePoints) | both | the classical `I` |

Three of those four know about the order and one does not, and `interiorLatticePoints` mixes them.
Under [`StrictlyConvexCCW`](#/node/Picks.LatticeFan.StrictlyConvexCCW) they all line up, which is
why that hypothesis is in every Pick result. Without it, they describe different shapes and the
formula relates nothing to nothing. The widget above makes this concrete: pick the `non-convex`
preset and watch the green interior points appear in places the outline excludes.

### Where it sits

The left-hand side of [`results_picks_theorem`](#/node/Results.results_picks_theorem) and
[`results_picks_of_empty_primitive_fan`](#/node/Results.results_picks_of_empty_primitive_fan) is
`MeasureTheory.volume P.convexHullRegion`. All of `LatticeArea.lean` is about computing it:
`volume_convexHullRegion_eq_sum_volume_fanTriangleRegion` breaks it into fan triangles, and
`volume_convexHull_lattice_triangle` measures each one.
