---
id: Picks.LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace
title: "The shoelace number really is the area"
summary: "For a strictly convex lattice polygon with distinct vertices, `volume P.convexHullRegion = ENNReal.ofReal P.shoelace`. This is the theorem that makes Pick's theorem a statement about area."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "It needs `StrictlyConvexCCW` and injective vertices. Without them the shoelace sum can be anything — negative, zero, or the sum of signed loop areas of a self-crossing path — while the hull's measure is still well defined."
  - "`volume` here is `MeasureTheory.volume` on `ℝ × ℝ`, i.e. two-dimensional Lebesgue measure, and it is `ℝ≥0∞`-valued, so the right-hand side is wrapped in `ENNReal.ofReal` of a `ℚ` cast to `ℝ`."
  - "`ROADMAP.md` lists \"Shoelace = Haar/Lebesgue\" as a prerequisite for *any* Pick-named Results claim. This is that prerequisite, discharged."
widgets:
  - type: pick
    title: "The shoelace number, and the corner fan it is summed over"
    config:
      preset: pentagon
      show: [counts, fan]
quiz:
  - q: "What are the hypotheses?"
    type: choice
    choices:
      - "`StrictlyConvexCCW P` and `Function.Injective P.vertex`"
      - "`PrimitiveEdges P` and `EmptyInterior P`"
      - "none"
      - "`ConvexCCW P` alone"
    answer: 0
    explain: "`theorem volume_convexHullRegion_eq_ofReal_shoelace (P : LatticePolygon) (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex) : volume P.convexHullRegion = ENNReal.ofReal P.shoelace` (LatticeArea.lean)."
  - q: "What is the structure of the proof?"
    type: choice
    choices:
      - "split the hull into the corner-fan triangle regions, measure each by `volume_convexHull_lattice_triangle`, and sum"
      - "integrate over the boundary"
      - "approximate by rectangles"
      - "`decide`"
    answer: 0
    explain: "`rw [volume_convexHullRegion_eq_sum_volume_fanTriangleRegion P hsc hinj]` and then each term by `volume_convexHull_lattice_triangle`, giving `ENNReal.ofReal (fanTriangle P i).shoelace`. The fan decomposition needs the triangles to be essentially disjoint and to cover the hull, which is what `FanDetsNonneg_of_ConvexCCW` and the strict convexity are for."
  - q: "Why is the right-hand side `ENNReal.ofReal P.shoelace` rather than just `P.shoelace`?"
    type: choice
    choices:
      - "`volume` is valued in `ℝ≥0∞`, so the rational shoelace has to be cast into that"
      - "to allow infinite area"
      - "because the shoelace can be negative"
      - "a stylistic choice"
    answer: 0
    explain: "Mathlib measures take values in `ℝ≥0∞`. `ENNReal.ofReal` sends a real to it, clamping negatives to `0` — harmless here, since `shoelace` takes an absolute value and is non-negative."
  - q: "Why does the shoelace need to be *proved* equal to the area at all? It is the standard formula."
    type: choice
    choices:
      - "the definition is a sum of coordinate products; nothing about it mentions measure, and the Lean's definition docstring explicitly declines the identification"
      - "it does not; the definition says so"
      - "because the formula is only approximately right"
    answer: 0
    explain: "[shoelace](#/node/Picks.LatticePolygon.shoelace)'s docstring: \"Not identified with Haar/Lebesgue measure.\" A development that quietly took the standard formula as a definition of area would be claiming Pick's theorem about something other than area. This theorem is what closes the gap, and it is most of a 1430-line module."
  - q: "Which `Results` theorem would be unprovable in its current form without this?"
    type: choice
    choices:
      - "`results_picks_theorem` — its conclusion is about `MeasureTheory.volume`"
      - "`results_pick_count_of_euler`"
      - "`results_fan_pick_of_euler`"
      - "`results_euler_polyhedron`"
    answer: 0
    explain: "`results_picks_theorem`'s last steps are `rw [hvol]` where `hvol` is this theorem, then `congrArg ENNReal.ofReal`. The other Pick results named here are arithmetic and never mention a measure. `results_picks_of_empty_primitive_fan` also depends on it, through `volume_pick_of_empty_primitive_from_characteristic`."
---

## Plain English

**Theorem.** For a strictly convex counterclockwise lattice polygon with distinct vertices, the
Lebesgue measure of the convex hull of its vertices equals its shoelace number.

```lean
theorem volume_convexHullRegion_eq_ofReal_shoelace
    (P : LatticePolygon) (hsc : StrictlyConvexCCW P)
    (hinj : Function.Injective P.vertex) :
    volume P.convexHullRegion = ENNReal.ofReal P.shoelace
```

You might reasonably ask why this needs proving. The shoelace formula *is* how you compute the area
of a polygon.

But in a formalization, `shoelace` is
[defined](#/node/Picks.LatticePolygon.shoelace) as a sum of products of coordinates, and `volume` is
Mathlib's Lebesgue measure. Nothing connects them until something does. A development that skipped
this step would be proving Pick's theorem about a coordinate sum, not about area — and the
`ROADMAP.md` lists "Shoelace = Haar/Lebesgue" as a precondition for naming any Results theorem after
Pick, precisely so that nobody skipped it.

### In one breath

The school formula for the area of a polygon from its corners gives a number. Lebesgue measure,
built from scratch out of rectangles and limits, also gives a number. This says they are the same
number. Obvious, true, and somebody had to do it.

### How

By cutting the hull into the corner-fan triangles and measuring each one:

1. `volume_convexHullRegion_eq_sum_volume_fanTriangleRegion` — the hull is the essentially disjoint
   union of the fan triangle regions `(v₀, vᵢ₊₁, vᵢ₊₂)`. This is where
   [`StrictlyConvexCCW`](#/node/Picks.LatticeFan.StrictlyConvexCCW) and injectivity earn their
   place: they give `FanDetsNonneg` (consistent orientation, so the triangles do not overlap) and
   `VerticesExtreme` (no vertex hides inside another triangle).
2. `volume_convexHull_lattice_triangle` — a lattice triangle's hull has measure
   `|det|/2 = triangleShoelace`. This is the base case, and it is where the measure theory
   actually happens (an affine change of variables scaling the measure by `|det|`).
3. Sum, and match against the polygon's fan identity: the signed fan determinants add up to the
   signed shoelace sum (`LatticeFan`'s fan identity), so the shoelaces add up to `P.shoelace`.

### Where it sits

The last line of [`results_picks_theorem`](#/node/Results.results_picks_theorem)'s proof, and the
reason that theorem's conclusion is about area rather than about arithmetic. Also under
[`results_picks_of_empty_primitive_fan`](#/node/Results.results_picks_of_empty_primitive_fan).
Needs [`convexHullRegion`](#/node/Picks.LatticePolygon.convexHullRegion),
[`shoelace`](#/node/Picks.LatticePolygon.shoelace) and
[`StrictlyConvexCCW`](#/node/Picks.LatticeFan.StrictlyConvexCCW).
