---
id: Picks.toReal
title: "toReal: moving a lattice point into the real plane"
summary: "`toReal (p : ℤ × ℤ) : ℝ × ℝ = (↑p.1, ↑p.2)` — the coordinate-wise cast. It is injective, and it is the one place the lattice meets the geometry."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "`Picks.toReal` is an `abbrev` for `LatticeTriangle.toReal`, so that polygon hulls and triangle barycentric membership share one embedding. The docstring says exactly that, and it matters: two different embeddings would make the hull lemmas and the triangle lemmas incompatible."
  - "The target is `ℝ × ℝ` with the product topology and the product (two-dimensional Lebesgue) measure — not `EuclideanSpace ℝ (Fin 2)`. For measure purposes they agree; for inner-product purposes they are different types."
widgets:
  - type: pick
    title: "Integer side: B and the determinants. Real side: the hull."
    config:
      preset: triangle
      show: [counts, hypotheses]
quiz:
  - q: "What is `toReal p`?"
    type: choice
    choices: ["`((p.1 : ℝ), (p.2 : ℝ))`", "`‖p‖`", "`(p.1 / p.2 : ℝ)`", "a lattice point nearest to `p`"]
    answer: 0
    explain: "`def toReal (p : ℤ × ℤ) : ℝ × ℝ := (↑p.1, ↑p.2)` (LatticeTriangle.lean), re-exported as `Picks.toReal`. Just the two casts."
  - q: "Is it injective, and where is that used?"
    type: choice
    choices:
      - "yes, `toReal_injective`, from injectivity of `Int.cast` in each coordinate — needed whenever a geometric conclusion is pulled back to lattice points"
      - "no"
      - "yes, but it is never used"
    answer: 0
    explain: "`lemma toReal_injective : Function.Injective toReal`, by `Prod.ext` and `Int.cast_injective` twice. Without it, distinct lattice points could collapse and every count would be suspect."
  - q: "Which two definitions use it to cross from `ℤ × ℤ` to geometry?"
    type: choice
    choices:
      - "[convexHullRegion](#/node/Picks.LatticePolygon.convexHullRegion) (`toReal '' vertexFinset`) and [interiorLatticePoints](#/node/Picks.LatticePolygon.interiorLatticePoints) (`toReal p ∈ convexHullRegion`)"
      - "`B` and `shoelaceSum`"
      - "`edgeGcd` and `latticeDet`"
      - "none; the development stays in `ℤ × ℤ`"
    answer: 0
    explain: "Those two. `B`, `shoelaceSum`, `edgeGcd` and `latticeDet` are all pure integer arithmetic and never leave `ℤ × ℤ` — which is why they are computable and the hull-based ones are not."
  - q: "`MemClosedTriangle a b c p` is defined using `toReal`. Why not stay in `ℤ × ℤ`?"
    type: choice
    choices:
      - "the barycentric coefficients `α, β, γ` are *real* and generally not integers, so the condition has to be checked in `ℝ × ℝ`"
      - "for efficiency"
      - "because `ℤ × ℤ` has no addition"
    answer: 0
    explain: "`def MemClosedTriangle (a b c p : ℤ × ℤ) : Prop := ∃ α β γ : ℝ, 0 ≤ α ∧ … ∧ α + β + γ = 1 ∧ α • toReal a + β • toReal b + γ • toReal c = toReal p`. A lattice point inside a triangle has rational, not integral, barycentric coordinates."
---

## Plain English

```lean
def toReal (p : ℤ × ℤ) : ℝ × ℝ := (↑p.1, ↑p.2)
```

A lattice point is a pair of integers. The plane is a pair of reals. `toReal` is the cast, and it is
the boundary between the two halves of the Pick lane.

**On the `ℤ × ℤ` side** everything is exact integer arithmetic and computable:
[`edgeGcd`](#/node/Picks.LatticeTriangle.edgeGcd),
[`latticeDet`](#/node/Picks.LatticeTriangle.latticeDet), `shoelaceSum`,
[`B`](#/node/Picks.LatticePolygon.B), and every convexity predicate.

**On the `ℝ × ℝ` side** live the geometric notions: the
[convex hull](#/node/Picks.LatticePolygon.convexHullRegion), barycentric membership in a triangle,
and Lebesgue measure.

`toReal` is how a statement crosses over, in both directions —
[`interiorLatticePoints`](#/node/Picks.LatticePolygon.interiorLatticePoints) is a set of *lattice*
points defined by a condition on their *real* images.

### In one breath

A grid crossing is a pair of whole numbers; a point of the plane is a pair of ordinary numbers. This
turns the first into the second, which is all it does, and it is the hinge the whole Pick argument
turns on: counting happens in whole numbers, area happens in ordinary ones.

### One design note

`Picks.toReal` is an `abbrev` for `LatticeTriangle.toReal` precisely so there is only one embedding
in the development. The docstring: "Alias of `LatticeTriangle.toReal` so polygon hull and triangle
barycentric membership share one embedding." If the polygon file had defined its own, every lemma
relating a polygon's hull to its fan triangles would have needed a translation step.

### Where it sits

In [`convexHullRegion`](#/node/Picks.LatticePolygon.convexHullRegion),
[`interiorLatticePoints`](#/node/Picks.LatticePolygon.interiorLatticePoints),
`latticePointsInConvexHull`, `MemClosedTriangle`, and throughout `LatticeArea.lean`.
