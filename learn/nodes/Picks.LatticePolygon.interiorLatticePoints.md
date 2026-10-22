---
id: Picks.LatticePolygon.interiorLatticePoints
title: "I: interior lattice points, measured against the convex hull"
summary: "Lattice points inside `convexHullRegion` that are not on the cyclic boundary. It is a `Set`, not a `Finset` — its finiteness is not proved here, and that is the Pick lane's remaining gap."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**It is a `Set`, deliberately.** Its own docstring: \"Left as a `Set` — finiteness of lattice points in a bounded convex set is not discharged here.\" That is why [results_picks_theorem](#/node/Results.results_picks_theorem) takes a `Finset S` with `↑S = P.interiorLatticePoints` as a hypothesis: the theorem cannot produce one itself."
  - "**It is relative to the convex hull of the vertex set**, not to the region the polygon traces out. The docstring again: \"**Not** classical Pick `I` unless the polygon is convex.\" For a non-convex polygon it counts points the shape does not enclose, so no Pick-shaped formula using it is about the shape you drew."
  - "A point on the boundary of the hull but not on a listed cyclic edge *is* counted as interior. For a strictly convex polygon that cannot happen; for a scrambled vertex order it can."
widgets:
  - type: pick
    title: "Green points are I. Try the non-convex preset."
    config:
      preset: non-convex
      show: [counts, hypotheses]
quiz:
  - q: "Write out the definition."
    type: choice
    choices:
      - "`{ p | toReal p ∈ P.convexHullRegion ∧ p ∉ P.boundaryLatticePoints }`"
      - "`{ p | toReal p ∈ interior P.convexHullRegion }`"
      - "`P.latticePointsInConvexHull \\ P.vertexFinset`"
      - "a `Finset` of lattice points strictly inside the polygon"
    answer: 0
    explain: "`def interiorLatticePoints : Set (ℤ × ℤ) := { p | toReal p ∈ P.convexHullRegion ∧ p ∉ P.boundaryLatticePoints }`. Note: membership in the *closed* hull, minus the *cyclic boundary* — not the topological interior, and not the hull's boundary."
  - q: "Why is it a `Set` rather than a `Finset`?"
    type: choice
    choices:
      - "because the repository does not prove that a bounded convex region contains finitely many lattice points"
      - "because `Finset` needs decidable equality on `ℤ × ℤ`, which is missing"
      - "for performance"
      - "because the set really can be infinite"
    answer: 0
    explain: "The docstring says it: finiteness is \"not discharged here\". The set *is* finite — a bounded region contains finitely many lattice points — but that is an unproved fact in this repository, so the type cannot claim it. `DecidableEq (ℤ × ℤ)` is available and not the issue."
  - q: "A dart-shaped polygon `(0,0), (4,0), (4,4), (2,1), (0,4)`. Does `interiorLatticePoints` count `(2,3)`, which is outside the dart but inside its convex hull?"
    type: choice
    choices:
      - "yes — the definition tests membership in the convex hull, so the Lean's `I` is bigger than the classical one here"
      - "no, the definition tests membership in the polygon"
      - "no, `(2,3)` is on the boundary"
    answer: 0
    explain: "Membership is `toReal p ∈ P.convexHullRegion`, and the hull of those five vertices is the square `[0,4]²` minus nothing — it contains `(2,3)`. This is why the Pick results all assume `ConvexCCW`: with it, the hull *is* the region. Try the `non-convex` preset in the widget."
  - q: "What is `I` for the unit square `(0,0), (1,0), (1,1), (0,1)`?"
    type: number
    answer: 0
    explain: "The hull is the closed unit square; its four lattice points are all vertices, hence all in `boundaryLatticePoints`. So `I = 0`, `B = 4`, and `I + B/2 − 1 = 1`, the square's area."
  - q: "How does `results_picks_theorem` work around the finiteness gap?"
    type: choice
    choices:
      - "it takes `S : Finset (ℤ × ℤ)` with `hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints` as hypotheses, and uses `S.card`"
      - "it proves finiteness inline"
      - "it uses `Set.ncard`, which is 0 on infinite sets"
      - "it restricts to polygons with `I = 0`"
    answer: 0
    explain: "Exactly that. The consequence is that the theorem is conditional: if for some polygon no such `S` existed, the statement would be vacuous for it. Closing that gap is the clearest next task on this lane. (The `I = 0` restriction is a *different* theorem, [results_picks_of_empty_primitive_fan](#/node/Results.results_picks_of_empty_primitive_fan), which needs no such hypothesis.)"
---

## Plain English

```lean
def interiorLatticePoints : Set (ℤ × ℤ) :=
  { p | toReal p ∈ P.convexHullRegion ∧ p ∉ P.boundaryLatticePoints }
```

The grid points *inside* the polygon: in the [convex hull of its vertices](#/node/Picks.LatticePolygon.convexHullRegion),
and not among the [boundary points](#/node/Picks.LatticePolygon.B).

This is the `I` of Pick's formula `A = I + B/2 − 1`. It carries two caveats that the Lean's own
docstring spells out, and both matter.

### In one breath

Count the grid crossings strictly inside your shape. The subtlety is what "inside" means. The Lean
decides it by taking the corners of your shape, stretching a rubber band round them, and asking
whether the crossing is inside *that* — then throwing away the ones you walk over on the outline.
For a convex shape the rubber band traces exactly your outline, and the two notions agree. For a
shape with a dent, the rubber band bridges the dent and the count comes out too big.

### Caveat one: the hull, not the region

`convexHullRegion` is the hull of the **vertex set**. For a convex polygon listed in order, that is
the filled polygon, and `I` is the classical interior count. For anything else it is not.

So: `interiorLatticePoints` is the right `I` under the hypothesis
[`StrictlyConvexCCW`](#/node/Picks.LatticeFan.StrictlyConvexCCW), and that is exactly the
hypothesis every Pick result carries. Outside it, `I + B/2 − 1` is not the classical Pick count of
anything, and **the Lean does not claim it is.**

Classical Pick's theorem does hold for simple non-convex polygons. It is not proved here.

### Caveat two: finiteness

It is a `Set`, not a `Finset`, and there is no theorem here saying it is finite. Of course it is
finite — a bounded region has finitely many lattice points — but that has to be *proved* to be
usable, and in this repository it is not.

The consequence is visible in the statement of
[`results_picks_theorem`](#/node/Results.results_picks_theorem):

```lean
(S : Finset (ℤ × ℤ)) (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
```

The theorem is handed a finite enumeration rather than producing one. If some polygon had no such
`S`, the theorem would say nothing about it. This is the biggest remaining gap in the Pick lane,
and it is a small one — it is a lemma, not a research problem.

### Related definitions

- `latticePointsInConvexHull` = `{ p | toReal p ∈ P.convexHullRegion }`, the hull points including
  the boundary.
- [`EmptyInterior P`](#/node/Picks.LatticeFan.EmptyInterior) = `P.interiorLatticePoints = ∅`, the
  `I = 0` hypothesis, which needs no enumeration at all.

### Where it sits

In the conclusion of [`results_picks_theorem`](#/node/Results.results_picks_theorem) via `S.card`,
and in the hypothesis [`EmptyInterior`](#/node/Picks.LatticeFan.EmptyInterior) of
[`results_picks_of_empty_primitive_fan`](#/node/Results.results_picks_of_empty_primitive_fan).
Also throughout `LatticeFanInterior.lean`, which handles the `I = 1` case geometrically.
