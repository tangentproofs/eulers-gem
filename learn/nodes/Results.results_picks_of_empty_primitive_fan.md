---
id: Results.results_picks_of_empty_primitive_fan
title: "Pick with no interior points: area = B/2 − 1"
summary: "A strictly convex lattice polygon with distinct vertices, primitive edges and no interior lattice points has Lebesgue area `B/2 − 1`. Geometric, and with no un-met hypothesis."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "This is the `I = 0` case, and `EmptyInterior P` is a strong hypothesis — it says `P.interiorLatticePoints = ∅`, which for a lattice polygon means it is small. The reward is that no finite enumeration `S` has to be supplied, so unlike [results_picks_theorem](#/node/Results.results_picks_theorem) there is no un-discharged existence hypothesis."
  - "`PrimitiveEdges P` — every edge has `edgeGcd = 1`, i.e. no lattice point strictly between consecutive vertices — is also a real restriction. With injective vertices it forces `B = nVertices`."
  - "The two hypotheses together make the polygon small. A classical fact — **literature, not proved anywhere in this repository** — is that a convex lattice polygon with no interior lattice point has at most four vertices. If that is right, this theorem covers triangles and quadrilaterals only; the Lean statement itself places no bound on `nVertices` beyond `3 ≤`."
widgets:
  - type: pick
    title: "The empty-primitive shape, and others where the hypotheses fail"
    config:
      preset: empty-primitive
      show: [counts, hypotheses, fan]
quiz:
  - q: "What is the conclusion?"
    type: choice
    choices:
      - "`MeasureTheory.volume P.convexHullRegion = ENNReal.ofReal ((P.B : ℚ) / 2 - 1)`"
      - "`P.shoelace = (P.B : ℚ) / 2 - 1`"
      - "`P.B = 2 * P.shoelace + 2`"
      - "`MeasureTheory.volume P.convexHullRegion = ENNReal.ofReal P.shoelace`"
    answer: 0
    explain: "Lebesgue measure on the left, `ofReal (B/2 − 1)` on the right. The shoelace version is the intermediate lemma `LatticeFan.shoelace_eq_B_div_two_sub_one_of_…`; the measure version is this theorem."
  - q: "How many hypotheses, and what are they?"
    type: choice
    choices:
      - "four: injective vertices, `PrimitiveEdges`, `StrictlyConvexCCW`, `EmptyInterior`"
      - "two: `StrictlyConvexCCW` and `EmptyInterior`"
      - "five, including a `Finset S`"
      - "three: injective vertices, `StrictlyConvexCCW`, `EmptyInterior`"
    answer: 0
    explain: "`(hverts : Function.Injective P.vertex) (hedge : PrimitiveEdges P) (hsc : StrictlyConvexCCW P) (hI : EmptyInterior P)`. Notably **no** `Finset S` — with `I = 0` there is nothing to enumerate, which is why this theorem has no un-discharged existence hypothesis."
  - q: "`EmptyInterior P` says what, exactly?"
    type: choice
    choices:
      - "`P.interiorLatticePoints = ∅`"
      - "`P.B = 0`"
      - "`P.convexHullRegion` has empty interior"
      - "`P` has no vertices"
    answer: 0
    explain: "`def EmptyInterior : Prop := P.interiorLatticePoints = ∅` (LatticeFan.lean). Its docstring: \"Matches classical Pick `I = 0` when the polygon is convex (listed vertices extreme)\" — and `StrictlyConvexCCW` is what makes the listed vertices extreme, via `VerticesExtreme_of_strictlyConvexCCW`."
  - q: "`PrimitiveEdges P` says what?"
    type: choice
    choices:
      - "every cyclic edge has `edgeGcd (P.edgePair i).1 (P.edgePair i).2 = 1`"
      - "every edge has length 1"
      - "every edge is axis-parallel"
      - "the polygon has a prime number of edges"
    answer: 0
    explain: "`def PrimitiveEdges : Prop := ∀ i : Fin P.nVertices, edgeGcd (P.edgePair i).1 (P.edgePair i).2 = 1`. Since a segment from `p` to `q` carries `edgeGcd p q + 1` lattice points (`card_edgeLatticePoints`), this says each edge has only its two endpoints — no lattice point in between."
  - q: "For the parallelogram `(0,0), (1,0), (2,1), (1,1)` — all edges primitive, no interior lattice point — what area does the theorem give?"
    type: number
    answer: 1
    explain: "`B = 4` (the four vertices, since every edge is primitive) and `B/2 − 1 = 1`. The shoelace sum is `0 + 1 + 1 + 0 = 2`, so the area is `1` too. This is the `empty-primitive` preset in the widget above."
  - q: "The triangle `(0,0), (2,1), (1,2)` has primitive edges and `B = 3`, so `B/2 − 1 = 1/2`. Its actual area is `3/2`. What has gone wrong?"
    type: choice
    choices:
      - "`EmptyInterior` fails: `(1,1)` is an interior lattice point, so `I = 1` and the right formula is `1 + 3/2 − 1 = 3/2`"
      - "`StrictlyConvexCCW` fails"
      - "the edges are not really primitive"
      - "the theorem is wrong"
    answer: 0
    explain: "`latticeDet (0,0) (2,1) (1,2) = 3`, so the area is `3/2`, and `(1,1)` sits strictly inside. `EmptyInterior P` is `P.interiorLatticePoints = ∅`, which fails, so this theorem does not apply — [results_picks_theorem](#/node/Results.results_picks_theorem) does, with `I = 1`. A good habit: when a Pick-shaped formula gives the wrong number, find the hypothesis that failed."
---

## Plain English

```lean
theorem results_picks_of_empty_primitive_fan
    (P : EulersGem.Picks.LatticePolygon)
    (hverts : Function.Injective P.vertex)
    (hedge : EulersGem.Picks.LatticeFan.PrimitiveEdges P)
    (hsc : EulersGem.Picks.LatticeFan.StrictlyConvexCCW P)
    (hI : EulersGem.Picks.LatticeFan.EmptyInterior P) :
    MeasureTheory.volume P.convexHullRegion = ENNReal.ofReal ((P.B : ℚ) / 2 - 1)
```

Pick's formula with `I = 0`. A strictly convex lattice polygon whose vertices are distinct, whose
edges carry no lattice points other than their endpoints, and which contains no lattice point in
its interior, has area `B/2 − 1`.

Its real interest is procedural: **it has no un-discharged hypothesis.** With `I = 0` there is
nothing to enumerate, so the `Finset S` that
[`results_picks_theorem`](#/node/Results.results_picks_theorem) must be handed is not needed here.
This statement stands on its own.

### In one breath

Draw a small convex shape on graph paper with corners on crossings, small enough that no crossing
lands inside it and none lands partway along an edge. Then its area is half the number of corners,
minus one. A single primitive triangle: three corners, half of three is one and a half, minus one
is a half — and a triangle of area a half is the smallest one you can draw on the grid. That is
Pick's formula at its smallest, and the smallest case is the one the general proof is built up from.

## What this does and does not prove

**It does prove:**

- The `I = 0` case of Pick's formula, as a statement about **Lebesgue measure**.
- Geometrically, with no free Euler hypothesis: the proof goes through
  `LatticeFan.volume_pick_of_empty_primitive_from_characteristic`, whose Euler input comes from the
  disk-Euler route and ultimately from a geometric triangle's Euler–Poincaré characteristic.
- With every hypothesis checkable from the vertex list by exact integer arithmetic — the widget
  above does exactly that.

**It does not prove:**

- Anything when there **is** an interior lattice point. That is
  [`results_picks_theorem`](#/node/Results.results_picks_theorem), with its extra hypothesis.
- Anything when an edge is **not primitive** (a lattice point sits partway along it), or when the
  polygon is **not strictly convex** in the listed order.
- Anything about non-convex polygons, for the same reason as the general theorem:
  [`convexHullRegion`](#/node/Picks.LatticePolygon.convexHullRegion) is the hull of the vertex set.

### How the hypotheses interact

`PrimitiveEdges` plus injective vertices gives `B = nVertices`
(`LatticeFan.B_eq_nVertices_of_primitive_edges`): the boundary lattice points are exactly the listed
vertices. `StrictlyConvexCCW` gives `VerticesExtreme` (every listed vertex is extreme in the hull)
and `FanDetsPos` (the corner fan is positively oriented) — both *discharged* in `LatticeFan.lean`
rather than assumed. `EmptyInterior` plus those gives `FanTrianglesEmpty` (no fan triangle contains
a stray lattice point), which gives `FanDetPrimitive` (each fan determinant is `±1`) by
`LatticeTriangleEmpty`'s nondegenerate-empty-triangle lemma. Each fan triangle then has shoelace
exactly `1/2`, there are `n − 2` of them, and `(n − 2)/2 = B/2 − 1`.

That chain is why the hypothesis list is four items long rather than one: each item discharges one
link.

### Where it sits

A sibling of [`results_picks_theorem`](#/node/Results.results_picks_theorem) on the Pick lane. Uses
[`PrimitiveEdges`](#/node/Picks.LatticeFan.PrimitiveEdges),
[`EmptyInterior`](#/node/Picks.LatticeFan.EmptyInterior),
[`StrictlyConvexCCW`](#/node/Picks.LatticeFan.StrictlyConvexCCW),
[`LatticePolygon`](#/node/Picks.LatticePolygon) and
[`B`](#/node/Picks.LatticePolygon.B).
