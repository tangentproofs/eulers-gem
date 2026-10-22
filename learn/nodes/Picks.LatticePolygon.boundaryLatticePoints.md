---
id: Picks.LatticePolygon.boundaryLatticePoints
title: "boundaryLatticePoints: the union over the cyclic edges"
summary: "`⋃ i, edgeLatticePoints (edgePair i)` as a `Finset` — every lattice point on the path the vertex list traces out. `B` is its cardinality."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "It follows the **listed** cyclic path, not the boundary of the convex hull. Scramble the vertex order and this set changes while [convexHullRegion](#/node/Picks.LatticePolygon.convexHullRegion) does not."
  - "It is a `Finset`, built by `Finset.biUnion` over `Fin nVertices` of the constructive [edgeLatticePoints](#/node/Picks.edgeLatticePoints). So it is finite and computable with no extra hypothesis — unlike [interiorLatticePoints](#/node/Picks.LatticePolygon.interiorLatticePoints)."
widgets:
  - type: pick
    title: "The orange points are this set"
    config:
      preset: triangle
      show: [counts]
quiz:
  - q: "How is it built?"
    type: choice
    choices:
      - "`Finset.univ.biUnion fun i => edgeLatticePoints (P.edgePair i).1 (P.edgePair i).2`"
      - "the lattice points on the boundary of `P.convexHullRegion`"
      - "`P.vertexFinset`"
      - "a search over a bounding box"
    answer: 0
    explain: "`def boundaryLatticePoints : Finset (ℤ × ℤ) := (Finset.univ : Finset (Fin P.nVertices)).biUnion fun i => edgeLatticePoints (P.edgePair i).1 (P.edgePair i).2`. A `biUnion`, so shared endpoints are counted once."
  - q: "`mem_boundaryLatticePoints_iff` characterises membership how?"
    type: choice
    choices:
      - "`p ∈ P.boundaryLatticePoints ↔ ∃ i, p ∈ edgeLatticePoints (P.edgePair i).1 (P.edgePair i).2`"
      - "`p` lies in the convex hull"
      - "`p` is a listed vertex"
      - "`edgeGcd` of some edge divides `p`"
    answer: 0
    explain: "Membership in a `biUnion` is existence of an index, and the lemma is a one-line `simp`. The third choice is a strictly weaker condition — `vertices_mem_boundary` proves the implication, not the converse."
  - q: "Is every listed vertex in it?"
    type: choice
    choices:
      - "yes, `vertices_mem_boundary` — each vertex starts an edge, and `self_mem_edgeLatticePoints` puts it there"
      - "no"
      - "only the first"
    answer: 0
    explain: "`theorem vertices_mem_boundary {v : ℤ × ℤ} (hv : v ∈ P.vertices) : v ∈ P.boundaryLatticePoints`. Together with injectivity this gives `nVertices ≤ B` (`LatticeFan.nVertices_le_B`)."
  - q: "With `PrimitiveEdges` and distinct vertices, what does this set equal?"
    type: choice
    choices:
      - "exactly the vertex set, so `B = nVertices`"
      - "the vertex set plus the edge midpoints"
      - "all lattice points in the hull"
    answer: 0
    explain: "`LatticeFan.boundaryLatticePoints_eq_vertexFinset`: `edgeGcd = 1` makes each `edgeLatticePoints` the two endpoints, so the union is the vertex set. That is how [results_picks_of_empty_primitive_fan](#/node/Results.results_picks_of_empty_primitive_fan) converts `(n − 2)/2` into `B/2 − 1`."
---

## Plain English

```lean
def boundaryLatticePoints : Finset (ℤ × ℤ) :=
  (Finset.univ : Finset (Fin P.nVertices)).biUnion fun i =>
    edgeLatticePoints (P.edgePair i).1 (P.edgePair i).2
```

Walk the cyclic path through the listed vertices and collect every lattice point you step on.
That is this set, and [`B`](#/node/Picks.LatticePolygon.B) is how many there are.

Because it is a union of the constructive
[`edgeLatticePoints`](#/node/Picks.edgeLatticePoints), it is a `Finset` outright: finite, and
computable from the vertex list by gcds. That is a pointed contrast with
[`interiorLatticePoints`](#/node/Picks.LatticePolygon.interiorLatticePoints), which is a `Set` whose
finiteness this repository does not prove — and which is why
[`results_picks_theorem`](#/node/Results.results_picks_theorem) needs a `Finset S` hypothesis for
the interior and none for the boundary.

### In one breath

Trace the outline, corner to corner in the order you wrote them, and note every grid crossing your
pencil goes through. Corners count. Crossings in the middle of a side count. A crossing you pass
twice counts once.

### It follows the list, not the shape

`boundaryLatticePoints` is a union over `edgePair i` for `i : Fin nVertices` — the path *you*
described. If your list visits a convex polygon's corners out of order, the path crosses itself and
this set collects points along the crossing path. Everything downstream carries
[`StrictlyConvexCCW`](#/node/Picks.LatticeFan.StrictlyConvexCCW), which makes the path the hull's
boundary.

### Where it sits

[`B`](#/node/Picks.LatticePolygon.B) is `boundaryLatticePoints.card`.
[`interiorLatticePoints`](#/node/Picks.LatticePolygon.interiorLatticePoints) is defined as the hull's
lattice points *minus* this set. `vertices_mem_boundary` and `LatticeFan.nVertices_le_B` relate it
to the vertex list.
