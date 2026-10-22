---
id: Picks.LatticePolygon
title: "LatticePolygon: a cyclic list of at least three grid points"
summary: "A structure with one field, `vertices : List (ℤ × ℤ)`, and one condition, `3 ≤ vertices.length`. It does not assert simplicity, convexity, or even that the vertices are distinct."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**It asserts almost nothing.** A list of three or more lattice points. Self-crossing polygons, repeated vertices, three collinear points — all are `LatticePolygon`s. Every real condition arrives as a separate hypothesis: `Function.Injective P.vertex` for distinctness, [StrictlyConvexCCW](#/node/Picks.LatticeFan.StrictlyConvexCCW) for convexity and orientation, [PrimitiveEdges](#/node/Picks.LatticeFan.PrimitiveEdges), [EmptyInterior](#/node/Picks.LatticeFan.EmptyInterior)."
  - "The structure's own docstring says so: \"Does **not** assert simplicity (no self-intersections) or convexity; those are left to witnesses / future predicates with honest names.\" That is a deliberate design choice and the reason the hypothesis lists downstream are long."
  - "The vertices are `ℤ × ℤ`, embedded into `ℝ × ℝ` by `Picks.toReal` when geometry is needed. So `ℝ × ℝ` with the product topology and Lebesgue measure, not `EuclideanSpace ℝ (Fin 2)`."
widgets:
  - type: pick
    title: "Build one by tapping, and watch which predicates hold"
    config:
      preset: pentagon
      show: [counts, hypotheses, fan]
quiz:
  - q: "What does `LatticePolygon` assert?"
    type: choice
    choices:
      - "a list of lattice points with `3 ≤ vertices.length`, and nothing else"
      - "a simple closed convex polygon with lattice vertices"
      - "a convex polygon, counterclockwise"
      - "a list of lattice points with no three collinear"
    answer: 0
    explain: "`structure LatticePolygon where vertices : List (ℤ × ℤ); length_ge : 3 ≤ vertices.length` (LatticePolygon.lean). Two fields, one of them a bound."
  - q: "Is a self-crossing \"bowtie\" list of four lattice points a `LatticePolygon`?"
    type: choice
    choices: ["yes", "no", "only if the crossing point is a lattice point"]
    answer: 0
    explain: "Yes — nothing rules it out. The predicates that do rule it out are stated separately, which is why [results_picks_theorem](#/node/Results.results_picks_theorem) carries `hverts` and `hsc` as hypotheses rather than getting them from the structure."
  - q: "`P.nextIdx i` and `P.prevIdx i` compute what?"
    type: choice
    choices:
      - "`(i + 1) % nVertices` and `(i + nVertices − 1) % nVertices`, so the list wraps around"
      - "`i + 1` and `i − 1`, erroring at the ends"
      - "the neighbours in the convex hull"
      - "the next and previous lattice points on the boundary"
    answer: 0
    explain: "Both are modular, with `nextIdx_prevIdx` and `prevIdx_nextIdx` proving they are inverse. The modular wrap is what makes the list *cyclic* and gives the closing edge from the last vertex back to the first."
  - q: "`P.edgePair i` is which pair?"
    type: choice
    choices:
      - "`(P.vertex i, P.vertex (P.nextIdx i))`"
      - "`(P.vertex i, P.vertex (P.prevIdx i))`"
      - "a pair of adjacent lattice points on the boundary"
      - "the two endpoints of the `i`-th hull edge"
    answer: 0
    explain: "`def edgePair (i : Fin P.nVertices) : (ℤ × ℤ) × (ℤ × ℤ) := (P.vertex i, P.vertex (P.nextIdx i))`. There are exactly `nVertices` of them, including the closing one from the last listed vertex to the first."
---

## Plain English

```lean
structure LatticePolygon where
  /-- Vertices in cyclic boundary order. -/
  vertices : List (ℤ × ℤ)
  /-- At least a triangle. -/
  length_ge : 3 ≤ vertices.length
```

A list of three or more points with integer coordinates, understood cyclically: after the last one
you come back to the first.

**That is the whole structure.** It is not asserted to be convex, or non-self-intersecting, or to
have distinct vertices. This is a deliberate choice, and the module docstring is explicit about it:
honest names, honest hypotheses. Every real condition — convexity, orientation, distinctness,
primitivity, emptiness of the interior — is a separate predicate you supply when you need it.

From the raw list, the module derives:

| | |
|---|---|
| `nVertices` | `vertices.length` |
| `vertex i` | the `i`-th entry, `i : Fin nVertices` |
| `nextIdx` / `prevIdx` | modular successor and predecessor, with `nextIdx_prevIdx` proving them inverse |
| `edgePair i` | `(vertex i, vertex (nextIdx i))` — the `i`-th directed edge, wrapping around |
| `boundaryLatticePoints` | the union of `edgeLatticePoints` over the cyclic edges |
| [`B`](#/node/Picks.LatticePolygon.B) | the cardinality of that |
| `vertexFinset` | `vertices.toFinset` |
| [`convexHullRegion`](#/node/Picks.LatticePolygon.convexHullRegion) | `convexHull ℝ (toReal '' vertexFinset)` |
| [`interiorLatticePoints`](#/node/Picks.LatticePolygon.interiorLatticePoints) | hull points not on the boundary |
| `shoelaceSum` / [`shoelace`](#/node/Picks.LatticePolygon.shoelace) | the oriented sum, and half its absolute value |

### In one breath

Mark three or more crossings on graph paper and write them down in the order you want to join them
up. That list is the object. Nothing stops you listing them in an order that makes the outline
cross itself, or writing the same crossing twice, and the definition does not pretend otherwise —
the conditions you actually want come later, one at a time, so that you can see which theorem needs
which.

### Why so bare?

Because the alternative is dishonest. The classical statement of Pick's theorem is about a *simple*
polygon, and "simple" (no self-intersections) is a genuinely awkward thing to define and work with.
Rather than bake in a condition and then prove theorems that quietly depend on more than they say,
this development keeps the structure trivial and makes every condition visible:

- `Function.Injective P.vertex` — distinct vertices;
- [`ConvexCCW`](#/node/Picks.LatticeFan.StrictlyConvexCCW) — every vertex weakly left of every
  directed edge;
- `LocalCCWTurns` — a strict left turn at every vertex;
- [`PrimitiveEdges`](#/node/Picks.LatticeFan.PrimitiveEdges) — no lattice point partway along an
  edge;
- [`EmptyInterior`](#/node/Picks.LatticeFan.EmptyInterior) — no interior lattice point.

The cost is long hypothesis lists. The benefit is that you can read
[`results_picks_theorem`](#/node/Results.results_picks_theorem) and know exactly what it covers.
The widget above will tell you which predicates hold for any polygon you draw.

### Where it sits

The base of the Pick lane. Used by every `Results` theorem on that lane, and by all of
`LatticeFan.lean`, `PickFromEuler.lean` and `LatticeArea.lean`.
