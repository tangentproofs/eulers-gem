---
id: Picks.LatticeFan.PrimitiveEdges
title: "PrimitiveEdges: no lattice point partway along an edge"
summary: "`∀ i, edgeGcd (P.edgePair i).1 (P.edgePair i).2 = 1` — every cyclic edge has coprime steps, so it carries only its two endpoints."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "A real restriction. The square `(0,0), (3,0), (3,3), (0,3)` has `edgeGcd = 3` on every edge and fails it. Only [results_picks_of_empty_primitive_fan](#/node/Results.results_picks_of_empty_primitive_fan) needs it; the general [results_picks_theorem](#/node/Results.results_picks_theorem) does not."
  - "With injective vertices it forces `B = nVertices` (`LatticeFan.B_eq_nVertices_of_primitive_edges`, via `LatticeFan.boundaryLatticePoints_eq_vertexFinset`). Without injectivity the conclusion fails, since a repeated vertex gives a degenerate edge with `edgeGcd = 0 ≠ 1`, so in fact `PrimitiveEdges` already rules out an immediately repeated vertex."
widgets:
  - type: pick
    title: "Which presets have primitive edges?"
    config:
      preset: empty-primitive
      show: [counts, hypotheses]
quiz:
  - q: "State the definition."
    type: choice
    choices:
      - "`∀ i : Fin P.nVertices, edgeGcd (P.edgePair i).1 (P.edgePair i).2 = 1`"
      - "`∀ i, edgeGcd (P.edgePair i).1 (P.edgePair i).2 ≠ 0`"
      - "`∀ i, |latticeDet …| = 1`"
      - "`P.B = P.nVertices`"
    answer: 0
    explain: "`def PrimitiveEdges : Prop := ∀ i : Fin P.nVertices, edgeGcd (P.edgePair i).1 (P.edgePair i).2 = 1` (LatticeFan.lean). The third choice is `IsDetPrimitive` for a triangle; the fourth is a consequence, not the definition."
  - q: "Why does `edgeGcd = 1` mean no lattice point strictly between the endpoints?"
    type: choice
    choices:
      - "`card_edgeLatticePoints` gives `edgeGcd + 1 = 2` points on the closed segment, which must be the two endpoints"
      - "because `1` is odd"
      - "it does not; that is a separate hypothesis"
      - "because the edge has length 1"
    answer: 0
    explain: "`theorem card_edgeLatticePoints (p q : ℤ × ℤ) : (edgeLatticePoints p q).card = edgeGcd p q + 1`, and `edgeLatticePoints_eq_endpoints` turns `edgeGcd = 1` into `edgeLatticePoints p q = {p, q}` directly. Note the edge can be arbitrarily long — `(0,0)` to `(100, 1)` is primitive."
  - q: "The square `(0,0), (3,0), (3,3), (0,3)`. Does it satisfy `PrimitiveEdges`?"
    type: choice
    choices: ["no — each edge has `edgeGcd = 3`", "yes", "only two of its edges do"]
    answer: 0
    explain: "`gcd(3,0) = 3`. Each edge carries two interior lattice points. `B = 12`, `I = 4`, area 9 — Pick still holds, and [results_picks_theorem](#/node/Results.results_picks_theorem) still applies; only the `empty primitive fan` corollary needs primitivity."
  - q: "With injective vertices, what does `PrimitiveEdges` give you about `B`?"
    type: choice
    choices:
      - "`B = P.nVertices`: the boundary lattice points are exactly the listed vertices"
      - "`B = 2 * P.nVertices`"
      - "`B ≥ 3`"
      - "nothing"
    answer: 0
    explain: "`LatticeFan.boundaryLatticePoints_eq_vertexFinset`: each edge contributes only its endpoints, so the union of edge point sets is the vertex set. That is how `results_picks_of_empty_primitive_fan` turns `(n − 2)/2` into `B/2 − 1`."
  - q: "Is `(0,0)` to `(100,1)` a primitive edge?"
    type: choice
    choices: ["yes — `gcd(100, 1) = 1`", "no, it is too long", "only if 100 is prime"]
    answer: 0
    explain: "`gcd(100, 1) = 1`, so the segment carries exactly two lattice points. Primitivity is about coprimality of the steps, not about length."
---

## Plain English

```lean
def PrimitiveEdges : Prop :=
  ∀ i : Fin P.nVertices, edgeGcd (P.edgePair i).1 (P.edgePair i).2 = 1
```

Each edge of the polygon goes `Δx` across and `Δy` up. `PrimitiveEdges` says those two numbers are
coprime, for every edge.

Why that matters: the closed segment from `p` to `q` carries exactly `gcd(Δx, Δy) + 1` lattice
points ([`card_edgeLatticePoints`](#/node/Picks.edgeLatticePoints)). Coprime means `gcd = 1` means
two points means **just the endpoints** — nothing in the middle.

A primitive edge can be long. `(0,0)` to `(100,1)` is primitive. `(0,0)` to `(2,2)` is not: it
passes through `(1,1)`.

### In one breath

Draw a straight line from one grid crossing to another. How many crossings you pass through
depends on one number — the largest number dividing both the across and the up. If nothing divides
both, you pass through none, and the edge is as fine as a grid edge can be. This condition asks
that every edge of your shape be that fine.

### What it is for

Two things.

**It makes `B` easy.** With distinct vertices, `PrimitiveEdges` gives `B = nVertices`
(`B_eq_nVertices_of_primitive_edges`). So `(n − 2)/2`, the area of a fan of `n − 2` primitive triangles,
becomes `B/2 − 1`, which is the Pick form —
[`results_picks_of_empty_primitive_fan`](#/node/Results.results_picks_of_empty_primitive_fan) in one
step.

**It feeds the emptiness argument.** `FanTrianglesEmpty_of_empty_interior` needs it: a stray lattice
point on an edge would sit in a fan triangle without being one of its vertices, breaking the
`|det| = 1` conclusion that gives each triangle area `1/2`.

Note that it is *not* a hypothesis of the general
[`results_picks_theorem`](#/node/Results.results_picks_theorem). That theorem builds its own
triangulation (`exists_primitive_polygon_list`) and copes with non-primitive edges by subdividing
them. Primitivity is a shortcut for the small case, not a requirement of Pick's formula.

### Where it sits

A hypothesis of
[`results_picks_of_empty_primitive_fan`](#/node/Results.results_picks_of_empty_primitive_fan) and
of the `LatticeFan.lean` lemmas leading to it. Defined in terms of
[`edgeGcd`](#/node/Picks.edgeLatticePoints), which is also what
[`B`](#/node/Picks.LatticePolygon.B) is built from.
