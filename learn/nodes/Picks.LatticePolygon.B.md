---
id: Picks.LatticePolygon.B
title: "B: boundary lattice points, counted through gcds"
summary: "`P.B = P.boundaryLatticePoints.card`, where the boundary points are the union over the cyclic edges of `edgeLatticePoints`. Each edge contributes `gcd(Δx, Δy) + 1` points, endpoints shared."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "`B` counts points on the **cyclic edges of the listed vertex order**, not on the boundary of the convex hull. For a convex polygon listed in order these agree; for a non-convex one, or a convex one listed with the vertices out of order, they do not."
  - "It is the cardinality of a `Finset`, so it is computable and always finite — unlike [interiorLatticePoints](#/node/Picks.LatticePolygon.interiorLatticePoints), which is a `Set` whose finiteness is not proved."
  - "If the polygon has a redundant collinear vertex, `B` is unchanged (the extra vertex was already a boundary lattice point) but [StrictlyConvexCCW](#/node/Picks.LatticeFan.StrictlyConvexCCW) fails, so the theorems stop applying. The `B` is fine; the hypothesis is not."
widgets:
  - type: pick
    title: "The orange points are B. Tap to change the polygon."
    config:
      preset: triangle
      show: [counts, hypotheses]
quiz:
  - q: "How many lattice points lie on the closed segment from `(0,0)` to `(6,4)`, endpoints included?"
    type: number
    answer: 3
    explain: "`edgeGcd (0,0) (6,4) = Int.gcd 6 4 = 2`, and `card_edgeLatticePoints` gives `edgeGcd + 1 = 3`: the points `(0,0)`, `(3,2)`, `(6,4)`. The step is `(Δx/d, Δy/d) = (3,2)`."
  - q: "A lattice triangle with vertices `(0,0)`, `(4,0)`, `(1,3)`. What is `B`?"
    type: number
    answer: 8
    explain: "Edge gcds: `gcd(4,0) = 4`, `gcd(-3,3) = 3`, `gcd(-1,-3) = 1`. Each edge has `gcd + 1` points, and consecutive edges share an endpoint, so `B = 4 + 3 + 1 = 8`. (Equivalently: the three vertices, three interior points of the bottom edge, and two of the slanted one.) The `triangle` preset in the widget confirms it."
  - q: "`edgeGcd p q = 0` happens exactly when?"
    type: choice
    choices: ["`p = q`", "`p` and `q` are adjacent", "never", "the edge is horizontal"]
    answer: 0
    explain: "`lemma edgeGcd_eq_zero_iff (p q : ℤ × ℤ) : edgeGcd p q = 0 ↔ p = q`, since `Int.gcd 0 0 = 0`. `edgeLatticePoints` special-cases it and returns `{p}`."
  - q: "`PrimitiveEdges P` holds. What is the relation between `B` and `nVertices`?"
    type: choice
    choices:
      - "`B = nVertices`, provided the vertices are distinct"
      - "`B = 2 * nVertices`"
      - "`B ≥ nVertices` with no equality in general"
      - "no relation"
    answer: 0
    explain: "`PrimitiveEdges` says every `edgeGcd = 1`, so each edge has only its endpoints, and the boundary points are exactly the listed vertices. `LatticeFan.boundaryLatticePoints_eq_vertexFinset` proves it, and `LatticeFan.B_eq_nVertices_of_primitive_edges` is the count; both need injectivity. In general only `nVertices ≤ B` holds (`LatticeFan.nVertices_le_B`)."
  - q: "Does `B` count points on the boundary of `convexHullRegion`?"
    type: choice
    choices:
      - "not in general — it counts points on the cyclic edges of the *listed* vertex order"
      - "yes, always"
      - "yes, when the vertices are distinct"
    answer: 0
    explain: "`boundaryLatticePoints` is `⋃ i, edgeLatticePoints (edgePair i).1 (edgePair i).2`. For a polygon listed out of convex order the edges criss-cross the hull and the two notions diverge. The theorems that use `B` alongside `convexHullRegion` all assume `StrictlyConvexCCW`, which makes them agree."
---

## Plain English

```lean
def boundaryLatticePoints : Finset (ℤ × ℤ) :=
  (Finset.univ : Finset (Fin P.nVertices)).biUnion fun i =>
    edgeLatticePoints (P.edgePair i).1 (P.edgePair i).2

def B : ℕ := P.boundaryLatticePoints.card
```

`B` is how many grid points sit on the outline of the polygon — corners included, and including any
grid point you happen to pass through partway along an edge.

The count per edge is a gcd:

> the closed segment from `p` to `q` carries `gcd(q₁ − p₁, q₂ − p₂) + 1` lattice points.

That is [`card_edgeLatticePoints`](#/node/Picks.edgeLatticePoints), and it is the reason the
construction is exact and computable rather than a search. From `(0,0)` to `(6,4)`: `gcd(6,4) = 2`,
three points — `(0,0)`, `(3,2)`, `(6,4)`. From `(0,0)` to `(2,1)`: `gcd = 1`, two points, just the
endpoints.

Take the union over all the cyclic edges (so shared endpoints are counted once) and `B` is its
cardinality.

### In one breath

Walk the outline of your shape and count every grid crossing you step on, corners included. On a
straight run from one corner to another, how many you step on is decided by a single number: the
greatest common divisor of how far across and how far up you went. Go across six and up four and you
step on two crossings in between, because both numbers share a factor of two. Go across two and up
one and you step on none, because they share nothing.

### Two things worth being careful about

**`B` is about the listed edges, not the hull.** `boundaryLatticePoints` is a union over
`edgePair i` for `i : Fin nVertices`, so it follows whatever path your vertex list describes. If you
list a convex polygon's vertices out of order, the "boundary" is a self-crossing path and `B` counts
points on *that*. Every theorem that pairs `B` with
[`convexHullRegion`](#/node/Picks.LatticePolygon.convexHullRegion) assumes
[`StrictlyConvexCCW`](#/node/Picks.LatticeFan.StrictlyConvexCCW), which rules that out.

**`B` is always finite**, being a `Finset.card`. That is a pointed contrast with
[`interiorLatticePoints`](#/node/Picks.LatticePolygon.interiorLatticePoints), which is left as a
`Set` because its finiteness is *not* proved in this repository — and which is why
[`results_picks_theorem`](#/node/Results.results_picks_theorem) has to be handed a `Finset S`.

### Where it sits

`B` appears in the conclusion of every Pick result:
[`results_picks_theorem`](#/node/Results.results_picks_theorem) (`S.card + B/2 − 1`),
[`results_picks_of_empty_primitive_fan`](#/node/Results.results_picks_of_empty_primitive_fan)
(`B/2 − 1`), and as the `B` of
[`results_pick_count_of_euler`](#/node/Results.results_pick_count_of_euler). `nVertices_le_B`
(`PickFromEuler.lean`) is the inequality that feeds
[`triangulated_disk_euler_from_characteristic`](#/node/Picks.triangulated_disk_euler_from_characteristic)
its `n ≤ B`.
