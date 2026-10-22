---
id: Picks.edgeLatticePoints
title: "edgeLatticePoints: a gcd decides how many points a segment carries"
summary: "The lattice points of the closed segment from `p` to `q`, built constructively from `edgeGcd p q`. There are `edgeGcd + 1` of them, endpoints included — `{p}` when `p = q`."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "It is a `Finset`, built by `Finset.range (d + 1) |>.image …` rather than by a search. So `B` is computable, and the proofs about it are arithmetic rather than geometric."
  - "The `p = q` case is special-cased to `{p}`, since `edgeGcd p q = 0` there and `range 1` with a zero step would give the same thing — but the `if` keeps the division by `d` from happening."
  - "The division `(q.1 - p.1) / (d : ℤ)` is integer division, and it is exact because `d` divides both differences (`Int.gcd_dvd_left`/`_right`). `card_edgeLatticePoints` has to prove the resulting map is injective, which is where the non-degeneracy of the step vector is used."
widgets:
  - type: pick
    title: "B is this count, summed over the cyclic edges"
    config:
      preset: triangle
      show: [counts]
quiz:
  - q: "How many lattice points are on the closed segment from `p` to `q`?"
    type: choice
    choices:
      - "`edgeGcd p q + 1`"
      - "`edgeGcd p q`"
      - "`max |Δx| |Δy| + 1`"
      - "`|Δx| + |Δy| + 1`"
    answer: 0
    explain: "`theorem card_edgeLatticePoints (p q : ℤ × ℤ) : (edgeLatticePoints p q).card = edgeGcd p q + 1`. The third and fourth choices are the Chebyshev and taxicab counts, which are not it: `(0,0)` to `(4,6)` has `gcd = 2`, so 3 points, while `max = 6` and the sum is `10`."
  - q: "`edgeGcd p q` is defined as what?"
    type: choice
    choices:
      - "`Int.gcd (q.1 - p.1) (q.2 - p.2)`"
      - "`Int.gcd p.1 q.1`"
      - "`Nat.gcd |Δx| |Δy| + 1`"
      - "the Euclidean distance"
    answer: 0
    explain: "`def edgeGcd (p q : ℤ × ℤ) : ℕ := Int.gcd (q.1 - p.1) (q.2 - p.2)` (LatticeTriangle.lean). `Int.gcd` returns an `ℕ` and is non-negative; it is `0` exactly when both differences are, i.e. `p = q` (`edgeGcd_eq_zero_iff`)."
  - q: "From `(0,0)` to `(4,6)`: how many lattice points, and which?"
    type: choice
    choices:
      - "3: `(0,0)`, `(2,3)`, `(4,6)`"
      - "2: just the endpoints"
      - "5: steps of `(1, 1.5)`"
      - "11"
    answer: 0
    explain: "`gcd(4,6) = 2`, so `2 + 1 = 3` points with step `(4/2, 6/2) = (2,3)`. The construction is `fun k => (p.1 + k * (Δx/d), p.2 + k * (Δy/d))` for `k ∈ range (d+1)`."
  - q: "Which two membership lemmas does the module prove about it?"
    type: choice
    choices:
      - "`self_mem_edgeLatticePoints` (`p` is in it, at `k = 0`) and `other_mem_edgeLatticePoints` (`q` is in it, at `k = edgeGcd`)"
      - "that it is convex"
      - "that it is nonempty and finite"
      - "that it contains no other lattice points"
    answer: 0
    explain: "Both endpoints, separately. The second needs the exactness of the integer divisions: `d * (Δx / d) = Δx` by `Int.ediv_mul_cancel` given `d ∣ Δx`."
  - q: "What makes the edge primitive?"
    type: choice
    choices:
      - "`edgeGcd p q = 1`, so the segment carries exactly its two endpoints"
      - "`edgeGcd p q = 0`"
      - "the edge having length 1"
      - "the edge being axis-parallel"
    answer: 0
    explain: "[PrimitiveEdges](#/node/Picks.LatticeFan.PrimitiveEdges) asks for `edgeGcd = 1` on every cyclic edge, and `edgeLatticePoints_eq_endpoints` turns that into `edgeLatticePoints p q = {p, q}`."
---

## Plain English

```lean
def edgeLatticePoints (p q : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  let d := edgeGcd p q
  if d = 0 then {p}
  else (Finset.range (d + 1)).image fun k : ℕ =>
    (p.1 + (k : ℤ) * ((q.1 - p.1) / (d : ℤ)),
     p.2 + (k : ℤ) * ((q.2 - p.2) / (d : ℤ)))
```

How many grid points does a straight segment between two grid points pass through?

Divide the step `(Δx, Δy)` by `d = gcd(Δx, Δy)`. The result `(Δx/d, Δy/d)` is a *primitive* step —
its two components share no factor — and walking it `d` times takes you from `p` to `q`, landing on
a grid point each time. So there are `d + 1` points in all, endpoints included.

```
(0,0) → (4,6):  gcd = 2,  step (2,3),  points (0,0) (2,3) (4,6)       — 3 points
(0,0) → (2,1):  gcd = 1,  step (2,1),  points (0,0) (2,1)             — 2 points
(0,0) → (0,5):  gcd = 5,  step (0,1),  six points up the y-axis
```

That is `card_edgeLatticePoints`, and it is what makes [`B`](#/node/Picks.LatticePolygon.B)
computable from the vertex list by pure arithmetic.

### In one breath

Walk in a straight line from one grid crossing to another. How many crossings you step on depends on
one number: the largest number dividing both how far you went across and how far up. Divide by it,
and you get the smallest step in that direction that still lands on crossings — then you take that
step exactly that many times. Across six, up four: two divides both, so your step is across three up
two, you take it twice, and you touch three crossings in all.

### Why constructive

The alternative would be to define the boundary points as a *set* and prove finiteness. The
development does that for the interior
([`interiorLatticePoints`](#/node/Picks.LatticePolygon.interiorLatticePoints)) and pays for it: the
finiteness is not proved, so [`results_picks_theorem`](#/node/Results.results_picks_theorem) needs a
`Finset S` hypothesis. For the boundary, the gcd construction gives a `Finset` outright, and `B` is
a `Finset.card` with no strings attached. The contrast is instructive.

### Where it sits

- [`boundaryLatticePoints`](#/node/Picks.LatticePolygon.B) is the union of these over the cyclic
  edges, and `B` is its cardinality.
- [`PrimitiveEdges`](#/node/Picks.LatticeFan.PrimitiveEdges) is `edgeGcd = 1` on every edge, which
  by `edgeLatticePoints_eq_endpoints` makes each edge carry nothing but its endpoints.
- `Picks.LatticeTriangle.edgeGcd` also divides `latticeDet` (`edgeGcd_dvd_latticeDet_left`), which is
  what links primitivity of edges to primitivity of triangles.
