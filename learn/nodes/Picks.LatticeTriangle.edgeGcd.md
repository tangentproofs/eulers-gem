---
id: Picks.LatticeTriangle.edgeGcd
title: "edgeGcd: one number decides a segment's lattice points"
summary: "`edgeGcd p q = Int.gcd (q.1 − p.1) (q.2 − p.2)`. Zero exactly when `p = q`, one exactly when the segment carries nothing but its endpoints."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "`Int.gcd` returns an `ℕ`, so `edgeGcd` is non-negative by typing. It is `0` only in the degenerate case `p = q` (`edgeGcd_eq_zero_iff`)."
  - "It is symmetric in the sense that `edgeGcd p q = edgeGcd q p` (the differences negate and `gcd` ignores sign), and the Lean does state it, as `LatticeFan.InteriorFan.edgeGcd_comm` in `OnSpoke.lean`."
widgets:
  - type: pick
    title: "Every edge's gcd, and the B it adds up to"
    config:
      preset: triangle
      show: [counts, hypotheses]
quiz:
  - q: "State the definition."
    type: choice
    choices:
      - "`Int.gcd (q.1 - p.1) (q.2 - p.2)`"
      - "`Nat.gcd p.1 p.2`"
      - "`Int.gcd p.1 q.2 - Int.gcd p.2 q.1`"
      - "`|q.1 - p.1| + |q.2 - p.2|`"
    answer: 0
    explain: "`def edgeGcd (p q : ℤ × ℤ) : ℕ := Int.gcd (q.1 - p.1) (q.2 - p.2)` (LatticeTriangle.lean). The gcd of the two coordinate differences."
  - q: "`edgeGcd p q = 0` happens when?"
    type: choice
    choices: ["exactly when `p = q`", "never", "when the segment is horizontal", "when the segment is primitive"]
    answer: 0
    explain: "`lemma edgeGcd_eq_zero_iff (p q : ℤ × ℤ) : edgeGcd p q = 0 ↔ p = q`, since `Int.gcd a b = 0 ↔ a = 0 ∧ b = 0`. [edgeLatticePoints](#/node/Picks.edgeLatticePoints) special-cases it."
  - q: "`edgeGcd (1,1) (4,7)`?"
    type: number
    answer: 3
    explain: "`gcd(4 − 1, 7 − 1) = gcd(3, 6) = 3`. So that segment carries `3 + 1 = 4` lattice points: `(1,1)`, `(2,3)`, `(3,5)`, `(4,7)`."
  - q: "`edgeGcd a b` divides which quantity, and why does that matter?"
    type: choice
    choices:
      - "`latticeDet a b c` for every `c` (`edgeGcd_dvd_latticeDet_left`) — so a non-primitive edge forces a non-primitive triangle"
      - "`a.1 * b.2`"
      - "nothing in particular"
      - "the area of any triangle on it"
    answer: 0
    explain: "`lemma edgeGcd_dvd_latticeDet_left (a b c : ℤ × ℤ) : (edgeGcd a b : ℤ) ∣ latticeDet a b c`, since the gcd divides both `b.1 − a.1` and `b.2 − a.2`, which the determinant is a combination of. Consequence: if `|latticeDet a b c| = 1` then `edgeGcd a b = 1`. That is how triangle primitivity forces edge primitivity."
---

## Plain English

```lean
def edgeGcd (p q : ℤ × ℤ) : ℕ := Int.gcd (q.1 - p.1) (q.2 - p.2)
```

Go from `p` to `q`: so far across, so far up. `edgeGcd` is the greatest common divisor of those two
numbers. One integer, and it answers everything about the lattice points on that segment:

| `edgeGcd p q` | means |
|---|---|
| `0` | `p = q` — a degenerate edge |
| `1` | the segment carries only its two endpoints — a **primitive** edge |
| `d` | the segment carries `d + 1` lattice points, at even spacing `(Δx/d, Δy/d)` |

### In one breath

Across six and up four: both share a factor of two, so halfway along you land exactly on a grid
crossing. Across two and up one: nothing divides both, so you land on none. The largest number
dividing both is the whole answer, and it is the number this definition computes.

### Two things it feeds

**[`edgeLatticePoints`](#/node/Picks.edgeLatticePoints) and hence [`B`](#/node/Picks.LatticePolygon.B).**
`card_edgeLatticePoints` is `edgeGcd + 1`, so the boundary count of a lattice polygon is arithmetic
on its vertex list. No search.

**Primitivity.** `edgeGcd_dvd_latticeDet_left` says `edgeGcd a b` divides `latticeDet a b c` for any
third point `c`. So if a triangle has `|det| = 1`, each of its edges must have `edgeGcd = 1`. That
one-line fact is the bridge between
[`PrimitiveEdges`](#/node/Picks.LatticeFan.PrimitiveEdges) (a condition on edges) and
`FanDetPrimitive` (a condition on triangles), and both appear in the Pick proof.

### Where it sits

Defined in `LatticeTriangle.lean`, used by [`edgeLatticePoints`](#/node/Picks.edgeLatticePoints),
[`B`](#/node/Picks.LatticePolygon.B) and
[`PrimitiveEdges`](#/node/Picks.LatticeFan.PrimitiveEdges).
