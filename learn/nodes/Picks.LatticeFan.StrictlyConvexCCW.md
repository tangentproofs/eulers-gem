---
id: Picks.LatticeFan.StrictlyConvexCCW
title: "StrictlyConvexCCW: convex, counterclockwise, no flat corners"
summary: "`ConvexCCW P ∧ LocalCCWTurns P` — every vertex weakly left of every directed edge, and a strict left turn at every vertex. The hypothesis that makes the Pick results true."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**Both halves are needed and they fail independently.** A convex polygon listed clockwise fails `ConvexCCW` (every determinant comes out negative). A convex polygon listed with a redundant collinear vertex satisfies `ConvexCCW` but fails `LocalCCWTurns`, because the turn there is exactly zero and the condition is strict."
  - "It does **not** include distinctness of the vertices. [results_picks_theorem](#/node/Results.results_picks_theorem) carries `hverts : Function.Injective P.vertex` as a separate hypothesis."
  - "`ConvexCCW` is a doubly-quantified condition over all `(i, j)` pairs, including `j = i` and `j = nextIdx i`, where the determinant is zero and the `≤` is satisfied trivially."
widgets:
  - type: pick
    title: "Three presets break it in three different ways"
    config:
      preset: collinear-vertex
      show: [counts, hypotheses, fan]
quiz:
  - q: "`StrictlyConvexCCW P` unfolds to what?"
    type: choice
    choices:
      - "`ConvexCCW P ∧ LocalCCWTurns P`"
      - "`ConvexCCW P ∧ Function.Injective P.vertex`"
      - "`LocalCCWTurns P` alone"
      - "`ConvexCCW P ∧ PrimitiveEdges P`"
    answer: 0
    explain: "`def StrictlyConvexCCW : Prop := ConvexCCW P ∧ LocalCCWTurns P` (LatticeFan.lean)."
  - q: "`ConvexCCW P` says what, precisely?"
    type: choice
    choices:
      - "`∀ i j, 0 ≤ latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j)`"
      - "`∀ i, 0 < latticeDet (P.vertex (P.prevIdx i)) (P.vertex i) (P.vertex (P.nextIdx i))`"
      - "`Convex ℝ P.convexHullRegion`"
      - "`∀ i j, P.vertex i ≠ P.vertex j → i = j`"
    answer: 0
    explain: "Every listed vertex lies weakly to the **left** of every directed edge. (The second choice is `LocalCCWTurns`; the third is trivially true of any hull; the fourth is injectivity.)"
  - q: "`LocalCCWTurns P` says what?"
    type: choice
    choices:
      - "`∀ i, 0 < latticeDet (P.vertex (P.prevIdx i)) (P.vertex i) (P.vertex (P.nextIdx i))`"
      - "`∀ i, 0 ≤ latticeDet …`"
      - "every edge has gcd 1"
      - "the polygon has no interior lattice points"
    answer: 0
    explain: "A **strict** left turn at every vertex — so no three consecutive listed vertices are collinear. The strictness is what rules out redundant vertices."
  - q: "A square listed `(0,0), (1,0), (2,0), (2,2), (0,2)`. Which half fails?"
    type: choice
    choices:
      - "`LocalCCWTurns`, at `(1,0)`: the turn there is zero, not positive"
      - "`ConvexCCW`"
      - "both"
      - "neither"
    answer: 0
    explain: "`(0,0), (1,0), (2,0)` are collinear, so `latticeDet` of that triple is `0`, and `LocalCCWTurns` demands `> 0`. `ConvexCCW` still holds — no vertex is strictly right of any edge. Remove `(1,0)` from the list and both hold, for the same region. The `collinear-vertex` preset in the widget."
  - q: "A triangle listed `(0,0), (0,3), (4,0)` — clockwise. Which half is the one that pins down the handedness globally, and fails here?"
    type: choice
    choices:
      - "`ConvexCCW`: the determinants come out negative, and the condition asks for `0 ≤`"
      - "`LocalCCWTurns` only"
      - "neither — orientation is irrelevant"
    answer: 0
    explain: "Both fail, in fact, since `LocalCCWTurns` is also a `0 <` on the same orientation-sensitive determinant; but `ConvexCCW` is the one that pins down the handedness globally. Reverse the list and both hold. The `clockwise` preset."
  - q: "Which two things does `StrictlyConvexCCW` get *discharged* in `LatticeFan.lean`?"
    type: choice
    choices:
      - "`VerticesExtreme` (every listed vertex is extreme in the hull) and `FanDetsPos` (the corner fan is positively oriented, with injectivity)"
      - "`PrimitiveEdges` and `EmptyInterior`"
      - "nothing; it is only used as a hypothesis"
      - "finiteness of the interior lattice points"
    answer: 0
    explain: "`VerticesExtreme_of_strictlyConvexCCW` and `FanDetsPos_of_strictlyConvexCCW`. `ROADMAP.md` records both as separate pieces of work — before them, those two were hypotheses of the Pick-form results."
---

## Plain English

```lean
def ConvexCCW : Prop :=
  ∀ i j : Fin P.nVertices,
    0 ≤ latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j)

def LocalCCWTurns : Prop :=
  ∀ i : Fin P.nVertices,
    0 < latticeDet (P.vertex (P.prevIdx i)) (P.vertex i) (P.vertex (P.nextIdx i))

def StrictlyConvexCCW : Prop := ConvexCCW P ∧ LocalCCWTurns P
```

Two conditions, both expressed with `latticeDet a b c`, which is positive when `c` lies strictly to
the left of the directed line from `a` to `b`, zero when the three are collinear, and negative when
`c` is to the right.

1. **`ConvexCCW`** — a global condition. For every directed edge of the polygon, *every* vertex is
   weakly on its left. That is convexity and counterclockwise orientation at once: if the shape bulged
   the wrong way somewhere, some vertex would be on the right of some edge.
2. **`LocalCCWTurns`** — a local condition. At every vertex, walking in order, you turn strictly
   left. No flat corners.

### In one breath

Walk around the outline of your shape in the order you listed the corners. Two things must be true.
Looking along any edge you are standing on, every corner of the shape is on your left — never on
your right. And at every corner you must actually turn left, not carry straight on. The first makes
it convex and anticlockwise; the second says you did not write down a corner that is not really a
corner.

### Why both

Because they fail separately, and the two failures look different:

| polygon | `ConvexCCW` | `LocalCCWTurns` | widget preset |
|---|---|---|---|
| ordinary convex, CCW | ✓ | ✓ | `triangle`, `pentagon` |
| convex, listed **clockwise** | ✗ | ✗ | `clockwise` |
| convex region, **collinear** listed vertex | ✓ | ✗ | `collinear-vertex` |
| **non-convex** dart | ✗ | ✗ | `non-convex` |

The third row is the one to watch for. `(0,0), (2,0), (4,0), (2,3)` is a perfectly good convex
triangle with a redundant vertex written down in the middle of its base. Pick's theorem is *true*
for it. [`results_picks_theorem`](#/node/Results.results_picks_theorem) does not apply, because
`LocalCCWTurns` is strict. **Re-list it without the middle vertex and the theorem applies**, to the
same region, with the same `I`, `B` and area. The restriction is on the description, not the shape.

### What it buys

`StrictlyConvexCCW` is not just a convenient hypothesis — two things that used to be hypotheses are
now *derived* from it in `LatticeFan.lean`:

- `VerticesExtreme_of_strictlyConvexCCW`: every listed vertex is extreme in the hull of the vertex
  set, so no vertex hides inside a fan triangle;
- `FanDetsPos_of_strictlyConvexCCW` (with injectivity): all the corner-fan determinants are
  strictly positive, so the fan triangles are non-degenerate and consistently oriented.

Those two feed `FanTrianglesEmpty` → `FanDetPrimitive` → "each fan triangle has area `1/2`", which
is the geometric backbone of the Pick proof.

### Where it sits

A hypothesis of [`results_picks_theorem`](#/node/Results.results_picks_theorem),
[`results_picks_of_empty_primitive_fan`](#/node/Results.results_picks_of_empty_primitive_fan), and
[`volume_convexHullRegion_eq_ofReal_shoelace`](#/node/Picks.LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace).
