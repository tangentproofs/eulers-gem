---
id: Picks.LatticePolygon.nVertices
title: "nVertices: how many points are in the list"
summary: "`P.nVertices = P.vertices.length`, at least 3 by the structure's own field. It is the number of *listed* vertices, which can exceed the number of actual corners."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "It counts **listed** vertices, not corners of the shape. A convex triangle listed with an extra collinear point on one side has `nVertices = 4`. That polygon fails [LocalCCWTurns](#/node/Picks.LatticeFan.StrictlyConvexCCW), so the Pick results exclude it — but `nVertices` itself does not notice."
  - "`nVertices_pos` is derived from `length_ge : 3 ≤ vertices.length`, and that bound is what makes the modular arithmetic in `nextIdx`/`prevIdx` well defined."
widgets:
  - type: pick
    title: "Count the pink points: that is nVertices"
    config:
      preset: pentagon
      show: [counts, fan]
quiz:
  - q: "What is `P.nVertices`?"
    type: choice
    choices: ["`P.vertices.length`", "`P.vertexFinset.card`", "`P.B`", "the number of corners of the hull"]
    answer: 0
    explain: "`def nVertices : ℕ := P.vertices.length`. Note it is the *list* length, so a repeated point counts twice — unlike `P.vertexFinset.card`, which would not."
  - q: "What is the smallest possible `nVertices`?"
    type: number
    answer: 3
    explain: "`length_ge : 3 ≤ vertices.length` is a field of [LatticePolygon](#/node/Picks.LatticePolygon), and `nVertices_pos` is derived from it. The bound is also what `3 ≤ n` in `triangulated_disk_euler_from_characteristic` is instantiated with, via `P.length_ge`."
  - q: "Can `nVertices` exceed `B`?"
    type: choice
    choices:
      - "not when the vertices are distinct: `LatticeFan.nVertices_le_B` gives `nVertices ≤ B`"
      - "yes, often"
      - "yes, when the polygon is non-convex"
    answer: 0
    explain: "`theorem nVertices_le_B (P : LatticePolygon) (hverts : Function.Injective P.vertex) : P.nVertices ≤ P.B` (PickFromEuler.lean) — every listed vertex is a boundary lattice point, so with no repeats the count can only grow. This is what supplies `n ≤ B` to the disk-Euler lemma."
  - q: "How many fan triangles does the corner fan of an `n`-gon have?"
    type: choice
    choices: ["`n − 2`", "`n`", "`n − 1`", "`2n − 3`"]
    answer: 0
    explain: "`fanTriangle P i hi` is defined for `i < P.nVertices - 2`, giving the triangles `(v₀, vᵢ₊₁, vᵢ₊₂)`. `card_fanTriangles` proves the count is `nVertices - 2` when the vertices are distinct."
---

## Plain English

```lean
def nVertices : ℕ := P.vertices.length
```

How many points you wrote down. At least 3, by the structure's `length_ge` field, which is also what
makes the modular index arithmetic in `nextIdx` and `prevIdx` safe.

### In one breath

The length of your list of corners. Three or more, because anything less is not a shape.

### Listed versus actual

`nVertices` is the length of the **list**, not the number of geometric corners:

- a repeated point counts twice (and `Function.Injective P.vertex` is what rules that out);
- a point sitting in the middle of a straight side counts as a vertex
  (and `LocalCCWTurns` is what rules that out).

So `nVertices` and `P.vertexFinset.card` can differ, and both can differ from the number of extreme
points of the hull. Under the Pick hypotheses — distinct vertices and
[`StrictlyConvexCCW`](#/node/Picks.LatticeFan.StrictlyConvexCCW) — all three agree.

### Where it is used

- `Fin P.nVertices` is the index type of [`vertex`](#/node/Picks.LatticePolygon.vertex),
  `nextIdx`, `prevIdx` and `edgePair`, so it is in the type of every polygon predicate.
- `nVertices - 2` is the number of corner-fan triangles (`card_fanTriangles`).
- `nVertices_le_B` (with injective vertices) supplies the `n ≤ B` of
  [`triangulated_disk_euler_from_characteristic`](#/node/Picks.triangulated_disk_euler_from_characteristic),
  and `length_ge` supplies the `3 ≤ n`. Those are the two bounds that make the natural subtractions
  in that lemma honest.
