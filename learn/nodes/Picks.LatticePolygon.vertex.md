---
id: Picks.LatticePolygon.vertex
title: "vertex: the i-th listed point, indexed by Fin"
summary: "`P.vertex i = P.vertices.get i` for `i : Fin P.nVertices`. Indexing by `Fin` is what makes `Function.Injective P.vertex` the right way to say \"the vertices are distinct\"."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "`P.vertex` is a function `Fin P.nVertices → ℤ × ℤ`. `Function.Injective P.vertex` therefore says distinct *indices* give distinct *points* — exactly distinctness of the listed vertices, which is also `P.vertices.Nodup` (`List.nodup_iff_injective_get`)."
  - "The `Fin` index means no out-of-range access is possible, so there is no default or junk value."
widgets:
  - type: pick
    title: "Tap to add or remove a listed vertex"
    config:
      preset: repeated-vertex
      show: [counts, hypotheses]
quiz:
  - q: "What is the type of `P.vertex`?"
    type: choice
    choices: ["`Fin P.nVertices → ℤ × ℤ`", "`ℕ → ℤ × ℤ`", "`Finset (ℤ × ℤ)`", "`List (ℤ × ℤ)`"]
    answer: 0
    explain: "`def vertex (i : Fin P.nVertices) : ℤ × ℤ := P.vertices.get i`. The `Fin` bound rules out out-of-range indices, so there is no junk value — contrast `LatticeFan.vertNat`, which takes an `ℕ` and returns `(0,0)` out of range."
  - q: "`Function.Injective P.vertex` says what about the polygon?"
    type: choice
    choices:
      - "no vertex is listed twice"
      - "no three vertices are collinear"
      - "the polygon does not cross itself"
      - "the polygon is convex"
    answer: 0
    explain: "Distinct indices give distinct points: the list has no repeats. `PickFromEuler.lean` uses `List.nodup_iff_injective_get` to move between this and `P.vertices.Nodup`. Non-crossing and convexity are separate conditions — [StrictlyConvexCCW](#/node/Picks.LatticeFan.StrictlyConvexCCW)."
  - q: "Why is injectivity a separate hypothesis rather than part of the structure?"
    type: choice
    choices:
      - "[LatticePolygon](#/node/Picks.LatticePolygon) deliberately asserts almost nothing, so every real condition is visible in the hypothesis list of whatever uses it"
      - "because it is not needed"
      - "because it follows from `3 ≤ nVertices`"
      - "an oversight"
    answer: 0
    explain: "The structure's docstring says it does not assert simplicity or convexity; distinctness goes the same way. The cost is longer hypothesis lists in `results_picks_theorem` and friends; the benefit is that you can see what each theorem needs."
  - q: "What does `P.vertex (P.nextIdx i)` give?"
    type: choice
    choices:
      - "the next vertex in the cycle, wrapping from the last back to the first"
      - "the next vertex, erroring at the end of the list"
      - "the nearest vertex"
      - "`(0,0)` when `i` is the last index"
    answer: 0
    explain: "`nextIdx i = ⟨(i.1 + 1) % P.nVertices, _⟩`, so it wraps. That wrap is what makes `edgePair` produce the closing edge and `shoelaceSum` a cyclic sum."
---

## Plain English

```lean
def nVertices : ℕ := P.vertices.length
def vertex (i : Fin P.nVertices) : ℤ × ℤ := P.vertices.get i
```

`P.vertex i` is the `i`-th listed corner. The index is a `Fin P.nVertices`, so it cannot be out of
range and there is no fallback value.

That typing choice is why distinctness of the vertices is phrased as

```lean
Function.Injective P.vertex
```

— different slots hold different points. It is equivalent to `P.vertices.Nodup`, and
`PickFromEuler.lean` converts between the two with `List.nodup_iff_injective_get`.

### In one breath

The corners, numbered. Slot zero, slot one, and so on, with the numbering wrapping round at the end
so the shape closes. Asking that different slots hold different corners is how you say you did not
write the same corner down twice.

### Why it is a hypothesis

[`LatticePolygon`](#/node/Picks.LatticePolygon) asserts nothing but `3 ≤ vertices.length`, on
purpose. So `Function.Injective P.vertex` appears explicitly in
[`results_picks_theorem`](#/node/Results.results_picks_theorem),
[`results_picks_of_empty_primitive_fan`](#/node/Results.results_picks_of_empty_primitive_fan) and
[`volume_convexHullRegion_eq_ofReal_shoelace`](#/node/Picks.LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace),
rather than being quietly available. The `repeated-vertex` preset in the `pick` widget is a polygon
where it fails.

### Related

- `nextIdx` / `prevIdx` — modular successor and predecessor, with `nextIdx_prevIdx` and
  `prevIdx_nextIdx` proving them mutually inverse.
- `edgePair i = (vertex i, vertex (nextIdx i))` — the `i`-th directed edge.
- `vertexFinset = vertices.toFinset` — the vertex *set*, which forgets both order and repeats, and
  which [`convexHullRegion`](#/node/Picks.LatticePolygon.convexHullRegion) is built from.
- `LatticeFan.vertNat k` — an `ℕ`-indexed variant returning `(0,0)` out of range, used where
  arithmetic on indices is easier than `Fin` juggling.
