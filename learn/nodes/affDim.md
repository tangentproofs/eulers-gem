---
id: affDim
title: "affDim: the dimension of a set, with −1 for the empty one"
summary: "`affDim s` is the dimension of the affine span of `s`, as an integer, with `affDim ∅ = -1`. It is what turns a face into a vertex, an edge or a 2-face."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "`affDim` has a **junk value**. It is built on Mathlib's `AffineSubspace.finDim`, which is built on `Module.finrank`, and `finrank` returns `0` for an infinite-dimensional space. So a set whose affine span has infinite dimension gets `affDim = 0`, indistinguishable from a point. The module's own docstring says so, and every Euler theorem in the repository carries `[FiniteDimensional ℝ E]`, where the junk value cannot arise."
  - "The value is an `ℤ`, not a `ℕ`, purely so that the empty set can have a dimension. That choice is Paulson's `aff_dim`, not Mathlib's: Mathlib's `AffineSubspace.finDim` lives in `WithBot ℕ` and sends the empty subspace to `⊥`."
  - "`affDim` is `noncomputable`."
widgets:
  - type: polyhedron
    title: "Tap a vertex (affDim 0), an edge (affDim 1) or a face (affDim 2)"
    config:
      preset: octahedron
      show: [counts, incidence]
quiz:
  - q: "What is `affDim (∅ : Set E)`?"
    type: number
    answer: -1
    explain: "`@[simp] lemma affDim_empty : affDim (∅ : Set E) = -1` (AffDim.lean). The affine span of `∅` is `⊥`, whose `finDim` is `⊥`, and the `match` sends `⊥` to `-1`."
  - q: "What is `affDim {x}` for a single point `x`?"
    type: number
    answer: 0
    explain: "`@[simp] lemma affDim_singleton (x : E) : affDim ({x} : Set E) = 0`. A point spans a 0-dimensional affine subspace — which is why vertices are the `d = 0` term of `faceEulerSum`."
  - q: "Why does the empty set get `-1` rather than `0`?"
    type: choice
    choices:
      - "so that it is never counted among the dimension-0 faces, even though it *is* a face"
      - "because the empty set has no points, and `0` would be wrong arithmetically"
      - "it is an arbitrary convention with no consequences"
      - "to make `affDim` injective"
    answer: 0
    explain: "`isFaceOf_empty` makes `∅` a face of every set, so without a separate value it would be counted as a vertex. `faceEulerSum` sums over `d ∈ Finset.range (n+1)`, i.e. `d ≥ 0`, and `affDim ∅ = -1` keeps the empty face out of every term. This is the single most load-bearing convention in the whole development."
  - q: "`affDim s = -1` holds. What follows?"
    type: choice
    choices: ["`s` is a point", "`s = ∅`", "`s` is unbounded", "nothing — `-1` is a junk value"]
    answer: 1
    explain: "`lemma affDim_eq_neg_one_iff_empty (s : Set E) : affDim s = -1 ↔ s = ∅`. It is an iff, proved in both directions. The junk value in this definition is `0`, not `-1`."
  - q: "In a finite-dimensional space, what is `affDim (univ : Set E)`?"
    type: choice
    choices: ["`0`", "`-1`", "`Module.finrank ℝ E`", "`Module.finrank ℝ E - 1`"]
    answer: 2
    explain: "`lemma affDim_univ [FiniteDimensional ℝ E] [Nonempty E] : affDim (univ : Set E) = Module.finrank ℝ E`. This is why `affDim p = Module.finrank ℝ E` is the right way to say \"`p` is full-dimensional\" in `results_euler_characteristic`."
---

## Plain English

`affDim s` answers "how many dimensions does `s` take up?" — not how big it is, but how many
independent directions you can move in without leaving the smallest flat piece of space that
contains it.

```lean
noncomputable def affDim (s : Set E) : ℤ :=
  match (affineSpan ℝ s).finDim with
  | ⊥ => -1
  | (n : ℕ) => n
```

Read it in two steps.

1. `affineSpan ℝ s` is Mathlib's smallest affine subspace containing `s` — the line through two
   points, the plane through three non-collinear ones, and so on. Affine, not linear: it does not
   have to pass through the origin.
2. `finDim` is that subspace's dimension in `WithBot ℕ`, which is `⊥` exactly when the subspace
   is empty. The `match` turns `⊥` into `-1` and a natural number `n` into the integer `n`.

So: a point has `affDim 0`, a segment `affDim 1`, a triangle or a square `affDim 2`, a cube
`affDim 3`. A square sitting inside ℝ³ still has `affDim 2` — the dimension is the set's own, not
the room's.

### In one breath

Ask of a shape: if I stand inside it, how many directions can I walk in? None at all, if it is a
single dot. One, back and forth, if it is a line segment. Two, if it is a flat patch. Three, if
it is a solid. That number is what `affDim` returns — with one special answer, `minus one`, for
the empty shape, which has no inside to stand in at all. That odd choice is doing real work, and
it is worth knowing why.

### Why the −1 matters so much

[IsFaceOf](#/node/IsFaceOf) makes the empty set a face of *everything* — `isFaceOf_empty` is a
one-line proof. If `affDim ∅` were `0`, the empty face would be counted as a vertex, and the
alternating sum in [faceEulerSum](#/node/faceEulerSum) would come out `2`, not `1`, for every
polytope. The `-1` keeps it out of the sum altogether, because `faceEulerSum` runs `d` over
`Finset.range (n+1)` — the non-negative dimensions only.

(This is also why the number you get is `1` and not `0`. If you *did* put the empty face back in
with its own sign, you would be computing the *reduced* Euler characteristic, which is `0` for a
polytope. Both conventions appear in the literature; the Lean uses this one.)

### Where the junk value is

The definition inherits `Module.finrank`'s convention that an infinite-dimensional space has
`finrank = 0`. So a set spanning infinitely many dimensions gets `affDim = 0`, which is a lie.
Every statement in this development that reasons with `affDim` is inside a
`[FiniteDimensional ℝ E]` context, where no such set exists. If you ever see `affDim` used
without that instance, be suspicious.

### Where it sits

`affDim` is the vocabulary of every Euler statement in the repository:

- [`faceEulerSum p n`](#/node/faceEulerSum) buckets the faces of `p` by their `affDim`.
- `affDim p = Module.finrank ℝ E` is the full-dimensionality hypothesis of
  [`results_euler_characteristic`](#/node/Results.results_euler_characteristic).
- `affDim p = 3` is the only geometric hypothesis besides `IsPolytope` in
  [`results_euler_polyhedron`](#/node/Results.results_euler_polyhedron).
- `affDim f = 0`, `1`, `2` are what "vertex", "edge" and "2-face" mean there — nothing else
  defines them.
