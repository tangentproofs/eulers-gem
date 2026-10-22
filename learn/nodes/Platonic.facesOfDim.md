---
id: Platonic.facesOfDim
title: "facesOfDim: the faces of one dimension, as a set"
summary: "`facesOfDim p d = {f | IsFaceOf p f ∧ affDim f = d}` — a name for the set-builder that `faceEulerSum` and the Euler relation already use. Definitionally equal, not a new idea."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "It lives in the `Platonic` namespace for historical reasons — it was introduced for the incidence counting in `PlatonicOfEuler.lean` — but there is nothing Platonic about it. It is the general face set of a given dimension."
  - "`d : ℤ`, not `ℕ`, so `facesOfDim p (-1) = {∅}` for a nonempty `p`: the empty face is a face and has `affDim = -1`. Nothing uses that instance, and `faceEulerSum` never reaches it."
  - "This is a `Set (Set E)`, not a `Finset`. Finiteness is a separate theorem (`facesOfDim_finite_of_isPolytope`), and until you have it `Set.ncard` of this set could be `0` for the wrong reason."
widgets:
  - type: polyhedron
    title: "facesOfDim p 0, 1 and 2: tap a vertex, an edge, a face"
    config:
      preset: cube
      show: [counts, incidence]
quiz:
  - q: "What is `facesOfDim p d`?"
    type: choice
    choices:
      - "`{f : Set E | IsFaceOf p f ∧ affDim f = d}`"
      - "`{f : Set E | IsFaceOf p f}`"
      - "`{f : Finset E | IsFaceOf p ↑f ∧ affDim ↑f = d}`"
      - "the number of faces of `p` of dimension `d`"
    answer: 0
    explain: "`def facesOfDim (p : Set E) (d : ℤ) : Set (Set E) := {f : Set E | IsFaceOf p f ∧ affDim f = d}` (PlatonicOfEuler.lean). It is a set of sets, not a count — the count is `(facesOfDim p d).ncard`."
  - q: "Is `facesOfDim p d` *definitionally* the set-builder appearing in `results_euler_relation_dimension_three`?"
    type: choice
    choices:
      - "yes — `mem_facesOfDim` is proved by `Iff.rfl`, and the Results proof moves between them with `simpa [facesOfDim]`"
      - "no, there is a nontrivial bijection"
      - "no, one uses `≤` and the other `=`"
    answer: 0
    explain: "`lemma mem_facesOfDim : f ∈ facesOfDim p d ↔ IsFaceOf p f ∧ affDim f = d := Iff.rfl`, and the docstring says \"definitionally the set-builder used by `euler_relation_convex_3polytope`\". In `results_five_platonic_solids` the step is literally `simpa [EulersGem.Platonic.facesOfDim] using hVEF`."
  - q: "For a cube `p`, what is `(facesOfDim p 2).ncard`?"
    type: number
    answer: 6
    explain: "The six square sides. `Cube.cube_face_counts` proves `V = 8`, `E = 12`, `F = 6` as geometric face counts, i.e. as `ncard`s of exactly these sets."
  - q: "Why does `(facesOfDim p d).ncard` need a finiteness theorem to be trustworthy?"
    type: choice
    choices:
      - "`Set.ncard` returns `0` on an infinite set, so a count of `0` would be ambiguous"
      - "`ncard` is noncomputable"
      - "it does not — `ncard` always errors on infinite sets"
      - "because `affDim` has a junk value"
    answer: 0
    explain: "Mathlib's `Set.ncard` is `Nat.card`, which is `0` for an infinite type. `facesOfDim_finite_of_isPolytope` rules that out for every `d`, from `PolytopeFaces.face_eq_convexHull_inter`. `regular_polytope_counts` opens by invoking it for `d = 0, 1, 2`."
---

## Plain English

```lean
def facesOfDim (p : Set E) (d : ℤ) : Set (Set E) :=
  {f : Set E | IsFaceOf p f ∧ affDim f = d}
```

A one-line abbreviation. `facesOfDim p 0` is the set of vertices (as singleton sets),
`facesOfDim p 1` the set of edges (as segments), `facesOfDim p 2` the set of 2-faces. It is
*definitionally* the set-builder that [`faceEulerSum`](#/node/faceEulerSum) and
[`results_euler_relation_dimension_three`](#/node/Results.results_euler_relation_dimension_three)
spell out longhand, so `mem_facesOfDim` is `Iff.rfl` and the two forms are interchangeable by
`simp`.

It exists so that the incidence statements in `PlatonicOfEuler.lean` are readable. Compare

```lean
∀ f ∈ facesOfDim p 2, {e ∈ facesOfDim p 1 | e ⊆ f}.ncard = s
```

with the same thing written out: it is the difference between "every 2-face has `s` edges" and a
wall of braces.

### In one breath

Just a label. "The corners", "the edges", "the flat sides" — each is a collection of pieces of a
solid, and this is how you ask for one of those collections by its dimension.

### One thing to remember

These are `Set`s, not `Finset`s. Nothing about the definition says there are finitely many faces,
and `Set.ncard` quietly answers `0` when there are infinitely many. The theorem that fixes this is
[`facesOfDim_finite_of_isPolytope`](#/node/facesOfDim_finite_of_isPolytope), and every count in the
development that matters cites it, directly or indirectly.

### Where it sits

- [`Platonic.regular_polytope_counts`](#/node/Platonic.regular_polytope_counts) states its three
  incidence hypotheses and its two double-counting conclusions in this vocabulary.
- [`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids) states its
  regularity hypotheses with it.
- `Simplex.ncard_facesOfDim_body_eq_choose`, `Octahedron.octahedron_face_counts`,
  `Cube.cube_face_counts` and `GeometricPlatonic.tetrahedron_face_counts` are the geometric
  face-count theorems, all phrased with it.
