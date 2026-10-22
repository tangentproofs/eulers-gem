---
id: IsFaceOf
title: "IsFaceOf: extreme and convex"
summary: "`IsFaceOf S T` is Mathlib's `IsExtreme ℝ S T` plus convexity of `T`. Both `∅` and `S` itself are faces, and only `affDim` keeps the empty one out of the counts."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**`∅` is a face of everything** (`isFaceOf_empty`) and **`S` is a face of itself** when `S` is convex (`isFaceOf_refl`). Neither is an accident, and both change the arithmetic: the body is the top term of `faceEulerSum`, and the empty face is excluded only because `affDim ∅ = -1`."
  - "This is a `structure`, not a `def`, so a face is built by giving two fields: `isExtreme` and `convex`. The second is not redundant — Mathlib's `IsExtreme` alone permits a non-convex `T`, and the module docstring says so explicitly."
  - "`IsFaceOf` is a relation between arbitrary sets. It does not require `S` to be a polytope, or `T` to be closed, or either to be nonempty."
  - "It is *not* the same as being *exposed* (cut out by a supporting hyperplane). Exposed sets are faces — `isFaceOf_of_isExposed` — but not every face of every convex set is exposed. For polytopes the two coincide, which is what makes `isFaceOf_convexHull_argmax` a usable recipe, but the definition does not assume it."
widgets:
  - type: polyhedron
    title: "Faces of each dimension: tap one"
    config:
      preset: cube
      show: [counts, incidence]
quiz:
  - q: "`IsFaceOf S T` is a structure with how many fields, and what are they?"
    type: choice
    choices:
      - "one: `IsExtreme ℝ S T`"
      - "two: `IsExtreme ℝ S T` and `Convex ℝ T`"
      - "two: `T ⊆ S` and `Convex ℝ T`"
      - "three: extreme, convex and closed"
    answer: 1
    explain: "`structure IsFaceOf (S T : Set E) : Prop where isExtreme : IsExtreme ℝ S T; convex : Convex ℝ T` (Polytope.lean). The docstring explains why the second field is there: Mathlib's `IsExtreme` does not require the face to be convex."
  - q: "Is `∅` a face of every set?"
    type: choice
    choices: ["yes", "no", "only of convex sets", "only of nonempty sets"]
    answer: 0
    explain: "`lemma isFaceOf_empty (S : Set E) : IsFaceOf S (∅ : Set E)` — the extreme condition is vacuous and `convex_empty` gives the other field. This is why `affDim ∅ = -1` is load-bearing: without it the empty face would count as a vertex."
  - q: "Is a convex set `S` a face of itself?"
    type: choice
    choices: ["yes, `isFaceOf_refl`", "no, faces are proper subsets", "only in dimension 0"]
    answer: 0
    explain: "`lemma isFaceOf_refl {S : Set E} (hS : Convex ℝ S) : IsFaceOf S S := ⟨IsExtreme.rfl, hS⟩`. So a 3-dimensional polytope has exactly one face of `affDim 3` — itself — and that is the `-1` term that turns `faceEulerSum = 1` into `V − E + F = 2`."
  - q: "Which direction does the subset relation go in `isFaceOf_subset`?"
    type: choice
    choices: ["`IsFaceOf S T → S ⊆ T`", "`IsFaceOf S T → T ⊆ S`", "neither; faces need not be subsets"]
    answer: 1
    explain: "`lemma isFaceOf_subset {S T : Set E} (h : IsFaceOf S T) : T ⊆ S := h.isExtreme.subset`. In `IsFaceOf S T`, `S` is the body and `T` is the face. Read the argument order carefully — it is body-first."
  - q: "If `T` and `U` are both faces of `S`, is `T ∩ U`?"
    type: choice
    choices: ["yes, `isFaceOf_inter`", "no", "only if they meet"]
    answer: 0
    explain: "`lemma isFaceOf_inter {S T U : Set E} (hT : IsFaceOf S T) (hU : IsFaceOf S U) : IsFaceOf S (T ∩ U)`, from `IsExtreme.inter` and `Convex.inter`. Together with `isFaceOf_trans` and `isFaceOf_empty` this is what makes the faces a *lattice* — the empty face being its bottom element."
---

## Plain English

A **face** of a shape is a piece you could slice off with a flat cut, without the cut passing
through the inside: a corner, an edge, a flat side.

The Lean says it differently, and more generally:

```lean
structure IsFaceOf (S T : Set E) : Prop where
  isExtreme : IsExtreme ℝ S T
  convex : Convex ℝ T
```

Mathlib's `IsExtreme ℝ S T` says `T ⊆ S` and: whenever a point of `T` lies strictly between two
points of `S`, both of those points are already in `T`. In words — **if any part of a segment in
`S` reaches into `T`, the whole segment is in `T`.** You cannot get into a face by averaging
things that are outside it.

That catches every corner, edge and side of a polytope, and nothing in the middle. The second
field asks `T` to be convex. Mathlib's `IsExtreme` alone does not, and for the face lattice you
want it; the module docstring calls this out.

Note the argument order: in `IsFaceOf S T`, the **body comes first** and the face second.

### In one breath

Lay a ruler flat against a solid and press. Whatever touches the ruler is a face: a flat side if
the ruler lies along one, an edge if it catches one, a single corner if it just touches there.
The test in the Lean is slightly different and slightly stronger — nothing in a face is ever the
midpoint of two things outside it — but you will not go wrong picturing the ruler.

### Two faces nobody draws

By the definition:

- `∅` is a face of absolutely everything (`isFaceOf_empty`);
- a convex `S` is a face of itself (`isFaceOf_refl`).

Both are in the count that [faceEulerSum](#/node/faceEulerSum) takes, or rather: the body is in,
and the empty face is thrown out, and the only thing throwing it out is
[`affDim ∅ = -1`](#/node/affDim). If you are ever reconstructing the arithmetic by hand, those two
are what you get wrong.

### Computing faces of a polytope

`PolytopeFaces.lean` supplies the practical recipe:
`isFaceOf_convexHull_argmax` says that for a V-polytope, the set where a linear functional attains
its maximum is a face. That is how `Cube.lean`, `Octahedron.lean` and `SimplexFaces.lean` get
their face lattices — and it is the recipe the `polyhedron` widget above runs in floating point to
work out the faces of each preset from its coordinates.

The other key fact from that module is `face_eq_convexHull_inter`: a face of `convexHull ℝ V` is
`convexHull ℝ (V ∩ F)`. So the map `F ↦ V ∩ F` is injective on faces, so there are finitely many
of them — which is [`facesOfDim_finite_of_isPolytope`](#/node/facesOfDim_finite_of_isPolytope), and
it is needed because `Set.ncard` reports `0` for an infinite set and would otherwise hand you
plausible-looking nonsense.

### Where it sits

`IsFaceOf` and [`affDim`](#/node/affDim) together are the entire vocabulary of the Euler
statements. `V`, `E` and `F` in
[`results_euler_polyhedron`](#/node/Results.results_euler_polyhedron) are literally

```lean
{f : Set E | IsFaceOf p f ∧ affDim f = 0}.ncard
{f : Set E | IsFaceOf p f ∧ affDim f = 1}.ncard
{f : Set E | IsFaceOf p f ∧ affDim f = 2}.ncard
```

and [`Platonic.facesOfDim`](#/node/Platonic.facesOfDim) is an abbreviation for that set-builder.
