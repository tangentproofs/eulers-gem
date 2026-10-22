---
id: euler_polyhedron
title: "Euler's polyhedron formula in real three-space"
summary: "In `EuclideanSpace ℝ (Fin 3)`, `IsPolytope p` and `affDim p = 3` give `V − E + F = 2`. Two hypotheses, both geometric, nothing supplied."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "`EuclideanSpace ℝ (Fin 3)` is ℝ³ with the standard inner product. The theorem is no stronger than [euler_relation_of_isPolytope](#/node/euler_relation_of_isPolytope), which holds in *any* 3-dimensional real inner product space; the specialization exists so that a reader can see a statement with no type-class hypotheses in it."
  - "`affDim p = 3` is doing real work: it rules out a flat or degenerate `p`, including `∅` and single points, which `IsPolytope` admits."
widgets:
  - type: polyhedron
    title: "Both hypotheses hold for seven of these, and fail for the eighth"
    config:
      preset: tetrahedron
      show: [counts, incidence, truncate]
quiz:
  - q: "How many hypotheses does `euler_polyhedron` have?"
    type: number
    answer: 2
    explain: "`theorem euler_polyhedron {p : Set (EuclideanSpace ℝ (Fin 3))} (hp : IsPolytope p) (hdim : affDim p = 3)` (UnconditionalEuler.lean). Both are about `p`; there is no halfspace presentation, no finiteness assumption about the faces, no Euler input."
  - q: "Why does the `Module.finrank ℝ E = 3` hypothesis of the general version disappear here?"
    type: choice
    choices:
      - "it is discharged by `simp`, since `finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3` is known to Mathlib"
      - "it is assumed silently"
      - "the specialization drops it, weakening the theorem"
      - "`EuclideanSpace` has no finrank"
    answer: 0
    explain: "The proof is `euler_relation_of_isPolytope hp hdim (by simp)`. `finrank_euclideanSpace_fin` gives the third argument."
  - q: "Does `IsPolytope p` alone give `V − E + F = 2`?"
    type: choice
    choices:
      - "yes"
      - "no — `∅` and a single point are polytopes too, and `affDim p = 3` excludes them"
      - "yes, provided `p` is nonempty"
    answer: 1
    explain: "`IsPolytope ∅` holds with `V = ∅`. A point, a segment and a square in ℝ³ are all polytopes with `affDim` 0, 1, 2 and face counts that do not satisfy this identity in this form. `affDim p = 3` is what makes the statement true."
  - q: "A square pyramid: 5 vertices, 8 edges, 5 faces. Does the theorem cover it, and does the identity hold?"
    type: choice
    choices:
      - "covered, and `5 − 8 + 5 = 2`"
      - "not covered: the faces are not all the same shape"
      - "covered, but the identity fails"
    answer: 0
    explain: "It is the convex hull of five points and it is 3-dimensional, so both hypotheses hold. Regularity is irrelevant — nothing in the statement mentions it. `5 − 8 + 5 = 2`."
---

## Plain English

```lean
theorem euler_polyhedron {p : Set (EuclideanSpace ℝ (Fin 3))}
    (hp : IsPolytope p) (hdim : affDim p = 3) :
    ({f | IsFaceOf p f ∧ affDim f = 0}.ncard : ℤ) -
      ({f | IsFaceOf p f ∧ affDim f = 1}.ncard : ℤ) +
      ({f | IsFaceOf p f ∧ affDim f = 2}.ncard : ℤ) = 2
```

Euler's polyhedron formula, in ordinary three-dimensional space, with the shortest hypothesis list
in the repository:

1. `p` is the convex hull of finitely many points;
2. `p` is three-dimensional.

Then corners minus edges plus flat sides is two. Nothing is supplied by the caller — not a list of
bounding planes, not finiteness of the face sets, certainly not Euler's relation itself.

### In one breath

Whittle something out of wood. Count the corners, the edges and the flat sides. Corners minus edges
plus sides is two. That is all this says, and the two conditions on the whittling are: finitely many
cuts, and don't end up with something flat.

### Why have both this and the general version?

[`euler_relation_of_isPolytope`](#/node/euler_relation_of_isPolytope) is the real theorem and holds
in any 3-dimensional real inner product space. This is the same statement with `E` pinned to
`EuclideanSpace ℝ (Fin 3)`, so that the `Module.finrank ℝ E = 3` hypothesis vanishes (by `simp`,
from `finrank_euclideanSpace_fin`) and what remains is a statement about ℝ³ that mentions no type
classes at all. Easier to read, easier to check against a textbook, and that is the whole point of
a `Results` file.

[`results_euler_polyhedron`](#/node/Results.results_euler_polyhedron) is this theorem again in
`Results.lean`.

### Where it sits

- From: [`euler_relation_of_isPolytope`](#/node/euler_relation_of_isPolytope), which is from
  [`Euler_Poincare_of_isPolytope`](#/node/Euler_Poincare_of_isPolytope).
- Restated as: [`results_euler_polyhedron`](#/node/Results.results_euler_polyhedron), which the
  graph on this site uses as its focal node.
