---
id: facesOfDim_finite_of_isPolytope
title: "A polytope has finitely many faces of each dimension"
summary: "For `IsPolytope p` and any `d`, the set `{f | IsFaceOf p f ∧ affDim f = d}` is finite. Without this, every `Set.ncard` in the Euler statements could be zero for the wrong reason."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "The statement is finiteness of the face set, not a bound on its size. The counting is done elsewhere."
  - "It is stated per dimension `d`, by restricting the stronger `faces_finite_of_isPolytope` (all faces at once) to one dimension."
  - "No finite-dimensionality hypothesis appears in the statement; the finiteness comes from the finite generating set, through `face_eq_convexHull_inter`."
widgets:
  - type: face-lattice
    title: "Finitely many in each dimension — and here are the exact counts"
    config:
      n: 4
quiz:
  - q: "What does the theorem say?"
    type: choice
    choices:
      - "`IsPolytope p → ∀ d, {f : Set E | IsFaceOf p f ∧ affDim f = d}.Finite`"
      - "`IsPolytope p → ∀ d, {f | IsFaceOf p f ∧ affDim f = d}.ncard ≤ 2 ^ d`"
      - "`IsPolytope p → {f | IsFaceOf p f}.Finite`"
      - "`IsPolytope p → ∀ d, (facesOfDim p d).Nonempty`"
    answer: 0
    explain: "`theorem facesOfDim_finite_of_isPolytope {p : Set E} (hP : IsPolytope p) (d : ℤ) : {f : Set E | IsFaceOf p f ∧ affDim f = d}.Finite := (faces_finite_of_isPolytope hP).subset fun _ hf => hf.1` (PolytopeFaces.lean). The third choice is the stronger lemma it is derived from."
  - q: "Why is finiteness needed at all, given that the Euler statements only mention `Set.ncard`?"
    type: choice
    choices:
      - "`Set.ncard` is `0` on an infinite set, so a statement about `ncard`s can be true and yet say nothing"
      - "`Set.ncard` is undefined on infinite sets"
      - "because `affDim` is noncomputable"
      - "it is not needed; it is a convenience"
    answer: 0
    explain: "Mathlib's `Set.ncard s = Nat.card s`, and `Nat.card` is `0` for an infinite type. So `V − E + F = 2` with infinitely many faces somewhere would be a statement about zeros. This theorem is what makes the counts mean counts — the honest reading of any `ncard` claim depends on it."
  - q: "What is the key geometric input to the proof?"
    type: choice
    choices:
      - "`face_eq_convexHull_inter`: a face of `convexHull ℝ V` is `convexHull ℝ (V ∩ F)`, so `F ↦ V ∩ F` is injective on faces"
      - "compactness of `p`"
      - "`IsPolytope.isPolyhedron`"
      - "that `p` has finitely many extreme points"
    answer: 0
    explain: "Per the module and `PLATONIC_CLAUDE_AUDIT.md`: a face of a V-polytope is the hull of the generators it contains, so distinct faces give distinct subsets of the finite `V`, and there are at most `2^|V|` of them. No halfspace presentation is needed."
  - q: "Which theorem opens by invoking this for `d = 0, 1, 2`?"
    type: choice
    choices:
      - "`Platonic.regular_polytope_counts`"
      - "`IsPolytope.isPolyhedron`"
      - "`affDim_univ`"
      - "`results_fan_pick_of_euler`"
    answer: 0
    explain: "`regular_polytope_counts` needs `(facesOfDim p d).Finite` for `d = 0, 1, 2` before it can double count, and its first three lines are exactly those three invocations — with the comment \"finiteness of each face set comes from the V-representation, not a hypothesis\"."
---

## Plain English

**Theorem.** A polytope has only finitely many faces of any given dimension.

```lean
theorem facesOfDim_finite_of_isPolytope {p : Set E} (hP : IsPolytope p) (d : ℤ) :
    {f : Set E | IsFaceOf p f ∧ affDim f = d}.Finite
```

Obvious? A cube has 8 vertices, 12 edges, 6 faces, and that is that. But the Lean statements count
with `Set.ncard`, and **Mathlib's `Set.ncard` is `0` on an infinite set.** So "`V − E + F = 2`"
would be perfectly provable, and perfectly meaningless, if some face set were infinite and quietly
reported `0`. This theorem closes that gap, and it is the reason you can read
[`results_euler_polyhedron`](#/node/Results.results_euler_polyhedron) as a statement about counts
rather than about `ncard`s.

### In one breath

A shape made by wrapping finitely many pins has only finitely many corners, edges and flat sides.
That has to be *said*, because of the way counting works in this system: ask how many things are in
an infinite collection and you are told "zero". A theorem that counts is only as good as its
promise that there was something finite to count.

### How

`PolytopeFaces.face_eq_convexHull_inter` does the work: if `p = convexHull ℝ V` and `F` is a face
of `p`, then

> `F = convexHull ℝ (V ∩ F)`.

A face is the hull of exactly the generators it happens to contain. So the map
`F ↦ V ∩ F` sends distinct faces to distinct subsets of `V`, which is finite — at most `2^|V|`
faces in all. Restrict to one dimension and you are done.

Notice what the proof does *not* need: no halfspace presentation, no compactness argument, no
dimension bound. It is the V-description doing the work.

### Where it sits

- [`Euler_Poincare_of_isPolytope`](#/node/Euler_Poincare_of_isPolytope) relies on it through
  `Euler_Poincare_full`, so every Euler count rests on it.
- [`Platonic.regular_polytope_counts`](#/node/Platonic.regular_polytope_counts) invokes it three
  times, for dimensions 0, 1 and 2, before the double counting — Mathlib's
  `Finset.card_mul_eq_card_mul` needs finite sets, and `ncard_mul_eq_ncard_mul` transports it to
  `Set.ncard` given exactly this.
- The README singles it out: "`facesOfDim_finite_of_isPolytope` supplies the geometric
  face-finiteness theorem."
