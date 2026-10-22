---
id: euler_relation_of_isPolytope
title: "V − E + F = 2 in any 3-dimensional space"
summary: "For a polytope with `affDim p = 3` in a real inner product space of dimension 3, the geometric face counts satisfy `V − E + F = 2`. The step from the characteristic is one line of bookkeeping."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "Two separate hypotheses look like one: `affDim p = 3` (the polytope is 3-dimensional) and `Module.finrank ℝ E = 3` (the room is). Both are needed — the first because a flat polytope would have a different face lattice, the second because the proof route homogenizes in `E × ℝ`."
  - "`V`, `E` and `F` are `Set.ncard`s of face sets, cast to `ℤ`. They are counts only because `facesOfDim_finite_of_isPolytope` says the sets are finite."
  - "Convexity is not optional. The toroidal picture-frame polyhedron has `V − E + F = 0`; it is not an `IsPolytope`, and this theorem makes no claim about it. Nor does it say anything about graphs drawn on a sphere, maps on surfaces, or a genus formula."
widgets:
  - type: polyhedron
    title: "Convex, and one that is not"
    config:
      preset: dodecahedron
      show: [counts, incidence, truncate]
quiz:
  - q: "How many hypotheses about dimension does the statement have?"
    type: choice
    choices:
      - "one: `affDim p = 3`"
      - "two: `affDim p = 3` and `Module.finrank ℝ E = 3`"
      - "none; the `3` is in the conclusion"
      - "three"
    answer: 1
    explain: "`theorem euler_relation_of_isPolytope {p : Set E} (hp : IsPolytope p) (hdim : affDim p = 3) (hE : Module.finrank ℝ E = 3)` (UnconditionalEuler.lean). The polytope is 3-dimensional *and* so is the ambient space."
  - q: "What exactly are `V`, `E` and `F` in the conclusion?"
    type: choice
    choices:
      - "`{f | IsFaceOf p f ∧ affDim f = d}.ncard` for `d = 0, 1, 2`, cast to `ℤ`"
      - "parameters of the theorem"
      - "the number of elements of the generating set `V` from `IsPolytope`"
      - "counts of faces of a combinatorial complex built from `p`"
    answer: 0
    explain: "The conclusion is written out in full: `({f : Set E | IsFaceOf p f ∧ affDim f = 0}.ncard : ℤ) - (… = 1 …) + (… = 2 …) = 2`. Geometric face sets, nothing combinatorial in between."
  - q: "Where does the `2` come from, given that the characteristic is `1`?"
    type: choice
    choices:
      - "a 3-dimensional polytope has exactly one face of `affDim 3` — itself — contributing `(-1)^3 · 1 = -1`, so `V − E + F − 1 = 1`"
      - "the empty face contributes `+1`"
      - "two of the terms cancel"
      - "it is a different theorem with a different proof"
    answer: 0
    explain: "`faceEulerSum p 3 = f₀ − f₁ + f₂ − f₃` and `f₃ = 1` by `isFaceOf_refl` plus the fact that `p` is the only 3-dimensional face. Move the `−1` across: `V − E + F = 1 + 1 = 2`. The expansion lemma is the private `faceEulerSum_three_expand` in `EulerPoincare.lean`."
  - q: "Does the theorem apply to a non-convex polyhedron with a hole, like a picture frame?"
    type: choice
    choices: ["yes", "no — `IsPolytope` fails for it, and in fact `V − E + F = 0` there"]
    answer: 1
    explain: "`IsPolytope` means \"convex hull of a finite set\", so every `IsPolytope` is convex. The picture frame is not, and its alternating sum is `16 − 32 + 16 = 0`. Euler's formula is a theorem about *convex* polyhedra, and this statement is honest about that through its hypothesis."
  - q: "Compute `V − E + F` for the icosahedron (`V = 12`, `E = 30`, `F = 20`)."
    type: number
    answer: 2
    explain: "`12 − 30 + 20 = 2`. Note that the Lean does *not* build an icosahedron: `Platonic.icosahedron` is a `RegularNumbers` record holding these three numbers, and no geometric icosahedron exists in this repository. This theorem would apply to one if someone constructed it."
---

## Plain English

**Theorem.** A convex polytope that is 3-dimensional, sitting in a 3-dimensional real inner product
space, satisfies

> `V − E + F = 2`,

where `V`, `E` and `F` are the numbers of faces of affine dimension 0, 1 and 2.

```lean
theorem euler_relation_of_isPolytope {p : Set E} (hp : IsPolytope p)
    (hdim : affDim p = 3) (hE : Module.finrank ℝ E = 3) :
    ({f : Set E | IsFaceOf p f ∧ affDim f = 0}.ncard : ℤ) -
      ({f : Set E | IsFaceOf p f ∧ affDim f = 1}.ncard : ℤ) +
      ({f : Set E | IsFaceOf p f ∧ affDim f = 2}.ncard : ℤ) = 2
```

This **is** Euler's polyhedron formula, for convex polyhedra. Freek Wiedijk's problem #13. The
counts are the honest geometric ones — the face sets themselves, by
[`IsFaceOf`](#/node/IsFaceOf) and [`affDim`](#/node/affDim), with no combinatorial surrogate in
between.

### In one breath

Take anything you could carve from a solid block without hollowing it out or making it dented: a
die, a pyramid, a crystal, a football. Count its corners. Count its edges. Count its flat sides.
Corners minus edges plus sides is two. Always two. A die: eight minus twelve plus six. A pyramid on
a square base: five minus eight plus five. A football cut to flat panels: still two. Euler noticed
it in 1750 and could not quite prove it; this file is a machine-checked proof of it, and the one
thing it insists on is that the solid be convex — no holes, no dents.

### The one-line step from the root

[`Euler_Poincare_of_isPolytope`](#/node/Euler_Poincare_of_isPolytope) gives
[`faceEulerSum p 3 = 1`](#/node/faceEulerSum), which spelled out is

> `f₀ − f₁ + f₂ − f₃ = 1`.

A 3-dimensional polytope has exactly one face of dimension 3: itself (`isFaceOf_refl`; any proper
face has strictly smaller span). So `f₃ = 1`, and

> `V − E + F = 1 + 1 = 2`.

That is the whole difference between the two statements. `faceEulerSum_three_expand` does the
expansion, `euler_relation_convex_3polytope` (`Embed.lean`) does the arithmetic, and this
declaration discharges the halfspace presentation with
[`IsPolytope.isPolyhedron`](#/node/IsPolytope.isPolyhedron).

### What convexity buys, and what it costs

Try the picture-frame preset in the widget above: a square slab with a square hole, 16 vertices, 32
edges, 16 faces, `V − E + F = 0`. It is a perfectly good polyhedron in the everyday sense. It is
not convex, so it is not the convex hull of its vertices, so `IsPolytope` is false for it, so this
theorem is silent about it — correctly.

The general statement for surfaces is `V − E + F = 2 − 2g` with `g` the genus, and **none of that
is in this repository.** No genus, no surfaces, no non-convex polyhedra. What is here is the convex
case, which is the case Euler and Lawrence were after.

### Where it sits

- From: [`Euler_Poincare_of_isPolytope`](#/node/Euler_Poincare_of_isPolytope).
- Restated as: [`results_euler_relation_dimension_three`](#/node/Results.results_euler_relation_dimension_three),
  and specialized to `EuclideanSpace ℝ (Fin 3)` as
  [`euler_polyhedron`](#/node/euler_polyhedron) /
  [`results_euler_polyhedron`](#/node/Results.results_euler_polyhedron).
- Used by: [`Platonic.regular_polytope_counts`](#/node/Platonic.regular_polytope_counts), which is
  how the Schläfli classification gets its Euler input without assuming it.
