---
id: Platonic.regular_polytope_counts
title: "Double counting on a real polytope, with Euler discharged"
summary: "For a convex 3-polytope with regular incidence counts, proves `s·F = 2E`, `m·V = 2E` and `V − E + F = 2`. The last is taken from the Euler root, not assumed — this is where the Platonic lane meets the geometry."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**`hedge_faces` is a hypothesis, and it is a polytope fact rather than a regularity assumption.** Every edge of a convex 3-polytope lies in exactly two 2-faces — the *diamond property* — and this theorem assumes it. The module docstring says so: \"One further incidence hypothesis is a *polytope fact* rather than regularity, and is assumed here rather than derived from the polytope structure.\" It is not vacuous: `tetrahedron_incidence`, `octahedron_incidence` and `cube_incidence` prove it for three of the solids, and `Platonic3.*_faceData` for all five constructed solids."
  - "By contrast the fourth incidence count — every edge has exactly two vertices — **is** derived in general, by `EdgeVertices.ncard_vertices_of_edge`. It used to be assumed too."
  - "It takes a halfspace presentation `hH`/`hp` as well as `hP : IsPolytope p`. The caller gets those from [IsPolytope.isPolyhedron](#/node/IsPolytope.isPolyhedron)."
  - "`hface_edges` and `hvert_edges` are *combinatorial* regularity: how many edges per 2-face and per vertex. Nothing metric — no equal lengths, no equal angles, no congruent faces."
widgets:
  - type: polyhedron
    title: "Check the incidence counts yourself: faces per edge, edges per vertex"
    config:
      preset: octahedron
      show: [counts, incidence]
quiz:
  - q: "Which three things does it conclude?"
    type: choice
    choices:
      - "`s * (facesOfDim p 2).ncard = 2 * (facesOfDim p 1).ncard`, `m * (facesOfDim p 0).ncard = 2 * (facesOfDim p 1).ncard`, and `V − E + F = 2`"
      - "`(s, m) ∈ schlafliPairs`"
      - "`(s−2)(m−2) < 4`"
      - "`0 < E`"
    answer: 0
    explain: "A three-way conjunction: the two double-counting identities and the Euler relation. The pair membership is [schlafli_pair_mem](#/node/Platonic.schlafli_pair_mem), one step further on."
  - q: "Where does `V − E + F = 2` come from in this proof?"
    type: choice
    choices:
      - "`euler_relation_convex_3polytope` — i.e. the Euler–Poincaré root — not a hypothesis"
      - "a hypothesis `hEuler`"
      - "`decide`"
      - "`RegularNumbers.hEuler`"
    answer: 0
    explain: "`PLATONIC_CLAUDE_AUDIT.md`: \"`V − E + F = 2` ← discharged from EP, NOT a hypothesis.\" This is the point of the whole module — `Platonic.lean` classifies pairs *given* Euler, and `PlatonicOfEuler.lean` removes that assumption for real polytopes."
  - q: "Which of the three incidence hypotheses is the diamond property, and is it proved in general here?"
    type: choice
    choices:
      - "`hedge_faces` (every edge in exactly two 2-faces) — assumed, not proved in general"
      - "`hface_edges` — proved from `IsPolytope`"
      - "`hvert_edges` — assumed"
      - "there is no such hypothesis"
    answer: 0
    explain: "`(hedge_faces : ∀ e ∈ facesOfDim p 1, {f ∈ facesOfDim p 2 | e ⊆ f}.ncard = 2)`. True of every convex 3-polytope; deriving it in general needs vertex-figure (quotient polytope) theory, which is not formalized here. `PLATONIC_CLAUDE_AUDIT.md` lists it as the one remaining hypothesis of the lane."
  - q: "Which incidence count *is* proved in general, and by what?"
    type: choice
    choices:
      - "every edge has exactly two vertices, by `EdgeVertices.ncard_vertices_of_edge`"
      - "every vertex has exactly three edges"
      - "every 2-face has exactly three edges"
      - "none of them"
    answer: 0
    explain: "`have hedge_verts : ∀ e ∈ facesOfDim p 1, {v ∈ facesOfDim p 0 | v ⊆ e}.ncard = 2 := fun e he => ncard_vertices_of_edge hP he.1 he.2`. The proof: a 1-dimensional face is a segment, a supporting functional along its direction is injective on it, so its extreme points are the argmin and argmax, and they differ."
  - q: "What supplies the finiteness that the double counting needs?"
    type: choice
    choices:
      - "`facesOfDim_finite_of_isPolytope`, invoked for `d = 0, 1, 2`"
      - "a hypothesis"
      - "compactness of `p`"
      - "`hH : H.Finite`"
    answer: 0
    explain: "The first three lines of the proof, with the comment \"finiteness of each face set comes from the V-representation, not a hypothesis\". `ncard_mul_eq_ncard_mul` transports Mathlib's `Finset.card_mul_eq_card_mul` to `Set.ncard` and needs both sets finite."
---

## Plain English

**Theorem.** Let `p` be a convex 3-polytope in a 3-dimensional real inner product space, presented
both by a finite halfspace list and as a finite convex hull. Suppose

- every 2-face has exactly `s` edges,
- every edge lies in exactly **two** 2-faces,
- every vertex lies on exactly `m` edges.

Then `s·F = 2E`, `m·V = 2E`, and `V − E + F = 2`.

This is where the Platonic lane touches the geometry. Everything after it
([`schlafli_pair_mem`](#/node/Platonic.schlafli_pair_mem),
[`sub_mul_lt_four`](#/node/Platonic.sub_mul_lt_four)) is arithmetic about numbers; everything before
it is the Euler root. This theorem converts between them.

### In one breath

Count the edges of a solid in two different ways. Walk round every face and count its edges —
that counts every edge twice, once from each side. Now walk round every corner and count the edges
there — that counts every edge twice too, once from each end. If every face has the same number of
edges and every corner the same number, both counts become multiplication, and you get two
equations. Add Euler's two, which you already have, and the arithmetic takes over.

### Why it matters that Euler is discharged here

The repository has a hard rule (`lean/UNIFIED_SPINE.md`):

> Platonic and Pick **discharge** Euler from the EP root (or a lemma derived from it).
> Forbidden: free `ℤ` hypothesis `V−E+F=2` as the only Euler input in a final Results claim.

`Platonic.lean` alone would violate it: [`RegularNumbers`](#/node/Platonic.RegularNumbers) carries
`hEuler` as a field, so building one by hand assumes Euler. This theorem is the fix. Its proof
calls `euler_relation_convex_3polytope` — the geometric relation, from
[`Euler_Poincare_full`](#/node/Euler_Poincare_of_isPolytope) — and so the `RegularNumbers` that
[`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids) assembles has every
field backed by a theorem about the actual polytope.

### What is still assumed

One thing: **`hedge_faces`**, that every edge lies in exactly two 2-faces. That is true of every
convex 3-polytope. It is not proved here, because the general proof needs the theory of vertex
figures / quotient polytopes, and that is not formalized.

It is not vacuous — the solids this repository builds all satisfy it, proved
(`tetrahedron_incidence`, `octahedron_incidence`, `cube_incidence`, and `Platonic3.*_faceData` for all
five). And the fourth incidence
count, two vertices per edge, used to be assumed alongside it and now is not:
`EdgeVertices.ncard_vertices_of_edge` proves it in general. So one hypothesis down, one to go.

The widget above lets you check the diamond property on each preset — including the toroidal one,
where it still holds, which is a reminder that it is a local condition and not a substitute for
convexity.

### The double counting itself

`ncard_mul_eq_ncard_mul` is Mathlib's `Finset.card_mul_eq_card_mul` transported to `Set.ncard`: if
every `a ∈ A` relates to exactly `m` elements of `B`, and every `b ∈ B` to exactly `n` of `A`, then
`|A|·m = |B|·n`. Apply it twice:

- with `A = facesOfDim p 2`, `B = facesOfDim p 1`, relation `e ⊆ f`: `F·s = E·2`;
- with `A = facesOfDim p 0`, `B = facesOfDim p 1`, relation `v ⊆ e`: `V·m = E·2`.

Both need the sets finite, which is
[`facesOfDim_finite_of_isPolytope`](#/node/facesOfDim_finite_of_isPolytope).

### Where it sits

- Below: [`facesOfDim`](#/node/Platonic.facesOfDim),
  [`facesOfDim_finite_of_isPolytope`](#/node/facesOfDim_finite_of_isPolytope),
  `EdgeVertices.ncard_vertices_of_edge`, and the Euler root.
- Above: [`schlafli_pair_mem`](#/node/Platonic.schlafli_pair_mem) and
  [`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids).
