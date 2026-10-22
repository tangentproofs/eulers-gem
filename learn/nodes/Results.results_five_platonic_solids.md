---
id: Results.results_five_platonic_solids
title: "Five Schläfli pairs — which is not the same as five solids"
summary: "A combinatorially regular convex 3-polytope has `(s, m)` among five pairs, with Euler discharged from the root; plus the `(V,E,F,s,m)` of five numeric records. It does not construct the solids."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**The name oversells the statement.** Part 1 classifies *pairs of numbers* `(s, m)`. Parts 2–6 state the `(V,E,F,s,m)` of five `Platonic.RegularNumbers` records. No Platonic solid is constructed, and no uniqueness is proved. The repository's own `PLATONIC_CLAUDE_AUDIT.md` says in as many words: \"Not safe to name: 'the five Platonic solids' as a classification of geometric solids\"."
  - "**A polytope fact is assumed.** `hedge : ∀ e ∈ facesOfDim p 1, {f ∈ facesOfDim p 2 | e ⊆ f}.ncard = 2` — every edge lies in exactly two 2-faces, the *diamond property* — is a hypothesis of part 1, not derived from `IsPolytope`. It is not vacuous: the three solids this repository builds satisfy it. Deriving it in general needs vertex-figure theory, which is not formalized."
  - "**No metric content.** Regularity here is combinatorial: *how many* edges per face and per vertex. Equal edge lengths, equal angles, congruent faces and a flag-transitive symmetry group appear nowhere in this statement. (`MetricRegular.lean` does add genuine metric facts for the octahedron, the cube and a regular tetrahedron — but those are not in `Results`.)"
  - "**Two of the five do not exist here as solids.** `Platonic.dodecahedron` and `Platonic.icosahedron` are `RegularNumbers` records: five natural numbers satisfying Euler and two double-counting identities. Golden-ratio coordinates put their face lattices out of `decide`'s reach, and they are not attempted."
  - "Parts 2–6 are proved by `omega` from the structure fields of the records plus `rfl`. They are arithmetic about five constants."
widgets:
  - type: schlafli
    title: "(s − 2)(m − 2) < 4: the grid, and the solve"
  - type: polyhedron
    title: "The five, drawn — two of which the Lean never builds"
    config:
      preset: dodecahedron
      show: [counts, incidence]
quiz:
  - q: "Part 1 concludes `(s, m) ∈ Platonic.schlafliPairs`. What kind of object is that?"
    type: choice
    choices:
      - "a `Finset (ℕ × ℕ)` with five elements"
      - "a set of polytopes"
      - "a list of five constructions in ℝ³"
      - "a proposition"
    answer: 0
    explain: "`def schlafliPairs : Finset (ℕ × ℕ) := {(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)}` (Platonic.lean). Five pairs of natural numbers. Membership in it is the whole conclusion of part 1."
  - q: "Which of part 1's incidence hypotheses is a *polytope fact* rather than a regularity assumption?"
    type: choice
    choices:
      - "every 2-face has exactly `s` edges"
      - "exactly `m` edges meet at every vertex"
      - "every edge lies in exactly two 2-faces"
      - "`3 ≤ s` and `3 ≤ m`"
    answer: 2
    explain: "The first two *are* the regularity input and belong there. The third — the diamond property — is true of every convex 3-polytope but is **assumed** here rather than derived. `PlatonicOfEuler.lean` and `PLATONIC_CLAUDE_AUDIT.md` both flag it. (The fourth incidence count, two vertices per edge, *is* proved in general, by `EdgeVertices.ncard_vertices_of_edge`.)"
  - q: "Is `V − E + F = 2` a hypothesis of part 1?"
    type: choice
    choices:
      - "yes, as a bare numeric hypothesis"
      - "no: the proof obtains it from `results_euler_relation_dimension_three`"
      - "no: it is not used"
    answer: 1
    explain: "The proof's second line is `have hVEF := results_euler_relation_dimension_three hP hdim hEdim`. The repository's standing rule (`lean/UNIFIED_SPINE.md`) forbids a free `V − E + F = 2` as the only Euler input in a `Results` claim, and this is the lane where that rule is honoured."
  - q: "Do parts 2–6 construct the five solids?"
    type: choice
    choices:
      - "yes, all five"
      - "no: they state the `(V, E, F, s, m)` of five `RegularNumbers` records, proved by `omega` and `rfl`"
      - "yes, three of them"
    answer: 1
    explain: "Each part is an equation between a 5-tuple of record fields and a 5-tuple of numerals, e.g. `(Platonic.cube.V, …) = (8, 12, 6, 4, 3)`. A `RegularNumbers` carries five naturals and proofs of `s·F = 2E`, `m·V = 2E` and `V − E + F = 2`. It is Euler bookkeeping. (Three solids *are* built geometrically in this repository — just not in `Results`.)"
  - q: "For `(s, m) = (5, 3)`, solve `E·(2s + 2m − sm) = 2sm`. What is `E`?"
    type: number
    answer: 30
    explain: "`2·5 + 2·3 − 15 = 1`, so `E · 1 = 2 · 5 · 3 = 30`. Then `F = 2E/s = 12` and `V = 2E/m = 20` — the dodecahedron's numbers. `Platonic.mul_euler_int` is the identity; the Lean's classification does not actually need to solve it, since `sub_mul_lt_four` already pins the pair down."
  - q: "True or false: this theorem proves there are exactly five Platonic solids."
    type: choice
    choices:
      - "True"
      - "False — it proves five admissible `(s, m)` pairs, with the diamond property assumed, no metric regularity, no construction of two of the five, and no uniqueness"
    answer: 1
    explain: "False, and the repository's own audit says so. What is proved is the Schläfli-pair classification of combinatorially regular convex 3-polytopes (Euler discharged from the root, diamond property assumed) plus the numbers of five records. \"Exactly five solids up to similarity\" needs existence and uniqueness of a realization for each pair, neither of which is attempted."
---

## Plain English

The theorem is a conjunction of six parts. Part 1:

> Let `p` be a convex polytope of affine dimension 3, in a 3-dimensional real inner product space.
> Suppose `3 ≤ s`, `3 ≤ m`, and
>
> - every 2-face of `p` has exactly `s` edges,
> - every edge of `p` lies in exactly **two** 2-faces,
> - every vertex of `p` lies on exactly `m` edges.
>
> Then `(s, m)` is one of `(3,3)`, `(3,4)`, `(3,5)`, `(4,3)`, `(5,3)`.

Parts 2 through 6 each state five numbers:

```lean
(Platonic.tetrahedron.V, …E, …F, …s, …m) = (4, 6, 4, 3, 3)
(Platonic.cube.V,        …) = (8, 12, 6, 4, 3)
(Platonic.octahedron.V,  …) = (6, 12, 8, 3, 4)
(Platonic.dodecahedron.V,…) = (20, 30, 12, 5, 3)
(Platonic.icosahedron.V, …) = (12, 30, 20, 3, 5)
```

### In one breath

Suppose you want to tile a closed surface with identical regular tiles, the same number meeting at
every corner. Say each tile has `s` sides and `m` tiles meet at a corner. Count the edges twice,
once from the tiles and once from the corners, feed both counts into Euler's two, and out comes a
single inequality: `(s − 2)(m − 2) < 4`. Since `s` and `m` are at least three, that leaves five
possibilities and no others — triangles three to a corner, triangles four, triangles five, squares
three, pentagons three. Those are the tetrahedron, octahedron, icosahedron, cube and dodecahedron.
The ancient Greeks knew the five; Euler's formula is what tells you the list is complete.

## What this does and does not prove

**It does prove:**

- **The Schläfli-pair classification**, for convex 3-polytopes that are *combinatorially* regular:
  the only possible `(s, m)` are the five.
- **With Euler discharged.** The proof calls
  [`results_euler_relation_dimension_three`](#/node/Results.results_euler_relation_dimension_three)
  for `V − E + F = 2`, and
  [`Platonic.regular_polytope_counts`](#/node/Platonic.regular_polytope_counts) *proves*
  `s·F = 2E` and `m·V = 2E` by double counting over face-lattice incidence. No bare `V − E + F = 2`
  hypothesis appears.
- **The arithmetic of the five records.** Parts 2–6, by `omega` and `rfl`.

**It does not prove:**

- **"There are exactly five Platonic solids."** That claim has three parts — the list is complete,
  each entry is realized, and each is unique up to similarity — and only the first is here, and
  only in its combinatorial form.
- **Metric regularity.** No equal edge lengths, no equal angles, no congruent faces, no symmetry
  group. "Regular" in this statement means two incidence counts. A combinatorially-{4,3} polytope
  could be a squashed box. (`MetricRegular.lean` adds real metric content for the octahedron, the
  cube and a regular tetrahedron — all vertices on a sphere, all edges the same length — but none
  of that is in this statement.)
- **The diamond property.** `hedge` — every edge in exactly two 2-faces — is a **hypothesis**. It
  is true of every convex 3-polytope, and the repository proves it for the three solids it builds
  (`tetrahedron_incidence`, `octahedron_incidence`, `cube_incidence`), so part 1 is not vacuous.
  But deriving it from `IsPolytope` in general needs vertex-figure theory, which is not here.
- **Existence of the dodecahedron or the icosahedron.** Those two appear only as `RegularNumbers`
  records. Drawing them in the widget above is this website's doing, not the Lean's.
- **Uniqueness.** Nothing rules out two non-similar polytopes with the same `(s, m)`.

### The argument

Multiply `V − E + F = 2` by `s·m` and substitute the double counts (`Platonic.mul_euler_int`):

> `E · (2s + 2m − s·m) = 2·s·m`.

The right side is positive and `E > 0` (`Platonic.pos_edges_of_euler`, itself derived rather than
assumed), so `2s + 2m − s·m > 0`, which rearranges to
[`(s − 2)(m − 2) < 4`](#/node/Platonic.sub_mul_lt_four). With `s, m ≥ 3`, both factors are at least
1, so each is at most 3 and the case analysis is finite:
[`Platonic.schlafli_pair_mem`](#/node/Platonic.schlafli_pair_mem). The `schlafli` widget above shows
the grid of `(s−2)(m−2)` with the five survivors highlighted, and what goes wrong at `(4,4)` (the
coefficient is zero — that is the square tiling of the plane) and at `(4,5)` (negative — hyperbolic).

### Where it sits

- Uses [`results_euler_relation_dimension_three`](#/node/Results.results_euler_relation_dimension_three),
  [`IsPolytope.isPolyhedron`](#/node/IsPolytope.isPolyhedron),
  [`Platonic.regular_polytope_counts`](#/node/Platonic.regular_polytope_counts),
  [`Platonic.schlafli_pair_mem`](#/node/Platonic.schlafli_pair_mem),
  [`Platonic.RegularNumbers`](#/node/Platonic.RegularNumbers),
  [`Platonic.facesOfDim`](#/node/Platonic.facesOfDim).
- Not used by anything: it is a leaf of the development, and one of the nine `Results` theorems.
- [Trust](#/trust) has the one-row summary.
