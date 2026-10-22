---
id: Platonic.dodecahedron
title: "Platonic.dodecahedron: twenty, thirty, twelve — the record, not the solid"
summary: "A `RegularNumbers` record with `V = 20, E = 30, F = 12, s = 5, m = 3`. The geometric dodecahedron is a different declaration, `Platonic3.dodecahedron`, built from golden-ratio coordinates and proved regular."
review: draft
authors: ["claude (for @tangentstorm)", "Grok Bot (for @tangentstorm)"]
caveats:
  - "**This declaration is five natural numbers.** It is not a subset of ℝ³ and carries no face lattice. The same goes for `Platonic.icosahedron`."
  - "A geometric dodecahedron **does** exist in the repository, under another name: `Platonic3.dodecahedron` (`EulersGem/PlatonicSolids.lean`), the convex hull of `(±1, ±1, ±1)` and the cyclic permutations of `(0, ±φ⁻¹, ±φ)`, proved to be a flag-transitive regular polyhedron with `V = 20, E = 30, F = 12` in [`results_five_platonic_solids_constructed`](#/node/Results.results_five_platonic_solids_constructed). That theorem does not mention this record."
  - "The picture the widget draws is this website's doing. It is a correct picture of a dodecahedron, and it is not evidence of anything in the Lean."
widgets:
  - type: polyhedron
    title: "A dodecahedron — the record's numbers, and the shape `Platonic3.dodecahedron` builds"
    config:
      preset: dodecahedron
      show: [counts, incidence]
quiz:
  - q: "What kind of object is `Platonic.dodecahedron`?"
    type: choice
    choices:
      - "a `RegularNumbers` record: `V = 20, E = 30, F = 12, s = 5, m = 3`, every field `by decide`"
      - "a convex polytope in `EuclideanSpace ℝ (Fin 3)`"
      - "a theorem that a dodecahedron exists"
      - "a `Finset` of 20 points"
    answer: 0
    explain: "Five numerals with five `by decide` certificates. No geometry. The geometric solid is the different declaration `Platonic3.dodecahedron : Set R3`."
  - q: "Does this repository construct a geometric dodecahedron?"
    type: choice
    choices:
      - "yes — `Platonic3.dodecahedron` in `PlatonicSolids.lean`, proved regular in `results_five_platonic_solids_constructed`; but not via this record"
      - "no"
      - "yes, in `Cube.lean`"
      - "yes, but only its Euler relation"
    answer: 0
    explain: "The face lattice is checked by `decide +kernel` over exact `ℤ[φ]` arithmetic (`ZPhi.lean`, `ExplicitPolyhedron.lean`), and flag-transitivity by three explicit reflections (`ExplicitRegular.lean`)."
  - q: "Verify `hFace : s * F = 2 * E` for these numbers."
    type: choice
    choices: ["`5 · 12 = 60 = 2 · 30` ✓", "`5 · 12 = 60 ≠ 2 · 30`", "`3 · 12 = 2 · 30`"]
    answer: 0
    explain: "Twelve pentagons, five edges each, every edge shared by two faces: `60 = 60`. And `hVert : 3 · 20 = 60 = 2 · 30`. And `hEuler : 20 − 30 + 12 = 2`."
  - q: "Solve `E · (2s + 2m − sm) = 2sm` for `(s,m) = (5,3)`."
    type: number
    answer: 30
    explain: "`2·5 + 2·3 − 15 = 1`, so `E · 1 = 30`. Then `F = 2E/s = 12` and `V = 2E/m = 20` — which is where the record's numbers come from. [mul_euler_int](#/node/Platonic.sub_mul_lt_four) is that identity."
  - q: "How does the Lean settle the geometric dodecahedron's face lattice, given that `φ` is irrational?"
    type: choice
    choices:
      - "exact arithmetic in `ℤ[φ]` (pairs `a + bφ` with `φ² = φ + 1`), with a kernel-checked sign test, plus certificates for every triple and pair of vertices"
      - "floating point"
      - "it is assumed"
      - "a new axiom"
    answer: 0
    explain: "`ZPhi.sgn` decides the sign of `a + bφ` exactly (`2(a + bφ) = (2a + b) + b√5`), with soundness lemmas `sgn_eq_one` etc. `Explicit.Data.face_cases` turns the kernel's `checkAll = true` into the complete face list."
---

## Plain English

```lean
/-- Dodecahedron `{5,3}`: `V=20, E=30, F=12`. -/
def dodecahedron : RegularNumbers where
  V := 20; E := 30; F := 12; s := 5; m := 3
  hs := by decide
  hm := by decide
  hE := by decide
  hFace := by decide
  hVert := by decide
  hEuler := by decide
```

Twenty, thirty, twelve, five, three. Plus five proofs by `decide` that those numbers satisfy the
double-counting identities and Euler's relation.

**This record is not a dodecahedron.** It is a census of one. The solid itself is a different
declaration, `Platonic3.dodecahedron`, a convex hull of twenty explicit points in ℝ³.

### In one breath

Twenty corners, thirty edges, twelve pentagonal faces, written down as numbers that are consistent
with Euler's count. The actual solid is built elsewhere in the repository, from the golden ratio.

### The geometric one

| solid | coordinates | how the face lattice is settled |
|---|---|---|
| `Platonic3.dodecahedron` | `(±1,±1,±1)` and cyclic `(0, ±φ⁻¹, ±φ)` | `decide +kernel` over exact `ℤ[φ]`: every vertex triple's plane separates or is a listed facet; every non-edge pair has a certificate |
| `Platonic3.icosahedron` | cyclic `(0, ±1, ±φ)` | the same |

Both are proved flag-transitive: three explicit reflections, with a checked word in them carrying a
base flag to each of the 120 flags.

### What this means for the headline claim

[`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids) proves the Schläfli
pair `(5,3)` is admissible, and separately states these five numbers. Existence of the solid is the
separate [`results_five_platonic_solids_constructed`](#/node/Results.results_five_platonic_solids_constructed).
Uniqueness up to similarity is only conditional:
[`results_regular_polyhedron_face_data`](#/node/Results.results_regular_polyhedron_face_data).

### Where it sits

- An instance of [`RegularNumbers`](#/node/Platonic.RegularNumbers).
- Part 5 of [`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids).
- The witness for `(5,3)` in `exists_regularNumbers_of_mem_schlafli`.
- Compare [`Platonic.tetrahedron`](#/node/Platonic.tetrahedron), which is also just a record.
