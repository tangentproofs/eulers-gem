---
id: Platonic.schlafliPairs
title: "schlafliPairs: five pairs of numbers"
summary: "`{(3,3), (3,4), (3,5), (4,3), (5,3)} : Finset (ℕ × ℕ)` — the five admissible Schläfli symbols, as a finite set of number pairs."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "A `Finset (ℕ × ℕ)`. It is a list of five pairs of naturals, nothing more. Membership in it is the conclusion of the classification; it is not a set of solids, or of polytopes, or of anything geometric."
  - "`card_schlafliPairs : schlafliPairs.card = 5` is proved `by decide`. The `AXIOM_AUDIT.md` notes that this was once a `native_decide` and was changed to plain `decide` so that the kernel checks it."
widgets:
  - type: schlafli
    title: "Why these five and no others"
quiz:
  - q: "What type is `schlafliPairs`?"
    type: choice
    choices: ["`Finset (ℕ × ℕ)`", "`Set (Set E)`", "`List (ℕ × ℕ)`", "`Finset RegularNumbers`"]
    answer: 0
    explain: "`def schlafliPairs : Finset (ℕ × ℕ) := {(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)}` (Platonic.lean). Pairs of natural numbers."
  - q: "`(4, 4)` — the square tiling of the plane. Why is it not in the set?"
    type: choice
    choices:
      - "`(4−2)(4−2) = 4`, not `< 4`; equivalently `2s + 2m − sm = 0`, so `E · 0 = 32` is impossible"
      - "because squares cannot meet four to a vertex"
      - "because `s = m` is excluded"
      - "it is in the set"
    answer: 0
    explain: "`sub_mul_lt_four` gives the strict bound `(s−2)(m−2) < 4`, and `(4,4)` sits exactly at 4. The identity `E·(2s + 2m − sm) = 2sm` becomes `E · 0 = 32`. Geometrically: `{4,4}` tiles the flat plane, which has infinitely many faces, so no finite `E` exists."
  - q: "`(3, 6)` and `(6, 3)` — are they in?"
    type: choice
    choices: ["no: `(3−2)(6−2) = 4`, again exactly at the bound", "yes", "only `(6,3)`"]
    answer: 0
    explain: "`1 · 4 = 4`, not `< 4`. These are the triangular and hexagonal tilings of the plane. All three flat tilings sit precisely on the boundary of the inequality, which is what makes `sub_mul_lt_four` strict and why it is exactly the right bound."
  - q: "Which pair corresponds to the cube?"
    type: choice
    choices: ["`(4, 3)`", "`(3, 4)`", "`(4, 4)`", "`(3, 3)`"]
    answer: 0
    explain: "`s = 4` (square faces), `m = 3` (three faces at each corner), so `{4,3}`. `(3,4)` is its dual, the octahedron: triangular faces, four at each vertex. The Schläfli symbol is written `{s, m}`, faces first."
  - q: "`schlafliPairs.card = 5` is proved how?"
    type: choice
    choices:
      - "`by decide` — and `AXIOM_AUDIT.md` records that it was deliberately changed from `native_decide` so the kernel checks it"
      - "`by norm_num`"
      - "`by native_decide`"
      - "by hand, element by element"
    answer: 0
    explain: "`theorem card_schlafliPairs : schlafliPairs.card = 5 := by decide`. `native_decide` adds an axiom asserting the compiler's evaluation, which the repository's standing bar rejects; `AXIOM_AUDIT.md` lists this as one of the places it was removed."
---

## Plain English

```lean
def schlafliPairs : Finset (ℕ × ℕ) := {(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)}
```

Five pairs of numbers. In a pair `(s, m)`, `s` is how many edges each face has and `m` is how many
edges meet at each vertex — the **Schläfli symbol** `{s, m}`.

| pair | faces are | at each vertex | classically |
|---|---|---|---|
| `(3,3)` | triangles | 3 | tetrahedron |
| `(3,4)` | triangles | 4 | octahedron |
| `(3,5)` | triangles | 5 | icosahedron |
| `(4,3)` | squares | 3 | cube |
| `(5,3)` | pentagons | 3 | dodecahedron |

The last column is **not** in the Lean. `schlafliPairs` is a set of ten natural numbers arranged
in five pairs. That the pairs correspond to those five solids is classical mathematics, and this
repository constructs three of the five (the tetrahedron, octahedron and cube, in
`GeometricPlatonic.lean`, `Octahedron.lean` and `Cube.lean`) and not the other two.

### In one breath

Five little pairs of numbers: three-three, three-four, three-five, four-three, five-three. Each
says "a face has this many sides, and this many faces meet at a corner". Those five are the only
combinations that can close up into a finite solid, and the reason is Euler's formula. The list is
short, it is complete, and that completeness is the theorem.

### Why exactly these

Because of the strict inequality `(s − 2)(m − 2) < 4`
([`sub_mul_lt_four`](#/node/Platonic.sub_mul_lt_four)), with `s, m ≥ 3`. Write `a = s − 2`,
`b = m − 2`, both at least 1. Then `ab < 4`, so `a ≤ 3` and `b ≤ 3`, and the only possibilities are

> `(a,b) ∈ {(1,1), (1,2), (1,3), (2,1), (3,1)}`

which is the five pairs. `schlafli_of_bounds` does that case analysis with `interval_cases` and
`omega`.

What is striking is how tight the bound is. The three cases with `(s−2)(m−2) = 4` exactly —
`{4,4}`, `{3,6}`, `{6,3}` — are the three tilings of the flat plane. Everything above 4 is a
hyperbolic tiling. The five spherical cases, the three flat ones, and infinitely many hyperbolic
ones, separated by one strict inequality. The `schlafli` widget above draws that grid.

### Where it sits

- Produced by [`schlafli_pair_mem`](#/node/Platonic.schlafli_pair_mem), from a
  [`RegularNumbers`](#/node/Platonic.RegularNumbers).
- `exists_regularNumbers_of_mem_schlafli` shows every pair is realized by a numeric record;
  `five_schlafli_pairs` and `exactly_five_platonic_schlafli` package that with the cardinality.
- It is the conclusion of part 1 of
  [`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids).
