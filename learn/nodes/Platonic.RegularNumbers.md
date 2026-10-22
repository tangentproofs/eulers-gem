---
id: Platonic.RegularNumbers
title: "RegularNumbers: five numbers with three identities"
summary: "A structure holding `V, E, F, s, m : ℕ` together with proofs of `s·F = 2E`, `m·V = 2E` and `V − E + F = 2`. It is bookkeeping about numbers — no polytope is involved."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**This structure contains no geometry whatsoever.** It has five natural numbers and four proof fields. `Platonic.dodecahedron` and `Platonic.icosahedron` are *instances of this structure* and nothing more: the repository does not construct those solids."
  - "The `hEuler` field is a plain numeric equation, so constructing a `RegularNumbers` by hand assumes Euler rather than proving it. The repository's rule against that (`lean/UNIFIED_SPINE.md`) is honoured by never assuming it at the top: [regular_polytope_counts](#/node/Platonic.regular_polytope_counts) *derives* all three identities for a real polytope and then feeds them in."
  - "`hE : 0 < E` is a field, but it is derivable from the others plus `3 ≤ s, m` — `Platonic.pos_edges_of_euler` does exactly that, so a caller with a real polytope does not have to assume it."
widgets:
  - type: schlafli
    title: "The identities, and the five pairs they allow"
quiz:
  - q: "Which fields does `RegularNumbers` carry?"
    type: choice
    choices:
      - "`V E F s m : ℕ` plus `hs : 3 ≤ s`, `hm : 3 ≤ m`, `hE : 0 < E`, `hFace : s * F = 2 * E`, `hVert : m * V = 2 * E`, `hEuler : (V : ℤ) - E + F = 2`"
      - "a set `p : Set E` and its face counts"
      - "`V E F : ℕ` only"
      - "a polytope and a proof that it is regular"
    answer: 0
    explain: "Exactly that list, in `Platonic.lean`. Five numbers and five proofs, none of them geometric."
  - q: "`Platonic.dodecahedron` is what sort of object?"
    type: choice
    choices:
      - "a `RegularNumbers` with `V = 20, E = 30, F = 12, s = 5, m = 3`, each proof field by `decide`"
      - "a subset of ℝ³"
      - "a theorem"
      - "an `AffineBasis`"
    answer: 0
    explain: "`def dodecahedron : RegularNumbers where V := 20; E := 30; F := 12; s := 5; m := 3; hs := by decide; …`. Five numerals. No dodecahedron exists in this repository as a geometric object — `PLATONIC_CLAUDE_AUDIT.md` lists that as open, since golden-ratio coordinates put the face lattice beyond `decide`."
  - q: "Which three of the five solids *are* built geometrically somewhere in the repository?"
    type: choice
    choices:
      - "tetrahedron, octahedron, cube"
      - "tetrahedron, cube, dodecahedron"
      - "all five"
      - "none"
    answer: 0
    explain: "`Simplex.tetrahedron_platonic` (`GeometricPlatonic.lean`, via `SimplexFaces.lean`), `Octahedron.octahedron_platonic` and `Cube.cube_platonic` — each with its geometric face lattice computed, all four incidence counts proved, and `V − E + F = 2` obtained from Euler–Poincaré. None of them is in `Results.lean`, though."
  - q: "`hEuler` as a field means that constructing a `RegularNumbers` by hand…"
    type: choice
    choices:
      - "assumes Euler's formula rather than proving it"
      - "proves Euler's formula"
      - "is impossible"
    answer: 0
    explain: "It is a hypothesis of the constructor. That is fine for the five records (where it is `by decide` on numerals) and would be dishonest at the top of a classification, which is why `regular_polytope_counts` derives it from [results_euler_relation_dimension_three](#/node/Results.results_euler_relation_dimension_three) before building the structure."
---

## Plain English

```lean
structure RegularNumbers where
  V : ℕ
  E : ℕ
  F : ℕ
  s : ℕ
  m : ℕ
  hs : 3 ≤ s
  hm : 3 ≤ m
  hE : 0 < E
  hFace : s * F = 2 * E
  hVert : m * V = 2 * E
  hEuler : (V : ℤ) - E + F = 2
```

Five numbers, and four conditions on them:

- `s ≥ 3`, `m ≥ 3`: faces have at least three sides, vertices at least three edges;
- `s·F = 2E`: count the (face, edge-on-that-face) pairs two ways — `s` per face, 2 per edge;
- `m·V = 2E`: same for (vertex, edge-at-that-vertex) pairs — `m` per vertex, 2 per edge;
- `V − E + F = 2`: Euler.

**There is no polytope here.** A `RegularNumbers` is a tuple of numbers with certificates. That is
deliberate, and it is worth being clear-eyed about: the five famous names in this namespace are
instances of this structure, not solids.

### In one breath

Write down five numbers: how many corners, how many edges, how many faces, how many sides each
face has, and how many edges meet at each corner. Promise three things about them: edges counted
through the faces comes out double, edges counted through the corners comes out double, and
corners minus edges plus faces is two. That bundle of five numbers and three promises is the
object. It is not a shape, and nothing here says a shape with those numbers exists.

### Why it is stated this way

Two reasons, one good and one historical.

The good reason: the Schläfli classification is genuinely an argument about numbers.
[`mul_euler_int`](#/node/Platonic.sub_mul_lt_four) multiplies `hEuler` by `s·m`, substitutes the two
double-counting identities, and arrives at `E·(2s + 2m − s·m) = 2sm`. Nothing geometric is used,
so stating it over a numeric structure is honest and keeps the arithmetic separable from the
geometry.

The historical reason: `Platonic.lean` was written before the Euler root was available, and at that
point `hEuler` *was* an assumption at the top. `PlatonicOfEuler.lean` fixed that. As
`PLATONIC_CLAUDE_AUDIT.md` puts it: "The old `Platonic.RegularNumbers` structure still has such a
field, but it is now *constructed* from EP inside
`schlafli_pair_mem_of_regular_polytope`, never assumed at the top."

So in [`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids) part 1, the
`RegularNumbers` that gets built looks like this:

```lean
{ V := (facesOfDim p 0).ncard
  E := (facesOfDim p 1).ncard
  F := (facesOfDim p 2).ncard
  s := s, m := m, hs := hs, hm := hm
  hE := Platonic.pos_edges_of_euler hs hm hFace hVert hEuler
  hFace := hFace, hVert := hVert, hEuler := hEuler }
```

Every proof field comes from a theorem about the actual polytope. The structure is a convenient
package, not a source of assumptions.

### The five records

| | V | E | F | s | m |
|---|---:|---:|---:|---:|---:|
| `tetrahedron` | 4 | 6 | 4 | 3 | 3 |
| `octahedron` | 6 | 12 | 8 | 3 | 4 |
| `icosahedron` | 12 | 30 | 20 | 3 | 5 |
| `cube` | 8 | 12 | 6 | 4 | 3 |
| `dodecahedron` | 20 | 30 | 12 | 5 | 3 |

Each field is `by decide`. `exists_regularNumbers_of_mem_schlafli` says every one of the
[five pairs](#/node/Platonic.schlafliPairs) is realized *by such a record* — which establishes that
the classification is not vacuous as a statement about numbers, and says nothing about solids.

### Where it sits

- [`mul_euler_int`](#/node/Platonic.sub_mul_lt_four),
  [`sub_mul_lt_four`](#/node/Platonic.sub_mul_lt_four) and
  [`schlafli_pair_mem`](#/node/Platonic.schlafli_pair_mem) all take one of these.
- [`regular_polytope_counts`](#/node/Platonic.regular_polytope_counts) produces the ingredients for
  one, from a real polytope.
- [`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids) parts 2–6 are
  statements about the five records above, and nothing else.
