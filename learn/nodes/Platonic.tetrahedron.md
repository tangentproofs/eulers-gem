---
id: Platonic.tetrahedron
title: "Platonic.tetrahedron: five numbers called a tetrahedron"
summary: "A `RegularNumbers` record with `V = 4, E = 6, F = 4, s = 3, m = 3`, every proof field `by decide`. It is not a tetrahedron — but unlike two of its siblings, a geometric one does exist elsewhere in the repository."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**This definition is not a geometric object.** It is five natural numbers with certificates. The name is a label."
  - "A *geometric* tetrahedron does exist in this repository, elsewhere: `SimplexFaces.lean` computes the face lattice of a simplex and `GeometricPlatonic.tetrahedron_platonic` proves a geometric tetrahedron is `{3,3}` with Euler from the root. `MetricRegular.Cube.regularTetra` goes further and builds a genuinely *regular* tetrahedron (four pairwise-equidistant alternating cube corners). None of that is in `Results.lean`."
  - "The same pattern holds for `Platonic.octahedron` and `Platonic.cube` (geometric versions in `Octahedron.lean` and `Cube.lean`). It does **not** hold for `Platonic.dodecahedron` and `Platonic.icosahedron`, which exist only as records."
widgets:
  - type: polyhedron
    title: "A real tetrahedron, drawn here but not in the Lean's Results"
    config:
      preset: tetrahedron
      show: [counts, incidence, truncate]
quiz:
  - q: "What kind of object is `Platonic.tetrahedron`?"
    type: choice
    choices:
      - "a `RegularNumbers` — five naturals plus five proof fields"
      - "a `Set (EuclideanSpace ℝ (Fin 3))`"
      - "an `AffineBasis (Fin 4) ℝ E`"
      - "a theorem"
    answer: 0
    explain: "`def tetrahedron : RegularNumbers where V := 4; E := 6; F := 4; s := 3; m := 3; hs := by decide; …`. Five numerals. No point of space appears anywhere in it."
  - q: "`4 − 6 + 4`. What is it, and which field asserts it?"
    type: choice
    choices:
      - "`2`, asserted by `hEuler`, discharged `by decide`"
      - "`2`, derived from `hFace` and `hVert`"
      - "`1`, asserted by `hEuler`"
      - "`2`, proved from `results_euler_polyhedron`"
    answer: 0
    explain: "`hEuler : (V : ℤ) - E + F = 2` is a field of [RegularNumbers](#/node/Platonic.RegularNumbers), and here it is `by decide` on numerals. For a *real* polytope it is instead derived from the Euler root, by [regular_polytope_counts](#/node/Platonic.regular_polytope_counts)."
  - q: "Check `hFace : s * F = 2 * E` for the tetrahedron."
    type: choice
    choices: ["`3 · 4 = 12 = 2 · 6` ✓", "`3 · 4 = 12 ≠ 2 · 6`", "`4 · 4 = 2 · 6`"]
    answer: 0
    explain: "Four triangular faces, three edges each, every edge shared by two faces: `12 = 12`. `hVert : m * V = 2 * E` is `3 · 4 = 12 = 2 · 6` as well, since the tetrahedron is self-dual."
  - q: "Does this repository construct a geometric tetrahedron anywhere?"
    type: choice
    choices:
      - "yes — `GeometricPlatonic.tetrahedron_platonic`, with its face lattice from `SimplexFaces.lean` and Euler from the root, and a metrically regular one in `MetricRegular.lean`"
      - "no"
      - "yes, but only in `Results.lean`"
    answer: 0
    explain: "`PLATONIC_CLAUDE_AUDIT.md` tabulates it: geometric face counts `V=4, E=6, F=4` (`tetrahedron_face_counts`), `V − E + F = 2` from Euler–Poincaré (`tetrahedron_euler_relation`), all four incidence counts (`tetrahedron_incidence`), and `{3,3}` membership (`tetrahedron_platonic`). It is simply not exported through `Results.lean`."
  - q: "Which two of the five solids have **no** geometric construction in this repository?"
    type: choice
    choices:
      - "the dodecahedron and the icosahedron"
      - "the cube and the octahedron"
      - "the tetrahedron and the cube"
      - "none; all five are built"
    answer: 0
    explain: "`PLATONIC_CLAUDE_AUDIT.md`, under \"Open\": they \"still exist only as `Platonic.RegularNumbers` witnesses … They need golden-ratio coordinates, where the face lattice cannot be settled by `decide`, and are not attempted here.\""
---

## Plain English

```lean
/-- Tetrahedron `{3,3}`: `V=4, E=6, F=4`. -/
def tetrahedron : RegularNumbers where
  V := 4; E := 6; F := 4; s := 3; m := 3
  hs := by decide
  hm := by decide
  hE := by decide
  hFace := by decide
  hVert := by decide
  hEuler := by decide
```

Five numbers, and five proofs that they fit together:

- `3 ≤ 3` and `3 ≤ 3` — faces are triangles, three meet at each corner;
- `0 < 6` — there are edges;
- `3 · 4 = 2 · 6` — count the (face, its edges) pairs two ways;
- `3 · 4 = 2 · 6` — count the (vertex, its edges) pairs two ways;
- `4 − 6 + 4 = 2` — Euler.

Every one is `by decide`, because they are claims about numerals.

**It is not a tetrahedron.** It is the arithmetic signature of one. Parts 2–6 of
[`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids) are statements about
these five records and nothing else, which is why that theorem's name oversells it.

### In one breath

Four corners, six edges, four triangular faces, three edges to a face, three faces to a corner.
Written down as five numbers with a note that they are consistent. There is no shape here — just
its census.

### But there *is* a real one, elsewhere

This is worth knowing, because it changes how the Platonic lane should be described. Three of the
five solids are built geometrically in this repository — just not in `Results.lean`:

| solid | module | what is proved |
|---|---|---|
| tetrahedron `{3,3}` | `SimplexFaces.lean` + `GeometricPlatonic.lean` | face lattice from barycentric coordinates, geometric `V=4, E=6, F=4`, `V − E + F = 2` from Euler–Poincaré, all four incidence counts, `{3,3}` membership |
| octahedron `{3,4}` | `Octahedron.lean` | H-representation by a padding trick, faces = partial sign assignments, `V=6, E=12, F=8`, Euler from the root, incidence |
| cube `{4,3}` | `Cube.lean` | V-rep as a Minkowski sum of segments, `2n` halfspaces, faces are subcubes, `V=8, E=12, F=6`, Euler from the root, incidence |

and `MetricRegular.lean` adds genuine metric content: the octahedron's and cube's vertices lie on a
sphere with all edges equal, and `Cube.regularTetra` is a **regular** tetrahedron — four pairwise
equidistant alternating cube corners, affinely independent, hence an `AffineBasis`, hence `{3,3}`
with Euler from the root.

The dodecahedron and the icosahedron have none of this. They need golden-ratio coordinates, where
the face lattice cannot be settled by `decide`, and they are not attempted.

So: "three of the five Platonic solids are constructed and shown to satisfy Euler's formula" is a
true and fair summary of this repository. "The five Platonic solids are classified" is not.

### Where it sits

- An instance of [`RegularNumbers`](#/node/Platonic.RegularNumbers).
- Its `(V,E,F,s,m)` is part 2 of
  [`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids).
- `exists_regularNumbers_of_mem_schlafli` uses it as the witness for the pair `(3,3)`.
