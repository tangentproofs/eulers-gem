---
id: Platonic.tetrahedron
title: "Platonic.tetrahedron: five numbers called a tetrahedron"
summary: "A `RegularNumbers` record with `V = 4, E = 6, F = 4, s = 3, m = 3`, every proof field `by decide`. It is not a tetrahedron — but a geometric one does exist elsewhere in the repository, as do geometric versions of all four siblings."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**This definition is not a geometric object.** It is five natural numbers with certificates. The name is a label."
  - "A *geometric* tetrahedron does exist in this repository, elsewhere: `SimplexFaces.lean` computes the face lattice of a simplex and `Simplex.tetrahedron_platonic` (`GeometricPlatonic.lean`) proves a geometric tetrahedron is `{3,3}` with Euler from the root. `Cube.regularTetra` (`MetricRegular.lean`) goes further and builds a genuinely *regular* tetrahedron (four pairwise-equidistant alternating cube corners). Since then `Platonic3.tetrahedron` (`PlatonicSolids.lean`) is proved flag-transitive, and *that* is in `Results`, as part of `results_five_platonic_solids_constructed`."
  - "The same pattern holds for `Platonic.octahedron` and `Platonic.cube` (geometric versions in `Octahedron.lean` and `Cube.lean`). The records `Platonic.dodecahedron` and `Platonic.icosahedron` are numbers too, but geometric, golden-ratio versions are now built in `PlatonicSolids.lean` (`Platonic3.dodecahedron`, `Platonic3.icosahedron`)."
widgets:
  - type: polyhedron
    title: "A real tetrahedron — built in the Lean as `Platonic3.tetrahedron`"
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
      - "yes — `Simplex.tetrahedron_platonic` (`GeometricPlatonic.lean`), with its face lattice from `SimplexFaces.lean` and Euler from the root, and a metrically regular one in `MetricRegular.lean`"
      - "no"
      - "yes, but only in `Results.lean`"
    answer: 0
    explain: "`PLATONIC_CLAUDE_AUDIT.md` tabulates it: geometric face counts `V=4, E=6, F=4` (`tetrahedron_face_counts`), `V − E + F = 2` from Euler–Poincaré (`tetrahedron_euler_relation`), all four incidence counts (`tetrahedron_incidence`), and `{3,3}` membership (`tetrahedron_platonic`). It is simply not exported through `Results.lean`."
  - q: "Which of the five solids have a geometric construction in this repository?"
    type: choice
    choices:
      - "all five — `PlatonicSolids.lean` builds each one from `ℤ[φ]` coordinates and proves it flag-transitive (`results_five_platonic_solids_constructed`)"
      - "only the tetrahedron, cube and octahedron"
      - "none; they are all `RegularNumbers` records"
      - "only the tetrahedron"
    answer: 0
    explain: "The records like `Platonic.tetrahedron` are still just numbers, but `Platonic3.tetrahedron` … `Platonic3.icosahedron` are convex hulls in ℝ³. The dodecahedron and icosahedron use golden-ratio coordinates; their face lattices are checked by `decide +kernel` over exact `ℤ[φ]` arithmetic (`ZPhi.lean`)."
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

This is worth knowing, because it changes how the Platonic lane should be described. The first
geometric constructions, of three of the five solids, were these:

| solid | module | what is proved |
|---|---|---|
| tetrahedron `{3,3}` | `SimplexFaces.lean` + `GeometricPlatonic.lean` | face lattice from barycentric coordinates, geometric `V=4, E=6, F=4`, `V − E + F = 2` from Euler–Poincaré, all four incidence counts, `{3,3}` membership |
| octahedron `{3,4}` | `Octahedron.lean` | H-representation by a padding trick, faces = partial sign assignments, `V=6, E=12, F=8`, Euler from the root, incidence |
| cube `{4,3}` | `Cube.lean` | V-rep as a Minkowski sum of segments, `2n` halfspaces, faces are subcubes, `V=8, E=12, F=6`, Euler from the root, incidence |

and `MetricRegular.lean` adds genuine metric content: the octahedron's and cube's vertices lie on a
sphere with all edges equal, and `Cube.regularTetra` is a **regular** tetrahedron — four pairwise
equidistant alternating cube corners, affinely independent, hence an `AffineBasis`, hence `{3,3}`
with Euler from the root.

All five — including the dodecahedron and the icosahedron, with golden-ratio coordinates — are now
built and proved **regular** (flag-transitive) in `PlatonicSolids.lean`, exported as
[`results_five_platonic_solids_constructed`](#/node/Results.results_five_platonic_solids_constructed).

So: "the five Platonic solids are constructed and proved regular" is a true and fair summary of
this repository. "The five Platonic solids are classified up to similarity" is **not** yet: that is
conditional on two unproved gaps
([`results_regular_polyhedron_face_data`](#/node/Results.results_regular_polyhedron_face_data)).

### Where it sits

- An instance of [`RegularNumbers`](#/node/Platonic.RegularNumbers).
- Its `(V,E,F,s,m)` is part 2 of
  [`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids).
- `exists_regularNumbers_of_mem_schlafli` uses it as the witness for the pair `(3,3)`.
