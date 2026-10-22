---
id: Platonic.dodecahedron
title: "Platonic.dodecahedron: twenty, thirty, twelve — and no dodecahedron"
summary: "A `RegularNumbers` record with `V = 20, E = 30, F = 12, s = 5, m = 3`. Unlike the tetrahedron, cube and octahedron, no geometric dodecahedron exists anywhere in this repository."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**This is the clearest place the Platonic lane's name overstates it.** `Platonic.dodecahedron` is five natural numbers. There is no subset of ℝ³ called a dodecahedron in this repository, no face lattice for one, and no theorem about one. The same goes for `Platonic.icosahedron`."
  - "`PLATONIC_CLAUDE_AUDIT.md`, under \"Open\": the dodecahedron `{5,3}` and icosahedron `{3,5}` \"still exist only as `Platonic.RegularNumbers` witnesses (Euler bookkeeping, `(V,E,F)` integers) — those are explicitly **not** geometric constructions. They need golden-ratio coordinates, where the face lattice cannot be settled by `decide`, and are not attempted here.\""
  - "The picture the widget draws is this website's doing. It is a correct picture of a dodecahedron, and it is not evidence of anything in the Lean."
widgets:
  - type: polyhedron
    title: "A dodecahedron, drawn here and nowhere in the Lean"
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
    explain: "Five numerals with five `by decide` certificates. No geometry. The repository's audit file is explicit that this is \"**not** a geometric construction\"."
  - q: "Does this repository construct a geometric dodecahedron?"
    type: choice
    choices:
      - "no — and `PLATONIC_CLAUDE_AUDIT.md` lists it as open, since golden-ratio coordinates put the face lattice beyond `decide`"
      - "yes, in `Cube.lean`"
      - "yes, in `GeometricPlatonic.lean`"
      - "yes, but only its Euler relation"
    answer: 0
    explain: "Three of the five are built: tetrahedron (`GeometricPlatonic.lean`), octahedron (`Octahedron.lean`), cube (`Cube.lean`). The dodecahedron and icosahedron are not attempted."
  - q: "Verify `hFace : s * F = 2 * E` for these numbers."
    type: choice
    choices: ["`5 · 12 = 60 = 2 · 30` ✓", "`5 · 12 = 60 ≠ 2 · 30`", "`3 · 12 = 2 · 30`"]
    answer: 0
    explain: "Twelve pentagons, five edges each, every edge shared by two faces: `60 = 60`. And `hVert : 3 · 20 = 60 = 2 · 30`. And `hEuler : 20 − 30 + 12 = 2`."
  - q: "Solve `E · (2s + 2m − sm) = 2sm` for `(s,m) = (5,3)`."
    type: number
    answer: 30
    explain: "`2·5 + 2·3 − 15 = 1`, so `E · 1 = 30`. Then `F = 2E/s = 12` and `V = 2E/m = 20` — which is where the record's numbers come from. [mul_euler_int](#/node/Platonic.sub_mul_lt_four) is that identity."
  - q: "What would it take to construct one in Lean?"
    type: choice
    choices:
      - "golden-ratio coordinates and a face-lattice argument that `decide` cannot do, since the coordinates are irrational"
      - "nothing; `decide` would handle it"
      - "a new axiom"
      - "a weaker definition of polytope"
    answer: 0
    explain: "The three built solids have coordinates in `{0, ±1}`, so their face lattices reduce to finite decidable checks (`Cube.lean` decides over `Fin 3 → Option Bool`, 27 functions). A dodecahedron's vertices involve `(1 + √5)/2`, and no `decide` reaches it — the supporting-hyperplane arguments have to be done by hand."
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

**This is not a dodecahedron.** It is the only thing in this repository that goes by that name, and
it is a record of five natural numbers. There is no set of points, no face lattice, no theorem
about a twelve-faced solid.

The `polyhedron` widget above draws one, because this website can draw whatever it likes. That
drawing is not evidence of anything in the Lean, and this node exists mainly to say so.

### In one breath

Someone wrote down the census of a dodecahedron — twenty corners, thirty edges, twelve pentagonal
faces — and checked the numbers are consistent with Euler's count. Nobody built the solid. If you
want to know whether this proof assistant has ever seen a dodecahedron, the answer is no.

### Why not?

Compare the three solids that *are* built:

| solid | coordinates | how the face lattice is settled |
|---|---|---|
| tetrahedron | a simplex's `AffineBasis` | barycentric coordinates + Riesz (`SimplexFaces.lean`) |
| octahedron | `±eᵢ` | partial sign assignments, with a padding trick for the H-rep |
| cube | `(±1, ±1, ±1)` | faces are subcubes, `decide` over `Fin 3 → Option Bool` (27 functions) |
| **dodecahedron** | `(±1,±1,±1)` and cyclic `(0, ±1/φ, ±φ)` | **not attempted** |
| **icosahedron** | cyclic `(0, ±1, ±φ)` | **not attempted** |

The first three have coordinates in `{0, ±1}`, which makes their face lattices finite decidable
checks. The last two need `φ = (1 + √5)/2`, which is irrational, so `decide` is useless and every
supporting-hyperplane argument has to be done by hand. `PLATONIC_CLAUDE_AUDIT.md` lists it as the
first open item on the lane.

### What this means for the headline claim

[`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids) proves the Schläfli
pair `(5,3)` is admissible, and separately states these five numbers. It does not prove a solid with
those numbers exists. Three of the five do exist in this repository, in modules outside `Results`;
two do not exist at all. Any summary that says otherwise is wrong.

### Where it sits

- An instance of [`RegularNumbers`](#/node/Platonic.RegularNumbers).
- Part 5 of [`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids).
- The witness for `(5,3)` in `exists_regularNumbers_of_mem_schlafli`.
- Compare [`Platonic.tetrahedron`](#/node/Platonic.tetrahedron), which is also just a record but has
  a geometric counterpart.
