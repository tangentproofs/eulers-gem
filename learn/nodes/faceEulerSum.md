---
id: faceEulerSum
title: "faceEulerSum: the alternating sum that is Euler's formula"
summary: "`faceEulerSum S n = ∑ d ∈ range (n+1), (−1)ᵈ · #{faces of affDim d}` — vertices minus edges plus 2-faces minus …, up to and including the body. For a full-dimensional convex polytope it is 1."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**The body is counted** and **the empty face is not.** `S` is a face of itself (`isFaceOf_refl`) with `affDim S = n`, so it is the `d = n` term. `∅` is also a face (`isFaceOf_empty`) but `affDim ∅ = -1` and the sum starts at `d = 0`, so it never appears. Get either wrong and every number on this page changes."
  - "`Set.ncard` is `0` on an infinite set. So a term of this sum reading `0` could in principle mean \"infinitely many faces of that dimension\" rather than \"none\". The repository proves there are finitely many — `facesOfDim_finite_of_isPolytope` — but the *definition* of `faceEulerSum` does not know that, and neither does any statement that does not cite it."
  - "`n` is a free `ℕ` parameter, not derived from `S`. `faceEulerSum S n` is meaningful for any `n`; the theorems instantiate it at the ambient `Module.finrank ℝ E`. Taking `n` too small truncates the sum and gives a different number."
  - "The faces are `Set E`-valued and compared as sets, so two faces are the same face exactly when they are equal as sets. This is the obvious thing, but it is worth saying, because a combinatorial treatment would instead index faces by vertex subsets and could double-count."
widgets:
  - type: face-lattice
    title: "f₀ … fₙ for the n-simplex and the n-cube, exactly"
    config:
      n: 3
quiz:
  - q: "Write out the definition."
    type: choice
    choices:
      - "`∑ d ∈ Finset.range (n+1), (-1)^d * ({f | IsFaceOf S f ∧ affDim f = d}.ncard : ℤ)`"
      - "`∑ d ∈ Finset.range n, (-1)^d * ({f | IsFaceOf S f ∧ affDim f = d}.ncard : ℤ)`"
      - "`∑ d ∈ Finset.range (n+1), (-1)^d * ({f | IsFaceOf S f}.ncard : ℤ)`"
      - "`({f | IsFaceOf S f ∧ affDim f = 0}.ncard : ℤ) - {f | IsFaceOf S f ∧ affDim f = 1}.ncard`"
    answer: 0
    explain: "`noncomputable def faceEulerSum (S : Set E) (n : ℕ) : ℤ := ∑ d ∈ Finset.range (n + 1), (-1 : ℤ) ^ d * (Set.ncard {f : Set E | IsFaceOf S f ∧ affDim f = (d : ℤ)} : ℤ)` (Polytope.lean). Note `range (n+1)`, so `d` runs `0 … n` inclusive."
  - q: "For a cube in ℝ³, what are the four terms of `faceEulerSum p 3`, in order?"
    type: choice
    choices: ["8, −12, 6, −1", "8, −12, 6", "1, −6, 12, −8", "8, 12, 6, 1"]
    answer: 0
    explain: "Eight vertices, twelve edges, six square faces, and one 3-dimensional face: the cube itself. `8 − 12 + 6 − 1 = 1`, which is what `results_euler_characteristic` says it must be. Drop that last `−1` and you have `V − E + F = 2`."
  - q: "`faceEulerSum p 3 = 1` for a 3-dimensional polytope. What is `V − E + F`?"
    type: number
    answer: 2
    explain: "The `d = 3` term is `−1 · 1 = −1`, since the body is the only 3-face. So `V − E + F − 1 = 1`, hence `V − E + F = 2`. That one line is the whole content of `euler_relation_of_isPolytope` given the characteristic — see the private `faceEulerSum_three_expand` in `EulerPoincare.lean` for the expansion."
  - q: "Does the empty face contribute a term?"
    type: choice
    choices:
      - "yes, as the `d = 0` term, since `∅` is a face"
      - "no: `affDim ∅ = -1`, and the sum runs over `d ≥ 0` only"
      - "no: `∅` is not a face"
      - "only when `S` is empty"
    answer: 1
    explain: "`isFaceOf_empty` makes `∅` a face of every set, so the first two clauses of the set-builder hold for it — but `affDim ∅ = -1 ≠ d` for every `d` in `range (n+1)`. The sum silently excludes it. Put it back in with sign `(-1)^(-1)` and you get `0`, the *reduced* Euler characteristic."
  - q: "What is `faceEulerSum p 2` for a *square* (a 2-dimensional polytope in the plane)?"
    type: number
    answer: 1
    explain: "Four vertices, four edges, one 2-face (the square itself): `4 − 4 + 1 = 1`. `results_euler_characteristic` gives `1` in every dimension; the familiar `2` appears only after the body's term is moved across, and only in dimension 3 does that produce `V − E + F = 2`."
---

## Plain English

```lean
noncomputable def faceEulerSum (S : Set E) (n : ℕ) : ℤ :=
  ∑ d ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ d *
      (Set.ncard {f : Set E | IsFaceOf S f ∧ affDim f = (d : ℤ)} : ℤ)
```

Count the [faces](#/node/IsFaceOf) of `S` of each [dimension](#/node/affDim) and add them up with
alternating signs:

> `#(vertices) − #(edges) + #(2-faces) − #(3-faces) + …`

all the way up to dimension `n`. For a polytope of dimension `n`, that top term is the polytope
itself, counted once.

[`results_euler_characteristic`](#/node/Results.results_euler_characteristic) says this number is
always **1**, for any convex polytope filling its ambient space, in any dimension. Not 2 — **1**.
The famous 2 comes from rearranging in dimension 3.

### In one breath

Count the corners of a solid. Subtract the edges. Add the flat sides. You will get two, every
time, for anything you could whittle out of a block of wood without putting a hole or a dent in
it. Now count the solid itself as one more thing, a side of dimension three, and subtract it: you
get one. That is the number the proof is really about, and the reason it is one rather than two is
that one is the answer in *every* dimension — for a square, for a cube, for a four-dimensional
cube. Euler's two is the three-dimensional shadow of it.

### Why 1 and not 2

| | f₀ | f₁ | f₂ | f₃ | f₄ | alternating sum |
|---|---|---|---|---|---|---|
| point | 1 | | | | | 1 |
| segment | 2 | 1 | | | | 1 |
| triangle | 3 | 3 | 1 | | | 1 |
| square | 4 | 4 | 1 | | | 1 |
| tetrahedron | 4 | 6 | 4 | 1 | | 1 |
| cube | 8 | 12 | 6 | 1 | | 1 |
| 5-cell | 5 | 10 | 10 | 5 | 1 | 1 |
| tesseract | 16 | 32 | 24 | 8 | 1 | 1 |

The last column is constant, and that constancy is what `faceEulerSum = 1` names. Euler's
`V − E + F = 2` is row "cube" or row "tetrahedron" with the final `−1` moved to the right-hand
side. The widget above computes these columns exactly, for the simplex and the cube, from
binomial formulas the Lean proves (`EulersGem.faceCount`, `Cube.affDim_face`).

In dimension 3 that move is clean, because the only 3-dimensional face is the body: so
`V − E + F − 1 = 1` and `V − E + F = 2`. In dimension 4 the body's sign is `+`, and dropping it
leaves `0`, not `2`. There is no "Euler's formula" in even dimensions with a nice right-hand side
— which is a good reason to think of `= 1` as the real theorem.

### Two traps in the definition

1. **The body is in the sum.** It has to be, or the number would be dimension-dependent.
2. **The empty face is not**, and nothing in `faceEulerSum` says so explicitly. It falls out
   because `affDim ∅ = -1` while `d` ranges over `0 … n`. If you are checking the arithmetic
   against a textbook, be aware the textbook may be using the *reduced* characteristic, which does
   include it and comes out `0`.

And one trap in reading a proved `= 0`: `Set.ncard` returns `0` for infinite sets, so a zero term
is ambiguous without a finiteness result. The repository has one
([`facesOfDim_finite_of_isPolytope`](#/node/facesOfDim_finite_of_isPolytope)) and uses it.

### Where it sits

- [`Euler_Poincare_of_isPolytope`](#/node/Euler_Poincare_of_isPolytope) and
  [`results_euler_characteristic`](#/node/Results.results_euler_characteristic) are the theorems
  about it.
- `faceEulerSum_three_expand` (private, in `EulerPoincare.lean`) and `faceEulerSum_two_expand`
  (`DiskEuler.lean`) expand it in low dimensions; those expansions are how
  [`euler_relation_of_isPolytope`](#/node/euler_relation_of_isPolytope) and the planar disk
  lemmas get at it.
- `faceEulerSum_halfspace_cone = 0` and `faceEulerSum_polyhedral_cone = 0` (Paulson's
  `Euler_polyhedral_cone`) are the *cone* version, where the
  answer is `0` instead of `1` — and the cone case is what the proof actually establishes first.
