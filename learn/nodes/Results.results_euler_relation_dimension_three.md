---
id: Results.results_euler_relation_dimension_three
title: "Euler's formula: V − E + F = 2 in dimension three"
summary: "The paper-facing `V − E + F = 2` for a 3-dimensional convex polytope in any 3-dimensional real inner product space, with `V`, `E`, `F` the geometric face counts."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "The docstring names Paulson's AFP theorem `Euler_relation` as the counterpart. That is a claim about the correspondence between two developments, not something the Lean proves; `lean-afp.html` is where the mapping is recorded."
  - "Two dimension hypotheses, not one: `affDim p = 3` and `Module.finrank ℝ E = 3`."
  - "A restatement: the proof is `EulersGem.euler_relation_of_isPolytope hP hdim hE`."
widgets:
  - type: polyhedron
    title: "Seven polytopes the theorem covers, and one it does not"
    config:
      preset: octahedron
      show: [counts, incidence, truncate]
  - type: face-lattice
    title: "Where the 2 comes from: drop the body's term"
    config:
      family: cube
      n: 3
quiz:
  - q: "What are `V`, `E` and `F` in the statement?"
    type: choice
    choices:
      - "`ncard`s of `{f | IsFaceOf p f ∧ affDim f = d}` for `d = 0, 1, 2`, cast to `ℤ`"
      - "universally quantified natural numbers"
      - "the counts of a combinatorial complex built from `p`"
      - "the number of generators of `p`"
    answer: 0
    explain: "The statement writes them out in full, three set-builders with `IsFaceOf` and `affDim`. There is no intermediate combinatorial object anywhere in this statement."
  - q: "Where does the `2` come from, given that `results_euler_characteristic` gives `1`?"
    type: choice
    choices:
      - "a 3-dimensional polytope has exactly one 3-face — itself — contributing `−1`"
      - "the empty face contributes `+1`"
      - "a different proof entirely"
      - "two vertices are counted twice"
    answer: 0
    explain: "`faceEulerSum p 3 = f₀ − f₁ + f₂ − f₃` with `f₃ = 1` (`isFaceOf_refl`, and nothing else is 3-dimensional). So `V − E + F − 1 = 1`."
  - q: "The toroidal picture-frame solid has `V = 16`, `E = 32`, `F = 16`. Is this a counterexample?"
    type: choice
    choices:
      - "yes, since `16 − 32 + 16 = 0`"
      - "no: it is not convex, so `IsPolytope` fails and the theorem says nothing about it"
      - "no: those counts are wrong"
    answer: 1
    explain: "`16 − 32 + 16 = 0` is correct, and harmless. `IsPolytope p` means `p = convexHull ℝ V` for some finite `V`, so every `IsPolytope` is convex; a solid with a hole through it is not. Euler's formula is a theorem about convex polyhedra."
  - q: "A triangular prism has 6 vertices, 9 edges and 5 faces. Is it covered?"
    type: choice
    choices:
      - "yes: it is a convex hull of 6 points and 3-dimensional, and `6 − 9 + 5 = 2`"
      - "no: its faces are not all the same shape"
      - "no: it is not regular"
    answer: 0
    explain: "Regularity is nowhere in the statement. The only hypotheses are `IsPolytope p`, `affDim p = 3` and `Module.finrank ℝ E = 3`."
  - q: "Does the theorem hold for a planar graph drawn on a sphere?"
    type: choice
    choices:
      - "yes, by the usual correspondence"
      - "no — nothing in this statement is about graphs, maps or surfaces; it is about face sets of a convex polytope"
      - "only for 3-connected graphs"
    answer: 1
    explain: "The classical correspondence (Steinitz, for 3-connected planar graphs) is real mathematics and is not in this repository. The statement quantifies over sets `p` in an inner product space; no graph, map or surface appears anywhere in it."
---

## Plain English

```lean
theorem results_euler_relation_dimension_three
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {p : Set E}
    (hP : EulersGem.IsPolytope p)
    (hdim : EulersGem.affDim p = 3)
    (hE : Module.finrank ℝ E = 3) :
    ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 0}.ncard : ℤ) -
        ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 1}.ncard : ℤ) +
        ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 2}.ncard : ℤ) =
      2
```

**`V − E + F = 2`.** Euler's polyhedron formula, for convex polyhedra. Freek Wiedijk's #13, and
the theorem this repository is named for.

Three hypotheses: `p` is a convex hull of finitely many points, `p` is three-dimensional, and the
space it lives in is three-dimensional too.

### In one breath

Take a die. Eight corners, twelve edges, six faces: eight minus twelve plus six is two. Take a
pyramid on a square base: five, eight, five — two again. A football stitched from flat panels, a
cut gemstone, a soccer-ball-shaped dome: two every time. Euler spotted this in 1750 in a letter to
Goldbach and never found a proof he was happy with. What makes it work is convexity: no holes, no
dents. Put a square hole through a square slab and you get zero instead.

## What this does and does not prove

**It does prove:**

- Euler's polyhedron formula for convex 3-polytopes. You may call it that. The counts are the
  geometric face sets — [`IsFaceOf`](#/node/IsFaceOf) and [`affDim`](#/node/affDim) — not a
  combinatorial substitute, and nothing is assumed about how `p` is presented.
- In **any** 3-dimensional real inner product space, not just ℝ³. (For the ℝ³ version with the
  type-class hypothesis discharged, see
  [`results_euler_polyhedron`](#/node/Results.results_euler_polyhedron).)

**It does not prove:**

- Euler's formula for **non-convex** polyhedra. The picture frame in the widget above has
  `V − E + F = 0`. `IsPolytope` excludes it, correctly.
- Anything about **graphs on a sphere** or **planar graphs**. The classical bridge (every
  3-connected planar graph is the graph of a convex polytope — Steinitz) is not formalized here, so
  you cannot route a graph-theoretic Euler formula through this theorem.
- Anything about **surfaces** or **genus**. `V − E + F = 2 − 2g` appears nowhere in the
  repository.
- A **converse**: that `V − E + F = 2` characterizes convex polytopes. It does not, and nothing
  here suggests it.

### How it is proved

One bookkeeping step from [`results_euler_characteristic`](#/node/Results.results_euler_characteristic).
That theorem gives [`faceEulerSum p 3 = 1`](#/node/faceEulerSum), i.e. `f₀ − f₁ + f₂ − f₃ = 1`. A
3-dimensional polytope has exactly one face of dimension 3 — itself — so `f₃ = 1` and the `−1`
moves across. The chain is
[`Euler_Poincare_of_isPolytope`](#/node/Euler_Poincare_of_isPolytope) →
[`euler_relation_of_isPolytope`](#/node/euler_relation_of_isPolytope) → this.

### Where it sits

This is the theorem the Platonic lane calls.
[`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids) invokes it by name,
which is how the Schläfli classification gets `V − E + F = 2` as a *consequence* rather than as a
hypothesis — the repository's standing rule
(`lean/UNIFIED_SPINE.md`) forbids the alternative.
