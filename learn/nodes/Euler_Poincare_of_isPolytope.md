---
id: Euler_Poincare_of_isPolytope
title: "The root: a full-dimensional polytope has characteristic 1"
summary: "`IsPolytope p`, `affDim p = finrank ℝ E` and `1 ≤ finrank ℝ E` give `faceEulerSum p (finrank ℝ E) = 1`. This is the theorem everything else in the repository hangs below."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**Full-dimensionality is used.** A square in ℝ³ has `affDim = 2 ≠ 3` and this theorem does not apply to it as stated. The characteristic of such a polytope is still 1 — apply the theorem inside its affine span — but that is a step the user has to take."
  - "`1 ≤ finrank ℝ E` excludes the zero-dimensional ambient space. There `affDim p = 0` would force `p` to be a point, and `faceEulerSum p 0 = 1` is in fact still true; the hypothesis is there because the proof route (homogenize, embed in `E × ℝ`, slice a cone) needs a dimension to work in."
  - "This is a restatement of `Euler_Poincare_full` (`Embed.lean`) with the halfspace presentation discharged. All of the mathematics is in `Embed.lean` and the modules under it; this declaration is four lines."
widgets:
  - type: walkthrough
    title: "How Euler_Poincare_full is proved, module by module"
    config:
      steps:
        - text: "Get a halfspace presentation from the finite vertex list"
          lean: "obtain ⟨H, hH, hrep⟩ := hp.isPolyhedron"
          note: "The argument needs finitely many hyperplanes to chop space with, and IsPolytope only gives points. IsPolytope.isPolyhedron closes that gap — it is the one step that was a hypothesis until PR #2."
          link: IsPolytope.isPolyhedron
          uses: [IsPolytope, IsPolyhedron, IsPolytope.isPolyhedron]
        - text: "Hyperplane arrangements and cell complexes: chop space by the hyperplanes"
          note: "Hyperplane.lean defines an arrangement, the equivalence of points with the same sign pattern, and the cells. CellGeometry.lean relates a cell to its affine hull and relative interior. EulerChar.lean defines the combinatorial alternating count over cells and proves it invariant under refining the arrangement — the engine of the whole proof."
          uses: [affDim]
          hard: true
        - text: "A polyhedral cone has cell Euler characteristic 0"
          note: "Cone.lean and ConeFaceCell.lean. For a cone given by homogeneous inequalities ⟪a, x⟫ ≤ 0, inclusion–exclusion over sign patterns gives 0 — not 1. The cone case is the one the counting argument settles directly, which is why the polytope case is reached by building a cone."
          hard: true
        - text: "Faces of the cone match its cells, so faceEulerSum of the cone is 0"
          lean: "faceEulerSum_halfspace_cone = 0  →  Euler_polyhedral_cone"
          note: "FaceCell.lean and ConeFaceCell.lean: each cell's closure is a face, and each face arises once. That converts a statement about cells into a statement about faces."
          uses: [IsFaceOf, faceEulerSum]
          hard: true
        - text: "Slice the cone at height 1 and the faces correspond"
          note: "ConeSlice.lean and ConeSliceFaceBijection: a face of the slice lifts to a face of the cone one dimension up, and the dimensions differ by exactly 1. The alternating sign therefore flips, turning the cone's 0 into the slice's 1 — this is where the 1 comes from."
          uses: [affDim]
          hard: true
        - text: "Embed p in E × ℝ at height 1 and homogenize"
          lean: "Euler_Poincare_full hH hrep hp hdim hn"
          note: "Embed.lean: put p on the hyperplane {(x,1)} of E × ℝ and take the cone over it. The slice of that cone is p, so the previous step applies to p itself."
          uses: [faceEulerSum, IsPolytope]
          hard: true
        - text: "Read it off: faceEulerSum p (finrank ℝ E) = 1"
          lean: |-
            theorem Euler_Poincare_of_isPolytope {p : Set E} (hp : IsPolytope p)
                (hdim : affDim p = Module.finrank ℝ E) (hn : 1 ≤ Module.finrank ℝ E) :
                faceEulerSum p (Module.finrank ℝ E) = 1
          link: Results.results_euler_characteristic
          uses: [faceEulerSum, Results.results_euler_characteristic]
quiz:
  - q: "What are the three hypotheses?"
    type: choice
    choices:
      - "`IsPolytope p`, `affDim p = Module.finrank ℝ E`, `1 ≤ Module.finrank ℝ E`"
      - "`IsPolyhedron p`, `affDim p = 3`, `p` compact"
      - "`IsPolytope p` and `Convex ℝ p`"
      - "`IsPolytope p`, `affDim p = 3`"
    answer: 0
    explain: "`theorem Euler_Poincare_of_isPolytope {p : Set E} (hp : IsPolytope p) (hdim : affDim p = Module.finrank ℝ E) (hn : 1 ≤ Module.finrank ℝ E) : faceEulerSum p (Module.finrank ℝ E) = 1` (UnconditionalEuler.lean), in a `[NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]` section."
  - q: "What value does it prove for the alternating sum?"
    type: number
    answer: 1
    explain: "`1`, in every dimension. The familiar `2` is what you get in dimension 3 after moving the body's `−1` term to the other side — see [euler_relation_of_isPolytope](#/node/euler_relation_of_isPolytope)."
  - q: "Does it apply to a square sitting inside ℝ³?"
    type: choice
    choices:
      - "yes, directly"
      - "no, as stated: `affDim p = 2` but `finrank ℝ E = 3`, so `hdim` fails"
      - "no, squares are not polytopes"
    answer: 1
    explain: "`hdim : affDim p = Module.finrank ℝ E` is the full-dimensionality hypothesis and it genuinely fails here. The square's characteristic is still 1, by applying the theorem in the plane it spans; the theorem itself does not do that for you."
  - q: "Where does the halfspace presentation that the proof needs come from?"
    type: choice
    choices:
      - "a hypothesis of this theorem"
      - "`IsPolytope.isPolyhedron`, invoked in the first line of the proof"
      - "it is not needed"
      - "`facesOfDim_finite_of_isPolytope`"
    answer: 1
    explain: "The proof is `obtain ⟨H, hH, hrep⟩ := hp.isPolyhedron; exact Euler_Poincare_full hH hrep hp hdim hn`. `Euler_Poincare_full` still takes `hH` and `hrep`; this theorem is exactly the version with them discharged."
  - q: "What does the underlying cone argument prove the alternating sum of a polyhedral *cone* to be?"
    type: number
    answer: 0
    explain: "`0`, not 1 — `Euler_polyhedral_cone` / `faceEulerSum_halfspace_cone = 0`. The polytope's 1 comes from slicing a cone one dimension up: the slice's faces correspond to the cone's with dimensions shifted by 1, so the signs flip. The cone case is the one the cell-counting argument settles."
---

## Plain English

**Theorem.** If `p` is the convex hull of finitely many points and it fills up its ambient space,
then

> `#(vertices) − #(edges) + #(2-faces) − … ± #(p itself) = 1`.

```lean
theorem Euler_Poincare_of_isPolytope {p : Set E} (hp : IsPolytope p)
    (hdim : affDim p = Module.finrank ℝ E) (hn : 1 ≤ Module.finrank ℝ E) :
    faceEulerSum p (Module.finrank ℝ E) = 1
```

This is the root of the repository. [`results_euler_characteristic`](#/node/Results.results_euler_characteristic)
is this theorem restated for the paper; [`results_euler_polyhedron`](#/node/Results.results_euler_polyhedron)
is its dimension-3 reading; the Platonic and Pick lanes both descend from it.

Three hypotheses, no more: a finite convex hull, full dimension, and at least one dimension to work
in. In particular **no halfspace presentation is supplied** — that used to be an extra hypothesis
and is now [a theorem](#/node/IsPolytope.isPolyhedron).

### In one breath

Count the corners of any solid you could whittle from a block of wood. Subtract the edges, add the
flat sides, and subtract the solid itself. You get one. Do the same in the plane — corners minus
edges plus the shape itself — and you get one. Do it in four dimensions and you get one. The number
one is the theorem; Euler's familiar two is what it looks like in three dimensions once you stop
counting the solid.

### The shape of the proof

The walkthrough above steps through it with the module names. The surprising part is the order of
operations: **the proof does not reason about polytopes.** It reasons about cones, where the answer
is `0`, and then gets the polytope by slicing one.

Why cones? Because the engine of the proof is invariance of an alternating cell count under
refining a hyperplane arrangement (`EulerChar.lean`), and for a cone cut out by *homogeneous*
inequalities `⟪a, x⟫ ≤ 0`, that count can be evaluated directly by inclusion–exclusion over sign
patterns. You get `0`.

Then: put `p` on the slice `{(x, 1)} ⊆ E × ℝ` and take the cone over it (`Embed.lean`). Faces of
`p` correspond to faces of that cone, with dimension shifted by one
(`ConeSliceFaceBijection`). A dimension shift of one flips every sign in the alternating sum, so
the cone's `0` becomes — after accounting for the cone's apex — the slice's `1`. That is where the
`1` comes from, and it is why `1` is the natural constant and `2` is the accident of dimension 3.

This is Jim Lawrence's 1997 argument, formalized by Lawrence C. Paulson in Isabelle/HOL (AFP 2023,
after HOL Light) and re-formalized here. `lean-afp.html` lines the two developments up theorem by
theorem.

### Where it sits

Below it: [`IsPolytope`](#/node/IsPolytope), [`IsFaceOf`](#/node/IsFaceOf),
[`affDim`](#/node/affDim), [`faceEulerSum`](#/node/faceEulerSum),
[`IsPolytope.isPolyhedron`](#/node/IsPolytope.isPolyhedron),
[`facesOfDim_finite_of_isPolytope`](#/node/facesOfDim_finite_of_isPolytope), and the whole cone and
cell-complex substrate.

Above it: [`euler_relation_of_isPolytope`](#/node/euler_relation_of_isPolytope) in dimension 3, then
[`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids) and, by a longer
route, the Pick lane.
