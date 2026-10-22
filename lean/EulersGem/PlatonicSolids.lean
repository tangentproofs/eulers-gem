/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.PlatonicSolids.Tetrahedron
import EulersGem.PlatonicSolids.Cube
import EulersGem.PlatonicSolids.Octahedron
import EulersGem.PlatonicSolids.Icosahedron
import EulersGem.PlatonicSolids.Dodecahedron

/-!
# The five Platonic solids, constructed in `ℝ³`

Each solid is the convex hull of explicit points of `ℤ[φ]³ ⊂ ℝ³`
(`φ = Real.goldenRatio`). For each we prove, with no hypotheses:

* it is a convex polytope of affine dimension `3` and a **regular polyhedron**
  (`IsRegularPolyhedron`: its isometries act transitively on flags);
* its numbers of geometric vertices, edges and facets (faces of affine dimension `0`, `1`,
  `2`, in the sense of `IsFaceOf`);
* its face type: every facet has `s` edges, every edge lies in two facets, every vertex lies in
  `m` edges — exactly the hypotheses of `results_five_platonic_solids`.

The face lattice is *computed*, not assumed: `Explicit.Data.face_cases` shows every face is
empty, the body, a vertex, a listed edge or a listed facet, from the exposed-face theorem and
kernel-checked certificates. Flag-transitivity is witnessed by products of three reflections.
-/

open Set

namespace EulersGem

namespace Platonic3

open Explicit Platonic

/-- The combinatorial data of a polyhedron: `V`, `E`, `F` and face type `{s, m}`. -/
def HasFaceData (P : Set R3) (V E F s m : ℕ) : Prop :=
  (facesOfDim P 0).ncard = V ∧ (facesOfDim P 1).ncard = E ∧ (facesOfDim P 2).ncard = F ∧
    (∀ f ∈ facesOfDim P 2, {e ∈ facesOfDim P 1 | e ⊆ f}.ncard = s) ∧
    (∀ e ∈ facesOfDim P 1, {f ∈ facesOfDim P 2 | e ⊆ f}.ncard = 2) ∧
    (∀ v ∈ facesOfDim P 0, {e ∈ facesOfDim P 1 | v ⊆ e}.ncard = m)

/-- The regular tetrahedron. -/
noncomputable def tetrahedron : Set R3 := tetraData.body
/-- The cube. -/
noncomputable def cube : Set R3 := cubeData.body
/-- The regular octahedron. -/
noncomputable def octahedron : Set R3 := octaData.body
/-- The regular dodecahedron. -/
noncomputable def dodecahedron : Set R3 := dodecaData.body
/-- The regular icosahedron. -/
noncomputable def icosahedron : Set R3 := icosaData.body

theorem tetrahedron_isRegular : IsRegularPolyhedron tetrahedron :=
  Data.Sym.isRegularPolyhedron tetra_checkAll tetra_checkFlags
theorem cube_isRegular : IsRegularPolyhedron cube :=
  Data.Sym.isRegularPolyhedron cube_checkAll cube_checkFlags
theorem octahedron_isRegular : IsRegularPolyhedron octahedron :=
  Data.Sym.isRegularPolyhedron octa_checkAll octa_checkFlags
theorem dodecahedron_isRegular : IsRegularPolyhedron dodecahedron :=
  Data.Sym.isRegularPolyhedron dodeca_checkAll dodeca_checkFlags
theorem icosahedron_isRegular : IsRegularPolyhedron icosahedron :=
  Data.Sym.isRegularPolyhedron icosa_checkAll icosa_checkFlags

theorem tetrahedron_faceData : HasFaceData tetrahedron 4 6 4 3 3 := by
  have := Data.counts_and_type tetra_checkAll tetra_checkType
  exact this
theorem cube_faceData : HasFaceData cube 8 12 6 4 3 := by
  have := Data.counts_and_type cube_checkAll cube_checkType
  exact this
theorem octahedron_faceData : HasFaceData octahedron 6 12 8 3 4 := by
  have := Data.counts_and_type octa_checkAll octa_checkType
  exact this
theorem dodecahedron_faceData : HasFaceData dodecahedron 20 30 12 5 3 := by
  have := Data.counts_and_type dodeca_checkAll dodeca_checkType
  exact this
theorem icosahedron_faceData : HasFaceData icosahedron 12 30 20 3 5 := by
  have := Data.counts_and_type icosa_checkAll icosa_checkType
  exact this

/-- **The five Platonic solids exist.** Each is a regular convex polyhedron in `ℝ³` with the
classical vertex, edge and facet counts and face type. -/
theorem five_platonic_solids_exist :
    (IsRegularPolyhedron tetrahedron ∧ HasFaceData tetrahedron 4 6 4 3 3) ∧
    (IsRegularPolyhedron cube ∧ HasFaceData cube 8 12 6 4 3) ∧
    (IsRegularPolyhedron octahedron ∧ HasFaceData octahedron 6 12 8 3 4) ∧
    (IsRegularPolyhedron dodecahedron ∧ HasFaceData dodecahedron 20 30 12 5 3) ∧
    (IsRegularPolyhedron icosahedron ∧ HasFaceData icosahedron 12 30 20 3 5) :=
  ⟨⟨tetrahedron_isRegular, tetrahedron_faceData⟩, ⟨cube_isRegular, cube_faceData⟩,
    ⟨octahedron_isRegular, octahedron_faceData⟩, ⟨dodecahedron_isRegular, dodecahedron_faceData⟩,
    ⟨icosahedron_isRegular, icosahedron_faceData⟩⟩

end Platonic3

end EulersGem
