/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.EulerChar
import EulersGem.Polytope
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Conical cell structure toward Euler–Poincaré (Paulson)

Port of the cone step of AFP `Euler_Formula`:

* polyhedral cones as cell complexes of their supporting arrangement
  (see `EulersGem.Polytope`)
* Euler characteristic of `univ` equals `(-1)^{finrank}`
* soft inclusion-exclusion identity `EC(S ∪ T) = EC(S)+EC(T)-EC(S ∩ T)`
* **proved:** cell-complex Euler char of a single nontrivial halfspace cone is `0`
* **proved (halfspace):** face ↔ cell bijection and `faceEulerSum = 0`
  (see `EulersGem.FaceCell`)
* targets stated as docs (not Results): general `Euler_polyhedral_cone`,
  `Euler_Poincare_full`, 3D `V−E+F=2`

Blocker for the general theorems: face ↔ relative-interior-cell bijection for
*general* polyhedral cones (Paulson `hyper1`/`hyper2`); needs face lattice /
minimal H-rep beyond the halfspace case.
-/

open scoped RealInnerProductSpace BigOperators
open Classical Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace EulersGem

/-! ### Euler char of the ambient space -/

/-- For any finite arrangement, `eulerCharacteristic A univ = (-1)^{finrank}`. -/
lemma eulerCharacteristic_univ [FiniteDimensional ℝ E] [Nonempty E]
    {A : Set (Hyperplane E)} (hA : A.Finite) :
    eulerCharacteristic A (univ : Set E) = (-1 : ℤ) ^ Module.finrank ℝ E := by
  have hEmpty : (∅ : Set (Hyperplane E)).Finite := finite_empty
  have hAuniv : IsHyperplaneCellComplex A (univ : Set E) :=
    isHyperplaneCellComplex_univ A
  have hEuniv : IsHyperplaneCellComplex (∅ : Set (Hyperplane E)) (univ : Set E) :=
    isHyperplaneCellComplex_univ _
  have hInv := eulerCharacteristic_invariant hA hEmpty hAuniv hEuniv
  rw [hInv, eulerCharacteristic_empty_arrangement_univ]

/-! ### Soft inclusion-exclusion -/

/-- Soft inclusion-exclusion from disjoint additivity:
`EC(S ∪ T) = EC(S) + EC(T) - EC(S ∩ T)`. -/
lemma eulerCharacteristic_union_inter {A : Set (Hyperplane E)} {S T : Set E}
    (hA : A.Finite)
    (hS : IsHyperplaneCellComplex A S) (hT : IsHyperplaneCellComplex A T) :
    eulerCharacteristic A (S ∪ T) =
      eulerCharacteristic A S + eulerCharacteristic A T -
        eulerCharacteristic A (S ∩ T) := by
  have hDiff : IsHyperplaneCellComplex A (T \ S) :=
    isHyperplaneCellComplex_diff hT hS
  have hInter : IsHyperplaneCellComplex A (S ∩ T) :=
    isHyperplaneCellComplex_inter hS hT
  have hdisj₁ : Disjoint S (T \ S) := disjoint_sdiff_right
  have hdisj₂ : Disjoint (S ∩ T) (T \ S) :=
    disjoint_left.mpr fun _x hx hx' => hx'.2 hx.1
  have hEq1 : S ∪ T = S ∪ (T \ S) := by
    ext x; by_cases hxS : x ∈ S <;> simp [hxS]
  have hEq2 : T = (S ∩ T) ∪ (T \ S) := by
    ext x; by_cases hxS : x ∈ S <;> simp [hxS]
  have h1 :=
    (eulerCharacteristic_cellcomplex_union hA hS hDiff hdisj₁).symm.trans
      (congrArg (eulerCharacteristic A) hEq1.symm)
  -- h1 : EC(S) + EC(T\S) = EC(S ∪ T)
  have h2 :=
    (eulerCharacteristic_cellcomplex_union hA hInter hDiff hdisj₂).symm.trans
      (congrArg (eulerCharacteristic A) hEq2.symm)
  -- h2 : EC(S∩T) + EC(T\S) = EC(T)
  have h1' : eulerCharacteristic A (S ∪ T) =
      eulerCharacteristic A S + eulerCharacteristic A (T \ S) := h1.symm
  have h2' : eulerCharacteristic A T =
      eulerCharacteristic A (S ∩ T) + eulerCharacteristic A (T \ S) := h2.symm
  linarith

/-! ### Halfspace cone: cell Euler char = 0 -/

lemma compl_closedHalfspace_zero (a : E) :
    (closedHalfspace a 0)ᶜ = {x : E | 0 < ⟪a, x⟫} := by
  ext x
  change ¬⟪a, x⟫ ≤ 0 ↔ 0 < ⟪a, x⟫
  constructor <;> intro h <;> linarith

lemma affDim_openHalfspace_gt [FiniteDimensional ℝ E] [Nonempty E]
    {a : E} (ha : a ≠ 0) :
    affDim {x : E | 0 < ⟪a, x⟫} = Module.finrank ℝ E := by
  have hne : (univ ∩ {x : E | (0 : ℝ) < ⟪a, x⟫}).Nonempty :=
    ⟨a, mem_univ a, real_inner_self_pos.mpr ha⟩
  have h := affDim_cell_inter_halfSpace_gt
    (A := (∅ : Set (Hyperplane E))) (C := (univ : Set E))
    finite_empty ((isHyperplaneCell_empty_arrangement univ).mpr rfl) a 0 hne
  have hEq : (univ : Set E) ∩ {x | (0 : ℝ) < ⟪a, x⟫} = {x | 0 < ⟪a, x⟫} := by
    ext; simp
  rw [← hEq, h, affDim_univ]

/-- Cell-complex Euler characteristic of a nontrivial closed halfspace cone is `0`.
Special case of the cone step toward Paulson `Euler_polyhedral_cone`. -/
theorem eulerCharacteristic_halfspace_cone [FiniteDimensional ℝ E] [Nonempty E]
    {a : E} (ha : a ≠ 0) :
    eulerCharacteristic {(a, (0 : ℝ))} (closedHalfspace a 0) = 0 := by
  have hA : ({(a, (0 : ℝ))} : Set (Hyperplane E)).Finite := finite_singleton _
  have hS : IsHyperplaneCellComplex {(a, (0 : ℝ))} (closedHalfspace a 0) :=
    isHyperplaneCellComplex_closedHalfspace_zero a
  have hComplCx : IsHyperplaneCellComplex {(a, (0 : ℝ))} (closedHalfspace a 0)ᶜ :=
    isHyperplaneCellComplex_compl hS
  have hUniv := eulerCharacteristic_univ (A := {(a, (0 : ℝ))}) hA
  have hdisj : Disjoint (closedHalfspace a 0) (closedHalfspace a 0)ᶜ :=
    disjoint_compl_right
  have hUnion : closedHalfspace a 0 ∪ (closedHalfspace a 0)ᶜ = univ :=
    union_compl_self _
  have hAdd :=
    eulerCharacteristic_cellcomplex_union hA hS hComplCx hdisj
  rw [hUnion, hUniv] at hAdd
  have hComplCell : IsHyperplaneCell {(a, (0 : ℝ))} (closedHalfspace a 0)ᶜ := by
    rw [compl_closedHalfspace_zero]
    exact isHyperplaneCell_eq_halfSpace_gt ha
  have hECcompl :
      eulerCharacteristic {(a, (0 : ℝ))} (closedHalfspace a 0)ᶜ =
        (-1 : ℤ) ^ Module.finrank ℝ E := by
    rw [eulerCharacteristic_cell hA hComplCell, cellSign,
      compl_closedHalfspace_zero, affDim_openHalfspace_gt ha]
    simp
  omega

lemma convex_linear_hyperplane (a : E) : Convex ℝ {x : E | ⟪a, x⟫ = 0} :=
  convex_hyperplane (isLinearMap_inner a) 0

/-- Bounding hyperplane is a face of the closed halfspace cone. -/
lemma isFaceOf_closedHalfspace_hyperplane (a : E) :
    IsFaceOf (closedHalfspace a 0) {x : E | ⟪a, x⟫ = 0} := by
  refine ⟨⟨fun x hx => le_of_eq hx, ?_⟩, convex_linear_hyperplane a⟩
  intro x hxA y hyA z hzB hzSeg
  obtain ⟨b, c, hb, hc, _hbc, rfl⟩ := hzSeg
  change ⟪a, x⟫ ≤ 0 at hxA
  change ⟪a, y⟫ ≤ 0 at hyA
  have hz : ⟪a, b • x + c • y⟫ = 0 := hzB
  have hsum : b * ⟪a, x⟫ + c * ⟪a, y⟫ = 0 := by
    simpa [inner_add_right, inner_smul_right] using hz
  have hx0 : ⟪a, x⟫ = 0 := by
    have hbax : b * ⟪a, x⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb.le hxA
    have hcoy : c * ⟪a, y⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le hyA
    nlinarith
  exact hx0

/-- Affine dimension of a nontrivial linear hyperplane is `finrank - 1`. -/
lemma affDim_linear_hyperplane [FiniteDimensional ℝ E] [Nonempty E]
    {a : E} (ha : a ≠ 0) :
    affDim {x : E | ⟪a, x⟫ = 0} = Module.finrank ℝ E - 1 := by
  have hne : (((⊤ : AffineSubspace ℝ E) : Set E) ∩ {x | ⟪a, x⟫ = 0}).Nonempty := by
    obtain ⟨p, hp⟩ := exists_mem_hyperplane (b := 0) ha
    exact ⟨p, trivial, hp⟩
  have hnot : ¬ ((⊤ : AffineSubspace ℝ E) : Set E) ⊆ {x | ⟪a, x⟫ = 0} := by
    intro h
    have : ⟪a, a⟫ = 0 := h (by trivial : a ∈ (⊤ : AffineSubspace ℝ E))
    exact ha (inner_self_eq_zero.mp this)
  have h := affDim_affine_inter_hyperplane (⊤ : AffineSubspace ℝ E) a 0 hne hnot
  -- (⊤ : Set) = univ
  have hTop : ((⊤ : AffineSubspace ℝ E) : Set E) = univ := rfl
  rw [hTop, univ_inter, affDim_univ] at h
  exact h

/-- Stated Paulson targets (not claimed in Results.lean until proved in full). -/
def EulerPolyhedralConeGoal : String :=
  "faceEulerSum S (finrank) = 0 for full-dim proper polyhedral cones"

def EulerPoincareFullGoal : String :=
  "faceEulerSum p (finrank) = 1 for full-dimensional convex polytopes"

def EulerRelation3DGoal : String :=
  "V - E + F = 2 for convex 3-polytopes (after Euler_Poincare_full)"

end EulersGem
