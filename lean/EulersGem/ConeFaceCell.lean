/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.FaceCell
import Mathlib.Topology.Order.OrderClosed

/-!
# General cone face ↔ cell substrate (Paulson `hyper1` / `hyper2`)

Beyond the halfspace special case in `FaceCell`:

* closure of a nontrivial open halfspace
* sign-pattern dichotomy for cone-arrangement cells inside a polyhedral cone
* supporting-hyperplane faces from finite zero-sets
* **hyper2 (face direction):** closure of a cell ⊆ cone is a face of the cone

Remaining for full `Euler_polyhedral_cone`:

* recover the cell as RI of its closure
* hyper1 (every face arises as such a closure) — needs minimal H-rep
* hence `faceEulerSum = eulerCharacteristic = 0`
-/

open scoped RealInnerProductSpace BigOperators
open Classical Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace EulersGem

/-! ### Closure of open halfspaces -/

lemma isClosed_closedHalfspace (a : E) (b : ℝ) : IsClosed (closedHalfspace a b) :=
  isClosed_le (continuous_const.inner continuous_id) continuous_const

/-- Nontrivial open halfspace `{⟪a,x⟫ < 0}` has closure the closed halfspace. -/
lemma closure_halfSpace_lt {a : E} (ha : a ≠ 0) :
    closure {x : E | ⟪a, x⟫ < 0} = closedHalfspace a 0 := by
  apply subset_antisymm
  · exact closure_minimal (fun x (hx : ⟪a, x⟫ < 0) => (le_of_lt hx : x ∈ closedHalfspace a 0))
      (isClosed_closedHalfspace a 0)
  · intro x hx
    change ⟪a, x⟫ ≤ 0 at hx
    refine mem_closure_iff_nhds.2 fun U hU => ?_
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    let t : ℝ := ε / (2 * ‖a‖)
    have ht : 0 < t := div_pos hε (by positivity)
    refine ⟨x - t • a, hball ?_, ?_⟩
    · simp [norm_smul, Real.norm_of_nonneg ht.le]
      have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
      have : t * ‖a‖ = ε / 2 := by simp only [t]; field_simp [hna]
      linarith
    · change ⟪a, x - t • a⟫ < 0
      have hpos : 0 < ⟪a, a⟫ := real_inner_self_pos.mpr ha
      have : ⟪a, x⟫ - t * ⟪a, a⟫ < 0 := by
        have : 0 < t * ⟪a, a⟫ := by positivity
        linarith
      simpa [inner_sub_right, inner_smul_right] using this

/-- Finite intersection of open halfspaces: closure is the closed orthant. -/
lemma closure_iInter_halfSpace_lt {As : Set E} (hAs : As.Finite)
    (hne : ({x : E | ∀ a ∈ As, ⟪a, x⟫ < 0}).Nonempty) :
    closure {x : E | ∀ a ∈ As, ⟪a, x⟫ < 0} =
      {x : E | ∀ a ∈ As, ⟪a, x⟫ ≤ 0} := by
  apply subset_antisymm
  · refine closure_minimal (fun x hx a ha => le_of_lt (hx a ha)) ?_
    classical
    have hEq : {x : E | ∀ a ∈ As, ⟪a, x⟫ ≤ 0} =
        ⋂ a ∈ hAs.toFinset, closedHalfspace a 0 := by
      ext x; simp [Finite.mem_toFinset, closedHalfspace]
    rw [hEq]
    exact isClosed_biInter fun _ _ => isClosed_closedHalfspace _ _
  · intro x hx
    obtain ⟨z, hz⟩ := hne
    refine mem_closure_iff_nhds.2 fun U hU => ?_
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    let t : ℝ := min (1 / 2) (ε / (2 * (‖z - x‖ + 1)))
    have ht0 : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
    have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
    let y : E := (1 - t) • x + t • z
    have hyOpen : ∀ a ∈ As, ⟪a, y⟫ < 0 := by
      intro a ha
      have hxA : ⟪a, x⟫ ≤ 0 := hx a ha
      have hzA : ⟪a, z⟫ < 0 := hz a ha
      have : ⟪a, y⟫ = (1 - t) * ⟪a, x⟫ + t * ⟪a, z⟫ := by
        simp only [y, inner_add_right, inner_smul_right]
      rw [this]
      have h1 : (1 - t) * ⟪a, x⟫ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) hxA
      have h2 : t * ⟪a, z⟫ < 0 := mul_neg_of_pos_of_neg ht0 hzA
      linarith
    have hdist : dist y x < ε := by
      have hdist' : dist y x = t * ‖z - x‖ := by
        simp only [y, dist_eq_norm]
        have : (1 - t) • x + t • z - x = t • (z - x) := by module
        rw [this, norm_smul, Real.norm_of_nonneg ht0.le]
      have hle : t ≤ ε / (2 * (‖z - x‖ + 1)) := min_le_right _ _
      have hden : 0 < ‖z - x‖ + 1 := by positivity
      have hfrac : ε / (2 * (‖z - x‖ + 1)) * ‖z - x‖ ≤ ε / 2 := by
        have hnn : 0 ≤ ‖z - x‖ := norm_nonneg _
        have hε0 : 0 ≤ ε := le_of_lt hε
        field_simp
        nlinarith
      have hmul : t * ‖z - x‖ ≤ ε / 2 := by
        have := mul_le_mul_of_nonneg_right hle (norm_nonneg (z - x))
        linarith
      calc dist y x = t * ‖z - x‖ := hdist'
        _ ≤ ε / 2 := hmul
        _ < ε := by linarith
    exact ⟨y, hball hdist, hyOpen⟩

/-! ### Sign patterns on cone-arrangement cells -/

/-- Normals that vanish identically on a cell. -/
def coneCellZeros (As : Set E) (C : Set E) : Set E :=
  {a ∈ As | ∀ x ∈ C, ⟪a, x⟫ = 0}

/-- Normals that are strictly negative on a cell. -/
def coneCellNegs (As : Set E) (C : Set E) : Set E :=
  {a ∈ As | ∀ x ∈ C, ⟪a, x⟫ < 0}

lemma coneCellZeros_subset (As : Set E) (C : Set E) : coneCellZeros As C ⊆ As :=
  fun _a ha => ha.1

lemma coneCellNegs_subset (As : Set E) (C : Set E) : coneCellNegs As C ⊆ As :=
  fun _a ha => ha.1

lemma coneCellZeros_disjoint_negs {As C : Set E} (hne : C.Nonempty) :
    Disjoint (coneCellZeros As C) (coneCellNegs As C) := by
  refine disjoint_left.mpr ?_
  intro a haZ haN
  obtain ⟨x, hx⟩ := hne
  have hlt := haN.2 x hx
  have heq := haZ.2 x hx
  linarith

/-- On a cone-arrangement cell contained in the polyhedral cone, every normal is either
identically zero or strictly negative. -/
lemma coneCell_sign_dichotomy {As : Set E} {C : Set E}
    (hC : IsHyperplaneCell (coneArrangement As) C)
    (hsub : C ⊆ ⋂ a ∈ As, closedHalfspace a 0) :
    As = coneCellZeros As C ∪ coneCellNegs As C := by
  obtain ⟨x, rfl⟩ := hC
  ext a
  constructor
  · intro ha
    have hxS : x ∈ closedHalfspace a 0 :=
      (mem_iInter.mp ((mem_iInter.mp (hsub (hyperplaneEquiv_refl _ x))) a)) ha
    change ⟪a, x⟫ ≤ 0 at hxS
    by_cases h0 : ⟪a, x⟫ = 0
    · refine Or.inl ⟨ha, ?_⟩
      intro y hy
      have hside : hyperplaneSide (a, (0 : ℝ)) x = hyperplaneSide (a, (0 : ℝ)) y :=
        hy (a, (0 : ℝ)) ⟨a, ha, rfl⟩
      have hxside : hyperplaneSide (a, (0 : ℝ)) x = 0 :=
        (hyperplaneSide_eq_zero_iff a 0 x).mpr h0
      exact (hyperplaneSide_eq_zero_iff a 0 y).mp (hside ▸ hxside)
    · have hlt : ⟪a, x⟫ < 0 := lt_of_le_of_ne hxS h0
      refine Or.inr ⟨ha, ?_⟩
      intro y hy
      have hside : hyperplaneSide (a, (0 : ℝ)) x = hyperplaneSide (a, (0 : ℝ)) y :=
        hy (a, (0 : ℝ)) ⟨a, ha, rfl⟩
      have hxside : hyperplaneSide (a, (0 : ℝ)) x = -1 :=
        (hyperplaneSide_eq_neg_one_iff a 0 x).mpr hlt
      exact (hyperplaneSide_eq_neg_one_iff a 0 y).mp (hside ▸ hxside)
  · rintro (h | h) <;> exact h.1

/-- Explicit sign-pattern description of a cone-arrangement cell inside the cone. -/
lemma coneCell_eq_sign_pattern {As : Set E} {C : Set E}
    (hC : IsHyperplaneCell (coneArrangement As) C)
    (hsub : C ⊆ ⋂ a ∈ As, closedHalfspace a 0) :
    C = {x : E | (∀ a ∈ coneCellNegs As C, ⟪a, x⟫ < 0) ∧
      (∀ a ∈ coneCellZeros As C, ⟪a, x⟫ = 0)} := by
  obtain ⟨z, rfl⟩ := hC
  set C : Set E := {y | HyperplaneEquiv (coneArrangement As) z y}
  have hdich := coneCell_sign_dichotomy (C := C) ⟨z, rfl⟩ hsub
  ext y
  constructor
  · intro hy
    exact ⟨fun a ha => ha.2 y hy, fun a ha => ha.2 y hy⟩
  · intro ⟨hyNeg, hyZero⟩ h hh
    obtain ⟨a, ha, rfl⟩ := hh
    have ha' : a ∈ coneCellZeros As C ∪ coneCellNegs As C := by
      rw [← hdich]; exact ha
    rcases ha' with haZ | haN
    · have hz0 : ⟪a, z⟫ = 0 := haZ.2 z (hyperplaneEquiv_refl _ z)
      have hy0 : ⟪a, y⟫ = 0 := hyZero a haZ
      rw [(hyperplaneSide_eq_zero_iff a 0 z).mpr hz0,
        (hyperplaneSide_eq_zero_iff a 0 y).mpr hy0]
    · have hzlt : ⟪a, z⟫ < 0 := haN.2 z (hyperplaneEquiv_refl _ z)
      have hylt : ⟪a, y⟫ < 0 := hyNeg a haN
      rw [(hyperplaneSide_eq_neg_one_iff a 0 z).mpr hzlt,
        (hyperplaneSide_eq_neg_one_iff a 0 y).mpr hylt]

/-! ### Supporting-hyperplane faces (finite intersections) -/

/-- Intersection of a polyhedral cone with finitely many defining hyperplanes is a face. -/
lemma isFaceOf_polyhedralCone_inter_zeros {As : Set E} {J : Set E} (hJ : J ⊆ As)
    (hJfin : J.Finite) :
    IsFaceOf (⋂ a ∈ As, closedHalfspace a 0)
      ((⋂ a ∈ As, closedHalfspace a 0) ∩ ⋂ a ∈ J, {x : E | ⟪a, x⟫ = 0}) := by
  classical
  refine Set.Finite.induction_on
    (motive := fun J' _ => J' ⊆ As →
      IsFaceOf (⋂ a ∈ As, closedHalfspace a 0)
        ((⋂ a ∈ As, closedHalfspace a 0) ∩ ⋂ a ∈ J', {x : E | ⟪a, x⟫ = 0}))
    J hJfin ?empty ?insert hJ
  · intro _
    have hEq : (⋂ a ∈ As, closedHalfspace a 0) ∩ ⋂ a ∈ (∅ : Set E), {x : E | ⟪a, x⟫ = 0} =
        ⋂ a ∈ As, closedHalfspace a 0 := by
      ext x; simp
    rw [hEq]
    exact isFaceOf_refl (convex_iInter fun a => convex_iInter fun _ => convex_closedHalfspace a 0)
  · intro a J' _haJ' _hJ'fin ih hsub
    have ha : a ∈ As := hsub (mem_insert a J')
    have hrest : J' ⊆ As := (subset_insert _ _).trans hsub
    have hEq :
        (⋂ b ∈ As, closedHalfspace b 0) ∩ ⋂ b ∈ insert a J', {x : E | ⟪b, x⟫ = 0} =
          ((⋂ b ∈ As, closedHalfspace b 0) ∩ ⋂ b ∈ J', {x : E | ⟪b, x⟫ = 0}) ∩
            ((⋂ b ∈ As, closedHalfspace b 0) ∩ {x : E | ⟪a, x⟫ = 0}) := by
      ext x
      simp only [mem_inter_iff, mem_iInter, mem_insert_iff, mem_ofPred_eq]
      constructor
      · intro ⟨hxS, hxJ⟩
        exact ⟨⟨hxS, fun b hb => hxJ b (Or.inr hb)⟩, hxS, hxJ a (Or.inl rfl)⟩
      · rintro ⟨⟨hxS, hxJ'⟩, -, hxa⟩
        refine ⟨hxS, ?_⟩
        intro b hb
        rcases hb with rfl | hb
        · exact hxa
        · exact hxJ' b hb
    rw [hEq]
    exact isFaceOf_inter (ih hrest) (isFaceOf_polyhedralCone_eq_hyperplane ha)

lemma isClosed_iInter_hyperplanes {J : Set E} (hJ : J.Finite) :
    IsClosed (⋂ a ∈ J, {x : E | ⟪a, x⟫ = 0}) := by
  classical
  have hEq : (⋂ a ∈ J, {x : E | ⟪a, x⟫ = 0}) =
      ⋂ a ∈ hJ.toFinset, {x : E | ⟪a, x⟫ = 0} := by
    ext x; simp [Finite.mem_toFinset]
  rw [hEq]
  exact isClosed_biInter fun _ _ =>
    isClosed_eq (continuous_const.inner continuous_id) continuous_const

lemma cone_face_eq_closed_pattern {As : Set E} {C : Set E}
    (hC : IsHyperplaneCell (coneArrangement As) C)
    (hsub : C ⊆ ⋂ a ∈ As, closedHalfspace a 0) :
    (⋂ a ∈ As, closedHalfspace a 0) ∩ ⋂ a ∈ coneCellZeros As C, {x : E | ⟪a, x⟫ = 0} =
      {x : E | (∀ a ∈ coneCellNegs As C, ⟪a, x⟫ ≤ 0) ∧
        (∀ a ∈ coneCellZeros As C, ⟪a, x⟫ = 0)} := by
  have hdich := coneCell_sign_dichotomy hC hsub
  ext x
  constructor
  · intro hx
    have hxS := hx.1
    have hxZ := hx.2
    refine ⟨?_, ?_⟩
    · intro a haN
      exact (mem_iInter₂.mp hxS a haN.1 : x ∈ closedHalfspace a 0)
    · intro a haZ
      exact (mem_iInter₂.mp hxZ a haZ : ⟪a, x⟫ = 0)
  · intro ⟨hxN, hxZ⟩
    constructor
    · refine mem_iInter₂.mpr fun a haAs => ?_
      have ha' : a ∈ coneCellZeros As C ∪ coneCellNegs As C := by
        rw [← hdich]; exact haAs
      rcases ha' with haZz | haNn
      · exact le_of_eq (hxZ a haZz)
      · exact hxN a haNn
    · exact mem_iInter₂.mpr hxZ

/-- `closure (U ∩ H) = closure U ∩ H` for open orthant `U` and closed flat `H`. -/
lemma closure_inter_closedOrthant_flat {Neg Zero : Set E}
    (hNeg : Neg.Finite)
    (hne : ({x : E | (∀ a ∈ Neg, ⟪a, x⟫ < 0) ∧ (∀ a ∈ Zero, ⟪a, x⟫ = 0)}).Nonempty)
    (hZero : Zero.Finite) :
    closure ({x : E | ∀ a ∈ Neg, ⟪a, x⟫ < 0} ∩ ⋂ a ∈ Zero, {x : E | ⟪a, x⟫ = 0}) =
      closure {x : E | ∀ a ∈ Neg, ⟪a, x⟫ < 0} ∩ ⋂ a ∈ Zero, {x : E | ⟪a, x⟫ = 0} := by
  set U : Set E := {x : E | ∀ a ∈ Neg, ⟪a, x⟫ < 0}
  set H : Set E := ⋂ a ∈ Zero, {x : E | ⟪a, x⟫ = 0}
  apply subset_antisymm
  · exact closure_minimal (fun _x hx => ⟨subset_closure hx.1, hx.2⟩)
      (isClosed_closure.inter (isClosed_iInter_hyperplanes hZero))
  · intro x hx
    have hxU : x ∈ closure U := hx.1
    have hxH : x ∈ H := hx.2
    obtain ⟨z, hzU, hzH⟩ := hne
    have hclU : closure U = {y : E | ∀ a ∈ Neg, ⟪a, y⟫ ≤ 0} :=
      closure_iInter_halfSpace_lt hNeg ⟨z, hzU⟩
    have hxN : ∀ a ∈ Neg, ⟪a, x⟫ ≤ 0 := by
      have : x ∈ closure U := hxU
      rwa [hclU] at this
    refine mem_closure_iff_nhds.2 fun V hV => ?_
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
    let t : ℝ := min (1 / 2) (ε / (2 * (‖z - x‖ + 1)))
    have ht0 : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
    have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
    let y : E := (1 - t) • x + t • z
    have hyH : y ∈ H := by
      refine mem_iInter₂.mpr fun a ha => ?_
      change ⟪a, y⟫ = 0
      have hx0 : ⟪a, x⟫ = 0 := mem_iInter₂.mp hxH a ha
      have hz0 : ⟪a, z⟫ = 0 := hzH a ha
      have : ⟪a, y⟫ = (1 - t) * ⟪a, x⟫ + t * ⟪a, z⟫ := by
        simp only [y, inner_add_right, inner_smul_right]
      rw [this, hx0, hz0]; ring
    have hyU : y ∈ U := by
      intro a ha
      have hzA : ⟪a, z⟫ < 0 := hzU a ha
      have hxA : ⟪a, x⟫ ≤ 0 := hxN a ha
      have : ⟪a, y⟫ = (1 - t) * ⟪a, x⟫ + t * ⟪a, z⟫ := by
        simp only [y, inner_add_right, inner_smul_right]
      rw [this]
      have h1 : (1 - t) * ⟪a, x⟫ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) hxA
      have h2 : t * ⟪a, z⟫ < 0 := mul_neg_of_pos_of_neg ht0 hzA
      linarith
    have hdist : dist y x < ε := by
      have hdist' : dist y x = t * ‖z - x‖ := by
        simp only [y, dist_eq_norm]
        have : (1 - t) • x + t • z - x = t • (z - x) := by module
        rw [this, norm_smul, Real.norm_of_nonneg ht0.le]
      have hle : t ≤ ε / (2 * (‖z - x‖ + 1)) := min_le_right _ _
      have hden : 0 < ‖z - x‖ + 1 := by positivity
      have hfrac : ε / (2 * (‖z - x‖ + 1)) * ‖z - x‖ ≤ ε / 2 := by
        have hnn : 0 ≤ ‖z - x‖ := norm_nonneg _
        have hε0 : 0 ≤ ε := le_of_lt hε
        field_simp
        nlinarith
      have hmul : t * ‖z - x‖ ≤ ε / 2 := by
        have := mul_le_mul_of_nonneg_right hle (norm_nonneg (z - x))
        linarith
      calc dist y x = t * ‖z - x‖ := hdist'
        _ ≤ ε / 2 := hmul
        _ < ε := by linarith
    exact ⟨y, hball hdist, ⟨hyU, hyH⟩⟩

/-- Closure of a cone-arrangement cell inside the cone equals the supporting-hyperplane face
cut out by the cell's zero normals. Paulson `hyper2` (closure). -/
theorem closure_coneCell_eq_face {As : Set E} (hAs : As.Finite) {C : Set E}
    (hC : IsHyperplaneCell (coneArrangement As) C)
    (hsub : C ⊆ ⋂ a ∈ As, closedHalfspace a 0) :
    closure C =
      (⋂ a ∈ As, closedHalfspace a 0) ∩
        ⋂ a ∈ coneCellZeros As C, {x : E | ⟪a, x⟫ = 0} := by
  set Neg := coneCellNegs As C
  set Zero := coneCellZeros As C
  set U : Set E := {x : E | ∀ a ∈ Neg, ⟪a, x⟫ < 0}
  set H : Set E := ⋂ a ∈ Zero, {x : E | ⟪a, x⟫ = 0}
  have hpat := coneCell_eq_sign_pattern hC hsub
  have hCeq : C = U ∩ H := by
    rw [hpat]
    ext x
    constructor
    · intro ⟨hN, hZ⟩
      exact ⟨hN, mem_iInter₂.mpr hZ⟩
    · intro ⟨hN, hZ⟩
      exact ⟨hN, fun a ha => mem_iInter₂.mp hZ a ha⟩
  have hneAnd : ({x : E | (∀ a ∈ Neg, ⟪a, x⟫ < 0) ∧ (∀ a ∈ Zero, ⟪a, x⟫ = 0)}).Nonempty := by
    obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hC
    have hx' : x ∈ C := hx
    rw [hpat] at hx'
    exact ⟨x, hx'.1, hx'.2⟩
  have hNegfin : Neg.Finite := hAs.subset (coneCellNegs_subset As C)
  have hZerofin : Zero.Finite := hAs.subset (coneCellZeros_subset As C)
  have hclUH :=
    closure_inter_closedOrthant_flat (Neg := Neg) (Zero := Zero) hNegfin hneAnd hZerofin
  obtain ⟨z0, hz0U, _⟩ := hneAnd
  have hclU : closure U = {x : E | ∀ a ∈ Neg, ⟪a, x⟫ ≤ 0} :=
    closure_iInter_halfSpace_lt hNegfin ⟨z0, hz0U⟩
  have hpatClosed := cone_face_eq_closed_pattern hC hsub
  have hEq : {x : E | ∀ a ∈ Neg, ⟪a, x⟫ ≤ 0} ∩ H =
      {x : E | (∀ a ∈ Neg, ⟪a, x⟫ ≤ 0) ∧ (∀ a ∈ Zero, ⟪a, x⟫ = 0)} := by
    ext x
    constructor
    · intro ⟨hN, hH⟩
      exact ⟨hN, fun a ha => mem_iInter₂.mp hH a ha⟩
    · intro ⟨hN, hZ⟩
      exact ⟨hN, mem_iInter₂.mpr hZ⟩
  calc
    closure C = closure (U ∩ H) := by rw [hCeq]
    _ = closure U ∩ H := hclUH
    _ = {x : E | ∀ a ∈ Neg, ⟪a, x⟫ ≤ 0} ∩ H := by rw [hclU]
    _ = {x : E | (∀ a ∈ Neg, ⟪a, x⟫ ≤ 0) ∧ (∀ a ∈ Zero, ⟪a, x⟫ = 0)} := hEq
    _ = (⋂ a ∈ As, closedHalfspace a 0) ∩ ⋂ a ∈ Zero, {x : E | ⟪a, x⟫ = 0} := by
        simpa [Neg, Zero] using hpatClosed.symm

/-- Paulson `hyper2`: the closure of a cone-arrangement cell inside the cone is a face. -/
theorem isFaceOf_closure_coneCell {As : Set E} (hAs : As.Finite) {C : Set E}
    (hC : IsHyperplaneCell (coneArrangement As) C)
    (hsub : C ⊆ ⋂ a ∈ As, closedHalfspace a 0) :
    IsFaceOf (⋂ a ∈ As, closedHalfspace a 0) (closure C) := by
  rw [closure_coneCell_eq_face hAs hC hsub]
  exact isFaceOf_polyhedralCone_inter_zeros (coneCellZeros_subset As C)
    (hAs.subset (coneCellZeros_subset As C))

end EulersGem
