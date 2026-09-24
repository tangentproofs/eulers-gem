/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.AffDim
import EulersGem.Hyperplane
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Topology.Order.Basic

/-!
# Geometry of hyperplane cells (Paulson open∩affine / relative interior)

Lean port of the geometric substrate for refinement invariance:

* open half-spaces
* cells as open ∩ affine
* relative (intrinsic) interior of a cell equals the cell
* affine-dimension facts for cuts by a hyperplane / half-space
-/

open scoped RealInnerProductSpace
open Classical Set SignType AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace EulersGem

/-! ### Open half-spaces and affine hyperplanes -/

lemma isOpen_halfSpace_lt (a : E) (b : ℝ) : IsOpen {x : E | ⟪a, x⟫ < b} := by
  change IsOpen ((fun x : E => ⟪a, x⟫) ⁻¹' Iio b)
  exact isOpen_Iio.preimage (continuous_const.inner continuous_id)

lemma isOpen_halfSpace_gt (a : E) (b : ℝ) : IsOpen {x : E | b < ⟪a, x⟫} := by
  change IsOpen ((fun x : E => ⟪a, x⟫) ⁻¹' Ioi b)
  exact isOpen_Ioi.preimage (continuous_const.inner continuous_id)

lemma exists_mem_hyperplane {a : E} (b : ℝ) (ha : a ≠ 0) : ∃ x, ⟪a, x⟫ = b := by
  refine ⟨(b / ⟪a, a⟫) • a, ?_⟩
  have hne : ⟪a, a⟫ ≠ 0 := inner_self_ne_zero.mpr ha
  rw [inner_smul_right]
  exact div_mul_cancel₀ b hne

/-- The set `{x | ⟪a, x⟫ = b}` as an affine subspace, given a witness point. -/
noncomputable def affineHyperplane (a : E) (b : ℝ) (p : E) (_hp : ⟪a, p⟫ = b) :
    AffineSubspace ℝ E :=
  mk' p (LinearMap.ker (innerₛₗ ℝ a))

lemma coe_affineHyperplane (a : E) (b : ℝ) (p : E) (hp : ⟪a, p⟫ = b) :
    (affineHyperplane a b p hp : Set E) = {x | ⟪a, x⟫ = b} := by
  ext x
  constructor
  · intro hx
    have hx' : x -ᵥ p ∈ LinearMap.ker (innerₛₗ ℝ a) := (mem_mk').mp hx
    have h0 : (innerₛₗ ℝ a) (x - p) = 0 := LinearMap.mem_ker.mp hx'
    change ⟪a, x - p⟫ = 0 at h0
    have : ⟪a, x⟫ = ⟪a, p⟫ := by
      have := congrArg (fun t => t + ⟪a, p⟫) h0
      simpa [inner_sub_right] using this
    exact this.trans hp
  · intro hx
    change ⟪a, x⟫ = b at hx
    refine (mem_mk').mpr (LinearMap.mem_ker.mpr ?_)
    change ⟪a, x - p⟫ = 0
    simp [inner_sub_right, hx, hp]

/-! ### Singleton arrangement cells -/

lemma isHyperplaneCell_singleton_zero (b : ℝ) (C : Set E) :
    IsHyperplaneCell {((0 : E), b)} C ↔ C = univ := by
  constructor
  · rintro ⟨x, rfl⟩
    ext y; simp [HyperplaneEquiv, hyperplaneSide, inner_zero_left]
  · rintro rfl
    refine ⟨(0 : E), ?_⟩
    ext y; simp [HyperplaneEquiv, hyperplaneSide, inner_zero_left]

lemma isHyperplaneCell_eq_hyperplane {a : E} {b : ℝ} (ha : a ≠ 0) :
    IsHyperplaneCell {(a, b)} {x | ⟪a, x⟫ = b} := by
  obtain ⟨p, hp⟩ := exists_mem_hyperplane b ha
  refine ⟨p, ?_⟩
  have hp0 : hyperplaneSide (a, b) p = 0 := (hyperplaneSide_eq_zero_iff a b p).mpr hp
  ext y
  simp only [mem_ofPred_eq]
  constructor
  · intro hy h hh
    rw [mem_singleton_iff] at hh; subst hh
    have hy0 : hyperplaneSide (a, b) y = 0 := (hyperplaneSide_eq_zero_iff a b y).mpr hy
    exact hp0.trans hy0.symm
  · intro h
    have : hyperplaneSide (a, b) p = hyperplaneSide (a, b) y := h (a, b) rfl
    exact (hyperplaneSide_eq_zero_iff a b y).mp (this ▸ hp0)

lemma isHyperplaneCell_eq_halfSpace_lt {a : E} {b : ℝ} (ha : a ≠ 0) :
    IsHyperplaneCell {(a, b)} {x | ⟪a, x⟫ < b} := by
  obtain ⟨p0, hp0⟩ := exists_mem_hyperplane b ha
  refine ⟨p0 - a, ?_⟩
  have hp : ⟪a, p0 - a⟫ < b := by
    have hcalc : ⟪a, p0 - a⟫ = b - ⟪a, a⟫ := by simp [inner_sub_right, hp0]
    have hpos : 0 < ⟪a, a⟫ := real_inner_self_pos.mpr ha
    linarith
  have hx : hyperplaneSide (a, b) (p0 - a) = -1 :=
    (hyperplaneSide_eq_neg_one_iff a b _).mpr hp
  ext y
  simp only [mem_ofPred_eq]
  constructor
  · intro hy h hh
    rw [mem_singleton_iff] at hh; subst hh
    have hy' : hyperplaneSide (a, b) y = -1 :=
      (hyperplaneSide_eq_neg_one_iff a b y).mpr hy
    exact hx.trans hy'.symm
  · intro h
    have : hyperplaneSide (a, b) (p0 - a) = hyperplaneSide (a, b) y := h (a, b) rfl
    exact (hyperplaneSide_eq_neg_one_iff a b y).mp (this ▸ hx)

lemma isHyperplaneCell_eq_halfSpace_gt {a : E} {b : ℝ} (ha : a ≠ 0) :
    IsHyperplaneCell {(a, b)} {x | b < ⟪a, x⟫} := by
  obtain ⟨p0, hp0⟩ := exists_mem_hyperplane b ha
  refine ⟨p0 + a, ?_⟩
  have hp : b < ⟪a, p0 + a⟫ := by
    have hcalc : ⟪a, p0 + a⟫ = b + ⟪a, a⟫ := by simp [inner_add_right, hp0]
    have hpos : 0 < ⟪a, a⟫ := real_inner_self_pos.mpr ha
    linarith
  have hx : hyperplaneSide (a, b) (p0 + a) = 1 :=
    (hyperplaneSide_eq_one_iff a b _).mpr hp
  ext y
  simp only [mem_ofPred_eq]
  constructor
  · intro hy h hh
    rw [mem_singleton_iff] at hh; subst hh
    have hy' : hyperplaneSide (a, b) y = 1 :=
      (hyperplaneSide_eq_one_iff a b y).mpr hy
    exact hx.trans hy'.symm
  · intro h
    have : hyperplaneSide (a, b) (p0 + a) = hyperplaneSide (a, b) y := h (a, b) rfl
    exact (hyperplaneSide_eq_one_iff a b y).mp (this ▸ hx)

/-- Singleton arrangement cells. Isabelle: `hyperplane_cell_singleton`. -/
lemma isHyperplaneCell_singleton (a : E) (b : ℝ) (C : Set E) :
    IsHyperplaneCell {(a, b)} C ↔
      if a = 0 then C = univ
      else C = {x | ⟪a, x⟫ = b} ∨ C = {x | ⟪a, x⟫ < b} ∨ C = {x | b < ⟪a, x⟫} := by
  split_ifs with ha
  · subst ha; exact isHyperplaneCell_singleton_zero b C
  · constructor
    · exact isHyperplaneCell_singleton_cases
    · rintro (h | h | h)
      · exact h ▸ isHyperplaneCell_eq_hyperplane ha
      · exact h ▸ isHyperplaneCell_eq_halfSpace_lt ha
      · exact h ▸ isHyperplaneCell_eq_halfSpace_gt ha

/-! ### Open ∩ affine structure -/

/-- Affine hull of a nonempty open∩affine set equals the affine subspace.
Isabelle helper: `affine_hull_affine_Int_open`. -/
lemma affineSpan_isOpen_inter {T : AffineSubspace ℝ E} {U : Set E}
    (hU : IsOpen U) (hne : (U ∩ (T : Set E)).Nonempty) :
    affineSpan ℝ (U ∩ (T : Set E)) = T := by
  obtain ⟨p, hpU, hpT⟩ := hne
  have : Nonempty T := ⟨⟨p, hpT⟩⟩
  let U' : Set T := (↑) ⁻¹' U
  have hU'open : IsOpen U' := continuous_subtype_val.isOpen_preimage U hU
  have hU'ne : U'.Nonempty := ⟨⟨p, hpT⟩, hpU⟩
  have hspan' : affineSpan ℝ U' = ⊤ :=
    IsOpen.affineSpan_eq_top (V := T.direction) hU'open hU'ne
  have heq : (↑) '' U' = U ∩ (T : Set E) :=
    (Subtype.image_preimage_coe (T : Set E) U).trans (by rw [inter_comm])
  have hmap := AffineSubspace.map_span (f := AffineSubspace.subtype T) (k := ℝ) U'
  rw [hspan'] at hmap
  have htop : (⊤ : AffineSubspace ℝ T).map (AffineSubspace.subtype T) = T := by
    refine SetLike.coe_injective ?_
    ext x; simp [AffineSubspace.coe_map]
  have hcoe : (⇑(AffineSubspace.subtype T) '' U') = (↑) '' U' := by
    simp [AffineSubspace.coe_subtype]
  rw [← heq, ← hcoe, ← hmap, htop]

/-- Every cell of a finite arrangement is the intersection of an open set and an
affine subspace. Isabelle: `hyperplane_cell_Int_open_affine`. -/
lemma isHyperplaneCell_exists_isOpen_affine {A : Set (Hyperplane E)}
    (hA : A.Finite) {C : Set E} (hC : IsHyperplaneCell A C) :
    ∃ U : Set E, ∃ T : AffineSubspace ℝ E, IsOpen U ∧ C = U ∩ (T : Set E) := by
  suffices h : ∀ (A : Set (Hyperplane E)) (_hA : A.Finite) (C : Set E),
      IsHyperplaneCell A C →
        ∃ U : Set E, ∃ T : AffineSubspace ℝ E, IsOpen U ∧ C = U ∩ (T : Set E) by
    exact h A hA C hC
  intro A hA
  refine Set.Finite.induction_on
    (motive := fun A _ => ∀ C, IsHyperplaneCell A C →
      ∃ U : Set E, ∃ T : AffineSubspace ℝ E, IsOpen U ∧ C = U ∩ (T : Set E))
    A hA ?empty ?insert
  · intro C hC
    have hEq : C = univ := (isHyperplaneCell_empty_arrangement C).mp hC
    refine ⟨univ, ⊤, isOpen_univ, ?_⟩
    simp [hEq]
  · intro p A hpA hA ih C hC
    obtain ⟨a, b⟩ := (p : Hyperplane E)
    have hC' : IsHyperplaneCell ({(a, b)} ∪ A) C := by
      rwa [show insert (a, b) A = {(a, b)} ∪ A from insert_eq _ _] at hC
    obtain ⟨hne, C1, C0, hC1, hC0, rfl⟩ := (isHyperplaneCell_union {(a, b)} A C).mp hC'
    obtain ⟨U, T, hU, hC0eq⟩ := ih C0 hC0
    by_cases ha : a = 0
    · have hC1eq : C1 = univ := by
        have := (isHyperplaneCell_singleton a b C1).mp hC1
        simpa [ha] using this
      refine ⟨U, T, hU, ?_⟩
      simp [hC1eq, hC0eq]
    · have hcases := (isHyperplaneCell_singleton a b C1).mp hC1
      simp only [ha, ↓reduceIte] at hcases
      rcases hcases with h1 | h1 | h1
      · obtain ⟨q, hq⟩ := exists_mem_hyperplane b ha
        let T' := T ⊓ affineHyperplane a b q hq
        refine ⟨U, T', hU, ?_⟩
        have hcoe : (T' : Set E) = (T : Set E) ∩ {x | ⟪a, x⟫ = b} := by
          simp [T', coe_inf, coe_affineHyperplane]
        calc C1 ∩ C0
            = {x | ⟪a, x⟫ = b} ∩ (U ∩ (T : Set E)) := by rw [h1, hC0eq]
          _ = U ∩ ((T : Set E) ∩ {x | ⟪a, x⟫ = b}) := by ac_rfl
          _ = U ∩ (T' : Set E) := by rw [hcoe]
      · refine ⟨U ∩ {x | ⟪a, x⟫ < b}, T, hU.inter (isOpen_halfSpace_lt a b), ?_⟩
        calc C1 ∩ C0
            = {x | ⟪a, x⟫ < b} ∩ (U ∩ (T : Set E)) := by rw [h1, hC0eq]
          _ = (U ∩ {x | ⟪a, x⟫ < b}) ∩ (T : Set E) := by ac_rfl
      · refine ⟨U ∩ {x | b < ⟪a, x⟫}, T, hU.inter (isOpen_halfSpace_gt a b), ?_⟩
        calc C1 ∩ C0
            = {x | b < ⟪a, x⟫} ∩ (U ∩ (T : Set E)) := by rw [h1, hC0eq]
          _ = (U ∩ {x | b < ⟪a, x⟫}) ∩ (T : Set E) := by ac_rfl

/-- The affine span of a cell equals the affine factor in its open∩affine
decomposition. -/
lemma affineSpan_eq_of_isHyperplaneCell {A : Set (Hyperplane E)} {C : Set E}
    (_hA : A.Finite) (hC : IsHyperplaneCell A C)
    {U : Set E} {T : AffineSubspace ℝ E}
    (hU : IsOpen U) (hCeq : C = U ∩ (T : Set E)) :
    affineSpan ℝ C = T := by
  have hCne : C.Nonempty := nonempty_isHyperplaneCell hC
  have hUT : (U ∩ (T : Set E)).Nonempty := by simpa [hCeq] using hCne
  rw [hCeq]; exact affineSpan_isOpen_inter hU hUT

/-- Cells are open in the subspace topology of their affine hull.
Isabelle: `hyperplane_cell_relatively_open`. -/
lemma isHyperplaneCell_isOpen_affineSpan {A : Set (Hyperplane E)} {C : Set E}
    (hA : A.Finite) (hC : IsHyperplaneCell A C) :
    ∃ U : Set E, IsOpen U ∧ C = U ∩ (affineSpan ℝ C : Set E) := by
  obtain ⟨U, T, hU, hCeq⟩ := isHyperplaneCell_exists_isOpen_affine hA hC
  have hspan : affineSpan ℝ C = T := affineSpan_eq_of_isHyperplaneCell hA hC hU hCeq
  refine ⟨U, hU, ?_⟩
  simpa [hspan] using hCeq

/-- Relative (intrinsic) interior of a cell equals the cell.
Isabelle: `hyperplane_cell_relative_interior`. -/
lemma isHyperplaneCell_intrinsicInterior {A : Set (Hyperplane E)} {C : Set E}
    (hA : A.Finite) (hC : IsHyperplaneCell A C) :
    intrinsicInterior ℝ C = C := by
  obtain ⟨U, hU, hCeq⟩ := isHyperplaneCell_isOpen_affineSpan hA hC
  have hmem : ∀ (x : affineSpan ℝ C), (x : E) ∈ C ↔ (x : E) ∈ U := by
    intro x
    constructor
    · intro hx
      have hx' : (x : E) ∈ U ∩ (affineSpan ℝ C : Set E) := by
        rw [← hCeq]; exact hx
      exact hx'.1
    · intro hxU
      have : (x : E) ∈ U ∩ (affineSpan ℝ C : Set E) := ⟨hxU, Subtype.property x⟩
      rwa [← hCeq] at this
  have hpre : ((↑) ⁻¹' C : Set (affineSpan ℝ C)) = (↑) ⁻¹' U := by
    ext x
    exact hmem x
  have hopen : IsOpen ((↑) ⁻¹' C : Set (affineSpan ℝ C)) := by
    rw [hpre]
    exact continuous_subtype_val.isOpen_preimage U hU
  have hinter : interior ((↑) ⁻¹' C : Set (affineSpan ℝ C)) = (↑) ⁻¹' C :=
    hopen.interior_eq
  unfold intrinsicInterior
  rw [hinter]
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, hyC, rfl⟩; exact hyC
  · intro hx; exact ⟨⟨x, subset_affineSpan ℝ C hx⟩, hx, rfl⟩

/-- Affine dimension of a cell equals that of its affine hull factor. -/
lemma affDim_eq_finDim_affineSpan (s : Set E) :
    affDim s =
      match (affineSpan ℝ s).finDim with
      | ⊥ => (-1 : ℤ)
      | (n : ℕ) => (n : ℤ) :=
  rfl


/-! ### Affine dimension of cells and cuts -/

/-- `affDim` depends only on the affine span. -/
lemma affDim_eq_of_affineSpan_eq {s t : Set E} (h : affineSpan ℝ s = affineSpan ℝ t) :
    affDim s = affDim t := by
  simp only [affDim, h]

/-- `affDim` of a nonempty open∩affine set equals `affDim` of the affine carrier. -/
lemma affDim_isOpen_inter {T : AffineSubspace ℝ E} {U : Set E}
    (hU : IsOpen U) (hne : (U ∩ (T : Set E)).Nonempty) :
    affDim (U ∩ (T : Set E)) = affDim (T : Set E) := by
  have hspan := affineSpan_isOpen_inter hU hne
  apply affDim_eq_of_affineSpan_eq
  rw [hspan, affineSpan_coe]

/-- Open half-space cut of a cell (when nonempty) preserves affine dimension.
Uses that the cut remains open∩affine with the same affine factor. -/
lemma affDim_cell_inter_halfSpace_lt {A : Set (Hyperplane E)} {C : Set E}
    (hA : A.Finite) (hC : IsHyperplaneCell A C) (a : E) (b : ℝ)
    (hne : (C ∩ {x | ⟪a, x⟫ < b}).Nonempty) :
    affDim (C ∩ {x | ⟪a, x⟫ < b}) = affDim C := by
  obtain ⟨U, T, hU, hCeq⟩ := isHyperplaneCell_exists_isOpen_affine hA hC
  have hspanC : affineSpan ℝ C = T := affineSpan_eq_of_isHyperplaneCell hA hC hU hCeq
  have hU' : IsOpen (U ∩ {x | ⟪a, x⟫ < b}) := hU.inter (isOpen_halfSpace_lt a b)
  have heq : C ∩ {x | ⟪a, x⟫ < b} = (U ∩ {x | ⟪a, x⟫ < b}) ∩ (T : Set E) := by
    simp only [hCeq]; ac_rfl
  have hne' : ((U ∩ {x | ⟪a, x⟫ < b}) ∩ (T : Set E)).Nonempty := by
    simpa [heq] using hne
  have hspan : affineSpan ℝ (C ∩ {x | ⟪a, x⟫ < b}) = T := by
    rw [heq]; exact affineSpan_isOpen_inter hU' hne'
  exact affDim_eq_of_affineSpan_eq (hspan.trans hspanC.symm)

lemma affDim_cell_inter_halfSpace_gt {A : Set (Hyperplane E)} {C : Set E}
    (hA : A.Finite) (hC : IsHyperplaneCell A C) (a : E) (b : ℝ)
    (hne : (C ∩ {x | b < ⟪a, x⟫}).Nonempty) :
    affDim (C ∩ {x | b < ⟪a, x⟫}) = affDim C := by
  obtain ⟨U, T, hU, hCeq⟩ := isHyperplaneCell_exists_isOpen_affine hA hC
  have hspanC : affineSpan ℝ C = T := affineSpan_eq_of_isHyperplaneCell hA hC hU hCeq
  have hU' : IsOpen (U ∩ {x | b < ⟪a, x⟫}) := hU.inter (isOpen_halfSpace_gt a b)
  have heq : C ∩ {x | b < ⟪a, x⟫} = (U ∩ {x | b < ⟪a, x⟫}) ∩ (T : Set E) := by
    simp only [hCeq]; ac_rfl
  have hne' : ((U ∩ {x | b < ⟪a, x⟫}) ∩ (T : Set E)).Nonempty := by
    simpa [heq] using hne
  have hspan : affineSpan ℝ (C ∩ {x | b < ⟪a, x⟫}) = T := by
    rw [heq]; exact affineSpan_isOpen_inter hU' hne'
  exact affDim_eq_of_affineSpan_eq (hspan.trans hspanC.symm)

end EulersGem
