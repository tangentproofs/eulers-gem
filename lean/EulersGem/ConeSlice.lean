/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.EulerPoincare
import Mathlib.LinearAlgebra.AffineSpace.Dimension

/-!
# Geometric cone↔slice correspondence (Paulson)

Partial geometric discharge of `ConeSliceFaceBijection` (Paulson slice lemma):

* `affDim = 0` ⇒ singleton (under `FiniteDimensional`)
* faces of conic sets are conic (`face_of_conic`)
* apex `{0}` is the unique 0-face of `conicHull p` on a height-1 convex slice
* homogenization H-rep **contains** the cone (one inclusion; equality still open)
* height-1 slice of a cone-face is a face of `p`
* recover conic face from its height-1 slice (nonzero points)
* `InjOn conicHull` on height-1 faces

Still open for full bijection: lift `IsFaceOf p F → IsFaceOf (conicHull p) (conicHull F)`,
`affDim (conicHull F) = affDim F + 1`, and homogenized H-rep equality.
-/

open scoped RealInnerProductSpace
open Classical Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace EulersGem

lemma eq_singleton_of_affDim_eq_zero [FiniteDimensional ℝ E]
    {s : Set E} (h : affDim s = 0) : ∃ a, s = {a} := by
  have hsne : s.Nonempty := by
    by_contra hempty
    have : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    subst this
    simp [affDim_empty] at h
  have hspanNe : (affineSpan ℝ s : Set E).Nonempty :=
    (affineSpan_nonempty (k := ℝ) (V := E) (P := E)).mpr hsne
  have hneBot : affineSpan ℝ s ≠ ⊥ := (AffineSubspace.nonempty_iff_ne_bot _).mp hspanNe
  have hfd : (affineSpan ℝ s).finDim = (0 : WithBot ℕ) := by
    cases hmatch : (affineSpan ℝ s).finDim with
    | bot => exact absurd (AffineSubspace.finDim_eq_bot_iff.mp hmatch) hneBot
    | coe n =>
      simp only [affDim, hmatch] at h
      have : n = 0 := by exact_mod_cast h
      simp [this]
  have : FiniteDimensional ℝ (affineSpan ℝ s).direction := inferInstance
  have hsub : (affineSpan ℝ s : Set E).Subsingleton :=
    (AffineSubspace.finDim_le_zero_iff_subsingleton (s := affineSpan ℝ s)).mp (by simp [hfd])
  obtain ⟨a, ha⟩ := hsne
  refine ⟨a, Subset.antisymm ?_ (singleton_subset_iff.mpr ha)⟩
  intro x hx
  exact hsub (mem_affineSpan ℝ hx) (mem_affineSpan ℝ ha) ▸ rfl

lemma isConic_of_isFaceOf {S F : Set E} (hS : IsConic S) (hF : IsFaceOf S F) :
    IsConic F := by
  intro x hxF c hc
  by_cases hx0 : x = 0
  · subst hx0; simpa using hxF
  · by_cases hc1 : c = 1
    · subst hc1; simpa using hxF
    · obtain ⟨d, e, hd0, he0, hdlt, hegt, hdc⟩ :
          ∃ d e : ℝ, 0 ≤ d ∧ 0 ≤ e ∧ d < 1 ∧ 1 < e ∧ (d = c ∨ e = c) := by
        by_cases hclt : c < 1
        · exact ⟨c, 2, hc, by norm_num, hclt, by norm_num, Or.inl rfl⟩
        · exact ⟨0, c, le_rfl, hc, by norm_num,
            lt_of_le_of_ne (not_lt.mp hclt) (Ne.symm hc1), Or.inr rfl⟩
      have hde : d < e := by rcases hdc with rfl | rfl <;> linarith
      have hxS : x ∈ S := hF.isExtreme.subset hxF
      have hdS : d • x ∈ S := hS hxS d hd0
      have heS : e • x ∈ S := hS hxS e he0
      set a : ℝ := (e - 1) / (e - d)
      set b : ℝ := (1 - d) / (e - d)
      have hden : e - d ≠ 0 := by linarith
      have ha : 0 < a := div_pos (by linarith) (by linarith)
      have hb : 0 < b := div_pos (by linarith) (by linarith)
      have hab : a + b = 1 := by
        dsimp [a, b]
        rw [← add_div, show (e - 1) + (1 - d) = e - d by ring, div_self hden]
      have hcoef : a * d + b * e = 1 := by
        dsimp [a, b]
        have := mul_div_cancel₀ ((e - 1) * d + (1 - d) * e) hden
        -- Direct computation
        field_simp [hden]
        ring
      have hcomb : a • (d • x) + b • (e • x) = x := by
        calc
          a • (d • x) + b • (e • x) = (a * d + b * e) • x := by module
          _ = (1 : ℝ) • x := by rw [hcoef]
          _ = x := one_smul _ _
      have hseg : x ∈ openSegment ℝ (d • x) (e • x) := ⟨a, b, ha, hb, hab, hcomb⟩
      have hdF := hF.isExtreme.left_mem_of_mem_openSegment hdS heS hxF hseg
      have heF := hF.isExtreme.right_mem_of_mem_openSegment hdS heS hxF hseg
      rcases hdc with rfl | rfl
      · exact hdF
      · exact heF

lemma height_pos_of_mem_conicHull {p : Set E} {i : E}
    (hp : ∀ x ∈ p, ⟪i, x⟫ = 1) {y : E}
    (hy : y ∈ conicHull p) (hne : y ≠ 0) : 0 < ⟪i, y⟫ := by
  obtain ⟨c, x, hc, hx, rfl⟩ := hy
  have hcne : c ≠ 0 := fun h => by subst h; exact hne (by simp)
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcne)
  simpa [inner_smul_right, hp x hx] using hcpos

lemma convex_conicHull {s : Set E} (hs : Convex ℝ s) : Convex ℝ (conicHull s) := by
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  obtain ⟨c₁, x₁, hc₁, hx₁, rfl⟩ := hy₁
  obtain ⟨c₂, x₂, hc₂, hx₂, rfl⟩ := hy₂
  by_cases hsum : a * c₁ + b * c₂ = 0
  · have ha0 : a * c₁ = 0 := by nlinarith [mul_nonneg ha hc₁, mul_nonneg hb hc₂]
    have hb0 : b * c₂ = 0 := by nlinarith [mul_nonneg ha hc₁, mul_nonneg hb hc₂]
    refine ⟨0, x₁, le_rfl, hx₁, ?_⟩
    simp [smul_smul, ha0, hb0]
  · set t := a * c₁ + b * c₂
    have htpos : 0 < t :=
      lt_of_le_of_ne (add_nonneg (mul_nonneg ha hc₁) (mul_nonneg hb hc₂)) (Ne.symm hsum)
    set w₁ : ℝ := (a * c₁) / t
    set w₂ : ℝ := (b * c₂) / t
    have hw1 : 0 ≤ w₁ := div_nonneg (mul_nonneg ha hc₁) htpos.le
    have hw2 : 0 ≤ w₂ := div_nonneg (mul_nonneg hb hc₂) htpos.le
    have hw12 : w₁ + w₂ = 1 := by
      dsimp [w₁, w₂]
      have ht0 : t ≠ 0 := htpos.ne'
      field_simp [ht0]
      rfl
    have hx : w₁ • x₁ + w₂ • x₂ ∈ s := hs hx₁ hx₂ hw1 hw2 hw12
    refine ⟨t, w₁ • x₁ + w₂ • x₂, htpos.le, hx, ?_⟩
    -- a • (c₁ • x₁) + b • (c₂ • x₂) = t • (w₁ • x₁ + w₂ • x₂)
    dsimp [w₁, w₂]
    have ht0 : t ≠ 0 := htpos.ne'
    simp only [smul_add, smul_smul]
    -- Goal: (a * c₁) • x₁ + (b * c₂) • x₂ = (t * (a * c₁ / t)) • x₁ + (t * (b * c₂ / t)) • x₂
    rw [mul_div_cancel₀ _ ht0, mul_div_cancel₀ _ ht0]

lemma coneSlice_zero_face [FiniteDimensional ℝ E] {p : Set E} {i : E}
    (hp : ∀ x ∈ p, ⟪i, x⟫ = 1) (hne : p.Nonempty) (hConv : Convex ℝ p) :
    {f : Set E | IsFaceOf (conicHull p) f ∧ affDim f = 0} =
      ({({0} : Set E)} : Set (Set E)) :=
  faces_dim_zero_eq_singleton_zero (isConic_conicHull p) (convex_conicHull hConv)
    (zero_mem_conicHull hne)
    (fun _x hx hxne => height_pos_of_mem_conicHull hp hx hxne)
    (fun _f _hf hd => eq_singleton_of_affDim_eq_zero hd)

lemma zero_not_mem_affineSpan_of_height {s : Set E} {i : E}
    (hs : ∀ x ∈ s, ⟪i, x⟫ = 1) :
    (0 : E) ∉ affineSpan ℝ s := by
  intro h0
  have hall : ∀ z, z ∈ affineSpan ℝ s → ⟪i, z⟫ = 1 := by
    intro z hz
    refine affineSpan_induction (k := ℝ) (P := E) (p := fun w => ⟪i, w⟫ = 1) hz
      hs fun c u v w hu hv hw => by
        simp [inner_add_right, inner_smul_right, inner_sub_right, hu, hv, hw]
  have : ⟪i, (0 : E)⟫ = 1 := hall 0 h0
  simp [inner_zero_right] at this

lemma conicHull_subset_homogenized_cone {H : Set (Hyperplane E)} {i : E} {p : Set E}
    (hp : p = ⋂ h ∈ H, closedHalfspace h.1 h.2)
    (hht : ∀ x ∈ p, ⟪i, x⟫ = 1) :
    conicHull p ⊆ ⋂ a ∈ homogenizeNormals H i, closedHalfspace a 0 := by
  intro y hy
  obtain ⟨c, x, hc, hx, rfl⟩ := hy
  refine mem_iInter.mpr fun a => mem_iInter.mpr fun ha => ?_
  unfold homogenizeNormals at ha
  rcases ha with hpos | hneg
  · obtain ⟨h, hh, rfl⟩ := hpos
    have hxH : ⟪h.1, x⟫ ≤ h.2 := by
      exact (mem_iInter.mp ((mem_iInter.mp (hp ▸ hx)) h)) hh
    have hle : ⟪h.1 - h.2 • i, c • x⟫ ≤ 0 := by
      have : ⟪h.1 - h.2 • i, c • x⟫ = c * (⟪h.1, x⟫ - h.2) := by
        simp [inner_sub_left, inner_smul_right, inner_smul_left, hht x hx]
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr hxH)
    simpa [closedHalfspace] using hle
  · have ha' : a = -i := by simpa using hneg
    subst ha'
    have hle : ⟪(-i), c • x⟫ ≤ 0 := by
      have hrew : ⟪(-i), c • x⟫ = -(c * ⟪i, x⟫) := by
        simp [inner_smul_right, inner_neg_left]
      rw [hrew, hht x hx, mul_one, neg_nonpos]; exact hc
    simpa [closedHalfspace] using hle

lemma isPolyhedralCone_of_conicHull_eq_homogenized {H : Set (Hyperplane E)} {i : E} {p : Set E}
    (hH : H.Finite)
    (heq : conicHull p = ⋂ a ∈ homogenizeNormals H i, closedHalfspace a 0) :
    IsPolyhedralCone (conicHull p) :=
  ⟨homogenizeNormals H i, homogenizeNormals_finite hH i, heq⟩

lemma isFaceOf_slice_of_isFaceOf_conicHull {p G : Set E} {i : E}
    (hht : ∀ x ∈ p, ⟪i, x⟫ = 1)
    (hG : IsFaceOf (conicHull p) G) :
    IsFaceOf p (G ∩ {x : E | ⟪i, x⟫ = 1}) := by
  set F := G ∩ {x : E | ⟪i, x⟫ = 1}
  have hsub : F ⊆ p := by
    intro x hx
    have : x ∈ conicHull p ∩ {y | ⟪i, y⟫ = 1} :=
      ⟨hG.isExtreme.subset hx.1, hx.2⟩
    rwa [conicHull_inter_height_one hht] at this
  refine ⟨⟨hsub, ?_⟩, hG.convex.inter (convex_hyperplane (isLinearMap_inner i) 1)⟩
  intro x hxP y hyP z hzF hzSeg
  exact ⟨hG.isExtreme.left_mem_of_mem_openSegment
    (subset_conicHull p hxP) (subset_conicHull p hyP) hzF.1 hzSeg, hht x hxP⟩

lemma conicHull_inter_height_eq_of_isConic {G : Set E} {i : E}
    (hG : IsConic G)
    (hpos : ∀ x ∈ G, x ≠ 0 → 0 < ⟪i, x⟫)
    (hne_nz : ∃ z ∈ G, z ≠ 0) :
    conicHull (G ∩ {x : E | ⟪i, x⟫ = 1}) = G := by
  apply subset_antisymm
  · rintro _ ⟨c, x, hc, hx, rfl⟩
    exact hG hx.1 c hc
  · intro y hy
    by_cases hy0 : y = 0
    · subst hy0
      obtain ⟨z, hz, hzne⟩ := hne_nz
      have hzpos := hpos z hz hzne
      refine ⟨0, (⟪i, z⟫)⁻¹ • z, le_rfl,
        ⟨hG hz _ (inv_nonneg.mpr hzpos.le), ?_⟩, by simp⟩
      simp [inner_smul_right, inv_mul_cancel₀ hzpos.ne']
    · have hypos := hpos y hy hy0
      refine ⟨⟪i, y⟫, (⟪i, y⟫)⁻¹ • y, hypos.le,
        ⟨hG hy _ (inv_nonneg.mpr hypos.le), ?_⟩, ?_⟩
      · simp [inner_smul_right, inv_mul_cancel₀ hypos.ne']
      · simp [smul_smul, mul_inv_cancel₀ hypos.ne']

lemma injOn_conicHull_faces {p : Set E} {i : E}
    (hht : ∀ F, IsFaceOf p F → ∀ x ∈ F, ⟪i, x⟫ = 1) (d : ℕ) :
    InjOn conicHull {F : Set E | IsFaceOf p F ∧ affDim F = (d : ℤ)} := by
  intro F₁ hF₁ F₂ hF₂ hEq
  have h1 := (conicHull_inter_height_one (hht F₁ hF₁.1)).symm
  have h2 := (conicHull_inter_height_one (hht F₂ hF₂.1)).symm
  calc
    F₁ = conicHull F₁ ∩ {x | ⟪i, x⟫ = 1} := h1
    _ = conicHull F₂ ∩ {x | ⟪i, x⟫ = 1} := by rw [hEq]
    _ = F₂ := h2.symm

end EulersGem
