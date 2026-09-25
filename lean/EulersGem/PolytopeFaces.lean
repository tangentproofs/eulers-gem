/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.Polytope
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Set.Finite.Powerset

/-!
# Faces of a V-polytope are hulls of their vertices; the face lattice is finite

The classical structure theorem for the face lattice of a polytope:

* `face_eq_convexHull_inter` — a face `F` of `convexHull ℝ V` satisfies
  `F = convexHull ℝ (V ∩ F)`; a face is the hull of the generating points it contains.
* `faces_finite_of_isPolytope` — hence `F ↦ V ∩ F` is injective on faces, so an
  `IsPolytope` has only finitely many faces.
* `facesOfDim_finite_of_isPolytope` — in particular the vertex / edge / 2-face sets
  counted by `euler_relation_convex_3polytope` are finite.

This discharges the face-finiteness hypotheses that `PlatonicOfEuler` would otherwise
have to assume. Everything here is proved from Mathlib convexity (`IsExtreme`,
`convexHull_eq`); nothing is postulated.

The key step (`mem_of_pos_weight`) is the standard argument: if an extreme set contains
a convex combination `∑ wᵢ zᵢ` of points of the ambient set with `w j > 0`, split the
combination as `w j • z j + (1 - w j) • y` and apply extremeness to the open segment
from `z j` to `y`.
-/

open Set

namespace EulersGem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Positive weights in a convex combination land in an extreme set -/

/-- If `F` is extreme in a convex set `A`, and a convex combination `∑ wᵢ • zᵢ` of points
of `A` lies in `F`, then every point with strictly positive weight lies in `F`. -/
theorem mem_of_pos_weight {A F : Set E} (hFext : IsExtreme ℝ A F) (hA : Convex ℝ A)
    {ι : Type*} [DecidableEq ι] {t : Finset ι} {w : ι → ℝ} {z : ι → E}
    (hw : ∀ i ∈ t, 0 ≤ w i) (hsum : ∑ i ∈ t, w i = 1) (hz : ∀ i ∈ t, z i ∈ A)
    (hx : ∑ i ∈ t, w i • z i ∈ F) {j : ι} (hj : j ∈ t) (hwj : 0 < w j) :
    z j ∈ F := by
  classical
  have hwj1 : w j ≤ 1 := by
    have h := Finset.single_le_sum (f := w) hw hj
    rwa [hsum] at h
  have hsplit : ∑ i ∈ t, w i • z i = w j • z j + ∑ i ∈ t.erase j, w i • z i :=
    (Finset.add_sum_erase t (fun i => w i • z i) hj).symm
  have hrest : ∑ i ∈ t.erase j, w i = 1 - w j := by
    have h := Finset.add_sum_erase t w hj
    rw [hsum] at h
    linarith
  rcases eq_or_lt_of_le hwj1 with hone | hlt
  · -- `w j = 1`: every other weight vanishes, so the combination *is* `z j`
    have hzero : ∀ i ∈ t.erase j, w i = 0 := by
      intro i hi
      have hnn : ∀ k ∈ t.erase j, 0 ≤ w k := fun k hk => hw k (Finset.mem_of_mem_erase hk)
      have hle := Finset.single_le_sum (f := w) hnn hi
      rw [hrest, hone] at hle
      have := hw i (Finset.mem_of_mem_erase hi)
      linarith
    have hz0 : ∑ i ∈ t.erase j, w i • z i = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hzero i hi, zero_smul]
    rw [hsplit, hz0, add_zero, hone, one_smul] at hx
    exact hx
  · -- `w j < 1`: `x` is interior to the segment from `z j` to the rescaled remainder
    have hcpos : (0 : ℝ) < 1 - w j := by linarith
    set y : E := ∑ i ∈ t.erase j, ((1 - w j)⁻¹ * w i) • z i with hy
    have hyA : y ∈ A := by
      refine hA.sum_mem (fun i hi => ?_) ?_ fun i hi => hz i (Finset.mem_of_mem_erase hi)
      · exact mul_nonneg (inv_nonneg.mpr hcpos.le) (hw i (Finset.mem_of_mem_erase hi))
      · rw [← Finset.mul_sum, hrest, inv_mul_cancel₀ hcpos.ne']
    have hcy : (1 - w j) • y = ∑ i ∈ t.erase j, w i • z i := by
      rw [hy, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
      congr 1
      field_simp
    have hseg : ∑ i ∈ t, w i • z i ∈ openSegment ℝ (z j) y :=
      ⟨w j, 1 - w j, hwj, hcpos, by ring, by rw [hcy, hsplit]⟩
    exact hFext.left_mem_of_mem_openSegment (hz j hj) hyA hx hseg

/-! ## A face of a V-polytope is the hull of the generators it contains -/

/-- **Faces of a V-polytope are hulls of their vertices.** If `F` is a face of
`convexHull ℝ V` then `F = convexHull ℝ (V ∩ F)`. -/
theorem face_eq_convexHull_inter {V F : Set E}
    (hF : IsFaceOf (convexHull ℝ V) F) :
    F = convexHull ℝ (V ∩ F) := by
  classical
  refine subset_antisymm ?_ (convexHull_min inter_subset_right hF.convex)
  intro x hxF
  have hxhull : x ∈ convexHull ℝ V := hF.isExtreme.subset hxF
  rw [convexHull_eq] at hxhull
  obtain ⟨ι, t, w, z, hw0, hw1, hzV, hcm⟩ := hxhull
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hcm
  -- discard the zero weights
  set t' := t.filter fun i => 0 < w i with ht'
  have hsub : t' ⊆ t := Finset.filter_subset _ _
  have hzeroOut : ∀ i ∈ t, i ∉ t' → w i = 0 := by
    intro i hi hni
    have hnot : ¬ 0 < w i := by
      intro hpos
      exact hni (Finset.mem_filter.mpr ⟨hi, hpos⟩)
    have := hw0 i hi
    linarith [not_lt.mp hnot]
  have hsum' : ∑ i ∈ t', w i = 1 := by
    rw [Finset.sum_subset hsub hzeroOut]; exact hw1
  have hcm' : ∑ i ∈ t', w i • z i = x := by
    rw [Finset.sum_subset hsub fun i hi hni => by rw [hzeroOut i hi hni, zero_smul]]
    exact hcm
  -- every surviving generator lies in the face
  have hmem : ∀ j ∈ t', z j ∈ V ∩ F := by
    intro j hj
    refine ⟨hzV j (hsub hj), ?_⟩
    refine mem_of_pos_weight hF.isExtreme (convex_convexHull ℝ V)
      (fun i hi => hw0 i (hsub hi)) hsum'
      (fun i hi => subset_convexHull ℝ V (hzV i (hsub hi))) ?_ hj
      (Finset.mem_filter.mp hj).2
    rw [hcm']; exact hxF
  rw [← hcm']
  exact (convex_convexHull ℝ (V ∩ F)).sum_mem (fun i hi => hw0 i (hsub hi)) hsum'
    fun i hi => subset_convexHull ℝ _ (hmem i hi)

/-! ## Finiteness of the face lattice -/

/-- **The face lattice of a polytope is finite.** `F ↦ V ∩ F` is injective on faces by
`face_eq_convexHull_inter`, and lands in the (finite) powerset of the generating set. -/
theorem faces_finite_of_isPolytope {p : Set E} (hP : IsPolytope p) :
    {f : Set E | IsFaceOf p f}.Finite := by
  obtain ⟨V, hVfin, rfl⟩ := hP
  refine Set.Finite.of_finite_image (f := fun f => V ∩ f) ?_ ?_
  · refine hVfin.finite_subsets.subset ?_
    rintro s ⟨f, -, rfl⟩
    exact inter_subset_left
  · intro f₁ h₁ f₂ h₂ heq
    have heq' : V ∩ f₁ = V ∩ f₂ := heq
    rw [face_eq_convexHull_inter h₁, face_eq_convexHull_inter h₂, heq']

/-- The faces of a polytope of a given affine dimension form a finite set: exactly the
`V`, `E`, `F` counts of `euler_relation_convex_3polytope`. -/
theorem facesOfDim_finite_of_isPolytope {p : Set E} (hP : IsPolytope p) (d : ℤ) :
    {f : Set E | IsFaceOf p f ∧ affDim f = d}.Finite :=
  (faces_finite_of_isPolytope hP).subset fun _ hf => hf.1

end EulersGem
