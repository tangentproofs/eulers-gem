/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.PolytopeHalfspaces
import EulersGem.PolytopeFaces

/-!
# Every nonempty face of a polytope is exposed

For a convex polytope `p = convexHull ℝ V` (`V` finite) in a finite-dimensional real inner
product space, every nonempty face `F` is cut out by a supporting hyperplane:
`F = {x ∈ p | ⟪a, x⟫ = c}` with `⟪a, ·⟫ ≤ c` on `p`.

Proof: by `IsPolytope.isPolyhedron` (V-to-H), `p` is a finite intersection of halfspaces.
Let `J` be the constraints tight on all of `F`, and sum them. A point `x₀ ∈ F` that is slack
on every other constraint (an average of witnesses) lets any `z ∈ p` tight on `J` be pushed
past `x₀`, so `x₀` lies in an open segment from `z`; extremality puts `z` in `F`.

This is the tool that turns the face lattice of an explicit polytope into a finite
computation: a face is the hull of the vertices maximising some linear functional.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace EulersGem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Faces of polytopes are exposed.** -/
theorem IsPolytope.exposed_of_isFaceOf [FiniteDimensional ℝ E] {p : Set E}
    (hP : IsPolytope p) {F : Set E} (hF : IsFaceOf p F) (hne : F.Nonempty) :
    ∃ a : E, ∃ c : ℝ, (∀ x ∈ p, ⟪a, x⟫ ≤ c) ∧ F = {x ∈ p | ⟪a, x⟫ = c} := by
  classical
  obtain ⟨H, hH, hp⟩ := hP.isPolyhedron
  have hmemp : ∀ x, x ∈ p ↔ ∀ h ∈ H, ⟪h.1, x⟫ ≤ h.2 := by
    intro x; rw [hp]; simp [closedHalfspace]
  have hFp : F ⊆ p := isFaceOf_subset hF
  set Hs := hH.toFinset with hHs
  set J := Hs.filter (fun h => ∀ x ∈ F, ⟪h.1, x⟫ = h.2) with hJ
  set K := Hs.filter (fun h => ¬ ∀ x ∈ F, ⟪h.1, x⟫ = h.2) with hK
  have hJH : ∀ h ∈ J, h ∈ H := fun h hh => hH.mem_toFinset.1 (Finset.mem_filter.1 hh).1
  have hKH : ∀ h ∈ K, h ∈ H := fun h hh => hH.mem_toFinset.1 (Finset.mem_filter.1 hh).1
  have hJtight : ∀ h ∈ J, ∀ x ∈ F, ⟪h.1, x⟫ = h.2 := fun h hh => (Finset.mem_filter.1 hh).2
  refine ⟨∑ h ∈ J, h.1, ∑ h ∈ J, h.2, ?_, ?_⟩
  · intro x hx
    rw [sum_inner]
    exact Finset.sum_le_sum fun h hh => (hmemp x).1 hx h (hJH h hh)
  ext z
  constructor
  · intro hz
    refine ⟨hFp hz, ?_⟩
    rw [sum_inner]
    exact Finset.sum_congr rfl fun h hh => hJtight h hh z hz
  rintro ⟨hzp, hzc⟩
  -- every constraint in `J` is tight at `z`
  have hzJ : ∀ h ∈ J, ⟪h.1, z⟫ = h.2 := by
    have hsum : ∑ h ∈ J, (h.2 - ⟪h.1, z⟫) = 0 := by
      rw [Finset.sum_sub_distrib, ← sum_inner, hzc, sub_self]
    have hnn : ∀ h ∈ J, 0 ≤ h.2 - ⟪h.1, z⟫ :=
      fun h hh => sub_nonneg.2 ((hmemp z).1 hzp h (hJH h hh))
    intro h hh
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum h hh
    linarith
  -- witnesses of slackness for the constraints in `K`
  have hy : ∀ h ∈ K, ∃ y ∈ F, ⟪h.1, y⟫ < h.2 := by
    intro h hh
    have hnot := (Finset.mem_filter.1 hh).2
    push Not at hnot
    obtain ⟨y, hyF, hyne⟩ := hnot
    exact ⟨y, hyF, lt_of_le_of_ne ((hmemp y).1 (hFp hyF) h (hKH h hh)) hyne⟩
  choose! y hyF hylt using hy
  obtain ⟨f0, hf0⟩ := hne
  let T : Finset (Option (Hyperplane E)) := K.insertNone
  let pt : Option (Hyperplane E) → E := fun o => o.elim f0 y
  let x0 : E := T.centerMass (fun _ => (1 : ℝ)) pt
  have hTpos : (0 : ℝ) < ∑ _i ∈ T, (1 : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast Finset.card_pos.2 ⟨none, Finset.mem_insertNone.2 (by simp)⟩
  have hptF : ∀ o ∈ T, pt o ∈ F := by
    intro o ho
    rcases o with _ | h
    · exact hf0
    · exact hyF h (Finset.mem_insertNone.1 ho h rfl)
  have hx0F : x0 ∈ F :=
    hF.convex.centerMass_mem (fun _ _ => zero_le_one) hTpos hptF
  -- `x0` is slack on every constraint of `K`
  have hx0K : ∀ h ∈ K, ⟪h.1, x0⟫ < h.2 := by
    intro h hh
    have hle : ∀ o ∈ T, ⟪h.1, pt o⟫ ≤ h.2 :=
      fun o ho => (hmemp _).1 (hFp (hptF o ho)) h (hKH h hh)
    have hlt : ∑ o ∈ T, ⟪h.1, pt o⟫ < ∑ _o ∈ T, h.2 :=
      Finset.sum_lt_sum hle ⟨some h, by simpa [T] using hh, hylt h hh⟩
    have hx0 : ⟪h.1, x0⟫ = (∑ _i ∈ T, (1 : ℝ))⁻¹ * ∑ o ∈ T, ⟪h.1, pt o⟫ := by
      simp only [x0, Finset.centerMass, inner_smul_right, inner_sum, one_smul]
    rw [hx0]
    have hc : ∑ _o ∈ T, h.2 = (∑ _i ∈ T, (1 : ℝ)) * h.2 := by
      rw [Finset.sum_mul, one_mul]
    rw [hc] at hlt
    rw [inv_mul_lt_iff₀ hTpos]
    linarith
  -- push `x0` slightly away from `z`
  set d : E := x0 - z
  have hev : ∀ h ∈ K, ∀ᶠ ε in 𝓝 (0 : ℝ), ⟪h.1, x0 + ε • d⟫ < h.2 := by
    intro h hh
    have hc : Continuous fun ε : ℝ => ⟪h.1, x0 + ε • d⟫ := by fun_prop
    have h0 : (fun ε : ℝ => ⟪h.1, x0 + ε • d⟫) 0 < h.2 := by simpa using hx0K h hh
    exact hc.continuousAt.eventually_lt continuousAt_const h0
  have hevK : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ h ∈ K, ⟪h.1, x0 + ε • d⟫ < h.2 :=
    ((Filter.eventually_all_finset K).2 hev).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, hεK, hεpos⟩ := (hevK.and self_mem_nhdsWithin).exists
  have hεpos : (0 : ℝ) < ε := hεpos
  set y' : E := x0 + ε • d
  have hy'p : y' ∈ p := by
    refine (hmemp y').2 fun h hh => ?_
    have hhs : h ∈ Hs := hH.mem_toFinset.2 hh
    by_cases ht : ∀ x ∈ F, ⟪h.1, x⟫ = h.2
    · have hhJ : h ∈ J := Finset.mem_filter.2 ⟨hhs, ht⟩
      have : ⟪h.1, y'⟫ = h.2 := by
        simp only [y', d, inner_add_right, inner_smul_right, inner_sub_right,
          ht x0 hx0F, hzJ h hhJ, sub_self, mul_zero, add_zero]
      exact this.le
    · exact (hεK h (Finset.mem_filter.2 ⟨hhs, ht⟩)).le
  have hseg : x0 ∈ openSegment ℝ z y' := by
    have h1 : (0 : ℝ) < 1 + ε := by positivity
    refine ⟨ε / (1 + ε), 1 / (1 + ε), by positivity, by positivity,
      by field_simp; ring, ?_⟩
    have ha : ε / (1 + ε) - 1 / (1 + ε) * ε = 0 := by field_simp; ring
    have hb : 1 / (1 + ε) + 1 / (1 + ε) * ε = 1 := by field_simp
    calc (ε / (1 + ε)) • z + (1 / (1 + ε)) • (x0 + ε • (x0 - z))
        = (ε / (1 + ε) - 1 / (1 + ε) * ε) • z + (1 / (1 + ε) + 1 / (1 + ε) * ε) • x0 := by
          simp only [smul_add, smul_sub, smul_smul, sub_smul, add_smul]; abel
      _ = x0 := by rw [ha, hb, zero_smul, zero_add, one_smul]
  exact hF.isExtreme.left_mem_of_mem_openSegment hzp hy'p hx0F hseg

/-- **Faces of a V-polytope are hulls of maximisers.** Every nonempty face of
`convexHull ℝ V` (`V` finite) is `convexHull ℝ {v ∈ V | ⟪a, v⟫ = c}` for some `a`, `c` with
`⟪a, ·⟫ ≤ c` on `V`. -/
theorem face_eq_convexHull_argmax [FiniteDimensional ℝ E] {V : Set E} (hV : V.Finite)
    {F : Set E} (hF : IsFaceOf (convexHull ℝ V) F) (hne : F.Nonempty) :
    ∃ a : E, ∃ c : ℝ, (∀ v ∈ V, ⟪a, v⟫ ≤ c) ∧
      F = convexHull ℝ {v ∈ V | ⟪a, v⟫ = c} := by
  obtain ⟨a, c, hle, hFeq⟩ := IsPolytope.exposed_of_isFaceOf ⟨V, hV, rfl⟩ hF hne
  have hleV : ∀ v ∈ V, ⟪a, v⟫ ≤ c := fun v hv => hle v (subset_convexHull ℝ V hv)
  exact ⟨a, c, hleV, hFeq.trans (inter_hyperplane_eq_convexHull_argmax hleV)⟩

end EulersGem
