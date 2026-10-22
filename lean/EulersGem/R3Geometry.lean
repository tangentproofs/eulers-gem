/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.ZPhi
import EulersGem.PolytopeFaces

/-!
# Coordinates in real three-space

`R3 = EuclideanSpace ℝ (Fin 3)`, a coordinate cross product `R3.crs`, and the facts the
explicit-polytope machinery needs:

* `inner_mul_crs` — if `a ⟂ x` and `a ⟂ y` then `a` is parallel to `x × y`, in the
  division-free form `⟪a, z⟫ ‖x × y‖² = ⟪a, x × y⟫ ⟪x × y, z⟫`;
* linear independence of two vectors with nonzero cross product, and of three with nonzero
  triple product;
* affine dimensions `1`, `2`, `3` of point sets witnessed this way.
-/

open Set
open scoped RealInnerProductSpace

namespace EulersGem

/-- Real three-space. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

namespace R3

/-- Coordinate cross product. -/
noncomputable def crs (x y : R3) : R3 :=
  !₂[x 1 * y 2 - x 2 * y 1, x 2 * y 0 - x 0 * y 2, x 0 * y 1 - x 1 * y 0]

@[simp] lemma crs_0 (x y : R3) : crs x y 0 = x 1 * y 2 - x 2 * y 1 := rfl
@[simp] lemma crs_1 (x y : R3) : crs x y 1 = x 2 * y 0 - x 0 * y 2 := rfl
@[simp] lemma crs_2 (x y : R3) : crs x y 2 = x 0 * y 1 - x 1 * y 0 := rfl

lemma inner_eq (p q : R3) : ⟪p, q⟫ = p 0 * q 0 + p 1 * q 1 + p 2 * q 2 :=
  ZPhi.V.inner_R3 p q

lemma toR3_cross (u v : ZPhi.V) : (ZPhi.V.cross u v).toR3 = crs u.toR3 v.toR3 :=
  ZPhi.V.ext_R3 (by simp [ZPhi.V.cross, ZPhi.V.toR3]) (by simp [ZPhi.V.cross, ZPhi.V.toR3])
    (by simp [ZPhi.V.cross, ZPhi.V.toR3])

/-- A vector orthogonal to `x` and `y` is parallel to `x × y` (division-free form). -/
theorem inner_mul_crs {a x y : R3} (hx : ⟪a, x⟫ = 0) (hy : ⟪a, y⟫ = 0) (z : R3) :
    ⟪a, z⟫ * ⟪crs x y, crs x y⟫ = ⟪a, crs x y⟫ * ⟪crs x y, z⟫ := by
  simp only [inner_eq, crs_0, crs_1, crs_2] at *
  set n0 := x 1 * y 2 - x 2 * y 1
  set n1 := x 2 * y 0 - x 0 * y 2
  set n2 := x 0 * y 1 - x 1 * y 0
  -- `x · (z × n)` and `y · (z × n)`
  linear_combination
    (x 0 * (z 1 * n2 - z 2 * n1) + x 1 * (z 2 * n0 - z 0 * n2) + x 2 * (z 0 * n1 - z 1 * n0)) * hy
    - (y 0 * (z 1 * n2 - z 2 * n1) + y 1 * (z 2 * n0 - z 0 * n2) + y 2 * (z 0 * n1 - z 1 * n0)) * hx

lemma inner_self_crs_pos {x y : R3} (h : crs x y ≠ 0) : 0 < ⟪crs x y, crs x y⟫ :=
  real_inner_self_pos.2 h

/-- Two vectors with nonzero cross product are linearly independent. -/
theorem linearIndependent_pair {x y : R3} (h : crs x y ≠ 0) : LinearIndependent ℝ ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have e : ∀ i, s * x i + t * y i = 0 := by
    intro i
    have := congrArg (fun v : R3 => v i) hst
    simpa using this
  have hpos := inner_self_crs_pos h
  rw [inner_eq] at hpos
  simp only [crs_0, crs_1, crs_2] at hpos
  have e0 := e 0; have e1 := e 1; have e2 := e 2
  constructor
  · have hs : s * ((x 1 * y 2 - x 2 * y 1) * (x 1 * y 2 - x 2 * y 1) +
        (x 2 * y 0 - x 0 * y 2) * (x 2 * y 0 - x 0 * y 2) +
        (x 0 * y 1 - x 1 * y 0) * (x 0 * y 1 - x 1 * y 0)) = 0 := by
      linear_combination ((x 1 * y 2 - x 2 * y 1) * y 2) * e1
        - ((x 1 * y 2 - x 2 * y 1) * y 1) * e2
        + ((x 2 * y 0 - x 0 * y 2) * y 0) * e2 - ((x 2 * y 0 - x 0 * y 2) * y 2) * e0
        + ((x 0 * y 1 - x 1 * y 0) * y 1) * e0 - ((x 0 * y 1 - x 1 * y 0) * y 0) * e1
    rcases mul_eq_zero.1 hs with hs | hs
    · exact hs
    · linarith
  · have ht : t * ((x 1 * y 2 - x 2 * y 1) * (x 1 * y 2 - x 2 * y 1) +
        (x 2 * y 0 - x 0 * y 2) * (x 2 * y 0 - x 0 * y 2) +
        (x 0 * y 1 - x 1 * y 0) * (x 0 * y 1 - x 1 * y 0)) = 0 := by
      linear_combination -((x 1 * y 2 - x 2 * y 1) * x 2) * e1
        + ((x 1 * y 2 - x 2 * y 1) * x 1) * e2
        - ((x 2 * y 0 - x 0 * y 2) * x 0) * e2 + ((x 2 * y 0 - x 0 * y 2) * x 2) * e0
        - ((x 0 * y 1 - x 1 * y 0) * x 1) * e0 + ((x 0 * y 1 - x 1 * y 0) * x 0) * e1
    rcases mul_eq_zero.1 ht with ht | ht
    · exact ht
    · linarith

/-- Three vectors with nonzero triple product are linearly independent. -/
theorem linearIndependent_triple {x y z : R3} (h : ⟪crs x y, z⟫ ≠ 0) :
    LinearIndependent ℝ ![x, y, z] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e : ∀ i, g 0 * x i + g 1 * y i + g 2 * z i = 0 := by
    intro i
    have := congrArg (fun v : R3 => v i) hg
    simpa [Fin.sum_univ_three] using this
  rw [inner_eq] at h
  simp only [crs_0, crs_1, crs_2] at h
  have e0 := e 0; have e1 := e 1; have e2 := e 2
  set d := (x 1 * y 2 - x 2 * y 1) * z 0 + (x 2 * y 0 - x 0 * y 2) * z 1 +
    (x 0 * y 1 - x 1 * y 0) * z 2 with hd
  have h0 : g 0 * d = 0 := by
    linear_combination (y 1 * z 2 - y 2 * z 1) * e0 + (y 2 * z 0 - y 0 * z 2) * e1
      + (y 0 * z 1 - y 1 * z 0) * e2
  have h1 : g 1 * d = 0 := by
    linear_combination (z 1 * x 2 - z 2 * x 1) * e0 + (z 2 * x 0 - z 0 * x 2) * e1
      + (z 0 * x 1 - z 1 * x 0) * e2
  have h2 : g 2 * d = 0 := by
    linear_combination (x 1 * y 2 - x 2 * y 1) * e0 + (x 2 * y 0 - x 0 * y 2) * e1
      + (x 0 * y 1 - x 1 * y 0) * e2
  intro i
  fin_cases i
  · exact (mul_eq_zero.1 h0).resolve_right h
  · exact (mul_eq_zero.1 h1).resolve_right h
  · exact (mul_eq_zero.1 h2).resolve_right h

lemma finrank_R3 : Module.finrank ℝ R3 = 3 := finrank_euclideanSpace_fin

lemma affDim_eq_finrank_vectorSpan {s : Set R3} (hs : s.Nonempty) :
    affDim s = (Module.finrank ℝ (vectorSpan ℝ s) : ℤ) := by
  rw [affDim_eq_finrank_direction hs, direction_affineSpan]

lemma affDim_convexHull (s : Set R3) : affDim (convexHull ℝ s) = affDim s := by
  simp only [affDim, affineSpan_convexHull]

/-- Lower bound on affine dimension from independent difference vectors. -/
lemma le_finrank_vectorSpan {s : Set R3} {k : ℕ} (v : Fin k → R3)
    (hv : LinearIndependent ℝ v) (hmem : ∀ i, v i ∈ vectorSpan ℝ s) :
    k ≤ Module.finrank ℝ (vectorSpan ℝ s) := by
  have hle : Submodule.span ℝ (range v) ≤ vectorSpan ℝ s :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hmem i)
  have := Submodule.finrank_mono hle
  rwa [finrank_span_eq_card hv, Fintype.card_fin] at this

/-- **A planar set spanned by a non-degenerate triangle has affine dimension 2.** -/
theorem affDim_eq_two {s : Set R3} {p q r : R3} (hp : p ∈ s) (hq : q ∈ s) (hr : r ∈ s)
    (hn : crs (q - p) (r - p) ≠ 0)
    (hplane : ∀ x ∈ s, ⟪crs (q - p) (r - p), x - p⟫ = 0) : affDim s = 2 := by
  rw [affDim_eq_finrank_vectorSpan ⟨p, hp⟩]
  set n := crs (q - p) (r - p)
  have hup : vectorSpan ℝ s ≤ (ℝ ∙ n)ᗮ := by
    rw [vectorSpan_def]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    show ⟪n, x -ᵥ y⟫ = 0
    have h1 := hplane x hx
    have h2 := hplane y hy
    have : x -ᵥ y = (x - p) - (y - p) := by rw [vsub_eq_sub]; abel
    rw [this, inner_sub_right, h1, h2, sub_zero]
  have hfact : Fact (Module.finrank ℝ R3 = 2 + 1) := ⟨finrank_R3⟩
  have hle : Module.finrank ℝ (vectorSpan ℝ s) ≤ 2 := by
    have := Submodule.finrank_mono hup
    rwa [Submodule.finrank_orthogonal_span_singleton (n := 2) hn] at this
  have hge : 2 ≤ Module.finrank ℝ (vectorSpan ℝ s) := by
    refine le_finrank_vectorSpan ![q - p, r - p] (linearIndependent_pair hn) ?_
    intro i; fin_cases i
    · exact vsub_mem_vectorSpan ℝ hq hp
    · exact vsub_mem_vectorSpan ℝ hr hp
  have : Module.finrank ℝ (vectorSpan ℝ s) = 2 := le_antisymm hle hge
  rw [this]; rfl

/-- **Four points with nonzero triple product span all of three-space.** -/
theorem affDim_eq_three {s : Set R3} {p q r t : R3} (hp : p ∈ s) (hq : q ∈ s) (hr : r ∈ s)
    (ht : t ∈ s) (hn : ⟪crs (q - p) (r - p), t - p⟫ ≠ 0) : affDim s = 3 := by
  rw [affDim_eq_finrank_vectorSpan ⟨p, hp⟩]
  have hle : Module.finrank ℝ (vectorSpan ℝ s) ≤ 3 := by
    have := Submodule.finrank_le (vectorSpan ℝ s)
    rwa [finrank_R3] at this
  have hge : 3 ≤ Module.finrank ℝ (vectorSpan ℝ s) := by
    refine le_finrank_vectorSpan ![q - p, r - p, t - p] (linearIndependent_triple hn) ?_
    intro i; fin_cases i
    · exact vsub_mem_vectorSpan ℝ hq hp
    · exact vsub_mem_vectorSpan ℝ hr hp
    · exact vsub_mem_vectorSpan ℝ ht hp
  have : Module.finrank ℝ (vectorSpan ℝ s) = 3 := le_antisymm hle hge
  rw [this]; rfl

/-- A segment between distinct points has affine dimension 1. -/
theorem affDim_pair {p q : R3} (h : p ≠ q) : affDim ({p, q} : Set R3) = 1 := by
  rw [affDim_eq_finrank_vectorSpan (insert_nonempty p {q}), vectorSpan_pair,
    finrank_span_singleton (vsub_ne_zero.2 h)]
  rfl

end R3

end EulersGem
