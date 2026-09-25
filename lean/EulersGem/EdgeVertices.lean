/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.PolytopeFaces
import EulersGem.ConeSlice

/-!
# An edge of a polytope has exactly two vertices

`PlatonicOfEuler.schlafli_pair_mem_of_regular_polytope` used to assume this as an incidence
hypothesis. Here it is proved:

* (`eq_singleton_of_affDim_eq_zero`, already in `ConeSlice.lean`: a `0`-dimensional set
  is a singleton);
* `exists_spanning_direction` — a `1`-dimensional set's affine direction is spanned by a
  single nonzero vector `d`;
* `injOn_inner_of_affDim_eq_one` — `⟪d, ·⟫` is then injective on the set;
* `extremePoints_eq_pair` — a `1`-dimensional V-polytope has exactly two extreme points,
  namely the argmin and argmax of `⟪d, ·⟫` over its generators;
* `ncard_vertices_of_edge` — hence exactly two `0`-faces of `p` lie inside a `1`-face.

The proof is the standard one: on a one-dimensional convex set a supporting functional is
injective, so the extreme points are exactly where it is extremal, and there are two of them
because otherwise the set would be a point.
-/

open Set
open scoped RealInnerProductSpace

namespace EulersGem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## One-dimensional sets: a spanning direction, and an injective functional -/

/-- The affine direction of a `1`-dimensional set is spanned by one nonzero vector. -/
lemma exists_spanning_direction [FiniteDimensional ℝ E] {e : Set E} (hne : e.Nonempty)
    (hdim : affDim e = 1) :
    ∃ d : E, d ≠ 0 ∧ (affineSpan ℝ e).direction = Submodule.span ℝ {d} := by
  have hfr : Module.finrank ℝ (affineSpan ℝ e).direction = 1 := by
    have hd := affDim_eq_finrank_direction (s := e) hne
    rw [hdim] at hd
    omega
  have hnbot : (affineSpan ℝ e).direction ≠ ⊥ := by
    intro hbot
    rw [hbot] at hfr
    simp at hfr
  obtain ⟨d, hdmem, hdne⟩ := (Submodule.ne_bot_iff _).mp hnbot
  refine ⟨d, hdne, ?_⟩
  have hle : Submodule.span ℝ {d} ≤ (affineSpan ℝ e).direction := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hdmem
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_span_singleton hdne, hfr]

/-- On a `1`-dimensional set, the functional along its direction is injective. -/
lemma injOn_inner_of_affDim_eq_one {e : Set E} {d : E} (hdne : d ≠ 0)
    (hspan : (affineSpan ℝ e).direction = Submodule.span ℝ {d}) :
    Set.InjOn (fun x => ⟪d, x⟫) e := by
  intro x hx y hy hxy
  have hinner : ⟪d, x⟫ = ⟪d, y⟫ := hxy
  have hmem : x -ᵥ y ∈ (affineSpan ℝ e).direction :=
    AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hx) (mem_affineSpan ℝ hy)
  rw [hspan, Submodule.mem_span_singleton] at hmem
  obtain ⟨t, ht⟩ := hmem
  have hsub : x - y = t • d := by simpa using ht.symm
  have hzero : ⟪d, x - y⟫ = 0 := by
    rw [inner_sub_right, hinner, sub_self]
  rw [hsub, real_inner_smul_right] at hzero
  have hdd : ⟪d, d⟫ ≠ 0 := inner_self_ne_zero.mpr hdne
  have ht0 : t = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h hdd
  rw [ht0, zero_smul] at hsub
  exact sub_eq_zero.mp hsub

/-! ## A one-dimensional V-polytope has exactly two extreme points -/

/-- The argmax of an injective supporting functional over the generators is an extreme
point of the hull. -/
lemma mem_extremePoints_of_isMaxOn {W : Set E} {d w : E}
    (hinj : Set.InjOn (fun x => ⟪d, x⟫) (convexHull ℝ W))
    (hwW : w ∈ W) (hmax : ∀ v ∈ W, ⟪d, v⟫ ≤ ⟪d, w⟫) :
    w ∈ (convexHull ℝ W).extremePoints ℝ := by
  refine ⟨subset_convexHull ℝ W hwW, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hseg
  obtain ⟨a, c, ha, hc, hac, hcomb⟩ := hseg
  have hb1 : ⟪d, x₁⟫ ≤ ⟪d, w⟫ := inner_le_of_mem_convexHull hmax x₁ hx₁
  have hb2 : ⟪d, x₂⟫ ≤ ⟪d, w⟫ := inner_le_of_mem_convexHull hmax x₂ hx₂
  have hsplit : ⟪d, w⟫ = a * ⟪d, x₁⟫ + c * ⟪d, x₂⟫ := by
    rw [← hcomb, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have h1 : ⟪d, x₁⟫ = ⟪d, w⟫ := by
    by_contra hne
    have hlt : ⟪d, x₁⟫ < ⟪d, w⟫ := lt_of_le_of_ne hb1 hne
    have hsc : a * ⟪d, w⟫ + c * ⟪d, w⟫ = ⟪d, w⟫ := by linear_combination ⟪d, w⟫ * hac
    linarith [mul_pos ha (sub_pos.mpr hlt), mul_nonneg hc.le (sub_nonneg.mpr hb2),
      mul_sub a ⟪d, w⟫ ⟪d, x₁⟫, mul_sub c ⟪d, w⟫ ⟪d, x₂⟫]
  exact hinj hx₁ (subset_convexHull ℝ W hwW) h1

/-- **A one-dimensional V-polytope has exactly two extreme points:** the extremes of an
injective supporting functional. -/
theorem extremePoints_eq_pair [FiniteDimensional ℝ E] {W : Set E} (hWfin : W.Finite)
    (hWne : W.Nonempty) (hdim : affDim (convexHull ℝ W) = 1) :
    ∃ u v : E, u ≠ v ∧ (convexHull ℝ W).extremePoints ℝ = {u, v} := by
  classical
  set e := convexHull ℝ W with he
  have hene : e.Nonempty := hWne.mono (subset_convexHull ℝ W)
  obtain ⟨d, hdne, hspan⟩ := exists_spanning_direction hene hdim
  have hinj : Set.InjOn (fun x => ⟪d, x⟫) e := injOn_inner_of_affDim_eq_one hdne hspan
  have hinj' : Set.InjOn (fun x => ⟪-d, x⟫) e := by
    intro x hx y hy hxy
    refine hinj hx hy ?_
    have h : -⟪d, x⟫ = -⟪d, y⟫ := by
      simpa [inner_neg_left] using hxy
    simpa using neg_injective h
  -- argmax and argmin over the (finite, nonempty) generating set
  obtain ⟨u, huW, hu⟩ := Finset.exists_max_image hWfin.toFinset (fun x => ⟪d, x⟫)
    (by simpa [Set.Finite.toFinset_nonempty] using hWne)
  obtain ⟨v, hvW, hv⟩ := Finset.exists_max_image hWfin.toFinset (fun x => ⟪-d, x⟫)
    (by simpa [Set.Finite.toFinset_nonempty] using hWne)
  have huW' : u ∈ W := hWfin.mem_toFinset.mp huW
  have hvW' : v ∈ W := hWfin.mem_toFinset.mp hvW
  have hu' : ∀ x ∈ W, ⟪d, x⟫ ≤ ⟪d, u⟫ := fun x hx => hu x (hWfin.mem_toFinset.mpr hx)
  have hv' : ∀ x ∈ W, ⟪-d, x⟫ ≤ ⟪-d, v⟫ := fun x hx => hv x (hWfin.mem_toFinset.mpr hx)
  have hvmin : ∀ x ∈ W, ⟪d, v⟫ ≤ ⟪d, x⟫ := by
    intro x hx
    have := hv' x hx
    rw [inner_neg_left, inner_neg_left] at this
    linarith
  have hextu : u ∈ e.extremePoints ℝ := mem_extremePoints_of_isMaxOn hinj huW' hu'
  have hextv : v ∈ e.extremePoints ℝ := by
    have := mem_extremePoints_of_isMaxOn hinj' hvW' hv'
    exact this
  -- the two extremes are distinct, else the whole hull is a point
  have huv : u ≠ v := by
    intro heq
    have hall : ∀ x ∈ W, x = u := by
      intro x hx
      refine hinj (subset_convexHull ℝ W hx) (subset_convexHull ℝ W huW') ?_
      have h1 := hu' x hx
      have h2 := hvmin x hx
      rw [← heq] at h2
      simp only
      linarith
    have hWsub : W ⊆ {u} := fun x hx => hall x hx
    have hWeq : W = {u} := subset_antisymm hWsub (by
      rw [Set.singleton_subset_iff]; exact huW')
    rw [he, hWeq, convexHull_singleton] at hdim
    rw [affDim_singleton] at hdim
    norm_num at hdim
  refine ⟨u, v, huv, subset_antisymm ?_ ?_⟩
  · -- any extreme point is one of the two
    intro z hz
    by_contra hzne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hzne
    obtain ⟨hzu, hzv⟩ := hzne
    have hze : z ∈ e := hz.1
    have hzu' : ⟪d, z⟫ < ⟪d, u⟫ := by
      have hle : ⟪d, z⟫ ≤ ⟪d, u⟫ := inner_le_of_mem_convexHull hu' z hze
      refine lt_of_le_of_ne hle ?_
      intro hEq
      exact hzu (hinj hze (subset_convexHull ℝ W huW') hEq)
    have hzv' : ⟪d, v⟫ < ⟪d, z⟫ := by
      have hle : ⟪-d, z⟫ ≤ ⟪-d, v⟫ := inner_le_of_mem_convexHull hv' z hze
      rw [inner_neg_left, inner_neg_left] at hle
      refine lt_of_le_of_ne (by linarith) ?_
      intro hEq
      exact hzv (hinj (subset_convexHull ℝ W hvW') hze hEq).symm
    -- `z` is interior to the segment from `v` to `u`
    set t : ℝ := (⟪d, u⟫ - ⟪d, z⟫) / (⟪d, u⟫ - ⟪d, v⟫) with ht
    have hden : 0 < ⟪d, u⟫ - ⟪d, v⟫ := by linarith
    have ht0 : 0 < t := div_pos (by linarith) hden
    have ht1 : t < 1 := by
      rw [ht, div_lt_one hden]
      linarith
    have hzmem : t • v + (1 - t) • u ∈ e :=
      (convex_convexHull ℝ W) (subset_convexHull ℝ W hvW') (subset_convexHull ℝ W huW')
        ht0.le (by linarith) (by ring)
    have hinner : ⟪d, t • v + (1 - t) • u⟫ = ⟪d, z⟫ := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, ht]
      field_simp
      ring
    have hzeq : t • v + (1 - t) • u = z := hinj hzmem hze hinner
    have hseg : z ∈ openSegment ℝ v u :=
      ⟨t, 1 - t, ht0, by linarith, by ring, hzeq⟩
    exact hzv (hz.2 (subset_convexHull ℝ W hvW') (subset_convexHull ℝ W huW') hseg).symm
  · intro z hz
    rcases hz with rfl | hz
    · exact hextu
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hextv

/-! ## An edge of a polytope has exactly two vertices -/

/-- **An edge of a polytope has exactly two vertices.** If `e` is a `1`-dimensional face of a
polytope `p`, exactly two `0`-dimensional faces of `p` are contained in `e`.

This discharges the `hedge_verts` hypothesis of the Platonic classification. -/
theorem ncard_vertices_of_edge [FiniteDimensional ℝ E] {p : Set E} (hP : IsPolytope p)
    {e : Set E} (he : IsFaceOf p e) (hdim : affDim e = 1) :
    {w : Set E | (IsFaceOf p w ∧ affDim w = 0) ∧ w ⊆ e}.ncard = 2 := by
  classical
  obtain ⟨V, hVfin, rfl⟩ := hP
  have heq : e = convexHull ℝ (V ∩ e) := face_eq_convexHull_inter he
  have hWfin : (V ∩ e).Finite := hVfin.subset Set.inter_subset_left
  have hene : e.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hemp
    rw [hemp, affDim_empty] at hdim
    norm_num at hdim
  have hWne : (V ∩ e).Nonempty := by
    rcases Set.eq_empty_or_nonempty (V ∩ e) with hemp | h
    · rw [hemp, convexHull_empty] at heq
      rw [heq] at hene
      exact absurd hene (by simp)
    · exact h
  have hdim' : affDim (convexHull ℝ (V ∩ e)) = 1 := by rw [← heq]; exact hdim
  obtain ⟨u, v, huv, hext⟩ := extremePoints_eq_pair hWfin hWne hdim'
  rw [← heq] at hext
  have hset : {w : Set E | (IsFaceOf (convexHull ℝ V) w ∧ affDim w = 0) ∧ w ⊆ e}
      = (fun x => ({x} : Set E)) '' (e.extremePoints ℝ) := by
    ext w
    constructor
    · rintro ⟨⟨hface, hd0⟩, hsub⟩
      obtain ⟨a, rfl⟩ := eq_singleton_of_affDim_eq_zero hd0
      have haP : a ∈ (convexHull ℝ V).extremePoints ℝ :=
        isExtreme_singleton.mp hface.isExtreme
      have hae : a ∈ e := hsub (Set.mem_singleton a)
      refine ⟨a, ?_, rfl⟩
      rw [he.isExtreme.extremePoints_eq]
      exact ⟨hae, haP⟩
    · rintro ⟨a, ha, rfl⟩
      rw [he.isExtreme.extremePoints_eq] at ha
      refine ⟨⟨⟨isExtreme_singleton.mpr ha.2, convex_singleton a⟩, affDim_singleton a⟩, ?_⟩
      exact Set.singleton_subset_iff.mpr ha.1
  rw [hset, hext, Set.ncard_image_of_injective _ Set.singleton_injective, Set.ncard_pair huv]


end EulersGem
