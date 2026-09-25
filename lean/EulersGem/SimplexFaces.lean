/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.PolytopeFaces
import EulersGem.AffDim
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# The face lattice of a geometric simplex

For an affine basis `b : AffineBasis ι ℝ E` (equivalently: `Fintype.card ι` affinely
independent points spanning `E`), the **simplex** `body b = convexHull ℝ (range b)` has a
completely explicit face lattice: its faces are exactly the subsimplices
`face b S = convexHull ℝ (b '' S)` for `S : Finset ι`, and `S ↦ face b S` is an order
isomorphism onto the face lattice.

Main results:

* `mem_face_iff` — inside the simplex, `x ∈ face b S` iff all barycentric coordinates
  outside `S` vanish;
* `isFaceOf_face` — every `face b S` really is a face (proved from barycentric
  coordinates, not assumed);
* `eq_face_of_isFaceOf` — conversely every face is some `face b S`
  (`S = ` the vertices it contains), via `face_eq_convexHull_inter`;
* `face_injective`, `face_subset_iff` — the correspondence is injective and
  order-reflecting;
* `affDim_face` — `affDim (face b S) = S.card - 1`, so the `d`-faces are exactly the
  `face b S` with `S.card = d + 1`;
* `ncard_facesOfDim` — the number of `d`-faces is the number of `(d+1)`-element subsets
  of `ι`.

Nothing here is postulated: everything comes from Mathlib's `AffineBasis.coord`
barycentric coordinates plus `PolytopeFaces.face_eq_convexHull_inter`.
-/

open Set

namespace EulersGem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## `affDim` via the direction of the affine span -/

/-- For a nonempty set, `affDim` is the `finrank` of the direction of its affine span. -/
lemma affDim_eq_finrank_direction {s : Set E} (hs : s.Nonempty) :
    affDim s = (Module.finrank ℝ (affineSpan ℝ s).direction : ℤ) := by
  have hspanNe : (affineSpan ℝ s : Set E).Nonempty :=
    (affineSpan_nonempty (k := ℝ) (V := E) (P := E)).mpr hs
  have hneBot : affineSpan ℝ s ≠ ⊥ := (AffineSubspace.nonempty_iff_ne_bot _).mp hspanNe
  have hfd := AffineSubspace.finDim_eq_finrank hneBot
  simp only [affDim]
  cases hmatch : (affineSpan ℝ s).finDim with
  | bot => exact absurd (AffineSubspace.finDim_eq_bot_iff.mp hmatch) hneBot
  | coe n =>
    rw [hmatch] at hfd
    have hn : n = Module.finrank ℝ (affineSpan ℝ s).direction := WithBot.coe_inj.mp hfd
    simp [hn]

namespace Simplex

variable {ι : Type*} [Fintype ι]

/-! ## The simplex and its subsimplices -/

/-- The geometric simplex spanned by an affine basis: the convex hull of its vertices. -/
def body (b : AffineBasis ι ℝ E) : Set E := convexHull ℝ (Set.range b)

/-- The subsimplex spanned by a subset `S` of the vertices. -/
def face (b : AffineBasis ι ℝ E) (S : Finset ι) : Set E := convexHull ℝ (b '' ↑S)

variable (b : AffineBasis ι ℝ E)

lemma body_eq_convexHull_range : body b = convexHull ℝ (Set.range b) := rfl

/-- Barycentric characterization of the simplex (Mathlib
`AffineBasis.convexHull_eq_nonneg_coord`). -/
lemma mem_body_iff {x : E} : x ∈ body b ↔ ∀ i, 0 ≤ b.coord i x := by
  rw [body, AffineBasis.convexHull_eq_nonneg_coord b]
  exact Iff.rfl

lemma coord_nonneg_of_mem_body {x : E} (hx : x ∈ body b) (i : ι) : 0 ≤ b.coord i x :=
  (mem_body_iff b).mp hx i

lemma convex_body : Convex ℝ (body b) := convex_convexHull ℝ _

lemma isPolytope_body : IsPolytope (body b) :=
  ⟨Set.range b, Set.finite_range b, rfl⟩

lemma convex_face (S : Finset ι) : Convex ℝ (face b S) := convex_convexHull ℝ _

lemma face_subset_body (S : Finset ι) : face b S ⊆ body b :=
  convexHull_mono (by rintro y ⟨i, -, rfl⟩; exact ⟨i, rfl⟩)

lemma face_empty : face b (∅ : Finset ι) = (∅ : Set E) := by
  simp [face]

/-! ## Barycentric description of the subsimplices -/

/-- Coordinates outside `S` vanish on `face b S`. -/
lemma coord_eq_zero_of_mem_face {S : Finset ι} {x : E} (hx : x ∈ face b S) {i : ι}
    (hi : i ∉ S) : b.coord i x = 0 := by
  have hconv : Convex ℝ {y : E | b.coord i y = 0} := by
    have hpre : {y : E | b.coord i y = 0} = (b.coord i) ⁻¹' ({0} : Set ℝ) := by
      ext y; simp
    rw [hpre]
    exact (convex_singleton (0 : ℝ)).affine_preimage (b.coord i)
  have hsub : b '' ↑S ⊆ {y : E | b.coord i y = 0} := by
    rintro y ⟨j, hj, rfl⟩
    have hij : i ≠ j := fun h => hi (h ▸ (Finset.mem_coe.mp hj))
    simpa using b.coord_apply_ne hij
  exact convexHull_min hsub hconv hx

/-- Conversely, a point of the simplex whose coordinates outside `S` vanish lies in
`face b S`. -/
lemma mem_face_of_coord_eq_zero {S : Finset ι} {x : E} (hx : x ∈ body b)
    (h0 : ∀ i ∉ S, b.coord i x = 0) : x ∈ face b S := by
  classical
  have hsum : ∑ i ∈ S, b.coord i x = 1 := by
    have h1 : ∑ i ∈ S, b.coord i x = ∑ i ∈ (Finset.univ : Finset ι), b.coord i x :=
      Finset.sum_subset (Finset.subset_univ S) fun i _ hiS => h0 i hiS
    rw [h1]
    exact b.sum_coord_apply_eq_one x
  have hall : ∑ i ∈ (Finset.univ : Finset ι), (b.coord i x) • b i = x := by
    have h1 := b.affineCombination_coord_eq_self x
    rwa [Finset.affineCombination_eq_linear_combination _ _ _
      (b.sum_coord_apply_eq_one x)] at h1
  have hrepr : ∑ i ∈ S, (b.coord i x) • b i = x := by
    have h2 : ∑ i ∈ S, (b.coord i x) • b i
        = ∑ i ∈ (Finset.univ : Finset ι), (b.coord i x) • b i :=
      Finset.sum_subset (f := fun i => (b.coord i x) • b i) (Finset.subset_univ S)
        fun i _ hiS => by rw [h0 i hiS, zero_smul]
    rw [h2]
    exact hall
  rw [face, ← hrepr]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => coord_nonneg_of_mem_body b hx i) hsum
    fun i hi => subset_convexHull ℝ _ ⟨i, Finset.mem_coe.mpr hi, rfl⟩

lemma mem_face_iff {S : Finset ι} {x : E} (hx : x ∈ body b) :
    x ∈ face b S ↔ ∀ i ∉ S, b.coord i x = 0 :=
  ⟨fun h _ hi => coord_eq_zero_of_mem_face b h hi, mem_face_of_coord_eq_zero b hx⟩

/-- A vertex lies in a subsimplex exactly when its index does. -/
lemma vertex_mem_face_iff {S : Finset ι} {i : ι} : b i ∈ face b S ↔ i ∈ S := by
  refine ⟨fun h => ?_, fun hi => subset_convexHull ℝ _ ⟨i, Finset.mem_coe.mpr hi, rfl⟩⟩
  by_contra hi
  have h0 := coord_eq_zero_of_mem_face b h hi
  rw [b.coord_apply_eq] at h0
  exact one_ne_zero h0

/-! ## Every subsimplex is a face -/

/-- **The subsimplices are faces.** Extremeness is read off the barycentric coordinates:
a coordinate vanishing at an interior point of a segment, with both endpoints in the
simplex, must vanish at both endpoints. -/
theorem isFaceOf_face (S : Finset ι) : IsFaceOf (body b) (face b S) := by
  refine ⟨⟨face_subset_body b S, ?_⟩, convex_face b S⟩
  intro y hy z hz w hw hseg
  obtain ⟨a, c, ha, hc, hac, hcomb⟩ := hseg
  refine (mem_face_iff b hy).mpr fun i hi => ?_
  have hw0 : b.coord i w = 0 := coord_eq_zero_of_mem_face b hw hi
  have hcy : (0 : ℝ) ≤ b.coord i y := coord_nonneg_of_mem_body b hy i
  have hcz : (0 : ℝ) ≤ b.coord i z := coord_nonneg_of_mem_body b hz i
  have hsplit : b.coord i w = a * b.coord i y + c * b.coord i z := by
    rw [← hcomb, Convex.combo_affine_apply hac]
    simp [smul_eq_mul]
  rcases eq_or_lt_of_le hcy with h | h
  · exact h.symm
  · exfalso
    have h1 : 0 < a * b.coord i y := mul_pos ha h
    have h2 : 0 ≤ c * b.coord i z := mul_nonneg hc.le hcz
    rw [hw0] at hsplit
    linarith

/-! ## Every face is a subsimplex -/

/-- The set of vertex indices lying in a given set. -/
noncomputable def faceIdx (F : Set E) : Finset ι :=
  open Classical in Finset.univ.filter fun i => b i ∈ F

lemma mem_faceIdx_iff {F : Set E} {i : ι} : i ∈ faceIdx b F ↔ b i ∈ F := by
  classical
  simp [faceIdx]

lemma range_inter_eq_image_faceIdx {F : Set E} :
    Set.range b ∩ F = b '' ↑(faceIdx b F) := by
  ext y
  constructor
  · rintro ⟨⟨i, rfl⟩, hyF⟩
    exact ⟨i, Finset.mem_coe.mpr ((mem_faceIdx_iff b).mpr hyF), rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, rfl⟩, (mem_faceIdx_iff b).mp (Finset.mem_coe.mp hi)⟩

/-- **Every face of a simplex is the subsimplex on the vertices it contains.** -/
theorem eq_face_of_isFaceOf {F : Set E} (hF : IsFaceOf (body b) F) :
    F = face b (faceIdx b F) := by
  have hF' : IsFaceOf (convexHull ℝ (Set.range b)) F := hF
  calc F = convexHull ℝ (Set.range b ∩ F) := face_eq_convexHull_inter hF'
    _ = convexHull ℝ (b '' ↑(faceIdx b F)) := by rw [range_inter_eq_image_faceIdx]
    _ = face b (faceIdx b F) := rfl

/-- The faces of a simplex are exactly the subsimplices. -/
theorem faces_eq_range_face :
    {F : Set E | IsFaceOf (body b) F} = Set.range (face b) := by
  ext F
  constructor
  · intro hF
    exact ⟨faceIdx b F, (eq_face_of_isFaceOf b hF).symm⟩
  · rintro ⟨S, rfl⟩
    exact isFaceOf_face b S

/-! ## The correspondence is an order embedding -/

lemma face_subset_iff {S T : Finset ι} : face b S ⊆ face b T ↔ S ⊆ T := by
  refine ⟨fun h i hi => ?_, fun h => convexHull_mono (Set.image_mono (by exact_mod_cast h))⟩
  exact (vertex_mem_face_iff b).mp (h ((vertex_mem_face_iff b).mpr hi))

lemma face_injective : Function.Injective (face b) := fun S T h =>
  Finset.Subset.antisymm ((face_subset_iff b).mp h.subset) ((face_subset_iff b).mp h.symm.subset)

/-! ## Dimension of a subsimplex -/

/-- `affDim (face b S) = S.card - 1`: the subsimplex on `k` vertices has dimension `k−1`
(and the empty face has dimension `-1`). -/
theorem affDim_face (S : Finset ι) : affDim (face b S) = (S.card : ℤ) - 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · rw [face_empty b]
    simp
  · have hne : (face b S).Nonempty := by
      obtain ⟨i, hi⟩ := hS
      exact ⟨b i, (vertex_mem_face_iff b).mpr hi⟩
    rw [affDim_eq_finrank_direction hne, face, affineSpan_convexHull, direction_affineSpan]
    have hind : AffineIndepOn ℝ (b : ι → E) (↑S : Set ι) := b.ind.subtype (↑S : Set ι)
    have hfin : (↑S : Set ι).Finite := S.finite_toSet
    have hnes : (↑S : Set ι).Nonempty := by
      obtain ⟨i, hi⟩ := hS
      exact ⟨i, Finset.mem_coe.mpr hi⟩
    have h := hind.finrank_vectorSpan_image hfin hnes
    rw [Set.ncard_coe_finset] at h
    rw [h]
    have hpos : 1 ≤ S.card := Finset.card_pos.mpr hS
    omega

/-! ## Counting faces by dimension -/

/-- The `d`-faces of a simplex are the subsimplices on `d + 1` vertices. -/
theorem facesOfDim_eq_image (d : ℤ) :
    {F : Set E | IsFaceOf (body b) F ∧ affDim F = d} =
      face b '' {S : Finset ι | (S.card : ℤ) = d + 1} := by
  ext F
  constructor
  · rintro ⟨hF, hdim⟩
    refine ⟨faceIdx b F, ?_, (eq_face_of_isFaceOf b hF).symm⟩
    show ((faceIdx b F).card : ℤ) = d + 1
    have hd : affDim (face b (faceIdx b F)) = ((faceIdx b F).card : ℤ) - 1 := affDim_face b _
    rw [← eq_face_of_isFaceOf b hF, hdim] at hd
    omega
  · rintro ⟨S, hS, rfl⟩
    have hS' : (S.card : ℤ) = d + 1 := hS
    refine ⟨isFaceOf_face b S, ?_⟩
    rw [affDim_face b S]
    omega

/-- The number of `d`-faces of a simplex equals the number of `(d+1)`-element subsets of
the vertex index set. -/
theorem ncard_facesOfDim (d : ℤ) :
    {F : Set E | IsFaceOf (body b) F ∧ affDim F = d}.ncard =
      {S : Finset ι | (S.card : ℤ) = d + 1}.ncard := by
  rw [facesOfDim_eq_image b d]
  exact Set.ncard_image_of_injective _ (face_injective b)

end Simplex

end EulersGem
