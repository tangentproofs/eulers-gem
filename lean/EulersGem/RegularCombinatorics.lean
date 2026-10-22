/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.PlatonicSolids
import EulersGem.EdgeVertices

/-!
# The combinatorial half of the classification

For a regular polyhedron `P` (`IsRegularPolyhedron`), symmetries carry faces to faces of
the same dimension and preserve inclusion, so flag-transitivity makes the incidence numbers
uniform. Together with the Euler chain (`schlafli_pair_mem_of_regular_polytope`) this pins the
Schläfli type `{s, m}` to the five pairs and the face counts `(V, E, F)` to the five classical
triples.

**What is assumed.** The repository does not yet formalize the face lattice of a general
3-polytope beyond "an edge has two vertices" (`ncard_vertices_of_edge`). The standard facts we
still need are collected, honestly labelled, in `FaceLatticeFacts`: every vertex, edge and
facet lies in a flag; every edge lies in exactly two facets; every facet has, and every vertex
meets, at least three edges. These hold for **every** convex 3-polytope (Ziegler, *Lectures on
Polytopes*, §2.2; Grünbaum, *Convex Polytopes*, §3.1, §13.1) — nothing in them mentions
regularity, symmetry, metric data or the five solids, so they do not smuggle in the
classification. `edge_in_flag` is partly proved here (an edge contains a vertex).
-/

open Set
open scoped RealInnerProductSpace

namespace EulersGem

open Platonic Platonic3

/-- Standard face-lattice facts of a convex 3-polytope that the repository does not yet
prove in general. They hold for the five constructed solids (`FaceLatticeFacts.of_faceData`,
`platonic_faceLatticeFacts`), so the hypothesis is not vacuous. -/
structure FaceLatticeFacts (P : Set R3) : Prop where
  exists_flag : ∃ v e f, IsFlag P v e f
  vertex_in_flag : ∀ v ∈ facesOfDim P 0, ∃ e f, IsFlag P v e f
  edge_in_facet : ∀ e ∈ facesOfDim P 1, ∃ f ∈ facesOfDim P 2, e ⊆ f
  facet_in_flag : ∀ f ∈ facesOfDim P 2, ∃ v e, IsFlag P v e f
  edge_two_facets : ∀ e ∈ facesOfDim P 1, {f ∈ facesOfDim P 2 | e ⊆ f}.ncard = 2
  facet_three_edges : ∀ f ∈ facesOfDim P 2, 3 ≤ {e ∈ facesOfDim P 1 | e ⊆ f}.ncard
  vertex_three_edges : ∀ v ∈ facesOfDim P 0, 3 ≤ {e ∈ facesOfDim P 1 | v ⊆ e}.ncard

lemma nonempty_of_le_ncard {α : Type*} {s : Set α} {k : ℕ} (hk : 0 < k) (h : k ≤ s.ncard) :
    s.Nonempty :=
  Set.nonempty_of_ncard_ne_zero (by omega)

/-- `FaceLatticeFacts` follows from the face data `{s, m}` with `s, m ≥ 3` and a facet. -/
theorem FaceLatticeFacts.of_faceData {P : Set R3} (hP : IsPolytope P) {V E F s m : ℕ}
    (h : Platonic3.HasFaceData P V E F s m) (hs : 3 ≤ s) (hm : 3 ≤ m) (hF : 0 < F) :
    FaceLatticeFacts P := by
  obtain ⟨-, -, hFc, hfs, hef, hvm⟩ := h
  have edge_in_facet : ∀ e ∈ facesOfDim P 1, ∃ f ∈ facesOfDim P 2, e ⊆ f := by
    intro e he
    obtain ⟨f, hf, hef'⟩ := nonempty_of_le_ncard (k := 2) (by omega) (hef e he).ge
    exact ⟨f, hf, hef'⟩
  have facet_in_flag : ∀ f ∈ facesOfDim P 2, ∃ v e, IsFlag P v e f := by
    intro f hf
    obtain ⟨e, he, hef'⟩ := nonempty_of_le_ncard (k := 3) (by omega) ((hfs f hf).symm ▸ hs)
    obtain ⟨v, hv, hve⟩ := nonempty_of_le_ncard (k := 2) (by omega)
      (ncard_vertices_of_edge hP he.1 he.2).ge
    exact ⟨v, e, hv, he, hf, hve, hef'⟩
  refine ⟨?_, ?_, edge_in_facet, facet_in_flag, hef, fun f hf => (hfs f hf).symm ▸ hs,
    fun v hv => (hvm v hv).symm ▸ hm⟩
  · obtain ⟨f, hf⟩ := Set.nonempty_of_ncard_ne_zero (s := facesOfDim P 2) (by omega)
    obtain ⟨v, e, hfl⟩ := facet_in_flag f hf
    exact ⟨v, e, f, hfl⟩
  · intro v hv
    obtain ⟨e, he, hve⟩ := nonempty_of_le_ncard (k := 3) (by omega) ((hvm v hv).symm ▸ hm)
    obtain ⟨f, hf, hef'⟩ := edge_in_facet e he
    exact ⟨e, f, hv, he, hf, hve, hef'⟩

/-- The five constructed solids satisfy `FaceLatticeFacts` (non-vacuity of the hypothesis). -/
theorem platonic_faceLatticeFacts :
    FaceLatticeFacts tetrahedron ∧ FaceLatticeFacts cube ∧ FaceLatticeFacts octahedron ∧
    FaceLatticeFacts dodecahedron ∧ FaceLatticeFacts icosahedron :=
  ⟨.of_faceData tetrahedron_isRegular.1 tetrahedron_faceData le_rfl le_rfl (by norm_num),
    .of_faceData cube_isRegular.1 cube_faceData (by norm_num) le_rfl (by norm_num),
    .of_faceData octahedron_isRegular.1 octahedron_faceData le_rfl (by norm_num) (by norm_num),
    .of_faceData dodecahedron_isRegular.1 dodecahedron_faceData (by norm_num) le_rfl (by norm_num),
    .of_faceData icosahedron_isRegular.1 icosahedron_faceData le_rfl (by norm_num) (by norm_num)⟩

/-! ## Symmetries permute faces -/

section Symmetry

variable {P : Set R3} {g : R3 ≃ᵃⁱ[ℝ] R3}

lemma image_mem_facesOfDim (hg : g '' P = P) {F : Set R3} {d : ℤ}
    (hF : F ∈ facesOfDim P d) : g '' F ∈ facesOfDim P d := by
  have hinj : Function.Injective (g.toAffineEquiv.toAffineMap) := g.injective
  refine ⟨?_, ?_⟩
  · have := isFaceOf_image_affine hinj hF.1
    change IsFaceOf (g '' P) (g '' F) at this
    rwa [hg] at this
  · have := affDim_image_affine _ hinj F
    change affDim (g '' F) = affDim F at this
    rw [this, hF.2]

lemma symm_image_eq (hg : g '' P = P) : g.symm '' P = P := by
  conv_lhs => rw [← hg]
  simp [Set.image_image]

lemma image_symm_image (s : Set R3) : g '' (g.symm '' s) = s := by
  simp [Set.image_image]

/-- A symmetry preserves the number of `d`-faces inside a set. -/
lemma ncard_sub_image (hg : g '' P = P) (d : ℤ) (x : Set R3) :
    {y ∈ facesOfDim P d | y ⊆ g '' x}.ncard = {y ∈ facesOfDim P d | y ⊆ x}.ncard := by
  have hset : {y ∈ facesOfDim P d | y ⊆ g '' x} =
      (fun y => g '' y) '' {y ∈ facesOfDim P d | y ⊆ x} := by
    ext y
    constructor
    · rintro ⟨hy, hyx⟩
      refine ⟨g.symm '' y, ⟨image_mem_facesOfDim (symm_image_eq hg) hy, ?_⟩,
        image_symm_image y⟩
      intro z hz
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨u, hu, rfl⟩ := hyx hw
      simpa using hu
    · rintro ⟨y, ⟨hy, hyx⟩, rfl⟩
      exact ⟨image_mem_facesOfDim hg hy, image_mono hyx⟩
  rw [hset, Set.ncard_image_of_injective _ (Set.image_injective.2 g.injective)]

/-- A symmetry preserves the number of `d`-faces containing a set. -/
lemma ncard_sup_image (hg : g '' P = P) (d : ℤ) (x : Set R3) :
    {y ∈ facesOfDim P d | g '' x ⊆ y}.ncard = {y ∈ facesOfDim P d | x ⊆ y}.ncard := by
  have hset : {y ∈ facesOfDim P d | g '' x ⊆ y} =
      (fun y => g '' y) '' {y ∈ facesOfDim P d | x ⊆ y} := by
    ext y
    constructor
    · rintro ⟨hy, hxy⟩
      refine ⟨g.symm '' y, ⟨image_mem_facesOfDim (symm_image_eq hg) hy, ?_⟩,
        image_symm_image y⟩
      intro z hz
      exact ⟨g z, hxy ⟨z, hz, rfl⟩, by simp⟩
    · rintro ⟨y, ⟨hy, hxy⟩, rfl⟩
      exact ⟨image_mem_facesOfDim hg hy, image_mono hxy⟩
  rw [hset, Set.ncard_image_of_injective _ (Set.image_injective.2 g.injective)]

end Symmetry

/-! ## Uniform incidences -/

/-- **Flag-transitivity makes the incidence numbers uniform.** -/
theorem IsRegularPolyhedron.uniform {P : Set R3} (hP : IsRegularPolyhedron P)
    (hL : FaceLatticeFacts P) :
    ∃ s m, (∀ f ∈ facesOfDim P 2, {e ∈ facesOfDim P 1 | e ⊆ f}.ncard = s) ∧
      (∀ v ∈ facesOfDim P 0, {e ∈ facesOfDim P 1 | v ⊆ e}.ncard = m) := by
  obtain ⟨-, -, htr⟩ := hP
  obtain ⟨v0, e0, f0, h0⟩ := hL.exists_flag
  refine ⟨{e ∈ facesOfDim P 1 | e ⊆ f0}.ncard, {e ∈ facesOfDim P 1 | v0 ⊆ e}.ncard,
    fun f hf => ?_, fun v hv => ?_⟩
  · obtain ⟨v, e, hfl⟩ := hL.facet_in_flag f hf
    obtain ⟨g, hg, -, -, hgf⟩ := htr _ _ _ _ _ _ h0 hfl
    rw [← hgf, ncard_sub_image hg]
  · obtain ⟨e, f, hfl⟩ := hL.vertex_in_flag v hv
    obtain ⟨g, hg, hgv, -, -⟩ := htr _ _ _ _ _ _ h0 hfl
    rw [← hgv, ncard_sup_image hg]

/-- The five classical `(s, m, V, E, F)`. -/
def platonicTypes : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(3, 3, 4, 6, 4), (4, 3, 8, 12, 6), (3, 4, 6, 12, 8), (5, 3, 20, 30, 12), (3, 5, 12, 30, 20)]

/-- **The combinatorial classification of regular polyhedra**, assuming only the general
face-lattice facts `FaceLatticeFacts`: the Schläfli type and the face counts are those of one
of the five Platonic solids. Euler's relation comes from the Euler–Poincaré root. -/
theorem IsRegularPolyhedron.faceData {P : Set R3} (hP : IsRegularPolyhedron P)
    (hL : FaceLatticeFacts P) :
    ∃ t ∈ platonicTypes, HasFaceData P t.2.2.1 t.2.2.2.1 t.2.2.2.2 t.1 t.2.1 := by
  obtain ⟨s, m, hs, hm⟩ := hP.uniform hL
  have hPoly := hP.1
  have hdim := hP.2.1
  obtain ⟨H, hH, hp⟩ := hPoly.isPolyhedron
  have hE3 : Module.finrank ℝ R3 = 3 := R3.finrank_R3
  -- `s, m ≥ 3`
  obtain ⟨v0, e0, f0, hv0, he0, hf0, -, -⟩ := hL.exists_flag
  have hs3 : 3 ≤ s := hs f0 hf0 ▸ hL.facet_three_edges f0 hf0
  have hm3 : 3 ≤ m := hm v0 hv0 ▸ hL.vertex_three_edges v0 hv0
  have hmem := schlafli_pair_mem_of_regular_polytope hH hp hPoly hdim hE3 hs3 hm3 hs
    hL.edge_two_facets hm
  obtain ⟨hF, hV, hEul⟩ := regular_polytope_counts hH hp hPoly hdim hE3 hs
    hL.edge_two_facets hm
  set V := (facesOfDim P 0).ncard
  set E := (facesOfDim P 1).ncard
  set F := (facesOfDim P 2).ncard
  have hdata : ∀ V' E' F', V = V' → E = E' → F = F' → HasFaceData P V' E' F' s m := by
    rintro _ _ _ rfl rfl rfl
    exact ⟨rfl, rfl, rfl, hs, hL.edge_two_facets, hm⟩
  simp only [schlafliPairs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨(3, 3, 4, 6, 4), by simp [platonicTypes], hdata 4 6 4 (by omega) (by omega) (by omega)⟩
  · exact ⟨(3, 4, 6, 12, 8), by simp [platonicTypes],
      hdata 6 12 8 (by omega) (by omega) (by omega)⟩
  · exact ⟨(3, 5, 12, 30, 20), by simp [platonicTypes],
      hdata 12 30 20 (by omega) (by omega) (by omega)⟩
  · exact ⟨(4, 3, 8, 12, 6), by simp [platonicTypes],
      hdata 8 12 6 (by omega) (by omega) (by omega)⟩
  · exact ⟨(5, 3, 20, 30, 12), by simp [platonicTypes],
      hdata 20 30 12 (by omega) (by omega) (by omega)⟩

/-! ## Similar polyhedra have the same face counts -/

/-- A similarity `x ↦ r • g x` as an injective affine map. -/
noncomputable def simMap (g : R3 ≃ᵃⁱ[ℝ] R3) (r : ℝ) : R3 →ᵃ[ℝ] R3 :=
  (LinearMap.lsmul ℝ R3 r).toAffineMap.comp g.toAffineEquiv.toAffineMap

lemma simMap_apply (g : R3 ≃ᵃⁱ[ℝ] R3) (r : ℝ) (x : R3) : simMap g r x = r • g x := rfl

lemma simMap_injective (g : R3 ≃ᵃⁱ[ℝ] R3) {r : ℝ} (hr : r ≠ 0) :
    Function.Injective (simMap g r) := by
  intro x y h
  simp only [simMap_apply] at h
  exact g.injective (smul_right_injective R3 hr h)

/-- Similar polyhedra have the same number of faces of each dimension. -/
theorem Similar.ncard_facesOfDim {P Q : Set R3} (h : Similar P Q) (d : ℤ) :
    (facesOfDim Q d).ncard = (facesOfDim P d).ncard := by
  obtain ⟨g, r, hr, rfl⟩ := h
  have hQ : (fun x => r • x) '' (g '' P) = simMap g r '' P := by
    rw [Set.image_image]; rfl
  have hinj := simMap_injective g hr.ne'
  have := faces_image_affine (simMap g r) hinj P d
  change facesOfDim (simMap g r '' P) d = (fun F => simMap g r '' F) '' facesOfDim P d at this
  rw [hQ, this, Set.ncard_image_of_injective _ (Set.image_injective.2 hinj)]

/-- **The five constructed solids are pairwise non-similar** (they have 4, 8, 6, 20 and 12
vertices). -/
theorem platonic_pairwise_not_similar :
    ¬ Similar tetrahedron cube ∧ ¬ Similar tetrahedron octahedron ∧
    ¬ Similar tetrahedron dodecahedron ∧ ¬ Similar tetrahedron icosahedron ∧
    ¬ Similar cube octahedron ∧ ¬ Similar cube dodecahedron ∧ ¬ Similar cube icosahedron ∧
    ¬ Similar octahedron dodecahedron ∧ ¬ Similar octahedron icosahedron ∧
    ¬ Similar dodecahedron icosahedron := by
  have t := tetrahedron_faceData.1
  have c := cube_faceData.1
  have o := octahedron_faceData.1
  have d := dodecahedron_faceData.1
  have i := icosahedron_faceData.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> have := h.ncard_facesOfDim 0 <;>
    simp_all

end EulersGem
