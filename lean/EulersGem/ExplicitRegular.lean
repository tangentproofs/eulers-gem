/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.ExplicitPolyhedron
import EulersGem.RegularPolyhedron

/-!
# Face counts, incidences and flag-transitivity of explicit polytopes

Continuing `ExplicitPolyhedron`: from a checker-accepted `Data` we compute

* `facesOfDim body d` for `d = 0, 1, 2` (points, listed edges, listed facets) and their
  cardinalities `V`, `E`, `F`;
* the incidence numbers in the exact form used by `results_five_platonic_solids`;
* with reflection generators and a table of words (`Sym`), that the body is a
  **regular polyhedron** (`IsRegularPolyhedron`): every flag is the image of a base flag
  under a product of reflections that permute the points.
-/

open Set
open scoped RealInnerProductSpace

namespace EulersGem

namespace Explicit

open ZPhi Platonic

/-- The two index lists have the same members. -/
def sameSet (a b : List ℕ) : Bool := a.all b.contains && b.all a.contains

/-- `a ⊆ b` as index lists. -/
def sub (a b : List ℕ) : Bool := a.all b.contains

lemma sub_iff {a b : List ℕ} : sub a b = true ↔ ∀ u ∈ a, u ∈ b := by
  simp [sub]

lemma sameSet_iff {a b : List ℕ} : sameSet a b = true ↔ ∀ u, u ∈ a ↔ u ∈ b := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true, List.elem_iff]
  constructor
  · rintro ⟨h1, h2⟩ u; exact ⟨h1 u, h2 u⟩
  · intro h; exact ⟨fun u => (h u).1, fun u => (h u).2⟩

namespace Data

variable (D : Data)

/-- Distinctness of the listed faces, and the face type `{s, m}` with two facets per edge. -/
def checkType (s m : ℕ) : Bool :=
  decide (((List.range D.n).map fun i => [i]).Pairwise fun a b => sameSet a b = false) &&
  decide (D.edges.Pairwise fun a b => sameSet a b = false) &&
  decide (D.facets.Pairwise fun a b => sameSet a b = false) &&
  D.facets.all (fun F => (D.edges.filter fun e => sub e F).length == s) &&
  D.edges.all (fun e => (D.facets.filter fun F => sub e F).length == 2) &&
  (List.range D.n).all (fun i => (D.edges.filter fun e => e.contains i).length == m)

variable {D}

lemma hull_congr {S T : List ℕ} (h : ∀ u, u ∈ S ↔ u ∈ T) : D.hull S = D.hull T := by
  unfold hull; congr 1; ext x; simp only [mem_image, mem_ofPred_eq, h]

theorem exposed_edge (h : D.checkAll = true) {e : List ℕ} (he : e ∈ D.edges) : D.Exposed e := by
  obtain ⟨-, -, -, hE, -, -⟩ := checkAll_parts h
  rw [List.all_eq_true] at hE
  obtain ⟨i, j, rfl, -, -, hx⟩ := edgeOk_spec (hE e he)
  exact hx

theorem exposed_facet' (h : D.checkAll = true) {f : List ℕ} (hf : f ∈ D.facets) :
    D.Exposed f := by
  obtain ⟨-, -, -, -, hF, -⟩ := checkAll_parts h
  rw [List.all_eq_true] at hF
  exact exposed_facet (hF f hf)

lemma affDim_edge' (h : D.checkAll = true) {e : List ℕ} (he : e ∈ D.edges) :
    affDim (D.hull e) = 1 := by
  obtain ⟨hv, -, -, hE, -, -⟩ := checkAll_parts h
  rw [List.all_eq_true] at hE
  exact affDim_edge hv (hE e he)

lemma affDim_facet' (h : D.checkAll = true) {f : List ℕ} (hf : f ∈ D.facets) :
    affDim (D.hull f) = 2 := by
  obtain ⟨-, -, -, -, hF, -⟩ := checkAll_parts h
  rw [List.all_eq_true] at hF
  exact affDim_facet (hF f hf)

lemma affDim_vertex (i : ℕ) : affDim (D.hull [i]) = 0 := by
  rw [hull_singleton]; exact affDim_singleton _

/-- The faces of each dimension. -/
theorem facesOfDim_eq (h : D.checkAll = true) :
    facesOfDim D.body 0 = {x | ∃ S ∈ (List.range D.n).map (fun i => [i]), x = D.hull S} ∧
    facesOfDim D.body 1 = {x | ∃ S ∈ D.edges, x = D.hull S} ∧
    facesOfDim D.body 2 = {x | ∃ S ∈ D.facets, x = D.hull S} := by
  have h3 := affDim_body h
  have hv := (checkAll_parts h).1
  have key : ∀ (d : ℤ) (L : List (List ℕ)), (∀ S ∈ L, D.Exposed S ∧ affDim (D.hull S) = d) →
      (∀ F, IsFaceOf D.body F → affDim F = d → ∃ S ∈ L, F = D.hull S) →
      facesOfDim D.body d = {x | ∃ S ∈ L, x = D.hull S} := by
    intro d L h1 h2
    ext F
    simp only [mem_facesOfDim, mem_ofPred_eq]
    constructor
    · rintro ⟨hF, hd⟩; exact h2 F hF hd
    · rintro ⟨S, hS, rfl⟩; exact ⟨(h1 S hS).1.isFaceOf, (h1 S hS).2⟩
  refine ⟨key 0 _ ?_ ?_, key 1 _ ?_ ?_, key 2 _ ?_ ?_⟩
  · intro S hS
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hS
    exact ⟨exposed_vertex hv (List.mem_range.1 hi), affDim_vertex i⟩
  · intro F hF hd
    rcases face_cases h hF with rfl | rfl | ⟨i, hi, rfl⟩ | ⟨e, he, rfl⟩ | ⟨f, hf, rfl⟩
    · simp at hd
    · rw [h3] at hd; norm_num at hd
    · exact ⟨[i], List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩, rfl⟩
    · rw [affDim_edge' h he] at hd; norm_num at hd
    · rw [affDim_facet' h hf] at hd; norm_num at hd
  · exact fun S hS => ⟨exposed_edge h hS, affDim_edge' h hS⟩
  · intro F hF hd
    rcases face_cases h hF with rfl | rfl | ⟨i, hi, rfl⟩ | ⟨e, he, rfl⟩ | ⟨f, hf, rfl⟩
    · simp at hd
    · rw [h3] at hd; norm_num at hd
    · rw [affDim_vertex] at hd; norm_num at hd
    · exact ⟨e, he, rfl⟩
    · rw [affDim_facet' h hf] at hd; norm_num at hd
  · exact fun S hS => ⟨exposed_facet' h hS, affDim_facet' h hS⟩
  · intro F hF hd
    rcases face_cases h hF with rfl | rfl | ⟨i, hi, rfl⟩ | ⟨e, he, rfl⟩ | ⟨f, hf, rfl⟩
    · simp at hd
    · rw [h3] at hd; norm_num at hd
    · rw [affDim_vertex] at hd; norm_num at hd
    · rw [affDim_edge' h he] at hd; norm_num at hd
    · exact ⟨f, hf, rfl⟩

/-- Distinct exposed index sets give distinct faces, so a family of them has as many faces as
list entries. -/
theorem ncard_hulls (L : List (List ℕ)) (hexp : ∀ S ∈ L, D.Exposed S)
    (hpw : L.Pairwise fun a b => sameSet a b = false) :
    {x | ∃ S ∈ L, x = D.hull S}.ncard = L.length := by
  classical
  have hnd : (L.map D.hull).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine hpw.imp_of_mem fun {a b} ha hb hab heq => ?_
    have := ((hexp a ha).hull_inj D (hexp b hb)).1 heq
    rw [← sameSet_iff] at this
    rw [this] at hab; exact absurd hab (by decide)
  have hset : {x | ∃ S ∈ L, x = D.hull S} = ((L.map D.hull).toFinset : Set (Set R3)) := by
    ext x; simp [eq_comm]
  rw [hset, ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map]

lemma setOf_filter (L : List (List ℕ)) (p : List ℕ → Bool) (Q : Set R3 → Prop)
    (hQ : ∀ S ∈ L, Q (D.hull S) ↔ p S = true) :
    {x ∈ {y | ∃ S ∈ L, y = D.hull S} | Q x} = {x | ∃ S ∈ L.filter p, x = D.hull S} := by
  ext x
  simp only [mem_ofPred_eq, List.mem_filter]
  constructor
  · rintro ⟨⟨S, hS, rfl⟩, hq⟩; exact ⟨S, ⟨hS, (hQ S hS).1 hq⟩, rfl⟩
  · rintro ⟨S, ⟨hS, hp⟩, rfl⟩; exact ⟨⟨S, hS, rfl⟩, (hQ S hS).2 hp⟩

/-- **Counts and face type.** -/
theorem counts_and_type (h : D.checkAll = true) {s m : ℕ} (ht : D.checkType s m = true) :
    (facesOfDim D.body 0).ncard = D.n ∧ (facesOfDim D.body 1).ncard = D.edges.length ∧
    (facesOfDim D.body 2).ncard = D.facets.length ∧
    (∀ f ∈ facesOfDim D.body 2, {e ∈ facesOfDim D.body 1 | e ⊆ f}.ncard = s) ∧
    (∀ e ∈ facesOfDim D.body 1, {f ∈ facesOfDim D.body 2 | e ⊆ f}.ncard = 2) ∧
    (∀ v ∈ facesOfDim D.body 0, {e ∈ facesOfDim D.body 1 | v ⊆ e}.ncard = m) := by
  obtain ⟨h0, h1, h2⟩ := facesOfDim_eq h
  have hv := (checkAll_parts h).1
  simp only [checkType, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq,
    List.mem_range] at ht
  obtain ⟨⟨⟨⟨⟨hpV, hpE⟩, hpF⟩, hs⟩, h2f⟩, hm⟩ := ht
  have hexpV : ∀ S ∈ (List.range D.n).map (fun i => [i]), D.Exposed S := by
    intro S hS; obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hS
    exact exposed_vertex hv (List.mem_range.1 hi)
  have hexpE := fun S (hS : S ∈ D.edges) => exposed_edge h hS
  have hexpF := fun S (hS : S ∈ D.facets) => exposed_facet' h hS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0, ncard_hulls _ hexpV hpV]; simp
  · rw [h1, ncard_hulls _ hexpE hpE]
  · rw [h2, ncard_hulls _ hexpF hpF]
  · rw [h2]; rintro _ ⟨F, hF, rfl⟩
    rw [h1, setOf_filter D.edges (fun e => sub e F) (· ⊆ D.hull F)
      (fun S hS => by rw [sub_iff]; exact (hexpE S hS).hull_subset_iff D (hexpF F hF)),
      ncard_hulls _ (fun S hS => hexpE S (List.mem_filter.1 hS).1)
        (hpE.sublist List.filter_sublist), hs F hF]
  · rw [h1]; rintro _ ⟨e, he, rfl⟩
    rw [h2, setOf_filter D.facets (fun F => sub e F) (D.hull e ⊆ ·)
      (fun S hS => by rw [sub_iff]; exact (hexpE e he).hull_subset_iff D (hexpF S hS)),
      ncard_hulls _ (fun S hS => hexpF S (List.mem_filter.1 hS).1)
        (hpF.sublist List.filter_sublist), h2f e he]
  · rw [h0]; rintro _ ⟨S, hS, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hS
    rw [h1, setOf_filter D.edges (fun e => e.contains i) (D.hull [i] ⊆ ·)
      (fun T hT => by
        rw [(hexpV [i] hS).hull_subset_iff D (hexpE T hT)]
        simp),
      ncard_hulls _ (fun S hS => hexpE S (List.mem_filter.1 hS).1)
        (hpE.sublist List.filter_sublist), hm i (List.mem_range.1 hi)]

/-! ## Reflections -/

/-- Reflection in the plane through the origin orthogonal to `w` (the identity if `w = 0`). -/
noncomputable def reflMap (w x : R3) : R3 := x - (2 * ⟪w, x⟫ / ⟪w, w⟫) • w

lemma inner_reflMap (w x : R3) : ⟪w, reflMap w x⟫ = -⟪w, x⟫ := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hww : ⟪w, w⟫ ≠ 0 := inner_self_ne_zero.2 hw
  rw [reflMap, inner_sub_right, inner_smul_right]
  field_simp
  ring

lemma reflMap_reflMap (w x : R3) : reflMap w (reflMap w x) = x := by
  rw [reflMap, inner_reflMap, reflMap]
  rw [sub_sub, ← add_smul]
  have : 2 * ⟪w, x⟫ / ⟪w, w⟫ + 2 * -⟪w, x⟫ / ⟪w, w⟫ = 0 := by ring
  rw [this, zero_smul, sub_zero]

lemma norm_reflMap (w x : R3) : ‖reflMap w x‖ = ‖x‖ := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [reflMap]
  have hww : ⟪w, w⟫ ≠ 0 := inner_self_ne_zero.2 hw
  have h : ‖reflMap w x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, reflMap]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      real_inner_comm x w, RCLike.conj_to_real]
    field_simp
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The reflection as a linear isometry equivalence. -/
noncomputable def refl (w : R3) : R3 ≃ₗᵢ[ℝ] R3 where
  toFun := reflMap w
  invFun := reflMap w
  map_add' x y := by
    simp only [reflMap, inner_add_right, add_div, mul_add, add_smul]; abel
  map_smul' c x := by
    simp only [reflMap, inner_smul_right, RingHom.id_apply, smul_sub, smul_smul]
    congr 1; congr 1; ring
  left_inv x := reflMap_reflMap w x
  right_inv x := reflMap_reflMap w x
  norm_map' x := norm_reflMap w x

lemma refl_apply (w x : R3) : refl w x = reflMap w x := rfl

/-! ## Symmetry data -/

/-- Reflection generators (normals and the permutations of the points they induce), a base
flag `(vertex, edge index, facet index)`, and for each flag a word in the generators
carrying the base flag to it. -/
structure Sym where
  gens : List V
  perms : List (List ℕ)
  base : ℕ × ℕ × ℕ
  table : List ((ℕ × ℕ × ℕ) × List ℕ)

namespace Sym

variable (G : Sym)

/-- The `t`-th normal. -/
def gen (t : ℕ) : V := G.gens.getD t 0
/-- The `t`-th permutation. -/
def perm (t u : ℕ) : ℕ := (G.perms.getD t []).getD u 0
/-- The permutation of a word, rightmost letter first. -/
def permWord : List ℕ → ℕ → ℕ
  | [], u => u
  | t :: w, u => G.perm t (permWord w u)

/-- Generator `t` is a reflection permuting the points as `perm t`. -/
def genOk (D : Data) (t : ℕ) : Bool :=
  sgn (V.dot (G.gen t) (G.gen t)) == 1 &&
    (List.range D.n).all fun u => decide (G.perm t u < D.n) &&
      V.smul (V.dot (G.gen t) (G.gen t)) (D.pt (G.perm t u) - D.pt u) ==
        V.smul (ofInt (-2) * V.dot (G.gen t) (D.pt u)) (G.gen t)

/-- Every flag has a word. -/
def checkFlags (D : Data) : Bool :=
  decide (G.base.1 < D.n) && (List.range G.gens.length).all (G.genOk D) &&
  (List.range D.edges.length).all fun eI => (List.range D.facets.length).all fun fI =>
    !sub (D.edges.getD eI []) (D.facets.getD fI []) ||
      (D.edges.getD eI []).all fun i =>
        match G.table.lookup (i, eI, fI) with
        | none => false
        | some w => w.all (fun t => decide (t < G.gens.length)) &&
            G.permWord w G.base.1 == i &&
            sameSet ((D.edges.getD G.base.2.1 []).map (G.permWord w)) (D.edges.getD eI []) &&
            sameSet ((D.facets.getD G.base.2.2 []).map (G.permWord w)) (D.facets.getD fI [])

/-- The isometry of a word. -/
noncomputable def iso : List ℕ → R3 ≃ₗᵢ[ℝ] R3
  | [] => LinearIsometryEquiv.refl ℝ R3
  | t :: w => (iso w).trans (refl (G.gen t).toR3)

variable {G} {D : Data}

lemma genOk_spec {t : ℕ} (h : G.genOk D t = true) {u : ℕ} (hu : u < D.n) :
    G.perm t u < D.n ∧ refl (G.gen t).toR3 (D.P u) = D.P (G.perm t u) := by
  simp only [genOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨hpos, hall⟩ := h
  obtain ⟨hlt, heq⟩ := hall u hu
  refine ⟨hlt, ?_⟩
  have hR := congrArg V.toR3 heq
  rw [V.toR3_smul, V.toR3_smul, V.toR3_sub, toReal_mul, toReal_ofInt, ← V.inner_toR3,
    ← V.inner_toR3] at hR
  set g := (G.gen t).toR3
  have hR' : ⟪g, g⟫ • (D.P (G.perm t u) - D.P u) = (-2 * ⟪g, D.P u⟫) • g := by
    change ⟪g, g⟫ • ((D.pt (G.perm t u)).toR3 - (D.pt u).toR3) = (-2 * ⟪g, (D.pt u).toR3⟫) • g
    rw [hR]; push_cast; rfl
  have hww : 0 < ⟪g, g⟫ := by
    rw [V.inner_toR3]; exact sgn_eq_one hpos
  rw [refl_apply, reflMap]
  have : D.P (G.perm t u) = D.P u + (1 / ⟪g, g⟫) • (⟪g, g⟫ • (D.P (G.perm t u) - D.P u)) := by
    rw [smul_smul, one_div, inv_mul_cancel₀ hww.ne', one_smul]; abel
  rw [this, hR', smul_smul, sub_eq_add_neg, ← neg_smul]
  congr 2
  field_simp

lemma iso_spec (hg : ∀ t < G.gens.length, G.genOk D t = true) :
    ∀ w : List ℕ, (∀ t ∈ w, t < G.gens.length) → ∀ u < D.n,
      G.permWord w u < D.n ∧ G.iso w (D.P u) = D.P (G.permWord w u) := by
  intro w
  induction w with
  | nil => intro _ u hu; exact ⟨hu, rfl⟩
  | cons t w ih =>
    intro hw u hu
    obtain ⟨h1, h2⟩ := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx)) u hu
    obtain ⟨h3, h4⟩ := genOk_spec (hg t (hw t List.mem_cons_self)) h1
    refine ⟨h3, ?_⟩
    simp only [iso, permWord, LinearIsometryEquiv.trans_apply, h2, h4]

lemma image_hull (hg : ∀ t < G.gens.length, G.genOk D t = true) {w : List ℕ}
    (hw : ∀ t ∈ w, t < G.gens.length) {S : List ℕ} (hS : ∀ u ∈ S, u < D.n) :
    G.iso w '' D.hull S = D.hull (S.map (G.permWord w)) := by
  have hlin := (G.iso w).toLinearEquiv.toLinearMap.image_convexHull (D.P '' {u | u ∈ S})
  change (G.iso w) '' _ = convexHull ℝ ((G.iso w) '' _) at hlin
  rw [Data.hull, hlin, Data.hull]
  congr 1
  ext x
  simp only [mem_image, mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨G.permWord w u, ⟨u, hu, rfl⟩, ((iso_spec hg w hw u (hS u hu)).2).symm⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨D.P u, ⟨u, hu, rfl⟩, (iso_spec hg w hw u (hS u hu)).2⟩

lemma image_verts (hg : ∀ t < G.gens.length, G.genOk D t = true) {w : List ℕ}
    (hw : ∀ t ∈ w, t < G.gens.length) : G.iso w '' D.verts = D.verts := by
  have hsub : G.iso w '' D.verts ⊆ D.verts := by
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    rw [(iso_spec hg w hw u hu).2]
    exact ⟨_, (iso_spec hg w hw u hu).1, rfl⟩
  exact Set.eq_of_subset_of_ncard_le hsub
    (by rw [Set.ncard_image_of_injective _ (G.iso w).injective]) D.verts_finite

lemma image_body (hg : ∀ t < G.gens.length, G.genOk D t = true) {w : List ℕ}
    (hw : ∀ t ∈ w, t < G.gens.length) : G.iso w '' D.body = D.body := by
  have hlin := (G.iso w).toLinearEquiv.toLinearMap.image_convexHull D.verts
  change (G.iso w) '' _ = convexHull ℝ ((G.iso w) '' _) at hlin
  rw [Data.body, hlin]
  exact congrArg _ (image_verts hg hw)

lemma getD_of_lt {α : Type*} {l : List α} {k : ℕ} (hk : k < l.length) (d : α) :
    l.getD k d = l[k] := by simp [List.getD_eq_getElem?_getD, hk]

lemma getD_of_ge {α : Type*} {l : List α} {k : ℕ} (hk : l.length ≤ k) (d : α) :
    l.getD k d = d := by simp [List.getD_eq_getElem?_getD, hk]

lemma lie_symm_image_image (g : R3 ≃ₗᵢ[ℝ] R3) (s : Set R3) : g.symm '' (g '' s) = s := by
  simp [Set.image_image]

lemma getD_edges_lt (h : D.checkAll = true) (k : ℕ) : ∀ u ∈ D.edges.getD k [], u < D.n := by
  intro u hu
  by_cases hk : k < D.edges.length
  · rw [getD_of_lt hk] at hu
    exact (exposed_edge h (List.getElem_mem hk)).lt D hu
  · rw [getD_of_ge (not_lt.1 hk)] at hu; simp at hu

lemma getD_facets_lt (h : D.checkAll = true) (k : ℕ) : ∀ u ∈ D.facets.getD k [], u < D.n := by
  intro u hu
  by_cases hk : k < D.facets.length
  · rw [getD_of_lt hk] at hu
    exact (exposed_facet' h (List.getElem_mem hk)).lt D hu
  · rw [getD_of_ge (not_lt.1 hk)] at hu; simp at hu

/-- The base flag, as sets. -/
noncomputable def baseV (G : Sym) (D : Data) : Set R3 := D.hull [G.base.1]
noncomputable def baseE (G : Sym) (D : Data) : Set R3 := D.hull (D.edges.getD G.base.2.1 [])
noncomputable def baseF (G : Sym) (D : Data) : Set R3 := D.hull (D.facets.getD G.base.2.2 [])

/-- Every flag is the image of the base flag under a symmetry. -/
theorem exists_sym_of_flag (h : D.checkAll = true) (hf : G.checkFlags D = true)
    {v e f : Set R3} (hfl : IsFlag D.body v e f) :
    ∃ g : R3 ≃ₗᵢ[ℝ] R3, g '' D.body = D.body ∧ g '' baseV G D = v ∧ g '' baseE G D = e ∧
      g '' baseF G D = f := by
  obtain ⟨h0, h1, h2⟩ := facesOfDim_eq h
  have hv := (checkAll_parts h).1
  obtain ⟨hvd, hed, hfd, hve, hef⟩ := hfl
  rw [h0] at hvd; rw [h1] at hed; rw [h2] at hfd
  obtain ⟨S, hS, rfl⟩ := hvd
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hS
  obtain ⟨E, hE, rfl⟩ := hed
  obtain ⟨F, hF, rfl⟩ := hfd
  have hin := List.mem_range.1 hi
  have hiE : i ∈ E :=
    ((exposed_vertex hv hin).hull_subset_iff D (exposed_edge h hE)).1 hve i (by simp)
  have hEF : sub E F = true := sub_iff.2
    (((exposed_edge h hE).hull_subset_iff D (exposed_facet' h hF)).1 hef)
  obtain ⟨eI, heI, rfl⟩ := List.mem_iff_getElem.1 hE
  obtain ⟨fI, hfI, rfl⟩ := List.mem_iff_getElem.1 hF
  simp only [checkFlags, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at hf
  obtain ⟨⟨hb, hg⟩, htab⟩ := hf
  have hsub' : sub (D.edges.getD eI []) (D.facets.getD fI []) = true := by
    rw [getD_of_lt heI, getD_of_lt hfI]; exact hEF
  have hentry := (htab eI heI fI hfI).resolve_left (by rw [hsub']; decide)
  have hiE' : i ∈ D.edges.getD eI [] := by rw [getD_of_lt heI]; exact hiE
  have hent := hentry i hiE'
  split at hent
  · exact absurd hent (by decide)
  rename_i w _
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hent
  obtain ⟨⟨⟨hwl, hwi⟩, hwe⟩, hwf⟩ := hent
  refine ⟨G.iso w, image_body hg hwl, ?_, ?_, ?_⟩
  · rw [baseV, image_hull hg hwl (by simpa using hb)]
    exact hull_congr (by simp [hwi])
  · rw [baseE, image_hull hg hwl (getD_edges_lt h _), ← getD_of_lt heI []]
    exact hull_congr (sameSet_iff.1 hwe)
  · rw [baseF, image_hull hg hwl (getD_facets_lt h _), ← getD_of_lt hfI []]
    exact hull_congr (sameSet_iff.1 hwf)

/-- **The body is a regular polyhedron.** -/
theorem isRegularPolyhedron (h : D.checkAll = true) (hf : G.checkFlags D = true) :
    IsRegularPolyhedron D.body := by
  refine ⟨D.isPolytope_body, affDim_body h, fun v e f v' e' f' h1 h2 => ?_⟩
  obtain ⟨g1, hb1, hv1, he1, hf1⟩ := exists_sym_of_flag h hf h1
  obtain ⟨g2, hb2, hv2, he2, hf2⟩ := exists_sym_of_flag h hf h2
  refine ⟨(g1.symm.trans g2).toAffineIsometryEquiv, ?_, ?_, ?_, ?_⟩ <;>
    simp only [LinearIsometryEquiv.coe_toAffineIsometryEquiv, LinearIsometryEquiv.coe_trans,
      image_comp]
  · rw [← hb1, lie_symm_image_image, hb1, hb2]
  · rw [← hv1, lie_symm_image_image, hv2]
  · rw [← he1, lie_symm_image_image, he2]
  · rw [← hf1, lie_symm_image_image, hf2]

end Sym

end Data

end Explicit

end EulersGem
