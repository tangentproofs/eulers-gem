/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.SimplexFaces
import EulersGem.PlatonicOfEuler

/-!
# A geometric solid on the Euler–Poincaré spine: the tetrahedron

This closes the loop `Euler → Platonic` on an actual geometric solid rather than a
combinatorial witness. For **any** geometric tetrahedron — the convex hull of four
affinely independent points in any 3-dimensional real inner product space — we prove:

* `faceEulerSum_body_eq_one` — Euler–Poincaré applies to the simplex, because
  `SimplexFaces.body_eq_iInter_closedHalfspace` gives it an H-representation;
* `tetrahedron_face_counts` — `V = 4`, `E = 6`, `F = 4`, counted by *geometric* faces
  (`IsFaceOf` + `affDim`), via the simplex face lattice;
* `tetrahedron_euler_relation` — `V − E + F = 2`, discharged from
  `euler_relation_convex_3polytope` (i.e. from `Euler_Poincare_full`), **not** assumed;
* `tetrahedron_incidence` — the four incidence counts (`3` edges per 2-face, `2` 2-faces
  per edge, `3` edges per vertex, `2` vertices per edge) *proved* from the face lattice;
* `tetrahedron_schlafli` — hence `(s, m) = (3, 3)` lands in the five Schläfli pairs via
  `schlafli_pair_mem_of_regular_polytope`.

Consequences for the honesty bar: the incidence hypotheses of
`schlafli_pair_mem_of_regular_polytope` are **not vacuous** — a geometric solid satisfies
them, and for that solid every one of them is proved here. The remaining Platonic gap is
the other four solids (their geometric constructions and face lattices), not the Euler
step. See `UNIFIED_SPINE.md`.
-/

open Set

namespace EulersGem
namespace Simplex

open Platonic (facesOfDim schlafliPairs)

/-! ## Euler–Poincaré for a geometric simplex -/

section EP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nonempty E]
variable {ι : Type*} [Fintype ι] (b : AffineBasis ι ℝ E)

/-- **Euler–Poincaré for a geometric simplex.** The alternating face-count sum is `1`,
obtained from `Euler_Poincare_full` applied to the H-representation of the simplex. -/
theorem faceEulerSum_body_eq_one (hn : 1 ≤ Module.finrank ℝ E) :
    faceEulerSum (body b) (Module.finrank ℝ E) = 1 :=
  Euler_Poincare_full (coordHyperplanes_finite b) (body_eq_iInter_closedHalfspace b)
    (isPolytope_body b) (affDim_body b) hn

end EP

/-! ## Faces of a simplex, indexed by vertex subsets -/

section Correspondence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] (b : AffineBasis ι ℝ E)

lemma facesOfDim_body (d : ℤ) :
    facesOfDim (body b) d = face b '' {S : Finset ι | (S.card : ℤ) = d + 1} :=
  facesOfDim_eq_image b d

lemma ncard_facesOfDim_body (d : ℤ) :
    (facesOfDim (body b) d).ncard = {S : Finset ι | (S.card : ℤ) = d + 1}.ncard := by
  rw [facesOfDim_body b d, Set.ncard_image_of_injective _ (face_injective b)]

/-- Faces of dimension `d` contained in a given subsimplex correspond to vertex subsets of
the right size inside its index set. -/
lemma ncard_facesOfDim_subset (d : ℤ) (T : Finset ι) :
    {e ∈ facesOfDim (body b) d | e ⊆ face b T}.ncard =
      {S : Finset ι | (S.card : ℤ) = d + 1 ∧ S ⊆ T}.ncard := by
  have hset : {e ∈ facesOfDim (body b) d | e ⊆ face b T}
      = face b '' {S : Finset ι | (S.card : ℤ) = d + 1 ∧ S ⊆ T} := by
    ext f
    rw [Set.mem_sep_iff, facesOfDim_body b d]
    constructor
    · rintro ⟨⟨S, hS, rfl⟩, hsub⟩
      exact ⟨S, ⟨hS, (face_subset_iff b).mp hsub⟩, rfl⟩
    · rintro ⟨S, ⟨hS, hsub⟩, rfl⟩
      exact ⟨⟨S, hS, rfl⟩, (face_subset_iff b).mpr hsub⟩
  rw [hset, Set.ncard_image_of_injective _ (face_injective b)]

/-- Faces of dimension `d` containing a given subsimplex correspond to vertex subsets of
the right size containing its index set. -/
lemma ncard_facesOfDim_superset (d : ℤ) (T : Finset ι) :
    {e ∈ facesOfDim (body b) d | face b T ⊆ e}.ncard =
      {S : Finset ι | (S.card : ℤ) = d + 1 ∧ T ⊆ S}.ncard := by
  have hset : {e ∈ facesOfDim (body b) d | face b T ⊆ e}
      = face b '' {S : Finset ι | (S.card : ℤ) = d + 1 ∧ T ⊆ S} := by
    ext f
    rw [Set.mem_sep_iff, facesOfDim_body b d]
    constructor
    · rintro ⟨⟨S, hS, rfl⟩, hsub⟩
      exact ⟨S, ⟨hS, (face_subset_iff b).mp hsub⟩, rfl⟩
    · rintro ⟨S, ⟨hS, hsub⟩, rfl⟩
      exact ⟨⟨S, hS, rfl⟩, (face_subset_iff b).mpr hsub⟩
  rw [hset, Set.ncard_image_of_injective _ (face_injective b)]

end Correspondence

/-! ## Counting vertex subsets (decidable) -/

/-- Bridge from a set of `Finset`s to a `Finset` of `Finset`s, so counts can be decided. -/
lemma ncard_setOf_finset {α : Type*} [Fintype α] [DecidableEq α] (p : Finset α → Prop)
    [DecidablePred p] :
    {S : Finset α | p S}.ncard =
      ((Finset.univ : Finset (Finset α)).filter p).card := by
  have h : {S : Finset α | p S} = ↑((Finset.univ : Finset (Finset α)).filter p) := by
    ext S; simp
  rw [h, Set.ncard_coe_finset]

section Fin4

private lemma count_card_eq_1 : {S : Finset (Fin 4) | (S.card : ℤ) = 0 + 1}.ncard = 4 := by
  rw [ncard_setOf_finset]; decide

private lemma count_card_eq_2 : {S : Finset (Fin 4) | (S.card : ℤ) = 1 + 1}.ncard = 6 := by
  rw [ncard_setOf_finset]; decide

private lemma count_card_eq_3 : {S : Finset (Fin 4) | (S.card : ℤ) = 2 + 1}.ncard = 4 := by
  rw [ncard_setOf_finset]; decide

/-- Each 3-element subset of a 4-element set has three 2-element subsets. -/
private lemma count_edges_of_face (T : Finset (Fin 4)) (hT : (T.card : ℤ) = 2 + 1) :
    {S : Finset (Fin 4) | (S.card : ℤ) = 1 + 1 ∧ S ⊆ T}.ncard = 3 := by
  rw [ncard_setOf_finset]
  have hT' : T.card = 3 := by omega
  revert hT'
  revert T
  decide

/-- Each 2-element subset of a 4-element set lies in two 3-element subsets. -/
private lemma count_faces_of_edge (T : Finset (Fin 4)) (hT : (T.card : ℤ) = 1 + 1) :
    {S : Finset (Fin 4) | (S.card : ℤ) = 2 + 1 ∧ T ⊆ S}.ncard = 2 := by
  rw [ncard_setOf_finset]
  have hT' : T.card = 2 := by omega
  revert hT'
  revert T
  decide

/-- Each singleton lies in three 2-element subsets of a 4-element set. -/
private lemma count_edges_of_vertex (T : Finset (Fin 4)) (hT : (T.card : ℤ) = 0 + 1) :
    {S : Finset (Fin 4) | (S.card : ℤ) = 1 + 1 ∧ T ⊆ S}.ncard = 3 := by
  rw [ncard_setOf_finset]
  have hT' : T.card = 1 := by omega
  revert hT'
  revert T
  decide

/-- Each 2-element subset has two singleton subsets. -/
private lemma count_vertices_of_edge (T : Finset (Fin 4)) (hT : (T.card : ℤ) = 1 + 1) :
    {S : Finset (Fin 4) | (S.card : ℤ) = 0 + 1 ∧ S ⊆ T}.ncard = 2 := by
  rw [ncard_setOf_finset]
  have hT' : T.card = 2 := by omega
  revert hT'
  revert T
  decide

end Fin4

/-! ## The geometric tetrahedron -/

section Tetrahedron

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nonempty E]
variable (b : AffineBasis (Fin 4) ℝ E)

/-- A geometric tetrahedron is a full-dimensional convex 3-polytope. -/
lemma affDim_body_tetra (hE : Module.finrank ℝ E = 3) : affDim (body b) = 3 := by
  rw [affDim_body b, hE]
  norm_num

/-- **Face counts of a geometric tetrahedron: `V = 4`, `E = 6`, `F = 4`.**
These count *geometric* faces (`IsFaceOf` + `affDim`), obtained from the simplex face
lattice, not postulated. -/
theorem tetrahedron_face_counts :
    (facesOfDim (body b) 0).ncard = 4 ∧
      (facesOfDim (body b) 1).ncard = 6 ∧
      (facesOfDim (body b) 2).ncard = 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ncard_facesOfDim_body b 0]; exact count_card_eq_1
  · rw [ncard_facesOfDim_body b 1]; exact count_card_eq_2
  · rw [ncard_facesOfDim_body b 2]; exact count_card_eq_3

/-- **Euler's relation for a geometric tetrahedron, discharged from Euler–Poincaré.**
`V − E + F = 2` is obtained from `euler_relation_convex_3polytope`, never assumed. -/
theorem tetrahedron_euler_relation (hE : Module.finrank ℝ E = 3) :
    ((facesOfDim (body b) 0).ncard : ℤ) - (facesOfDim (body b) 1).ncard
      + (facesOfDim (body b) 2).ncard = 2 :=
  euler_relation_convex_3polytope (coordHyperplanes_finite b)
    (body_eq_iInter_closedHalfspace b) (isPolytope_body b) (affDim_body_tetra b hE) hE

/-- Sanity cross-check: the geometric face counts satisfy the Euler relation numerically,
i.e. `4 − 6 + 4 = 2`. Both sides are independently derived (counts from the face lattice,
the relation from EP). -/
theorem tetrahedron_euler_counts : (4 : ℤ) - 6 + 4 = 2 := by norm_num

/-- **The four incidence counts of a geometric tetrahedron, proved from its face lattice.**
Every 2-face has `3` edges, every edge lies in `2` 2-faces, every vertex meets `3` edges,
every edge has `2` vertices. These are exactly the hypotheses of
`schlafli_pair_mem_of_regular_polytope`, so they are not vacuous. -/
theorem tetrahedron_incidence :
    (∀ f ∈ facesOfDim (body b) 2, {e ∈ facesOfDim (body b) 1 | e ⊆ f}.ncard = 3) ∧
      (∀ e ∈ facesOfDim (body b) 1, {f ∈ facesOfDim (body b) 2 | e ⊆ f}.ncard = 2) ∧
      (∀ v ∈ facesOfDim (body b) 0, {e ∈ facesOfDim (body b) 1 | v ⊆ e}.ncard = 3) ∧
      (∀ e ∈ facesOfDim (body b) 1, {v ∈ facesOfDim (body b) 0 | v ⊆ e}.ncard = 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf
    rw [facesOfDim_body b 2] at hf
    obtain ⟨S, hS, rfl⟩ := hf
    rw [ncard_facesOfDim_subset b 1 S]
    exact count_edges_of_face S hS
  · intro e he
    rw [facesOfDim_body b 1] at he
    obtain ⟨S, hS, rfl⟩ := he
    rw [ncard_facesOfDim_superset b 2 S]
    exact count_faces_of_edge S hS
  · intro v hv
    rw [facesOfDim_body b 0] at hv
    obtain ⟨S, hS, rfl⟩ := hv
    rw [ncard_facesOfDim_superset b 1 S]
    exact count_edges_of_vertex S hS
  · intro e he
    rw [facesOfDim_body b 1] at he
    obtain ⟨S, hS, rfl⟩ := he
    rw [ncard_facesOfDim_subset b 0 S]
    exact count_vertices_of_edge S hS

/-- **A geometric tetrahedron is Platonic `{3,3}` on the Euler–Poincaré spine.**

For any tetrahedron (hull of four affinely independent points in a 3-dimensional inner
product space) the geometric face counts satisfy the two Platonic double-counting
identities with `(s, m) = (3, 3)`, satisfy Euler's relation, and `(3, 3)` is one of the
five classical Schläfli pairs.

Provenance of each conjunct:
* the double-counting identities come from `Platonic.regular_polytope_counts`, i.e. from
  face-lattice incidence via `ncard_mul_eq_ncard_mul`, using `tetrahedron_incidence`;
* Euler's relation comes from `euler_relation_convex_3polytope` = `Euler_Poincare_full`;
* the Schläfli membership comes from `schlafli_pair_mem_of_regular_polytope`.

Nothing in this chain assumes `V − E + F = 2`. -/
theorem tetrahedron_platonic (hE : Module.finrank ℝ E = 3) :
    3 * (facesOfDim (body b) 2).ncard = 2 * (facesOfDim (body b) 1).ncard ∧
      3 * (facesOfDim (body b) 0).ncard = 2 * (facesOfDim (body b) 1).ncard ∧
      ((facesOfDim (body b) 0).ncard : ℤ) - (facesOfDim (body b) 1).ncard
        + (facesOfDim (body b) 2).ncard = 2 ∧
      ((3 : ℕ), (3 : ℕ)) ∈ schlafliPairs := by
  obtain ⟨h2e, he2, hv3, he0⟩ := tetrahedron_incidence b
  obtain ⟨hFace, hVert, hEuler⟩ :=
    Platonic.regular_polytope_counts (s := 3) (m := 3) (coordHyperplanes_finite b)
      (body_eq_iInter_closedHalfspace b) (isPolytope_body b) (affDim_body_tetra b hE) hE
      h2e he2 hv3 he0
  refine ⟨hFace, hVert, hEuler, ?_⟩
  exact Platonic.schlafli_pair_mem_of_regular_polytope (coordHyperplanes_finite b)
    (body_eq_iInter_closedHalfspace b) (isPolytope_body b) (affDim_body_tetra b hE) hE
    (by norm_num) (by norm_num) h2e he2 hv3 he0

end Tetrahedron

/-! ## Existence of a geometric tetrahedron -/

/-- Every 3-dimensional real inner product space contains a geometric tetrahedron, so the
statements above are about a nonempty class of solids. -/
theorem exists_tetrahedron {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 3) :
    Nonempty (AffineBasis (Fin 4) ℝ E) :=
  AffineBasis.exists_affineBasis_of_finiteDimensional (ι := Fin 4) (k := ℝ) (V := E) (P := E)
    (by simp [hE])

end Simplex
end EulersGem
