/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.Cube
import EulersGem.GeometricPlatonic

/-!
# Metric regularity of the three geometric solids

The face-lattice results say the tetrahedron, octahedron and cube are *combinatorially*
regular. This file adds the first metric facts, so the solids are not merely combinatorial:

* all vertices lie on a sphere about the origin (`norm_sq_vtx`, `norm_sq_corner`);
* all edges have the same length (`Octahedron.edge_norm_sq`, `Cube.edge_norm_sq`);
* `Cube.regularTetra` — the **regular** tetrahedron inscribed in the cube: four alternating
  corners, affinely independent, so the whole simplex face-lattice machinery applies, and all
  six of its edges have the same length.

These are *equilateral* statements (equal edge lengths, vertices concyclic). Full metric
regularity — congruent regular faces, a flag-transitive symmetry group — is still **not**
formalized; see `PLATONIC_CLAUDE_AUDIT.md`.
-/

open Set
open scoped RealInnerProductSpace

namespace EulersGem

/-! ## Octahedron: vertices on the unit sphere, edges of length `√2` -/

namespace Octahedron

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)

/-- Every vertex of the cross-polytope is a unit vector. -/
lemma norm_sq_vtx (p : Fin n × Bool) : ‖vtx b p‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, inner_vtx_self]

/-- Two vertices of the cross-polytope on different coordinates are at distance `√2`:
every edge has the same length. -/
lemma edge_norm_sq {p q : Fin n × Bool} (h : p.1 ≠ q.1) :
    ‖vtx b p - vtx b q‖ ^ 2 = 2 := by
  rw [norm_sub_sq_real, norm_sq_vtx b p, norm_sq_vtx b q, inner_vtx_vtx, if_neg h]
  ring

/-- The two vertices selected by an edge of the cross-polytope sit on different coordinates,
hence (`edge_norm_sq`) the edge has squared length `2`. -/
lemma edge_vtx_coord_ne {c : Fin n → Option Bool} {p q : Fin n × Bool}
    (hp : p ∈ vtxIdx c) (hq : q ∈ vtxIdx c) (hpq : p ≠ q) : p.1 ≠ q.1 := by
  intro hcoord
  have hcp : c p.1 = some p.2 := mem_vtxIdx.mp hp
  have hcq : c q.1 = some q.2 := mem_vtxIdx.mp hq
  rw [hcoord, hcq] at hcp
  exact hpq (Prod.ext hcoord (Option.some_injective _ hcp).symm)

/-- **All edges of the cross-polytope have squared length `2`.** -/
theorem edges_equilateral {c : Fin n → Option Bool} {p q : Fin n × Bool}
    (hp : p ∈ vtxIdx c) (hq : q ∈ vtxIdx c) (hpq : p ≠ q) :
    ‖vtx b p - vtx b q‖ ^ 2 = 2 :=
  edge_norm_sq b (edge_vtx_coord_ne hp hq hpq)

end Octahedron

/-! ## Cube: vertices on a sphere of radius `√n`, edges of length `2` -/

namespace Cube

open Octahedron (sgn sgn_true sgn_false)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)

lemma inner_corner_corner (σ τ : Fin n → Bool) :
    ⟪corner b σ, corner b τ⟫ = ∑ i, sgn (σ i) * sgn (τ i) := by
  rw [corner, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, inner_b_corner]

/-- Every corner of the cube has squared norm `n`: the corners are concyclic. -/
lemma norm_sq_corner (σ : Fin n → Bool) : ‖corner b σ‖ ^ 2 = n := by
  rw [← real_inner_self_eq_norm_sq, inner_corner_corner]
  have h : ∀ i : Fin n, sgn (σ i) * sgn (σ i) = 1 := fun i => Octahedron.sgn_mul_self _
  rw [Finset.sum_congr rfl fun i _ => h i]
  simp

/-- Two corners differing in exactly one coordinate are at distance `2`. -/
lemma edge_norm_sq {σ τ : Fin n → Bool} {j : Fin n} (hτ : τ = Function.update σ j (τ j))
    (hj : σ j ≠ τ j) :
    ‖corner b σ - corner b τ‖ ^ 2 = 4 := by
  have hsub : corner b σ - corner b τ = (sgn (σ j) - sgn (τ j)) • b j := by
    have h := corner_sub_corner_update b σ j (τ j)
    rw [← hτ] at h
    exact h
  rw [hsub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hnb : ‖b j‖ = 1 := b.orthonormal.1 j
  have hval : (sgn (σ j) - sgn (τ j)) ^ 2 = 4 := by
    have h : ∀ s t : Bool, s ≠ t → (sgn s - sgn t) ^ 2 = 4 := by
      intro s t hst
      cases s <;> cases t <;> first | exact absurd rfl hst | norm_num [sgn]
    exact h _ _ hj
  rw [hnb, hval]
  norm_num

/-- Two corners of a subcube can only differ on a free coordinate. -/
lemma edge_free_coord {c : Fin n → Option Bool} {σ τ : Fin n → Bool}
    (hσ : σ ∈ cornerIdx c) (hτ : τ ∈ cornerIdx c) {j : Fin n} (hj : σ j ≠ τ j) :
    c j = none := by
  rcases hc : c j with _ | s
  · rfl
  · exact absurd ((mem_cornerIdx.mp hσ j s hc).trans (mem_cornerIdx.mp hτ j s hc).symm) hj

/-- **All edges of the cube have squared length `4`.** An edge is a subcube with exactly one
free coordinate, and its two corners differ precisely there. -/
theorem edges_equilateral {c : Fin n → Option Bool} {σ τ : Fin n → Bool}
    (hσ : σ ∈ cornerIdx c) (hτ : τ ∈ cornerIdx c) (hne : σ ≠ τ)
    (hfree : ∀ i j : Fin n, c i = none → c j = none → i = j) :
    ‖corner b σ - corner b τ‖ ^ 2 = 4 := by
  -- the coordinates where they differ are free, and there is at most one free coordinate
  obtain ⟨j, hj⟩ : ∃ j, σ j ≠ τ j := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  have hcj : c j = none := edge_free_coord hσ hτ hj
  have hupd : τ = Function.update σ j (τ j) := by
    funext i
    by_cases hij : i = j
    · subst hij; rw [Function.update_self]
    · rw [Function.update_of_ne hij]
      by_cases hci : c i = none
      · exact absurd (hfree i j hci hcj) hij
      · rcases hc : c i with _ | s
        · exact absurd hc hci
        · exact ((mem_cornerIdx.mp hτ i s hc).trans (mem_cornerIdx.mp hσ i s hc).symm)
  exact edge_norm_sq b hupd hj

end Cube

/-! ## The regular tetrahedron inscribed in the cube

Four corners of the cube with an even number of minus signs are pairwise equidistant, so they
span a **regular** tetrahedron. They are affinely independent, hence form an `AffineBasis`, so
the whole simplex face-lattice machinery (and with it `Simplex.tetrahedron_platonic`) applies
to a genuinely regular tetrahedron.
-/

namespace Cube

open Octahedron (sgn)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (b : OrthonormalBasis (Fin 3) ℝ E)

/-- Sign patterns of the four alternating corners: `(+,+,+)`, `(+,−,−)`, `(−,+,−)`, `(−,−,+)`. -/
def tetraSign : Fin 4 → (Fin 3 → Bool)
  | 0 => fun _ => true
  | 1 => fun i => i = 0
  | 2 => fun i => i = 1
  | 3 => fun i => i = 2

/-- Vertices of the regular tetrahedron inscribed in the cube. -/
noncomputable def tetraVtx (k : Fin 4) : E := corner b (tetraSign k)

/-- Gram matrix of the inscribed tetrahedron: `3` on the diagonal, `−1` off it. -/
lemma inner_tetraVtx (k l : Fin 4) :
    ⟪tetraVtx b k, tetraVtx b l⟫ = if k = l then 3 else -1 := by
  rw [tetraVtx, tetraVtx, inner_corner_corner]
  fin_cases k <;> fin_cases l <;>
    simp [tetraSign, Fin.sum_univ_three, sgn] <;> norm_num

lemma norm_sq_tetraVtx (k : Fin 4) : ‖tetraVtx b k‖ ^ 2 = 3 := by
  rw [← real_inner_self_eq_norm_sq, inner_tetraVtx, if_pos rfl]

/-- **The inscribed tetrahedron is regular:** all six edges have squared length `8`. -/
theorem tetraVtx_dist_sq {k l : Fin 4} (h : k ≠ l) :
    ‖tetraVtx b k - tetraVtx b l‖ ^ 2 = 8 := by
  rw [norm_sub_sq_real, norm_sq_tetraVtx, norm_sq_tetraVtx, inner_tetraVtx, if_neg h]
  norm_num

/-- The four alternating corners are affinely independent: testing an affine relation against
each vertex turns the Gram matrix `3 δ − 1` into `4 w j = 0`. -/
theorem affineIndependent_tetraVtx : AffineIndependent ℝ (tetraVtx b) := by
  classical
  rw [affineIndependent_iff]
  intro s w hw hcomb j hj
  have hinner : ∑ i ∈ s, w i * ⟪tetraVtx b j, tetraVtx b i⟫ = 0 := by
    have h := congrArg (fun y => ⟪tetraVtx b j, y⟫) hcomb
    simp only [inner_zero_right, inner_sum] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => (real_inner_smul_right _ _ _).symm
  have hsplit : ∀ i : Fin 4, w i * ⟪tetraVtx b j, tetraVtx b i⟫
      = -w i + (if i = j then 4 * w i else 0) := by
    intro i
    rw [inner_tetraVtx]
    by_cases hij : i = j
    · rw [if_pos hij.symm, if_pos hij]
      ring
    · rw [if_neg (fun h => hij h.symm), if_neg hij]
      ring
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib,
    Finset.sum_ite_eq' s j fun i => 4 * w i, if_pos hj, Finset.sum_neg_distrib, hw] at hinner
  simp only [neg_zero, zero_add] at hinner
  linarith

theorem affineSpan_tetraVtx (hE : Module.finrank ℝ E = 3) :
    affineSpan ℝ (Set.range (tetraVtx b)) = ⊤ := by
  haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b.toBasis
  rw [(affineIndependent_tetraVtx b).affineSpan_eq_top_iff_card_eq_finrank_add_one]
  simp [hE]

/-- **The regular tetrahedron inscribed in the cube**, as an affine basis: every result about
`Simplex.body` therefore applies to it. -/
noncomputable def regularTetra (hE : Module.finrank ℝ E = 3) : AffineBasis (Fin 4) ℝ E where
  toFun := tetraVtx b
  ind' := affineIndependent_tetraVtx b
  tot' := affineSpan_tetraVtx b hE

@[simp] lemma regularTetra_apply (hE : Module.finrank ℝ E = 3) (k : Fin 4) :
    regularTetra b hE k = tetraVtx b k := rfl

/-- **A regular tetrahedron is Platonic `{3,3}` on the Euler–Poincaré spine.**

The solid is the hull of four *pairwise equidistant* points (squared distance `8`, all on a
sphere of squared radius `3`); its geometric face counts are `4, 6, 4`, its Euler relation
comes from `Euler_Poincare_full`, and `(3,3)` is one of the five Schläfli pairs. -/
theorem regularTetra_platonic (hE : Module.finrank ℝ E = 3) :
    (∀ k l : Fin 4, k ≠ l →
        ‖regularTetra b hE k - regularTetra b hE l‖ ^ 2 = 8) ∧
      (∀ k : Fin 4, ‖regularTetra b hE k‖ ^ 2 = 3) ∧
      (Platonic.facesOfDim (Simplex.body (regularTetra b hE)) 0).ncard = 4 ∧
      (Platonic.facesOfDim (Simplex.body (regularTetra b hE)) 1).ncard = 6 ∧
      (Platonic.facesOfDim (Simplex.body (regularTetra b hE)) 2).ncard = 4 ∧
      ((Platonic.facesOfDim (Simplex.body (regularTetra b hE)) 0).ncard : ℤ)
          - (Platonic.facesOfDim (Simplex.body (regularTetra b hE)) 1).ncard
          + (Platonic.facesOfDim (Simplex.body (regularTetra b hE)) 2).ncard = 2 ∧
      ((3 : ℕ), (3 : ℕ)) ∈ Platonic.schlafliPairs := by
  haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b.toBasis
  haveI : Nonempty E := ⟨0⟩
  obtain ⟨hV, hE6, hF⟩ := Simplex.tetrahedron_face_counts (regularTetra b hE)
  obtain ⟨-, -, -, hpair⟩ := Simplex.tetrahedron_platonic (regularTetra b hE) hE
  exact ⟨fun k l h => tetraVtx_dist_sq b h, fun k => norm_sq_tetraVtx b k, hV, hE6, hF,
    Simplex.tetrahedron_euler_relation (regularTetra b hE) hE, hpair⟩

end Cube

end EulersGem
