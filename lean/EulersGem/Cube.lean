/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.Octahedron

/-!
# The cube (box) as a geometric solid

Given an orthonormal basis `b : OrthonormalBasis (Fin n) ℝ E`, the **cube**
`body b = convexHull ℝ {∑ ±b i}` is the convex hull of the `2 ^ n` sign vectors. For `n = 3`
it is a geometric cube.

Unlike the simplex and the cross-polytope, the cube's face lattice is a *subcube* lattice:
faces correspond to partial sign assignments `c : Fin n → Option Bool`, a face being the set
of corners that agree with `c` on its support. The hard direction — every face is a subcube —
comes from the **coordinate-transfer** lemma `mem_of_transfer`: if two corners lie in a face,
so does the corner obtained by transferring one coordinate between them, because the two
midpoints coincide.

* `body_eq_sum_segment` — the cube is the Minkowski sum `∑ᵢ [-bᵢ, bᵢ]`, which makes the
  H-representation easy in both directions;
* `body_eq_iInter_closedHalfspace` — the H-representation needed by `Euler_Poincare_full`;
* `isFaceOf_face` / `eq_face_of_isFaceOf` — the face lattice;
* `affDim_face` — a face with `k` fixed coordinates has dimension `n − k`.
-/

open Set
open scoped RealInnerProductSpace Pointwise

namespace EulersGem
namespace Cube

open Octahedron (sgn sgn_true sgn_false sgn_mul_self sgn_mul_sgn_le_one sgn_mul_sgn_eq_one_iff
  sgn_mul_sgn_of_ne sgn_not inner_b_b normal coeff coeff_none coeff_some normal_eq_sum)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ}
variable (b : OrthonormalBasis (Fin n) ℝ E)

/-! ## Corners and body -/

/-- Corner of the cube for a total sign vector. -/
noncomputable def corner (σ : Fin n → Bool) : E := ∑ i, sgn (σ i) • b i

/-- The cube: convex hull of the `2 ^ n` corners. -/
noncomputable def body : Set E := convexHull ℝ (Set.range (corner b))

lemma isPolytope_body : IsPolytope (body b) :=
  ⟨Set.range (corner b), Set.finite_range _, rfl⟩

lemma convex_body : Convex ℝ (body b) := convex_convexHull ℝ _

lemma corner_mem_body (σ : Fin n → Bool) : corner b σ ∈ body b :=
  subset_convexHull ℝ _ ⟨σ, rfl⟩

/-- The `j`-th coordinate of a corner is its `j`-th sign. -/
lemma inner_b_corner (j : Fin n) (σ : Fin n → Bool) : ⟪b j, corner b σ⟫ = sgn (σ j) := by
  rw [corner, inner_sum]
  have h : ∀ i : Fin n, ⟪b j, sgn (σ i) • b i⟫ = if i = j then sgn (σ i) else 0 := by
    intro i
    rw [real_inner_smul_right, inner_b_b]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  rw [Finset.sum_congr rfl fun i _ => h i,
    Finset.sum_ite_eq' Finset.univ j fun i => sgn (σ i)]
  simp

/-! ## Minkowski-sum description and the H-representation -/

lemma range_corner_eq_sum :
    Set.range (corner b) = ∑ i : Fin n, ({-b i, b i} : Set E) := by
  classical
  ext y
  rw [Set.mem_fintype_sum]
  constructor
  · rintro ⟨σ, rfl⟩
    refine ⟨fun i => sgn (σ i) • b i, fun i => ?_, rfl⟩
    cases hσ : σ i
    · simp [hσ, sgn]
    · simp [hσ, sgn]
  · rintro ⟨g, hg, rfl⟩
    refine ⟨fun i => decide (g i = b i), ?_⟩
    rw [corner]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : g i = b i
    · simp [hi, sgn]
    · have hneg : g i = -b i := by
        rcases hg i with h | h
        · exact h
        · exact absurd h hi
      rw [decide_eq_false hi, hneg, sgn_false]
      module

/-- **The cube is the Minkowski sum of the segments `[-bᵢ, bᵢ]`.** -/
theorem body_eq_sum_segment :
    body b = ∑ i : Fin n, segment ℝ (-b i) (b i) := by
  rw [body, range_corner_eq_sum, convexHull_sum]
  exact Finset.sum_congr rfl fun i _ => convexHull_pair _ _

/-- Corners have coordinates `±1`, hence so does everything in the cube, in absolute value. -/
lemma abs_inner_le_one_of_mem_body {x : E} (hx : x ∈ body b) (j : Fin n) :
    |⟪b j, x⟫| ≤ 1 := by
  rw [abs_le]
  constructor
  · have h : ⟪-b j, x⟫ ≤ 1 :=
      inner_le_of_mem_convexHull (fun v hv => by
        obtain ⟨σ, rfl⟩ := hv
        rw [inner_neg_left, inner_b_corner]
        cases σ j <;> norm_num [sgn]) x hx
    rw [inner_neg_left] at h
    linarith
  · exact inner_le_of_mem_convexHull (fun v hv => by
      obtain ⟨σ, rfl⟩ := hv
      rw [inner_b_corner]
      exact Octahedron.sgn_le_one _) x hx

/-- Conversely, coordinates bounded by `1` put a point in the cube: decompose it
coordinatewise along the segments. -/
lemma mem_body_of_abs_inner_le {x : E} (hx : ∀ j, |⟪b j, x⟫| ≤ 1) : x ∈ body b := by
  rw [body_eq_sum_segment, Set.mem_fintype_sum]
  refine ⟨fun i => b.repr x i • b i, fun i => ?_, b.sum_repr x⟩
  have hri : |b.repr x i| ≤ 1 := by
    rw [b.repr_apply_apply]
    exact hx i
  rw [abs_le] at hri
  refine ⟨(1 - b.repr x i) / 2, (1 + b.repr x i) / 2, by linarith [hri.1, hri.2],
    by linarith [hri.1, hri.2], by ring, ?_⟩
  dsimp only
  module

/-- The `2n` supporting hyperplanes of the cube. -/
noncomputable def hyperplanes : Set (Hyperplane E) :=
  Set.range fun p : Fin n × Bool => (sgn p.2 • b p.1, (1 : ℝ))

lemma hyperplanes_finite : (hyperplanes b).Finite := Set.finite_range _

/-- **H-representation of the cube.** -/
theorem body_eq_iInter_closedHalfspace :
    body b = ⋂ h ∈ hyperplanes b, closedHalfspace h.1 h.2 := by
  ext x
  simp only [Set.mem_iInter, hyperplanes, Set.mem_range]
  constructor
  · intro hx h hh
    obtain ⟨⟨j, s⟩, rfl⟩ := hh
    have habs := abs_inner_le_one_of_mem_body b hx j
    rw [abs_le] at habs
    simp only [closedHalfspace, Set.mem_setOf_eq, real_inner_smul_left]
    cases s
    · simp only [sgn_false]
      linarith [habs.1]
    · simp only [sgn_true]
      linarith [habs.2]
  · intro hx
    refine mem_body_of_abs_inner_le b fun j => ?_
    have h1 := hx _ ⟨(j, true), rfl⟩
    have h2 := hx _ ⟨(j, false), rfl⟩
    simp only [closedHalfspace, Set.mem_setOf_eq, real_inner_smul_left, sgn_true,
      sgn_false] at h1 h2
    rw [abs_le]
    constructor <;> linarith

/-! ## Full dimension -/

lemma zero_mem_body : (0 : E) ∈ body b := by
  refine mem_body_of_abs_inner_le b fun j => ?_
  simp

lemma b_mem_body (i : Fin n) : b i ∈ body b := by
  refine mem_body_of_abs_inner_le b fun j => ?_
  rw [inner_b_b]
  by_cases h : j = i <;> simp [h]

lemma affDim_body [FiniteDimensional ℝ E] :
    affDim (body b) = (Module.finrank ℝ E : ℤ) := by
  have hne : (body b).Nonempty := ⟨0, zero_mem_body b⟩
  rw [affDim_eq_finrank_direction hne, direction_affineSpan]
  have hspan : Submodule.span ℝ (Set.range (b : Fin n → E)) ≤ vectorSpan ℝ (body b) := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨i, rfl⟩
    have := vsub_mem_vectorSpan ℝ (b_mem_body b i) (zero_mem_body b)
    simpa using this
  have htop : vectorSpan ℝ (body b) = ⊤ := by
    refine top_le_iff.mp ?_
    calc (⊤ : Submodule ℝ E) = Submodule.span ℝ (Set.range (b : Fin n → E)) := by
          rw [← OrthonormalBasis.coe_toBasis b, b.toBasis.span_eq]
      _ ≤ vectorSpan ℝ (body b) := hspan
  rw [htop, finrank_top]

/-! ## Faces: corners agreeing with a partial sign assignment -/

/-- `σ` agrees with the partial sign assignment `c`. -/
def Agrees (c : Fin n → Option Bool) (σ : Fin n → Bool) : Prop :=
  ∀ i s, c i = some s → σ i = s

instance (c : Fin n → Option Bool) (σ : Fin n → Bool) : Decidable (Agrees c σ) := by
  unfold Agrees; infer_instance

/-- Corners selected by `c`: those agreeing with it on its support. -/
def cornerIdx (c : Fin n → Option Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun σ => Agrees c σ

@[simp] lemma mem_cornerIdx {c : Fin n → Option Bool} {σ : Fin n → Bool} :
    σ ∈ cornerIdx c ↔ Agrees c σ := by simp [cornerIdx]

/-- Coordinates fixed by `c`. -/
def supp (c : Fin n → Option Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => (c i).isSome

@[simp] lemma mem_supp {c : Fin n → Option Bool} {i : Fin n} :
    i ∈ supp c ↔ (c i).isSome := by simp [supp]

lemma coeff_eq_zero_of_notMem_supp {c : Fin n → Option Bool} {i : Fin n} (h : i ∉ supp c) :
    coeff c i = 0 := by
  have : c i = none := by
    rcases hc : c i with _ | s
    · rfl
    · exact absurd (mem_supp.mpr (by rw [hc]; rfl)) h
  exact coeff_none this

/-- The face of the cube spanned by the corners `c` selects. -/
noncomputable def face (c : Fin n → Option Bool) : Set E :=
  convexHull ℝ (corner b '' ↑(cornerIdx c))

/-- The canonical corner selected by `c`. -/
def pick (c : Fin n → Option Bool) : Fin n → Bool := fun i => (c i).getD true

lemma pick_mem_cornerIdx (c : Fin n → Option Bool) : pick c ∈ cornerIdx c := by
  refine mem_cornerIdx.mpr fun i s hs => ?_
  simp [pick, hs]

lemma face_nonempty (c : Fin n → Option Bool) : (face b c).Nonempty :=
  ⟨corner b (pick c), subset_convexHull ℝ _
    ⟨pick c, Finset.mem_coe.mpr (pick_mem_cornerIdx c), rfl⟩⟩

lemma face_subset_body (c : Fin n → Option Bool) : face b c ⊆ body b :=
  convexHull_mono (by rintro y ⟨σ, -, rfl⟩; exact ⟨σ, rfl⟩)

end Cube
end EulersGem
