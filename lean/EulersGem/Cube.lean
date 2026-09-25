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

/-! ## Every subcube is a face -/

lemma sgn_injective {s t : Bool} (h : sgn s = sgn t) : s = t := by
  cases s <;> cases t
  · rfl
  · exfalso; rw [sgn_false, sgn_true] at h; norm_num at h
  · exfalso; rw [sgn_true, sgn_false] at h; norm_num at h
  · rfl

/-- The supporting functional of `c` evaluated at a corner. -/
lemma inner_normal_corner (c : Fin n → Option Bool) (σ : Fin n → Bool) :
    ⟪normal b c, corner b σ⟫ = ∑ i, coeff c i * sgn (σ i) := by
  rw [normal_eq_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, inner_b_corner]

lemma coeff_mul_sgn_le_one (c : Fin n → Option Bool) (σ : Fin n → Bool) (i : Fin n)
    (hi : i ∈ supp c) : coeff c i * sgn (σ i) ≤ 1 := by
  rcases hc : c i with _ | s
  · exact absurd (mem_supp.mp hi) (by rw [hc]; simp)
  · rw [coeff_some hc]
    exact sgn_mul_sgn_le_one _ _

lemma sum_coeff_mul_sgn_eq_supp (c : Fin n → Option Bool) (σ : Fin n → Bool) :
    ∑ i, coeff c i * sgn (σ i) = ∑ i ∈ supp c, coeff c i * sgn (σ i) :=
  (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
    rw [coeff_eq_zero_of_notMem_supp hi, zero_mul]).symm

lemma inner_normal_corner_le (c : Fin n → Option Bool) (σ : Fin n → Bool) :
    ⟪normal b c, corner b σ⟫ ≤ ((supp c).card : ℝ) := by
  rw [inner_normal_corner, sum_coeff_mul_sgn_eq_supp]
  calc ∑ i ∈ supp c, coeff c i * sgn (σ i) ≤ ∑ _i ∈ supp c, (1 : ℝ) :=
        Finset.sum_le_sum fun i hi => coeff_mul_sgn_le_one c σ i hi
    _ = ((supp c).card : ℝ) := by simp

/-- The functional `normal b c` attains its bound `|supp c|` exactly at the corners
selected by `c`. -/
lemma inner_normal_corner_eq_iff (c : Fin n → Option Bool) (σ : Fin n → Bool) :
    ⟪normal b c, corner b σ⟫ = ((supp c).card : ℝ) ↔ Agrees c σ := by
  rw [inner_normal_corner, sum_coeff_mul_sgn_eq_supp]
  constructor
  · intro heq i s hs
    by_contra hne
    have hi : i ∈ supp c := mem_supp.mpr (by rw [hs]; rfl)
    have hterm : coeff c i * sgn (σ i) < 1 := by
      rw [coeff_some hs, sgn_mul_sgn_of_ne (fun h => hne h.symm)]
      norm_num
    have hstrict : ∑ j ∈ supp c, coeff c j * sgn (σ j) < ∑ _j ∈ supp c, (1 : ℝ) :=
      Finset.sum_lt_sum (fun j hj => coeff_mul_sgn_le_one c σ j hj) ⟨i, hi, hterm⟩
    rw [heq] at hstrict
    simp at hstrict
  · intro hagree
    have hterm : ∀ i ∈ supp c, coeff c i * sgn (σ i) = 1 := by
      intro i hi
      rcases hc : c i with _ | s
      · exact absurd (mem_supp.mp hi) (by rw [hc]; simp)
      · rw [coeff_some hc, hagree i s hc]
        exact sgn_mul_self _
    rw [Finset.sum_congr rfl hterm]
    simp

lemma argmax_eq_image_cornerIdx (c : Fin n → Option Bool) :
    {v ∈ Set.range (corner b) | ⟪normal b c, v⟫ = ((supp c).card : ℝ)}
      = corner b '' ↑(cornerIdx c) := by
  ext y
  constructor
  · rintro ⟨⟨σ, rfl⟩, hσ⟩
    exact ⟨σ, Finset.mem_coe.mpr (mem_cornerIdx.mpr
      ((inner_normal_corner_eq_iff b c σ).mp hσ)), rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, rfl⟩, (inner_normal_corner_eq_iff b c σ).mpr
      (mem_cornerIdx.mp (Finset.mem_coe.mp hσ))⟩

/-- **Every subcube is a face of the cube**, cut out by the supporting hyperplane of `c`. -/
theorem isFaceOf_face (c : Fin n → Option Bool) : IsFaceOf (body b) (face b c) := by
  have h := isFaceOf_convexHull_argmax (V := Set.range (corner b)) (a := normal b c)
    (c := ((supp c).card : ℝ))
    (fun v hv => by
      obtain ⟨σ, rfl⟩ := hv
      exact inner_normal_corner_le b c σ)
  rw [argmax_eq_image_cornerIdx b c] at h
  exact h

/-! ## Coordinates are constant on a face -/

/-- On a face, the coordinates fixed by `c` take the prescribed values. -/
lemma inner_b_eq_of_mem_face {c : Fin n → Option Bool} {i : Fin n} {s : Bool}
    (hc : c i = some s) {x : E} (hx : x ∈ face b c) : ⟪b i, x⟫ = sgn s := by
  refine inner_eq_of_mem_convexHull (fun v hv => ?_) x hx
  obtain ⟨σ, hσ, rfl⟩ := hv
  rw [inner_b_corner, mem_cornerIdx.mp (Finset.mem_coe.mp hσ) i s hc]

lemma corner_mem_face_iff {c : Fin n → Option Bool} {σ : Fin n → Bool} :
    corner b σ ∈ face b c ↔ σ ∈ cornerIdx c := by
  refine ⟨fun h => mem_cornerIdx.mpr fun i s hs => ?_,
    fun h => subset_convexHull ℝ _ ⟨σ, Finset.mem_coe.mpr h, rfl⟩⟩
  have h1 := inner_b_eq_of_mem_face b hs h
  rw [inner_b_corner] at h1
  exact sgn_injective h1

lemma face_subset_iff {c c' : Fin n → Option Bool} :
    face b c ⊆ face b c' ↔ cornerIdx c ⊆ cornerIdx c' := by
  refine ⟨fun h σ hσ => ?_, fun h => convexHull_mono (Set.image_mono (by exact_mod_cast h))⟩
  exact (corner_mem_face_iff b).mp (h ((corner_mem_face_iff b).mpr hσ))

/-! ## The indexing is injective -/

lemma update_mem_cornerIdx {c : Fin n → Option Bool} {i : Fin n} (hc : c i = none)
    (σ : Fin n → Bool) (hσ : σ ∈ cornerIdx c) (v : Bool) :
    Function.update σ i v ∈ cornerIdx c := by
  refine mem_cornerIdx.mpr fun j s hs => ?_
  by_cases hij : j = i
  · rw [hij, hc] at hs; exact absurd hs (by simp)
  · rw [Function.update_of_ne hij]
    exact mem_cornerIdx.mp hσ j s hs

lemma eq_some_of_forall_eq {c : Fin n → Option Bool} {i : Fin n} {s : Bool}
    (h : ∀ σ ∈ cornerIdx c, σ i = s) : c i = some s := by
  rcases hc : c i with _ | s'
  · exfalso
    have h1 := h _ (update_mem_cornerIdx hc (pick c) (pick_mem_cornerIdx c) (!s))
    rw [Function.update_self] at h1
    exact (Bool.not_ne_self s) h1
  · have h2 := h _ (pick_mem_cornerIdx c)
    have hps : pick c i = s' := by simp [pick, hc]
    rw [hps] at h2
    rw [h2]

lemma cornerIdx_injective : Function.Injective (cornerIdx (n := n)) := by
  intro c c' h
  funext i
  refine Option.ext fun s => ?_
  constructor
  · intro hs
    refine eq_some_of_forall_eq (c := c') fun σ hσ => ?_
    rw [← h] at hσ
    exact mem_cornerIdx.mp hσ i s hs
  · intro hs
    refine eq_some_of_forall_eq (c := c) fun σ hσ => ?_
    rw [h] at hσ
    exact mem_cornerIdx.mp hσ i s hs

lemma face_injective : Function.Injective (face b) := fun c c' h =>
  cornerIdx_injective (Finset.Subset.antisymm ((face_subset_iff b).mp h.subset)
    ((face_subset_iff b).mp h.symm.subset))


/-! ## Dimension of a face: `n` minus the number of fixed coordinates -/

/-- Coordinates left free by `c`. -/
def freeIdx (c : Fin n → Option Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => ¬ ((c i).isSome = true)

lemma mem_freeIdx {c : Fin n → Option Bool} {i : Fin n} :
    i ∈ freeIdx c ↔ c i = none := by
  simp [freeIdx, Option.isSome_iff_exists, Option.eq_none_iff_forall_ne_some]

lemma card_freeIdx_add_card_supp (c : Fin n → Option Bool) :
    (freeIdx c).card + (supp c).card = n := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i => ((c i).isSome = true))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  rw [supp, freeIdx]
  omega

/-- Changing one coordinate of a corner moves it along that basis vector. -/
lemma corner_sub_corner_update (σ : Fin n → Bool) (j : Fin n) (v : Bool) :
    corner b σ - corner b (Function.update σ j v) = (sgn (σ j) - sgn v) • b j := by
  have h : ∀ i : Fin n, sgn (σ i) • b i - sgn (Function.update σ j v i) • b i
      = if i = j then (sgn (σ j) - sgn v) • b j else 0 := by
    intro i
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self, if_pos rfl, sub_smul]
    · rw [Function.update_of_ne hij, if_neg hij, sub_self]
  calc corner b σ - corner b (Function.update σ j v)
      = ∑ i, (sgn (σ i) • b i - sgn (Function.update σ j v i) • b i) := by
        rw [corner, corner, Finset.sum_sub_distrib]
    _ = ∑ i, (if i = j then (sgn (σ j) - sgn v) • b j else 0) :=
        Finset.sum_congr rfl fun i _ => h i
    _ = (sgn (σ j) - sgn v) • b j := by simp

lemma sgn_sub_sgn_not (s : Bool) : sgn s - sgn (!s) = 2 * sgn s := by
  cases s <;> norm_num [sgn]

/-- A free basis direction lies in the direction of the face. -/
lemma b_mem_vectorSpan_face {c : Fin n → Option Bool} {j : Fin n} (hj : c j = none) :
    b j ∈ vectorSpan ℝ (face b c) := by
  have h1 : corner b (pick c) ∈ face b c :=
    (corner_mem_face_iff b).mpr (pick_mem_cornerIdx c)
  have h2 : corner b (Function.update (pick c) j (!(pick c j))) ∈ face b c :=
    (corner_mem_face_iff b).mpr
      (update_mem_cornerIdx hj (pick c) (pick_mem_cornerIdx c) _)
  have hdiff := vsub_mem_vectorSpan ℝ h1 h2
  rw [vsub_eq_sub, corner_sub_corner_update, sgn_sub_sgn_not] at hdiff
  have hne : (2 : ℝ) * sgn (pick c j) ≠ 0 := by
    have := sgn_mul_self (pick c j)
    intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · norm_num at h
    · rw [h] at this; norm_num at this
  have := Submodule.smul_mem _ ((2 * sgn (pick c j))⁻¹) hdiff
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this

/-- Differences within a face are supported on the free coordinates. -/
lemma vectorSpan_face_le (c : Fin n → Option Bool) :
    vectorSpan ℝ (face b c) ≤ Submodule.span ℝ (b '' ↑(freeIdx c)) := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro z ⟨x, hx, y, hy, rfl⟩
  have hzero : ∀ i ∈ supp c, ⟪b i, x -ᵥ y⟫ = 0 := by
    intro i hi
    rcases hc : c i with _ | s
    · exact absurd (mem_supp.mp hi) (by rw [hc]; simp)
    · rw [vsub_eq_sub, inner_sub_right, inner_b_eq_of_mem_face b hc hx,
        inner_b_eq_of_mem_face b hc hy, sub_self]
  have hrepr : ∑ i, ⟪b i, x -ᵥ y⟫ • b i = x -ᵥ y := b.sum_repr' (x -ᵥ y)
  have hsuppOf : ∀ i : Fin n, i ∉ freeIdx c → i ∈ supp c := by
    intro i hi
    rcases hc : c i with _ | s
    · exact absurd (mem_freeIdx.mpr hc) hi
    · exact mem_supp.mpr (by rw [hc]; rfl)
  have hrestrict : ∑ i ∈ freeIdx c, ⟪b i, x -ᵥ y⟫ • b i = x -ᵥ y := by
    have hsub : ∑ i ∈ freeIdx c, ⟪b i, x -ᵥ y⟫ • b i
        = ∑ i ∈ (Finset.univ : Finset (Fin n)), ⟪b i, x -ᵥ y⟫ • b i :=
      Finset.sum_subset (f := fun i => ⟪b i, x -ᵥ y⟫ • b i) (Finset.subset_univ _)
        fun i _ hi => by rw [hzero i (hsuppOf i hi), zero_smul]
    rw [hsub, hrepr]
  show (x -ᵥ y) ∈ Submodule.span ℝ (b '' ↑(freeIdx c))
  rw [← hrestrict]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩

lemma vectorSpan_face_eq (c : Fin n → Option Bool) :
    vectorSpan ℝ (face b c) = Submodule.span ℝ (b '' ↑(freeIdx c)) := by
  refine le_antisymm (vectorSpan_face_le b c) ?_
  rw [Submodule.span_le]
  rintro y ⟨j, hj, rfl⟩
  exact b_mem_vectorSpan_face b (mem_freeIdx.mp (Finset.mem_coe.mp hj))

lemma finrank_span_free (c : Fin n → Option Bool) :
    Module.finrank ℝ (Submodule.span ℝ (b '' ↑(freeIdx c))) = (freeIdx c).card := by
  classical
  have hlin : LinearIndependent ℝ fun j : (↑(freeIdx c) : Set (Fin n)) => b (j : Fin n) :=
    (b.orthonormal.comp _ Subtype.val_injective).linearIndependent
  have hrange : Set.range (fun j : (↑(freeIdx c) : Set (Fin n)) => b (j : Fin n))
      = b '' ↑(freeIdx c) := by
    rw [Set.image_eq_range]
  have := finrank_span_eq_card hlin
  rw [hrange] at this
  rw [this]
  simp

/-- **`affDim (face b c) = n − |supp c|`**: fixing `k` coordinates drops the dimension
by `k`. -/
theorem affDim_face (c : Fin n → Option Bool) :
    affDim (face b c) = (n : ℤ) - (supp c).card := by
  rw [affDim_eq_finrank_direction (face_nonempty b c), direction_affineSpan,
    vectorSpan_face_eq b c, finrank_span_free b c]
  have h := card_freeIdx_add_card_supp c
  omega


end Cube
end EulersGem
