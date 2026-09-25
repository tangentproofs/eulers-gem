/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.PolytopeFaces
import EulersGem.Embed
import EulersGem.PlatonicOfEuler
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The cross-polytope (octahedron) as a geometric solid

Given an orthonormal basis `b : OrthonormalBasis (Fin n) ℝ E`, the **cross-polytope**
`body b = convexHull ℝ {±b i}` is a geometric polytope with `2n` vertices. For `n = 3` it is
a geometric octahedron.

This file supplies, for the Euler–Poincaré spine:

* `body_eq_iInter_closedHalfspace` — the H-representation: `body b` is the intersection of
  the `2 ^ n` halfspaces `⟪∑ ± b i, x⟫ ≤ 1` (needed by `Euler_Poincare_full`);
* `neg_mem_body` — the cross-polytope is symmetric;
* the face lattice (`Octahedron.face`), indexed by partial sign assignments
  `c : Fin n → Option Bool`.

Everything is proved; nothing about the octahedron is postulated.
-/

open Set Finset
open scoped RealInnerProductSpace

namespace EulersGem
namespace Octahedron

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ}

/-! ## Signs -/

/-- `±1` from a Boolean sign. -/
def sgn (s : Bool) : ℝ := if s then 1 else -1

@[simp] lemma sgn_true : sgn true = 1 := rfl
@[simp] lemma sgn_false : sgn false = -1 := rfl

lemma sgn_mul_self (s : Bool) : sgn s * sgn s = 1 := by cases s <;> norm_num [sgn]

lemma sgn_le_one (s : Bool) : sgn s ≤ 1 := by cases s <;> norm_num [sgn]

lemma neg_one_le_sgn (s : Bool) : (-1 : ℝ) ≤ sgn s := by cases s <;> norm_num [sgn]

lemma sgn_mul_sgn_le_one (s t : Bool) : sgn s * sgn t ≤ 1 := by
  cases s <;> cases t <;> norm_num [sgn]

lemma sgn_mul_sgn_eq_one_iff (s t : Bool) : sgn s * sgn t = 1 ↔ s = t := by
  cases s <;> cases t <;> norm_num [sgn]

lemma sgn_mul_sgn_of_ne {s t : Bool} (h : s ≠ t) : sgn s * sgn t = -1 := by
  cases s <;> cases t <;> simp_all [sgn]

lemma abs_eq_sgn_mul (x : ℝ) : |x| = sgn (decide (0 ≤ x)) * x := by
  rcases le_or_gt 0 x with h | h
  · simp [sgn, h, abs_of_nonneg h]
  · simp [sgn, not_le.mpr h, abs_of_neg h]

/-! ## Vertices and body -/

variable (b : OrthonormalBasis (Fin n) ℝ E)

/-- Vertex `± b i` of the cross-polytope, indexed by a coordinate and a sign. -/
noncomputable def vtx (p : Fin n × Bool) : E := sgn p.2 • b p.1

/-- The cross-polytope: convex hull of `±b i`. For `n = 3`, a geometric octahedron. -/
noncomputable def body : Set E := convexHull ℝ (Set.range (vtx b))

lemma isPolytope_body : IsPolytope (body b) :=
  ⟨Set.range (vtx b), Set.finite_range _, rfl⟩

lemma convex_body : Convex ℝ (body b) := convex_convexHull ℝ _

lemma vtx_mem_body (p : Fin n × Bool) : vtx b p ∈ body b :=
  subset_convexHull ℝ _ ⟨p, rfl⟩

lemma inner_b_b (i j : Fin n) : ⟪b i, b j⟫ = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp b.orthonormal i j

/-- Inner products of vertices: `±1` on equal coordinates, `0` otherwise. -/
lemma inner_vtx_vtx (p q : Fin n × Bool) :
    ⟪vtx b p, vtx b q⟫ = sgn p.2 * sgn q.2 * (if p.1 = q.1 then 1 else 0) := by
  rw [vtx, vtx, real_inner_smul_left, real_inner_smul_right, inner_b_b]
  ring

lemma inner_vtx_self (p : Fin n × Bool) : ⟪vtx b p, vtx b p⟫ = 1 := by
  rw [inner_vtx_vtx]
  simp [sgn_mul_self]

/-! ## Supporting functionals from partial sign assignments -/

/-- The supporting normal of a partial sign assignment `c`: `∑ᵢ (sign of c i) • b i`, with
coordinates outside the support contributing `0`. -/
noncomputable def normal (c : Fin n → Option Bool) : E :=
  ∑ i, ((c i).elim 0 sgn) • b i

/-- The coefficient of the `i`-th coordinate in `normal b c`. -/
def coeff (c : Fin n → Option Bool) (i : Fin n) : ℝ := (c i).elim 0 sgn

@[simp] lemma coeff_none {c : Fin n → Option Bool} {i : Fin n} (h : c i = none) :
    coeff c i = 0 := by simp [coeff, h]

@[simp] lemma coeff_some {c : Fin n → Option Bool} {i : Fin n} {s : Bool} (h : c i = some s) :
    coeff c i = sgn s := by simp [coeff, h]

lemma normal_eq_sum (c : Fin n → Option Bool) : normal b c = ∑ i, coeff c i • b i := rfl

/-- The supporting functional evaluated at a vertex. -/
lemma inner_normal_vtx (c : Fin n → Option Bool) (q : Fin n × Bool) :
    ⟪normal b c, vtx b q⟫ = sgn q.2 * coeff c q.1 := by
  rw [normal_eq_sum, vtx, real_inner_smul_right, sum_inner]
  have h : ∀ i : Fin n, ⟪coeff c i • b i, b q.1⟫ = if i = q.1 then coeff c i else 0 := by
    intro i
    rw [real_inner_smul_left, inner_b_b]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => h i,
    Finset.sum_ite_eq' Finset.univ q.1 fun i => coeff c i]
  simp

/-- On a vertex, the supporting functional of a *total* sign assignment is at most `1`. -/
lemma inner_normal_vtx_le_one (σ : Fin n → Bool) (q : Fin n × Bool) :
    ⟪normal b (fun i => some (σ i)), vtx b q⟫ ≤ 1 := by
  rw [inner_normal_vtx, coeff_some rfl]
  exact sgn_mul_sgn_le_one _ _

/-- The supporting functional of a total sign assignment, evaluated anywhere, is the signed
sum of coordinates. -/
lemma inner_normal_full (σ : Fin n → Bool) (x : E) :
    ⟪normal b (fun i => some (σ i)), x⟫ = ∑ i, sgn (σ i) * b.repr x i := by
  rw [normal_eq_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, coeff_some rfl, b.repr_apply_apply]

/-! ## H-representation -/

/-- The `2 ^ n` supporting hyperplanes of the cross-polytope. -/
noncomputable def hyperplanes : Set (Hyperplane E) :=
  Set.range fun σ : Fin n → Bool => (normal b (fun i => some (σ i)), (1 : ℝ))

lemma hyperplanes_finite : (hyperplanes b).Finite := Set.finite_range _

lemma inner_le_one_of_mem_body {x : E} (hx : x ∈ body b) (σ : Fin n → Bool) :
    ⟪normal b (fun i => some (σ i)), x⟫ ≤ 1 :=
  inner_le_of_mem_convexHull (fun v hv => by
    obtain ⟨q, rfl⟩ := hv
    exact inner_normal_vtx_le_one b σ q) x hx

/-- The `ℓ¹` norm of the coordinates is at most `1` on the cross-polytope's H-region. -/
lemma sum_abs_repr_le_one {x : E}
    (hx : ∀ σ : Fin n → Bool, ⟪normal b (fun i => some (σ i)), x⟫ ≤ 1) :
    ∑ i, |b.repr x i| ≤ 1 := by
  have h := hx fun i => decide (0 ≤ b.repr x i)
  rw [inner_normal_full] at h
  calc ∑ i, |b.repr x i|
      = ∑ i, sgn (decide (0 ≤ b.repr x i)) * b.repr x i :=
        Finset.sum_congr rfl fun i _ => abs_eq_sgn_mul _
    _ ≤ 1 := h

/-- **The H-region is contained in the cross-polytope.** The padding trick: a point with
`∑ |rᵢ| ≤ 1` is a convex combination of vertices, the slack being split evenly between
`+b i₀` and `-b i₀` (which cancel). -/
lemma mem_body_of_forall_inner_le (hn : 0 < n) {x : E}
    (hx : ∀ σ : Fin n → Bool, ⟪normal b (fun i => some (σ i)), x⟫ ≤ 1) :
    x ∈ body b := by
  classical
  set r : Fin n → ℝ := fun i => b.repr x i with hr
  set S : ℝ := ∑ i, |r i| with hS
  have hS1 : S ≤ 1 := sum_abs_repr_le_one b hx
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  set w : Fin n × Bool → ℝ := fun p =>
    (if p.2 = decide (0 ≤ r p.1) then |r p.1| else 0)
      + (if p.1 = i₀ then (1 - S) / 2 else 0) with hw
  have hw0 : ∀ p ∈ (Finset.univ : Finset (Fin n × Bool)), 0 ≤ w p := by
    intro p _
    have h1 : 0 ≤ (if p.2 = decide (0 ≤ r p.1) then |r p.1| else 0) := by
      split_ifs
      · exact abs_nonneg _
      · exact le_refl 0
    have h2 : 0 ≤ (if p.1 = i₀ then (1 - S) / 2 else 0) := by
      split_ifs
      · linarith
      · exact le_refl 0
    simp only [hw]
    linarith
  -- the two signs of one coordinate: weights add to `|rᵢ|` plus the slack at `i₀`
  have hsumBool : ∀ i : Fin n, ∑ s : Bool, w (i, s)
      = |r i| + (if i = i₀ then 1 - S else 0) := by
    intro i
    have key : w (i, true) + w (i, false)
        = ((if (true : Bool) = decide (0 ≤ r i) then |r i| else 0)
            + (if (false : Bool) = decide (0 ≤ r i) then |r i| else 0))
          + 2 * (if i = i₀ then (1 - S) / 2 else 0) := by
      simp only [hw]; ring
    have hpair : (if (true : Bool) = decide (0 ≤ r i) then |r i| else 0)
        + (if (false : Bool) = decide (0 ≤ r i) then |r i| else 0) = |r i| := by
      rcases le_or_gt 0 (r i) with hle | hlt
      · rw [decide_eq_true hle]; norm_num
      · rw [decide_eq_false (not_le.mpr hlt)]; norm_num
    have hslack : 2 * (if i = i₀ then (1 - S) / 2 else 0)
        = (if i = i₀ then 1 - S else 0) := by
      split_ifs <;> ring
    rw [Fintype.sum_bool, key, hpair, hslack]
  -- the two signs of one coordinate: vertices combine to `rᵢ • bᵢ` (slack cancels)
  have hsumBoolVtx : ∀ i : Fin n, ∑ s : Bool, w (i, s) • vtx b (i, s) = r i • b i := by
    intro i
    rw [Fintype.sum_bool]
    simp only [vtx, smul_smul]
    rw [← add_smul]
    congr 1
    have key : w (i, true) * sgn true + w (i, false) * sgn false
        = (if (true : Bool) = decide (0 ≤ r i) then |r i| else 0)
          - (if (false : Bool) = decide (0 ≤ r i) then |r i| else 0) := by
      simp only [hw, sgn_true, sgn_false]; ring
    rw [key]
    rcases le_or_gt 0 (r i) with hle | hlt
    · rw [decide_eq_true hle, abs_of_nonneg hle]; norm_num
    · rw [decide_eq_false (not_le.mpr hlt), abs_of_neg hlt]; norm_num
  have hw1 : ∑ p : Fin n × Bool, w p = 1 := by
    have hstep : ∑ i : Fin n, (∑ s : Bool, w (i, s))
        = ∑ i : Fin n, (|r i| + (if i = i₀ then 1 - S else 0)) :=
      Finset.sum_congr rfl fun i _ => hsumBool i
    rw [Fintype.sum_prod_type, hstep, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ i₀ fun _ => 1 - S]
    simp [← hS]
  have hcomb : ∑ p : Fin n × Bool, w p • vtx b p = x := by
    have hstep : ∑ i : Fin n, (∑ s : Bool, w (i, s) • vtx b (i, s))
        = ∑ i : Fin n, r i • b i :=
      Finset.sum_congr rfl fun i _ => hsumBoolVtx i
    rw [Fintype.sum_prod_type, hstep]
    exact b.sum_repr x
  rw [body, ← hcomb]
  exact (convex_convexHull ℝ _).sum_mem hw0 hw1 fun p _ =>
    subset_convexHull ℝ _ ⟨p, rfl⟩

/-- **H-representation of the cross-polytope.** -/
theorem body_eq_iInter_closedHalfspace (hn : 0 < n) :
    body b = ⋂ h ∈ hyperplanes b, closedHalfspace h.1 h.2 := by
  ext x
  simp only [Set.mem_iInter, hyperplanes, Set.mem_range]
  constructor
  · intro hx h hh
    obtain ⟨σ, rfl⟩ := hh
    exact inner_le_one_of_mem_body b hx σ
  · intro hx
    refine mem_body_of_forall_inner_le b hn fun σ => ?_
    exact hx _ ⟨σ, rfl⟩

/-! ## Symmetry and full dimension -/

lemma sgn_not (s : Bool) : sgn (!s) = -sgn s := by cases s <;> norm_num [sgn]

lemma neg_vtx (p : Fin n × Bool) : -vtx b p = vtx b (p.1, !p.2) := by
  simp [vtx, sgn_not, neg_smul]

lemma neg_range_vtx : -Set.range (vtx b) = Set.range (vtx b) := by
  ext y
  constructor
  · rintro hy
    obtain ⟨p, hp⟩ : ∃ p, vtx b p = -y := by
      simpa [Set.mem_neg] using hy
    exact ⟨(p.1, !p.2), by rw [← neg_vtx, hp, neg_neg]⟩
  · rintro ⟨p, rfl⟩
    exact Set.mem_neg.mpr ⟨(p.1, !p.2), by rw [neg_vtx]⟩

/-- The cross-polytope is symmetric about the origin. -/
lemma neg_mem_body {x : E} (hx : x ∈ body b) : -x ∈ body b := by
  have h : -body b = body b := by
    rw [body, ← convexHull_neg, neg_range_vtx]
  rw [← h]
  exact Set.mem_neg.mpr (by simpa using hx)

lemma zero_mem_body (hn : 0 < n) : (0 : E) ∈ body b := by
  have h1 : vtx b (⟨0, hn⟩, true) ∈ body b := vtx_mem_body b _
  have h2 : vtx b (⟨0, hn⟩, false) ∈ body b := vtx_mem_body b _
  have := (convex_body b) h1 h2 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num)
  simpa [vtx, sgn, smul_smul] using this

/-- The cross-polytope is full-dimensional. -/
lemma affDim_body [FiniteDimensional ℝ E] (hn : 0 < n) :
    affDim (body b) = (Module.finrank ℝ E : ℤ) := by
  have hne : (body b).Nonempty := ⟨0, zero_mem_body b hn⟩
  rw [affDim_eq_finrank_direction hne, direction_affineSpan]
  have hspan : Submodule.span ℝ (Set.range (b : Fin n → E)) ≤ vectorSpan ℝ (body b) := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨i, rfl⟩
    have h1 : b i ∈ body b := by
      have : vtx b (i, true) = b i := by simp [vtx]
      rw [← this]; exact vtx_mem_body b _
    have h2 : (0 : E) ∈ body b := zero_mem_body b hn
    have := vsub_mem_vectorSpan ℝ h1 h2
    simpa using this
  have htop : vectorSpan ℝ (body b) = ⊤ := by
    refine top_le_iff.mp ?_
    calc (⊤ : Submodule ℝ E) = Submodule.span ℝ (Set.range (b : Fin n → E)) := by
          rw [← OrthonormalBasis.coe_toBasis b, b.toBasis.span_eq]
      _ ≤ vectorSpan ℝ (body b) := hspan
  rw [htop, finrank_top]

/-! ## The face lattice, indexed by partial sign assignments -/

/-- Vertices selected by a partial sign assignment. -/
def vtxIdx (c : Fin n → Option Bool) : Finset (Fin n × Bool) :=
  Finset.univ.filter fun p => c p.1 = some p.2

@[simp] lemma mem_vtxIdx {c : Fin n → Option Bool} {p : Fin n × Bool} :
    p ∈ vtxIdx c ↔ c p.1 = some p.2 := by simp [vtxIdx]

/-- The subface spanned by a partial sign assignment. -/
noncomputable def face (c : Fin n → Option Bool) : Set E :=
  convexHull ℝ (vtx b '' ↑(vtxIdx c))

lemma convex_face (c : Fin n → Option Bool) : Convex ℝ (face b c) := convex_convexHull ℝ _

lemma face_subset_body (c : Fin n → Option Bool) : face b c ⊆ body b :=
  convexHull_mono (by rintro y ⟨p, -, rfl⟩; exact ⟨p, rfl⟩)

/-- The supporting functional of `c` is bounded by `1` on the vertices. -/
lemma inner_normal_vtx_le_one' (c : Fin n → Option Bool) (q : Fin n × Bool) :
    ⟪normal b c, vtx b q⟫ ≤ 1 := by
  rw [inner_normal_vtx]
  cases hq : c q.1 with
  | none => simp [coeff_none hq]
  | some s =>
    rw [coeff_some hq]
    exact sgn_mul_sgn_le_one _ _

/-- The vertices on the supporting hyperplane of `c` are exactly those selected by `c`. -/
lemma argmax_eq_image_vtxIdx (c : Fin n → Option Bool) :
    {v ∈ Set.range (vtx b) | ⟪normal b c, v⟫ = 1} = vtx b '' ↑(vtxIdx c) := by
  ext y
  constructor
  · rintro ⟨⟨q, rfl⟩, hq⟩
    rw [inner_normal_vtx] at hq
    refine ⟨q, ?_, rfl⟩
    cases hc : c q.1 with
    | none => rw [coeff_none hc] at hq; norm_num at hq
    | some s =>
      rw [coeff_some hc] at hq
      have : q.2 = s := (sgn_mul_sgn_eq_one_iff _ _).mp hq
      simp [mem_vtxIdx, hc, this]
  · rintro ⟨q, hq, rfl⟩
    refine ⟨⟨q, rfl⟩, ?_⟩
    have hc : c q.1 = some q.2 := mem_vtxIdx.mp (Finset.mem_coe.mp hq)
    rw [inner_normal_vtx, coeff_some hc]
    exact (sgn_mul_sgn_eq_one_iff _ _).mpr rfl

/-- **Every subface is a face**, cut out by the supporting hyperplane of `c`. -/
theorem isFaceOf_face (c : Fin n → Option Bool) : IsFaceOf (body b) (face b c) := by
  have h := isFaceOf_convexHull_argmax (V := Set.range (vtx b)) (a := normal b c) (c := 1)
    (fun v hv => by obtain ⟨q, rfl⟩ := hv; exact inner_normal_vtx_le_one' b c q)
  rw [argmax_eq_image_vtxIdx b c] at h
  exact h

/-- A vertex lies in a subface exactly when `c` selects it. -/
lemma vtx_mem_face_iff {c : Fin n → Option Bool} {q : Fin n × Bool} :
    vtx b q ∈ face b c ↔ q ∈ vtxIdx c := by
  refine ⟨fun h => ?_, fun h => subset_convexHull ℝ _ ⟨q, Finset.mem_coe.mpr h, rfl⟩⟩
  by_contra hq
  -- `⟪vtx q, ·⟫ ≤ 0` on the subface, yet `⟪vtx q, vtx q⟫ = 1`
  have hle : ∀ v ∈ vtx b '' ↑(vtxIdx c), ⟪vtx b q, v⟫ ≤ 0 := by
    rintro v ⟨p, hp, rfl⟩
    have hcp : c p.1 = some p.2 := mem_vtxIdx.mp (Finset.mem_coe.mp hp)
    rw [inner_vtx_vtx]
    by_cases hpq : q.1 = p.1
    · have hne : q.2 ≠ p.2 := by
        intro hsign
        exact hq (mem_vtxIdx.mpr (by rw [hpq, hsign]; exact hcp))
      rw [if_pos hpq, sgn_mul_sgn_of_ne hne]
      norm_num
    · rw [if_neg hpq]
      norm_num
  have h0 : ⟪vtx b q, vtx b q⟫ ≤ 0 := inner_le_of_mem_convexHull hle _ h
  rw [inner_vtx_self] at h0
  norm_num at h0

lemma face_subset_iff {c c' : Fin n → Option Bool} :
    face b c ⊆ face b c' ↔ vtxIdx c ⊆ vtxIdx c' := by
  refine ⟨fun h p hp => ?_, fun h => convexHull_mono (Set.image_mono (by exact_mod_cast h))⟩
  exact (vtx_mem_face_iff b).mp (h ((vtx_mem_face_iff b).mpr hp))

lemma vtxIdx_injective : Function.Injective (vtxIdx (n := n)) := by
  intro c c' h
  funext i
  refine Option.ext fun s => ?_
  constructor
  · intro hs
    have hmem : (i, s) ∈ vtxIdx c := mem_vtxIdx.mpr hs
    rw [h] at hmem
    exact mem_vtxIdx.mp hmem
  · intro hs
    have hmem : (i, s) ∈ vtxIdx c' := mem_vtxIdx.mpr hs
    rw [← h] at hmem
    exact mem_vtxIdx.mp hmem

lemma face_injective : Function.Injective (face b) := fun c c' h =>
  vtxIdx_injective (Finset.Subset.antisymm ((face_subset_iff b).mp h.subset)
    ((face_subset_iff b).mp h.symm.subset))

/-! ## Dimension of a subface -/

/-- The selected vertices form an orthonormal family. -/
lemma orthonormal_vtx_vtxIdx (c : Fin n → Option Bool) :
    Orthonormal ℝ fun p : (↑(vtxIdx c) : Set (Fin n × Bool)) => vtx b p := by
  rw [orthonormal_iff_ite]
  intro p q
  rw [inner_vtx_vtx]
  by_cases hpq : p = q
  · subst hpq; simp [sgn_mul_self]
  · have hcoord : (p : Fin n × Bool).1 ≠ (q : Fin n × Bool).1 := by
      intro h
      have hp : c (p : Fin n × Bool).1 = some (p : Fin n × Bool).2 :=
        mem_vtxIdx.mp (Finset.mem_coe.mp p.2)
      have hq : c (q : Fin n × Bool).1 = some (q : Fin n × Bool).2 :=
        mem_vtxIdx.mp (Finset.mem_coe.mp q.2)
      rw [h, hq] at hp
      exact hpq (Subtype.ext (Prod.ext h (Option.some_injective _ hp).symm))
    simp [hpq, hcoord]

/-- `affDim (face b c) = |vtxIdx c| - 1`: a subface on `k` selected vertices has
dimension `k − 1` (and the empty subface has dimension `-1`). -/
theorem affDim_face (c : Fin n → Option Bool) :
    affDim (face b c) = ((vtxIdx c).card : ℤ) - 1 := by
  rcases Finset.eq_empty_or_nonempty (vtxIdx c) with hempty | hne
  · rw [face, hempty]
    simp
  · obtain ⟨p, hp⟩ := hne
    have hfne : (face b c).Nonempty := ⟨vtx b p, (vtx_mem_face_iff b).mpr hp⟩
    rw [affDim_eq_finrank_direction hfne, face, affineSpan_convexHull, direction_affineSpan]
    have hlin : LinearIndepOn ℝ (vtx b) (↑(vtxIdx c) : Set (Fin n × Bool)) :=
      (orthonormal_vtx_vtxIdx b c).linearIndependent
    have haff : AffineIndepOn ℝ (vtx b) (↑(vtxIdx c) : Set (Fin n × Bool)) :=
      hlin.affineIndepOn
    have hfin : (↑(vtxIdx c) : Set (Fin n × Bool)).Finite := (vtxIdx c).finite_toSet
    have hnes : (↑(vtxIdx c) : Set (Fin n × Bool)).Nonempty := ⟨p, Finset.mem_coe.mpr hp⟩
    have hrank := haff.finrank_vectorSpan_image hfin hnes
    rw [Set.ncard_coe_finset] at hrank
    rw [hrank]
    have hpos : 1 ≤ (vtxIdx c).card := Finset.card_pos.mpr ⟨p, hp⟩
    omega


/-! ## Classification of all faces -/

lemma finrank_eq_of_orthonormalBasis (v : OrthonormalBasis (Fin n) ℝ E) :
    Module.finrank ℝ E = n := by
  haveI : Module.Finite ℝ E := Module.Finite.of_basis v.toBasis
  simpa using Module.finrank_eq_card_basis v.toBasis

/-- A face containing the origin is the whole cross-polytope: the body is symmetric, so
every point lies on a segment through `0`. -/
lemma eq_body_of_zero_mem {F : Set E} (hF : IsFaceOf (body b) F) (h0 : (0 : E) ∈ F) :
    F = body b := by
  refine subset_antisymm hF.isExtreme.subset ?_
  intro x hx
  by_cases hx0 : x = 0
  · rw [hx0]; exact h0
  · have hneg : -x ∈ body b := neg_mem_body b hx
    have hseg : (0 : E) ∈ openSegment ℝ x (-x) :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
    exact hF.isExtreme.left_mem_of_mem_openSegment hx hneg h0 hseg

/-- Vertices contained in a given set. -/
noncomputable def faceVtxIdx (F : Set E) : Finset (Fin n × Bool) :=
  open Classical in Finset.univ.filter fun p => vtx b p ∈ F

lemma mem_faceVtxIdx {F : Set E} {p : Fin n × Bool} :
    p ∈ faceVtxIdx b F ↔ vtx b p ∈ F := by
  classical simp [faceVtxIdx]

lemma range_inter_eq_image_faceVtxIdx {F : Set E} :
    Set.range (vtx b) ∩ F = vtx b '' ↑(faceVtxIdx b F) := by
  ext y
  constructor
  · rintro ⟨⟨p, rfl⟩, hyF⟩
    exact ⟨p, Finset.mem_coe.mpr ((mem_faceVtxIdx b).mpr hyF), rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, rfl⟩, (mem_faceVtxIdx b).mp (Finset.mem_coe.mp hp)⟩

/-- **Every face of the cross-polytope is either a subface `face b c` or the whole body.**
A face containing two antipodal vertices contains the origin, hence is everything. -/
theorem eq_face_or_eq_body {F : Set E} (hF : IsFaceOf (body b) F) :
    (∃ c : Fin n → Option Bool, F = face b c) ∨ F = body b := by
  classical
  by_cases hanti : ∃ i : Fin n, (i, true) ∈ faceVtxIdx b F ∧ (i, false) ∈ faceVtxIdx b F
  · right
    obtain ⟨i, h1, h2⟩ := hanti
    have hv1 : vtx b (i, true) ∈ F := (mem_faceVtxIdx b).mp h1
    have hv2 : vtx b (i, false) ∈ F := (mem_faceVtxIdx b).mp h2
    have h0 : (0 : E) ∈ F := by
      have hmid := hF.convex hv1 hv2 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num)
      have : (1/2 : ℝ) • vtx b (i, true) + (1/2 : ℝ) • vtx b (i, false) = 0 := by
        simp [vtx, sgn, smul_smul]
      rwa [this] at hmid
    exact eq_body_of_zero_mem b hF h0
  · left
    push_neg at hanti
    refine ⟨fun i => if (i, true) ∈ faceVtxIdx b F then some true
      else if (i, false) ∈ faceVtxIdx b F then some false else none, ?_⟩
    have hvtx : vtxIdx (fun i => if (i, true) ∈ faceVtxIdx b F then some true
        else if (i, false) ∈ faceVtxIdx b F then some false else none)
        = faceVtxIdx b F := by
      ext p
      obtain ⟨i, s⟩ := p
      simp only [mem_vtxIdx]
      by_cases h1 : (i, true) ∈ faceVtxIdx b F
      · have h2 : (i, false) ∉ faceVtxIdx b F := hanti i h1
        rw [if_pos h1]
        cases s
        · simp [h2]
        · simp [h1]
      · by_cases h2 : (i, false) ∈ faceVtxIdx b F
        · rw [if_neg h1, if_pos h2]
          cases s
          · simp [h2]
          · simp [h1]
        · rw [if_neg h1, if_neg h2]
          cases s <;> simp [h1, h2]
    have hF' : IsFaceOf (convexHull ℝ (Set.range (vtx b))) F := hF
    calc F = convexHull ℝ (Set.range (vtx b) ∩ F) := face_eq_convexHull_inter hF'
      _ = convexHull ℝ (vtx b '' ↑(faceVtxIdx b F)) := by
          rw [range_inter_eq_image_faceVtxIdx]
      _ = face b _ := by rw [face, hvtx]

/-! ## Counting faces by dimension -/

/-- For `d < n` the `d`-faces are exactly the subfaces on `d + 1` selected vertices
(the whole body is the only other face, and it has dimension `n`). -/
theorem facesOfDim_eq_image (hn : 0 < n) (d : ℤ) (hd : d < (n : ℤ)) :
    Platonic.facesOfDim (body b) d
      = face b '' {c : Fin n → Option Bool | ((vtxIdx c).card : ℤ) = d + 1} := by
  haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b.toBasis
  ext F
  constructor
  · rintro ⟨hF, hdim⟩
    rcases eq_face_or_eq_body b hF with ⟨c, rfl⟩ | rfl
    · refine ⟨c, ?_, rfl⟩
      have := affDim_face b c
      rw [hdim] at this
      simp only [Set.mem_setOf_eq]
      omega
    · exfalso
      rw [affDim_body b hn, finrank_eq_of_orthonormalBasis b] at hdim
      omega
  · rintro ⟨c, hc, rfl⟩
    have hcard : ((vtxIdx c).card : ℤ) = d + 1 := hc
    refine ⟨isFaceOf_face b c, ?_⟩
    rw [affDim_face b c, hcard]
    ring

theorem ncard_facesOfDim (hn : 0 < n) (d : ℤ) (hd : d < (n : ℤ)) :
    (Platonic.facesOfDim (body b) d).ncard
      = {c : Fin n → Option Bool | ((vtxIdx c).card : ℤ) = d + 1}.ncard := by
  rw [facesOfDim_eq_image b hn d hd, Set.ncard_image_of_injective _ (face_injective b)]

/-- Faces of dimension `d` inside a given subface, indexed by vertex selections. -/
theorem ncard_facesOfDim_subset (hn : 0 < n) (d : ℤ) (hd : d < (n : ℤ))
    (c₀ : Fin n → Option Bool) :
    {e ∈ Platonic.facesOfDim (body b) d | e ⊆ face b c₀}.ncard
      = {c : Fin n → Option Bool |
          ((vtxIdx c).card : ℤ) = d + 1 ∧ vtxIdx c ⊆ vtxIdx c₀}.ncard := by
  have hset : {e ∈ Platonic.facesOfDim (body b) d | e ⊆ face b c₀}
      = face b '' {c : Fin n → Option Bool |
          ((vtxIdx c).card : ℤ) = d + 1 ∧ vtxIdx c ⊆ vtxIdx c₀} := by
    ext f
    rw [Set.mem_sep_iff, facesOfDim_eq_image b hn d hd]
    constructor
    · rintro ⟨⟨c, hc, rfl⟩, hsub⟩
      exact ⟨c, ⟨hc, (face_subset_iff b).mp hsub⟩, rfl⟩
    · rintro ⟨c, ⟨hc, hsub⟩, rfl⟩
      exact ⟨⟨c, hc, rfl⟩, (face_subset_iff b).mpr hsub⟩
  rw [hset, Set.ncard_image_of_injective _ (face_injective b)]

/-- Faces of dimension `d` containing a given subface, indexed by vertex selections. -/
theorem ncard_facesOfDim_superset (hn : 0 < n) (d : ℤ) (hd : d < (n : ℤ))
    (c₀ : Fin n → Option Bool) :
    {e ∈ Platonic.facesOfDim (body b) d | face b c₀ ⊆ e}.ncard
      = {c : Fin n → Option Bool |
          ((vtxIdx c).card : ℤ) = d + 1 ∧ vtxIdx c₀ ⊆ vtxIdx c}.ncard := by
  have hset : {e ∈ Platonic.facesOfDim (body b) d | face b c₀ ⊆ e}
      = face b '' {c : Fin n → Option Bool |
          ((vtxIdx c).card : ℤ) = d + 1 ∧ vtxIdx c₀ ⊆ vtxIdx c} := by
    ext f
    rw [Set.mem_sep_iff, facesOfDim_eq_image b hn d hd]
    constructor
    · rintro ⟨⟨c, hc, rfl⟩, hsub⟩
      exact ⟨c, ⟨hc, (face_subset_iff b).mp hsub⟩, rfl⟩
    · rintro ⟨c, ⟨hc, hsub⟩, rfl⟩
      exact ⟨⟨c, hc, rfl⟩, (face_subset_iff b).mpr hsub⟩
  rw [hset, Set.ncard_image_of_injective _ (face_injective b)]


/-! ## The geometric octahedron (`n = 3`)

All four incidence counts and the three face counts are decided from the vertex-selection
correspondence: faces of the octahedron are the `26` partial sign assignments of
`Fin 3 → Option Bool` with nonempty support, plus the body.
-/

section Oct3

set_option maxRecDepth 100000

private lemma count_card_1 :
    {c : Fin 3 → Option Bool | ((vtxIdx c).card : ℤ) = 0 + 1}.ncard = 6 := by
  rw [ncard_setOf_fintype]; decide

private lemma count_card_2 :
    {c : Fin 3 → Option Bool | ((vtxIdx c).card : ℤ) = 1 + 1}.ncard = 12 := by
  rw [ncard_setOf_fintype]; decide

private lemma count_card_3 :
    {c : Fin 3 → Option Bool | ((vtxIdx c).card : ℤ) = 2 + 1}.ncard = 8 := by
  rw [ncard_setOf_fintype]; decide

/-- Every triangular 2-face of the octahedron has three edges. -/
private lemma count_edges_of_face (c₀ : Fin 3 → Option Bool)
    (h : ((vtxIdx c₀).card : ℤ) = 2 + 1) :
    {c : Fin 3 → Option Bool |
      ((vtxIdx c).card : ℤ) = 1 + 1 ∧ vtxIdx c ⊆ vtxIdx c₀}.ncard = 3 := by
  rw [ncard_setOf_fintype]
  revert h
  revert c₀
  decide

/-- Every edge of the octahedron lies in two 2-faces. -/
private lemma count_faces_of_edge (c₀ : Fin 3 → Option Bool)
    (h : ((vtxIdx c₀).card : ℤ) = 1 + 1) :
    {c : Fin 3 → Option Bool |
      ((vtxIdx c).card : ℤ) = 2 + 1 ∧ vtxIdx c₀ ⊆ vtxIdx c}.ncard = 2 := by
  rw [ncard_setOf_fintype]
  revert h
  revert c₀
  decide

/-- Four edges meet at every vertex of the octahedron. -/
private lemma count_edges_of_vertex (c₀ : Fin 3 → Option Bool)
    (h : ((vtxIdx c₀).card : ℤ) = 0 + 1) :
    {c : Fin 3 → Option Bool |
      ((vtxIdx c).card : ℤ) = 1 + 1 ∧ vtxIdx c₀ ⊆ vtxIdx c}.ncard = 4 := by
  rw [ncard_setOf_fintype]
  revert h
  revert c₀
  decide

/-- Every edge of the octahedron has two vertices. -/
private lemma count_vertices_of_edge (c₀ : Fin 3 → Option Bool)
    (h : ((vtxIdx c₀).card : ℤ) = 1 + 1) :
    {c : Fin 3 → Option Bool |
      ((vtxIdx c).card : ℤ) = 0 + 1 ∧ vtxIdx c ⊆ vtxIdx c₀}.ncard = 2 := by
  rw [ncard_setOf_fintype]
  revert h
  revert c₀
  decide

variable (b : OrthonormalBasis (Fin 3) ℝ E)

/-- **Face counts of a geometric octahedron: `V = 6`, `E = 12`, `F = 8`.**
Geometric face counts (`IsFaceOf` + `affDim`), via the cross-polytope face lattice. -/
theorem octahedron_face_counts :
    (Platonic.facesOfDim (body b) 0).ncard = 6 ∧
      (Platonic.facesOfDim (body b) 1).ncard = 12 ∧
      (Platonic.facesOfDim (body b) 2).ncard = 8 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ncard_facesOfDim b (by norm_num) 0 (by norm_num)]; exact count_card_1
  · rw [ncard_facesOfDim b (by norm_num) 1 (by norm_num)]; exact count_card_2
  · rw [ncard_facesOfDim b (by norm_num) 2 (by norm_num)]; exact count_card_3

lemma affDim_body_oct : affDim (body b) = 3 := by
  haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b.toBasis
  rw [affDim_body b (by norm_num), finrank_eq_of_orthonormalBasis b]
  norm_num

/-- **`V − E + F = 2` for a geometric octahedron, discharged from Euler–Poincaré.** -/
theorem octahedron_euler_relation :
    ((Platonic.facesOfDim (body b) 0).ncard : ℤ) - (Platonic.facesOfDim (body b) 1).ncard
      + (Platonic.facesOfDim (body b) 2).ncard = 2 := by
  haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b.toBasis
  haveI : Nonempty E := ⟨0⟩
  exact euler_relation_convex_3polytope (hyperplanes_finite b)
    (body_eq_iInter_closedHalfspace b (by norm_num)) (isPolytope_body b)
    (affDim_body_oct b) (finrank_eq_of_orthonormalBasis b)

/-- **The four incidence counts of a geometric octahedron, proved from its face lattice:**
`3` edges per 2-face (triangles), `2` 2-faces per edge, `4` edges per vertex, `2` vertices
per edge. -/
theorem octahedron_incidence :
    (∀ f ∈ Platonic.facesOfDim (body b) 2,
        {e ∈ Platonic.facesOfDim (body b) 1 | e ⊆ f}.ncard = 3) ∧
      (∀ e ∈ Platonic.facesOfDim (body b) 1,
        {f ∈ Platonic.facesOfDim (body b) 2 | e ⊆ f}.ncard = 2) ∧
      (∀ v ∈ Platonic.facesOfDim (body b) 0,
        {e ∈ Platonic.facesOfDim (body b) 1 | v ⊆ e}.ncard = 4) ∧
      (∀ e ∈ Platonic.facesOfDim (body b) 1,
        {v ∈ Platonic.facesOfDim (body b) 0 | v ⊆ e}.ncard = 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf
    rw [facesOfDim_eq_image b (by norm_num) 2 (by norm_num)] at hf
    obtain ⟨c₀, hc₀, rfl⟩ := hf
    rw [ncard_facesOfDim_subset b (by norm_num) 1 (by norm_num) c₀]
    exact count_edges_of_face c₀ hc₀
  · intro e he
    rw [facesOfDim_eq_image b (by norm_num) 1 (by norm_num)] at he
    obtain ⟨c₀, hc₀, rfl⟩ := he
    rw [ncard_facesOfDim_superset b (by norm_num) 2 (by norm_num) c₀]
    exact count_faces_of_edge c₀ hc₀
  · intro v hv
    rw [facesOfDim_eq_image b (by norm_num) 0 (by norm_num)] at hv
    obtain ⟨c₀, hc₀, rfl⟩ := hv
    rw [ncard_facesOfDim_superset b (by norm_num) 1 (by norm_num) c₀]
    exact count_edges_of_vertex c₀ hc₀
  · intro e he
    rw [facesOfDim_eq_image b (by norm_num) 1 (by norm_num)] at he
    obtain ⟨c₀, hc₀, rfl⟩ := he
    rw [ncard_facesOfDim_subset b (by norm_num) 0 (by norm_num) c₀]
    exact count_vertices_of_edge c₀ hc₀

/-- **A geometric octahedron is Platonic `{3,4}` on the Euler–Poincaré spine.**

The double-counting identities come from face-lattice incidence, Euler's relation from
`Euler_Poincare_full`, and `(3,4)` is one of the five classical Schläfli pairs. Nothing in
this chain assumes `V − E + F = 2`. -/
theorem octahedron_platonic :
    3 * (Platonic.facesOfDim (body b) 2).ncard
        = 2 * (Platonic.facesOfDim (body b) 1).ncard ∧
      4 * (Platonic.facesOfDim (body b) 0).ncard
        = 2 * (Platonic.facesOfDim (body b) 1).ncard ∧
      ((Platonic.facesOfDim (body b) 0).ncard : ℤ) - (Platonic.facesOfDim (body b) 1).ncard
        + (Platonic.facesOfDim (body b) 2).ncard = 2 ∧
      ((3 : ℕ), (4 : ℕ)) ∈ Platonic.schlafliPairs := by
  haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b.toBasis
  haveI : Nonempty E := ⟨0⟩
  obtain ⟨h2e, he2, hv4, he0⟩ := octahedron_incidence b
  obtain ⟨hFace, hVert, hEuler⟩ :=
    Platonic.regular_polytope_counts (s := 3) (m := 4) (hyperplanes_finite b)
      (body_eq_iInter_closedHalfspace b (by norm_num)) (isPolytope_body b)
      (affDim_body_oct b) (finrank_eq_of_orthonormalBasis b) h2e he2 hv4 he0
  refine ⟨hFace, hVert, hEuler, ?_⟩
  exact Platonic.schlafli_pair_mem_of_regular_polytope (hyperplanes_finite b)
    (body_eq_iInter_closedHalfspace b (by norm_num)) (isPolytope_body b)
    (affDim_body_oct b) (finrank_eq_of_orthonormalBasis b) (by norm_num) (by norm_num)
    h2e he2 hv4 he0

end Oct3

/-- Every 3-dimensional real inner product space contains a geometric octahedron. -/
theorem exists_octahedron_basis {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 3) :
    Nonempty (OrthonormalBasis (Fin 3) ℝ E) := by
  have h := stdOrthonormalBasis ℝ E
  rw [hE] at h
  exact ⟨h⟩


end Octahedron
end EulersGem
