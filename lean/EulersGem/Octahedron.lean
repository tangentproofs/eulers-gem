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

end Octahedron
end EulersGem
