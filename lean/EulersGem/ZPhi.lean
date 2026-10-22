/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exact arithmetic in `ℤ[φ]` for kernel-checked geometry

`ℤ[φ] = {a + b φ}` with `φ² = φ + 1` contains every vertex coordinate of the five Platonic
solids in their standard positions. Elements are pairs of integers, so equality and sign are
decided by integer arithmetic that the kernel evaluates (`decide`, no `native_decide`).
`toReal` is the evaluation at `φ = Real.goldenRatio`; the lemmas below say that it is a ring
map and that the computed sign is the real sign.

`ZPhi.V` is a vector in `ℤ[φ]³`, with dot and cross products, and `V.toR3` puts it in
`EuclideanSpace ℝ (Fin 3)`.
-/

open scoped RealInnerProductSpace goldenRatio

namespace EulersGem

/-- `a + b φ`. -/
structure ZPhi where
  a : Int
  b : Int
  deriving DecidableEq, Repr

namespace ZPhi

instance : Zero ZPhi := ⟨⟨0, 0⟩⟩
instance : One ZPhi := ⟨⟨1, 0⟩⟩
instance : Add ZPhi := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg ZPhi := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub ZPhi := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
/-- `(a + bφ)(c + dφ) = (ac + bd) + (ad + bc + bd)φ`, using `φ² = φ + 1`. -/
instance : Mul ZPhi := ⟨fun x y => ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩⟩

@[simp] lemma zero_a : (0 : ZPhi).a = 0 := rfl
@[simp] lemma zero_b : (0 : ZPhi).b = 0 := rfl
@[simp] lemma one_a : (1 : ZPhi).a = 1 := rfl
@[simp] lemma one_b : (1 : ZPhi).b = 0 := rfl
@[simp] lemma add_a (x y : ZPhi) : (x + y).a = x.a + y.a := rfl
@[simp] lemma add_b (x y : ZPhi) : (x + y).b = x.b + y.b := rfl
@[simp] lemma neg_a (x : ZPhi) : (-x).a = -x.a := rfl
@[simp] lemma neg_b (x : ZPhi) : (-x).b = -x.b := rfl
@[simp] lemma sub_a (x y : ZPhi) : (x - y).a = x.a - y.a := rfl
@[simp] lemma sub_b (x y : ZPhi) : (x - y).b = x.b - y.b := rfl
@[simp] lemma mul_a (x y : ZPhi) : (x * y).a = x.a * y.a + x.b * y.b := rfl
@[simp] lemma mul_b (x y : ZPhi) : (x * y).b = x.a * y.b + x.b * y.a + x.b * y.b := rfl

/-- An integer. -/
def ofInt (n : Int) : ZPhi := ⟨n, 0⟩

/-- Evaluation at the golden ratio. -/
noncomputable def toReal (x : ZPhi) : ℝ := x.a + x.b * φ

@[simp] lemma toReal_zero : toReal 0 = 0 := by simp [toReal]
@[simp] lemma toReal_one : toReal 1 = 1 := by simp [toReal]
@[simp] lemma toReal_ofInt (n : Int) : toReal (ofInt n) = n := by simp [toReal, ofInt]
@[simp] lemma toReal_add (x y : ZPhi) : toReal (x + y) = toReal x + toReal y := by
  simp [toReal]; ring
@[simp] lemma toReal_neg (x : ZPhi) : toReal (-x) = -toReal x := by simp [toReal]; ring
@[simp] lemma toReal_sub (x y : ZPhi) : toReal (x - y) = toReal x - toReal y := by
  simp [toReal]; ring
@[simp] lemma toReal_mul (x y : ZPhi) : toReal (x * y) = toReal x * toReal y := by
  have h := Real.goldenRatio_sq
  simp only [toReal, mul_a, mul_b]
  push_cast
  linear_combination (-(x.b : ℝ) * y.b) * h

/-- Sign of `p + q√5` for integers `p, q`; `2` flags the impossible case `p² = 5q² ≠ 0`. -/
def sgnPQ (p q : Int) : Int :=
  if p = 0 ∧ q = 0 then 0
  else if 0 ≤ p ∧ 0 ≤ q then 1
  else if p ≤ 0 ∧ q ≤ 0 then -1
  else if 0 < p then (if 5 * q * q < p * p then 1 else if p * p < 5 * q * q then -1 else 2)
  else (if p * p < 5 * q * q then 1 else if 5 * q * q < p * p then -1 else 2)

/-- The sign of `a + bφ`, computed with integers: `2(a + bφ) = (2a + b) + b√5`. -/
def sgn (x : ZPhi) : Int := sgnPQ (2 * x.a + x.b) x.b

lemma two_toReal (x : ZPhi) :
    2 * toReal x = ((2 * x.a + x.b : Int) : ℝ) + (x.b : ℝ) * √5 := by
  simp only [toReal, Real.goldenRatio]; push_cast; ring

private lemma sqrt5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)

private lemma pos_of_sgnPQ {p q : Int} (h : sgnPQ p q = 1) : 0 < (p : ℝ) + q * √5 := by
  have hs := sqrt5
  have hs0 : 0 ≤ √5 := Real.sqrt_nonneg _
  have hs1 : 0 < √5 := by nlinarith
  unfold sgnPQ at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 <;> try exact absurd h (by decide)
  · obtain ⟨hp, hq⟩ := h2
    have hp' : (0 : ℝ) ≤ p := by exact_mod_cast hp
    have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
    rcases hp'.lt_or_eq with hp'' | hp''
    · nlinarith
    · rcases hq'.lt_or_eq with hq'' | hq''
      · nlinarith
      · exact absurd ⟨by exact_mod_cast hp''.symm, by exact_mod_cast hq''.symm⟩ h1
  · have hp' : (0 : ℝ) < p := by exact_mod_cast h4
    have hpq : (5 : ℝ) * q * q < p * p := by exact_mod_cast h5
    by_contra hle
    push Not at hle
    have h0 : (0 : ℝ) ≤ p := hp'.le
    have h1' : (p : ℝ) ≤ -(q * √5) := by linarith
    have := mul_self_le_mul_self h0 h1'
    nlinarith
  · have hp' : (p : ℝ) ≤ 0 := by exact_mod_cast (not_lt.mp h4)
    have hq' : (0 : ℝ) ≤ q := by
      by_contra hq'
      push Not at hq'
      exact h3 ⟨not_lt.mp h4, by exact_mod_cast hq'.le⟩
    have hpq : (p : ℝ) * p < 5 * q * q := by exact_mod_cast h7
    by_contra hle
    push Not at hle
    have h0 : (0 : ℝ) ≤ q * √5 := mul_nonneg hq' hs0
    have h1' : q * √5 ≤ -(p : ℝ) := by linarith
    have := mul_self_le_mul_self h0 h1'
    nlinarith

private lemma sgnPQ_neg (p q : Int) (h : sgnPQ p q = -1) : sgnPQ (-p) (-q) = 1 := by
  unfold sgnPQ at *
  split_ifs at * <;> first | omega | (exfalso; nlinarith)

private lemma eq_of_sgnPQ {p q : Int} (h : sgnPQ p q = 0) : p = 0 ∧ q = 0 := by
  unfold sgnPQ at h
  split_ifs at h with h1 <;> first | exact h1 | exact absurd h (by decide)

/-- A computed sign `1` is a positive real. -/
lemma sgn_eq_one {x : ZPhi} (h : sgn x = 1) : 0 < toReal x := by
  have := pos_of_sgnPQ h
  have h2 := two_toReal x
  linarith

/-- A computed sign `-1` is a negative real. -/
lemma sgn_eq_neg_one {x : ZPhi} (h : sgn x = -1) : toReal x < 0 := by
  have h' := sgnPQ_neg _ _ h
  have := pos_of_sgnPQ h'
  have h2 := two_toReal x
  push_cast at this h2
  linarith

/-- A computed sign `0` is zero. -/
lemma sgn_eq_zero {x : ZPhi} (h : sgn x = 0) : toReal x = 0 := by
  obtain ⟨hp, hq⟩ := eq_of_sgnPQ h
  have hb : x.b = 0 := hq
  have ha : x.a = 0 := by omega
  simp [toReal, ha, hb]

lemma sgn_nonneg {x : ZPhi} (h0 : sgn x ≠ -1) (h2 : sgn x ≠ 2) : 0 ≤ toReal x := by
  have : sgn x = 0 ∨ sgn x = 1 := by
    unfold sgn sgnPQ at *; split_ifs at * <;> omega
  rcases this with h | h
  · exact (sgn_eq_zero h).ge
  · exact (sgn_eq_one h).le

lemma sgn_cases (x : ZPhi) : sgn x = 0 ∨ sgn x = 1 ∨ sgn x = -1 ∨ sgn x = 2 := by
  unfold sgn sgnPQ; split_ifs <;> simp

/-- A computed sign other than `0` (and not the error value) is a nonzero real. -/
lemma toReal_eq_zero_iff_sgn {x : ZPhi} (h2 : sgn x ≠ 2) : toReal x = 0 ↔ sgn x = 0 := by
  rcases sgn_cases x with h | h | h | h
  · exact ⟨fun _ => h, fun _ => sgn_eq_zero h⟩
  · exact ⟨fun h' => absurd h' (sgn_eq_one h).ne', fun h' => by rw [h] at h'; exact absurd h' (by decide)⟩
  · exact ⟨fun h' => absurd h' (sgn_eq_neg_one h).ne, fun h' => by rw [h] at h'; exact absurd h' (by decide)⟩
  · exact absurd h h2

/-! ## Vectors in `ℤ[φ]³` -/

/-- A vector in `ℤ[φ]³`. -/
structure V where
  x : ZPhi
  y : ZPhi
  z : ZPhi
  deriving DecidableEq, Repr

namespace V

instance : Zero V := ⟨⟨0, 0, 0⟩⟩
instance : Add V := ⟨fun u v => ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩⟩
instance : Sub V := ⟨fun u v => ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩⟩
instance : Neg V := ⟨fun u => ⟨-u.x, -u.y, -u.z⟩⟩
@[simp] lemma add_x (u v : V) : (u + v).x = u.x + v.x := rfl
@[simp] lemma add_y (u v : V) : (u + v).y = u.y + v.y := rfl
@[simp] lemma add_z (u v : V) : (u + v).z = u.z + v.z := rfl
@[simp] lemma sub_x (u v : V) : (u - v).x = u.x - v.x := rfl
@[simp] lemma sub_y (u v : V) : (u - v).y = u.y - v.y := rfl
@[simp] lemma sub_z (u v : V) : (u - v).z = u.z - v.z := rfl
@[simp] lemma zero_x : (0 : V).x = 0 := rfl
@[simp] lemma zero_y : (0 : V).y = 0 := rfl
@[simp] lemma zero_z : (0 : V).z = 0 := rfl

/-- Scalar multiple. -/
def smul (c : ZPhi) (u : V) : V := ⟨c * u.x, c * u.y, c * u.z⟩
/-- Dot product. -/
def dot (u v : V) : ZPhi := u.x * v.x + u.y * v.y + u.z * v.z
/-- Cross product. -/
def cross (u v : V) : V :=
  ⟨u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x⟩

/-- The real point. -/
noncomputable def toR3 (u : V) : EuclideanSpace ℝ (Fin 3) :=
  !₂[toReal u.x, toReal u.y, toReal u.z]

@[simp] lemma toR3_apply0 (u : V) : u.toR3 0 = toReal u.x := rfl
@[simp] lemma toR3_apply1 (u : V) : u.toR3 1 = toReal u.y := rfl
@[simp] lemma toR3_apply2 (u : V) : u.toR3 2 = toReal u.z := rfl

lemma ext_R3 {p q : EuclideanSpace ℝ (Fin 3)} (h0 : p 0 = q 0) (h1 : p 1 = q 1)
    (h2 : p 2 = q 2) : p = q := by
  ext i; fin_cases i <;> assumption

lemma inner_R3 (p q : EuclideanSpace ℝ (Fin 3)) :
    ⟪p, q⟫ = p 0 * q 0 + p 1 * q 1 + p 2 * q 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]; ring

@[simp] lemma toR3_add (u v : V) : (u + v).toR3 = u.toR3 + v.toR3 :=
  ext_R3 (by simp [toR3]) (by simp [toR3]) (by simp [toR3])

@[simp] lemma toR3_sub (u v : V) : (u - v).toR3 = u.toR3 - v.toR3 :=
  ext_R3 (by simp [toR3]) (by simp [toR3]) (by simp [toR3])

@[simp] lemma toR3_zero : (0 : V).toR3 = 0 :=
  ext_R3 (by simp [toR3]) (by simp [toR3]) (by simp [toR3])

@[simp] lemma toR3_smul (c : ZPhi) (u : V) : (smul c u).toR3 = toReal c • u.toR3 :=
  ext_R3 (by simp [toR3, smul]) (by simp [toR3, smul]) (by simp [toR3, smul])

lemma inner_toR3 (u v : V) : ⟪u.toR3, v.toR3⟫ = toReal (dot u v) := by
  rw [inner_R3]; simp [dot]

end V

end ZPhi


end EulersGem
