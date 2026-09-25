/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.Tactic
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Int.GCD

/-!
# Lattice-triangle shoelace helpers (not yet classical Pick)

Defines the corner determinant and the **shoelace rational**
`triangleShoelace = |det|/2`.

**Proved:**

* `triangleShoelace_eq_half_of_natAbs_det_eq_one`: if `|det|=1` then shoelace `= 1/2`.
* Edge gcds divide the determinant; hence `|det|=1` ⇒ each `edgeGcd = 1`.
* Cramer: if `|det(u,v)|=1` then every `p : ℤ×ℤ` is an integer combination of `u,v`.
* Integer barycentric cells with `α,β ≥ 0`, `α+β ≤ 1` are only `(0,0),(1,0),(0,1)`.
* Sum of shoelaces over a finite set of `|det|=1` triangles equals `#/2`.

**Explicitly not proved here (Claude audit):**

* Equality of shoelace with Lebesgue/Haar measure of the triangle.
* That `|det|=1` implies empty interior in the measure-theoretic sense without
  additional convex-hull work (Cramer is the algebraic half).
* Triangulation existence, planar Euler, or Pick for polygons.

See `PICKS_CLAUDE_AUDIT.md`.
-/

namespace EulersGem
namespace Picks
namespace LatticeTriangle

/-- Oriented 2×2 determinant of edge vectors from `a` to `b` and `a` to `c`. -/
def latticeDet (a b c : ℤ × ℤ) : ℤ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Shoelace area as a rational (`|det|/2`). Not yet identified with Haar measure. -/
def triangleShoelace (a b c : ℤ × ℤ) : ℚ :=
  (Int.natAbs (latticeDet a b c) : ℚ) / 2

lemma latticeDet_translate (a b c : ℤ × ℤ) :
    latticeDet a b c = latticeDet (0, 0) (b - a) (c - a) := by
  simp [latticeDet, Prod.sub_def]

lemma triangleShoelace_translate (a b c : ℤ × ℤ) :
    triangleShoelace a b c = triangleShoelace (0, 0) (b - a) (c - a) := by
  unfold triangleShoelace
  rw [latticeDet_translate]

/-- If `|det| = 1`, the shoelace rational equals `1/2`.

This is arithmetic on the shoelace definition, **not** a Haar-measure volume
theorem. Claude audit: do not cite this alone as “primitive triangle area”. -/
theorem triangleShoelace_eq_half_of_natAbs_det_eq_one
    (a b c : ℤ × ℤ) (h : Int.natAbs (latticeDet a b c) = 1) :
    triangleShoelace a b c = 1 / 2 := by
  simp [triangleShoelace, h]

lemma latticeDet_origin_eq_matrix_det (u v : ℤ × ℤ) :
    latticeDet (0, 0) u v = Matrix.det !![u.1, v.1; u.2, v.2] := by
  unfold latticeDet
  rw [Matrix.det_fin_two_of]
  ring

/-- Lattice content of the edge from `p` to `q`. -/
def edgeGcd (p q : ℤ × ℤ) : ℕ :=
  Int.gcd (q.1 - p.1) (q.2 - p.2)

lemma edgeGcd_dvd_latticeDet_left (a b c : ℤ × ℤ) :
    (edgeGcd a b : ℤ) ∣ latticeDet a b c := by
  unfold edgeGcd latticeDet
  have hdx : (Int.gcd (b.1 - a.1) (b.2 - a.2) : ℤ) ∣ (b.1 - a.1) :=
    Int.gcd_dvd_left _ _
  have hdy : (Int.gcd (b.1 - a.1) (b.2 - a.2) : ℤ) ∣ (b.2 - a.2) :=
    Int.gcd_dvd_right _ _
  exact dvd_sub (hdx.mul_right _) (hdy.mul_right _)

lemma latticeDet_swap_sign (a b c : ℤ × ℤ) :
    latticeDet a c b = -latticeDet a b c := by
  unfold latticeDet; ring

lemma edgeGcd_dvd_latticeDet_right (a b c : ℤ × ℤ) :
    (edgeGcd a c : ℤ) ∣ latticeDet a b c := by
  have h := edgeGcd_dvd_latticeDet_left a c b
  rw [latticeDet_swap_sign] at h
  exact dvd_neg.mp h

lemma edgeGcd_dvd_latticeDet_bc (a b c : ℤ × ℤ) :
    (edgeGcd b c : ℤ) ∣ latticeDet a b c := by
  unfold edgeGcd latticeDet
  set u1 := b.1 - a.1
  set u2 := b.2 - a.2
  set v1 := c.1 - a.1
  set v2 := c.2 - a.2
  have h1 : c.1 - b.1 = v1 - u1 := by omega
  have h2 : c.2 - b.2 = v2 - u2 := by omega
  rw [h1, h2]
  have heq : u1 * v2 - u2 * v1 = u1 * (v2 - u2) - u2 * (v1 - u1) := by ring
  rw [heq]
  have hx : (Int.gcd (v1 - u1) (v2 - u2) : ℤ) ∣ (v1 - u1) := Int.gcd_dvd_left _ _
  have hy : (Int.gcd (v1 - u1) (v2 - u2) : ℤ) ∣ (v2 - u2) := Int.gcd_dvd_right _ _
  exact dvd_sub (hy.mul_left _) (hx.mul_left _)

/-- `|det| = 1` ⇒ every edge is primitive (`edgeGcd = 1`). -/
theorem edgeGcd_eq_one_of_natAbs_det_eq_one
    (a b c : ℤ × ℤ) (h : Int.natAbs (latticeDet a b c) = 1) :
    edgeGcd a b = 1 ∧ edgeGcd a c = 1 ∧ edgeGcd b c = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · have hd := edgeGcd_dvd_latticeDet_left a b c
    have : (edgeGcd a b : ℤ) ∣ (Int.natAbs (latticeDet a b c) : ℤ) :=
      Int.dvd_natAbs.mpr hd
    have : edgeGcd a b ∣ Int.natAbs (latticeDet a b c) :=
      Int.natCast_dvd_natCast.mp this
    simpa [h] using this
  · have hd := edgeGcd_dvd_latticeDet_right a b c
    have : (edgeGcd a c : ℤ) ∣ (Int.natAbs (latticeDet a b c) : ℤ) :=
      Int.dvd_natAbs.mpr hd
    have : edgeGcd a c ∣ Int.natAbs (latticeDet a b c) :=
      Int.natCast_dvd_natCast.mp this
    simpa [h] using this
  · have hd := edgeGcd_dvd_latticeDet_bc a b c
    have : (edgeGcd b c : ℤ) ∣ (Int.natAbs (latticeDet a b c) : ℤ) :=
      Int.dvd_natAbs.mpr hd
    have : edgeGcd b c ∣ Int.natAbs (latticeDet a b c) :=
      Int.natCast_dvd_natCast.mp this
    simpa [h] using this

def cramerα (_u v p : ℤ × ℤ) : ℤ := v.2 * p.1 - v.1 * p.2
def cramerβ (u _v p : ℤ × ℤ) : ℤ := u.1 * p.2 - u.2 * p.1

lemma cramer_mul_det (u v p : ℤ × ℤ) :
    u.1 * cramerα u v p + v.1 * cramerβ u v p =
      latticeDet (0, 0) u v * p.1 ∧
    u.2 * cramerα u v p + v.2 * cramerβ u v p =
      latticeDet (0, 0) u v * p.2 := by
  unfold cramerα cramerβ latticeDet
  constructor <;> ring

/-- If `|det(u,v)| = 1`, every lattice point is an integer linear combination of `u,v`. -/
theorem exists_coords_of_natAbs_det_eq_one
    (u v p : ℤ × ℤ) (h : Int.natAbs (latticeDet (0, 0) u v) = 1) :
    ∃ α β : ℤ, α * u.1 + β * v.1 = p.1 ∧ α * u.2 + β * v.2 = p.2 := by
  have hdet : latticeDet (0, 0) u v = 1 ∨ latticeDet (0, 0) u v = -1 :=
    Int.natAbs_eq_iff.mp h
  have hm := cramer_mul_det u v p
  rcases hdet with hd | hd
  · refine ⟨cramerα u v p, cramerβ u v p, ?_⟩
    constructor
    · have := hm.1; simp only [hd, one_mul] at this; linarith
    · have := hm.2; simp only [hd, one_mul] at this; linarith
  · refine ⟨-cramerα u v p, -cramerβ u v p, ?_⟩
    constructor
    · have := hm.1; simp only [hd] at this; linarith
    · have := hm.2; simp only [hd] at this; linarith

lemma coords_unique_of_natAbs_det_eq_one
    (u v : ℤ × ℤ) (h : Int.natAbs (latticeDet (0, 0) u v) = 1)
    {α β α' β' : ℤ}
    (eq1 : α * u.1 + β * v.1 = α' * u.1 + β' * v.1)
    (eq2 : α * u.2 + β * v.2 = α' * u.2 + β' * v.2) :
    α = α' ∧ β = β' := by
  have hd : latticeDet (0, 0) u v ≠ 0 := by
    intro hz; simp [hz] at h
  set δα := α - α'
  set δβ := β - β'
  have e1 : u.1 * δα + v.1 * δβ = 0 := by
    change u.1 * (α - α') + v.1 * (β - β') = 0; linarith
  have e2 : u.2 * δα + v.2 * δβ = 0 := by
    change u.2 * (α - α') + v.2 * (β - β') = 0; linarith
  have hδα : latticeDet (0, 0) u v * δα = 0 := by
    have : latticeDet (0, 0) u v * δα =
        v.2 * (u.1 * δα + v.1 * δβ) - v.1 * (u.2 * δα + v.2 * δβ) := by
      unfold latticeDet; ring
    simpa [e1, e2] using this
  have hδβ : latticeDet (0, 0) u v * δβ = 0 := by
    have : latticeDet (0, 0) u v * δβ =
        u.1 * (u.2 * δα + v.2 * δβ) - u.2 * (u.1 * δα + v.1 * δβ) := by
      unfold latticeDet; ring
    simpa [e1, e2] using this
  have δα0 : δα = 0 := (mul_eq_zero.mp hδα).resolve_left hd
  have δβ0 : δβ = 0 := (mul_eq_zero.mp hδβ).resolve_left hd
  exact ⟨sub_eq_zero.mp δα0, sub_eq_zero.mp δβ0⟩



/-! ## Integer barycentric cells (algebraic half of “no extra lattice points”) -/

/-- Nonnegative integer barycentric coordinates with sum at most 1 (origin triangle). -/
def IsIntegerBarycentric (α β : ℤ) : Prop :=
  0 ≤ α ∧ 0 ≤ β ∧ α + β ≤ 1

/-- The only integer barycentric cells in the origin triangle are the three vertices.
Together with Cramer uniqueness, this is the algebraic half of “`|det|=1` ⇒ no
other lattice points”; the remaining half is identifying geometric convex-hull
membership with these coordinates (still open here — not Haar / not Pick). -/
theorem integerBarycentric_eq_vertices {α β : ℤ}
    (h : IsIntegerBarycentric α β) :
    (α = 0 ∧ β = 0) ∨ (α = 1 ∧ β = 0) ∨ (α = 0 ∧ β = 1) := by
  rcases h with ⟨hα, hβ, hsum⟩
  omega

/-! ## Bundled triangle + shoelace sum -/

/-- Three lattice vertices. -/
structure Triangle where
  a : ℤ × ℤ
  b : ℤ × ℤ
  c : ℤ × ℤ

namespace Triangle

def det (t : Triangle) : ℤ := latticeDet t.a t.b t.c

def shoelace (t : Triangle) : ℚ := triangleShoelace t.a t.b t.c

def IsDetPrimitive (t : Triangle) : Prop := Int.natAbs t.det = 1

theorem shoelace_eq_half_of_isDetPrimitive (t : Triangle) (h : t.IsDetPrimitive) :
    t.shoelace = 1 / 2 :=
  triangleShoelace_eq_half_of_natAbs_det_eq_one t.a t.b t.c h

end Triangle

/-- Sum of shoelaces of det-primitive triangles equals `#triangles / 2`.

Does **not** prove area additivity of a geometric polygon — only the rational
sum identity for the shoelace values on the listed triangles. -/
theorem sum_shoelace_eq_card_div_two
    (S : Finset Triangle) (h : ∀ t ∈ S, t.IsDetPrimitive) :
    (∑ t ∈ S, t.shoelace) = (S.card : ℚ) / 2 := by
  have hsum : ∑ t ∈ S, t.shoelace = ∑ t ∈ S, (1 / 2 : ℚ) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact Triangle.shoelace_eq_half_of_isDetPrimitive t (h t ht)
  have hcard : ∑ t ∈ S, (1 / 2 : ℚ) = (S.card : ℚ) / 2 := by
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  exact hsum.trans hcard

end LatticeTriangle
end Picks
end EulersGem
