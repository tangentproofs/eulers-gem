/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.Tactic
import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.Convex.Combination
import EulersGem.LatticeTriangle
import EulersGem.LatticeTriangleEmpty
import EulersGem.LatticePolygon
import EulersGem.Picks

/-!
# Geometric fan triangulation of a lattice polygon

Algebraic shoelace fan identity + empty-interior Pick-form under fan
primitivity / primitive edges.

**Honesty / not classical Pick:**
* Fan primitivity discharged from empty fan triangles + nondeg (`FanDetPrimitive_of_empty_fan_triangles`).
* `FanTrianglesEmpty` from polygon `I=∅` + primitive edges + extreme vertices.
* `VerticesExtreme` discharged from `StrictlyConvexCCW` (edge half-planes + local CCW turns).
* Shoelace ≠ Haar/Lebesgue.
* Consistent orientation is a hyp (`FanDetsPos`) or follows from CCW convexity for nonnegativity.
* General lattice-polygon triangulation existence still open.
* See `PICKS_CLAUDE_AUDIT.md`.
-/

namespace EulersGem
namespace Picks
namespace LatticeFan

open LatticeTriangle
open LatticePolygon
open BigOperators

/-! ## Cross product + abstract fan identity -/

def cross (p q : ℤ × ℤ) : ℤ := p.1 * q.2 - p.2 * q.1

lemma latticeDet_eq_cross_cycle (a b c : ℤ × ℤ) :
    latticeDet a b c = cross a b + cross b c + cross c a := by
  unfold latticeDet cross; ring

lemma cross_anticomm (p q : ℤ × ℤ) : cross p q = -cross q p := by
  unfold cross; ring

lemma cross_self (p : ℤ × ℤ) : cross p p = 0 := by
  unfold cross; ring

/-- Oriented fan-triangle content as a cross-cycle (equals `latticeDet`). -/
def latDet (a b c : ℤ × ℤ) : ℤ := cross a b + cross b c + cross c a

lemma latDet_eq_latticeDet (a b c : ℤ × ℤ) : latDet a b c = latticeDet a b c :=
  (latticeDet_eq_cross_cycle a b c).symm

private lemma sum_shift_one (m : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ Finset.range m, f (i + 1) = ∑ j ∈ Finset.range (m + 1), f j - f 0 := by
  rw [Finset.sum_range_succ' f m]; ring

private lemma sum_shift_two (m : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ Finset.range m, f (i + 2) =
      ∑ j ∈ Finset.range (m + 2), f j - f 0 - f 1 := by
  have h1 := sum_shift_one m (fun j => f (j + 1))
  have h2 : ∑ j ∈ Finset.range (m + 1), f (j + 1) =
      ∑ j ∈ Finset.range (m + 2), f j - f 0 := by simpa using sum_shift_one (m + 1) f
  calc
    ∑ i ∈ Finset.range m, f (i + 2)
        = ∑ j ∈ Finset.range (m + 1), f (j + 1) - f 1 := h1
    _ = (∑ j ∈ Finset.range (m + 2), f j - f 0) - f 1 := by rw [h2]
    _ = ∑ j ∈ Finset.range (m + 2), f j - f 0 - f 1 := by ring

/-- **Abstract algebraic fan identity** (Nat-indexed vertices). -/
theorem fan_shoelace_identity (n : ℕ) (hn : 3 ≤ n) (v : ℕ → ℤ × ℤ) :
    ∑ i ∈ Finset.range n, cross (v i) (v ((i + 1) % n)) =
      ∑ i ∈ Finset.range (n - 2), latDet (v 0) (v (i + 1)) (v (i + 2)) := by
  classical
  have hexpand :
      ∑ i ∈ Finset.range (n - 2), latDet (v 0) (v (i + 1)) (v (i + 2)) =
        (∑ i ∈ Finset.range (n - 2), cross (v 0) (v (i + 1))) +
        (∑ i ∈ Finset.range (n - 2), cross (v (i + 1)) (v (i + 2))) +
        (∑ i ∈ Finset.range (n - 2), cross (v (i + 2)) (v 0)) := by
    simp only [latDet, Finset.sum_add_distrib]
  set S1 := ∑ i ∈ Finset.range (n - 2), cross (v 0) (v (i + 1))
  set S2 := ∑ i ∈ Finset.range (n - 2), cross (v (i + 1)) (v (i + 2))
  set S3 := ∑ i ∈ Finset.range (n - 2), cross (v (i + 2)) (v 0)
  have hexpand' :
      ∑ i ∈ Finset.range (n - 2), latDet (v 0) (v (i + 1)) (v (i + 2)) = S1 + S2 + S3 := by
    simpa [S1, S2, S3] using hexpand
  have hS1 : S1 = ∑ k ∈ Finset.range (n - 1), cross (v 0) (v k) := by
    change ∑ i ∈ Finset.range (n - 2), cross (v 0) (v (i + 1)) = _
    have h := sum_shift_one (n - 2) (fun k => cross (v 0) (v k))
    have : n - 2 + 1 = n - 1 := by omega
    rw [h, this, cross_self, sub_zero]
  have hS3 :
      S3 = -(∑ k ∈ Finset.range n, cross (v 0) (v k) - cross (v 0) (v 1)) := by
    have hneg : S3 = -∑ i ∈ Finset.range (n - 2), cross (v 0) (v (i + 2)) := by
      change ∑ i ∈ Finset.range (n - 2), cross (v (i + 2)) (v 0) = _
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => cross_anticomm _ _
    rw [hneg]
    have h := sum_shift_two (n - 2) (fun k => cross (v 0) (v k))
    have : n - 2 + 2 = n := by omega
    rw [this, cross_self, sub_zero] at h
    exact congrArg Neg.neg h
  have h13 : S1 + S3 = cross (v 0) (v 1) - cross (v 0) (v (n - 1)) := by
    rw [hS1, hS3]
    have h := Finset.sum_range_succ (fun k => cross (v 0) (v k)) (n - 1)
    have : n - 1 + 1 = n := by omega
    have h' : ∑ k ∈ Finset.range n, cross (v 0) (v k) =
        ∑ k ∈ Finset.range (n - 1), cross (v 0) (v k) + cross (v 0) (v (n - 1)) :=
      this ▸ h
    rw [h']; ring
  have h0 : (0 + 1) % n = 1 := Nat.mod_eq_of_lt (by omega)
  have hlast : (n - 1 + 1) % n = 0 := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
  have hrange : Finset.range n =
      insert 0 ((Finset.range (n - 2)).image (· + 1)) ∪ {n - 1} := by
    ext k; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_range]
    constructor
    · intro hk
      by_cases h0' : k = 0; · exact Or.inl (Or.inl h0')
      by_cases hl : k = n - 1; · exact Or.inr hl
      exact Or.inl (Or.inr ⟨k - 1, by omega, by omega⟩)
    · rintro ((rfl | ⟨i, hi, rfl⟩) | rfl) <;> omega
  have hd1 : 0 ∉ (Finset.range (n - 2)).image (· + 1) := by
    intro h; rcases Finset.mem_image.mp h with ⟨_, _, eq⟩; omega
  have hd2 : n - 1 ∉ insert 0 ((Finset.range (n - 2)).image (· + 1)) := by
    intro h
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range] at h
    rcases h with h | ⟨w, hw, hw'⟩ <;> omega
  have himg :
      ∑ k ∈ (Finset.range (n - 2)).image (· + 1),
          cross (v k) (v ((k + 1) % n)) = S2 := by
    rw [Finset.sum_image (fun a _ b _ h => Nat.add_right_cancel h)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have : (i + 1 + 1) % n = i + 2 :=
      Nat.mod_eq_of_lt (by have := Finset.mem_range.mp hi; omega)
    rw [this]
  have hleft :
      ∑ i ∈ Finset.range n, cross (v i) (v ((i + 1) % n)) =
        cross (v 0) (v 1) + S2 + cross (v (n - 1)) (v 0) := by
    rw [hrange, Finset.sum_union (Finset.disjoint_singleton_right.mpr hd2),
      Finset.sum_insert hd1, Finset.sum_singleton, himg, h0, hlast]
  have hclose : cross (v (n - 1)) (v 0) = -cross (v 0) (v (n - 1)) :=
    cross_anticomm _ _
  calc
    ∑ i ∈ Finset.range n, cross (v i) (v ((i + 1) % n))
        = cross (v 0) (v 1) + S2 + cross (v (n - 1)) (v 0) := hleft
    _ = cross (v 0) (v 1) + S2 - cross (v 0) (v (n - 1)) := by
        rw [hclose]; ring
    _ = S1 + S2 + S3 := by linarith [h13]
    _ = ∑ i ∈ Finset.range (n - 2), latDet (v 0) (v (i + 1)) (v (i + 2)) :=
        hexpand'.symm

/-! ## Discharge `VerticesExtreme` from CCW convexity (ℝ² helpers) -/


def detR (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

lemma detR_toReal (a b c : ℤ × ℤ) :
    detR (toReal a) (toReal b) (toReal c) = (latticeDet a b c : ℝ) := by
  simp only [detR, toReal, LatticeTriangle.toReal, latticeDet]
  norm_cast

lemma exists_smul_of_cross_eq_zero (u w : ℝ × ℝ) (hu : u ≠ 0)
    (h : u.1 * w.2 - u.2 * w.1 = 0) : ∃ t : ℝ, w = t • u := by
  by_cases h1 : u.1 = 0
  · have h2 : u.2 ≠ 0 := fun h2 => hu (Prod.ext h1 h2)
    have hw1 : w.1 = 0 := by
      have hh : -(u.2 * w.1) = 0 := by simpa [h1, sub_eq_add_neg] using h
      exact (mul_eq_zero.mp (neg_eq_zero.mp hh)).resolve_left h2
    refine ⟨w.2 / u.2, Prod.ext ?_ ?_⟩
    · simp [h1, hw1, smul_eq_mul]
    · simp [smul_eq_mul]; exact (div_mul_cancel₀ w.2 h2).symm
  · refine ⟨w.1 / u.1, Prod.ext ?_ ?_⟩
    · simp [smul_eq_mul]; exact (div_mul_cancel₀ w.1 h1).symm
    · simp [smul_eq_mul]
      field_simp [h1]
      linear_combination h

lemma detR_sum_smul {ι : Type*} [Fintype ι] (a b : ℝ × ℝ) (w : ι → ℝ) (z : ι → ℝ × ℝ)
    (hw1 : ∑ i, w i = 1) :
    detR a b (∑ i, w i • z i) = ∑ i, w i * detR a b (z i) := by
  set p : ℝ := b.1 - a.1
  set q : ℝ := b.2 - a.2
  set c0 : ℝ := p * a.2 - q * a.1
  have hform (x : ℝ × ℝ) : detR a b x = p * x.2 - q * x.1 - c0 := by
    dsimp [detR, p, q, c0]; ring
  have hs1 : (∑ i, w i • z i).1 = ∑ i, (w i • z i).1 := Prod.fst_sum
  have hs1' : ∑ i, (w i • z i).1 = ∑ i, w i * (z i).1 := by
    refine Finset.sum_congr rfl fun i _ => by simp [Prod.smul_def, smul_eq_mul]
  have hs2 : (∑ i, w i • z i).2 = ∑ i, (w i • z i).2 := Prod.snd_sum
  have hs2' : ∑ i, (w i • z i).2 = ∑ i, w i * (z i).2 := by
    refine Finset.sum_congr rfl fun i _ => by simp [Prod.smul_def, smul_eq_mul]
  calc
    detR a b (∑ i, w i • z i)
        = p * (∑ i, w i • z i).2 - q * (∑ i, w i • z i).1 - c0 := hform _
    _ = p * (∑ i, w i * (z i).2) - q * (∑ i, w i * (z i).1) - c0 := by
        rw [hs2, hs2', hs1, hs1']
    _ = p * (∑ i, w i * (z i).2) - q * (∑ i, w i * (z i).1) - (∑ i, w i) * c0 := by
        rw [hw1, one_mul]
    _ = ∑ i, (p * (w i * (z i).2) - q * (w i * (z i).1) - w i * c0) := by
        simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_mul]
    _ = ∑ i, w i * (p * (z i).2 - q * (z i).1 - c0) := by
        refine Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, w i * detR a b (z i) := by
        refine Finset.sum_congr rfl fun i _ => by rw [hform]

lemma eq_of_detR_corner
    (A B C X : ℝ × ℝ) (hne : detR A B C ≠ 0)
    (hAB : detR A B X = 0) (hBC : detR B C X = 0) : X = B := by
  set u1 : ℝ := B.1 - A.1
  set u2 : ℝ := B.2 - A.2
  set v1 : ℝ := C.1 - B.1
  set v2 : ℝ := C.2 - B.2
  have hcross_eq : detR A B C = u1 * v2 - u2 * v1 := by
    dsimp [detR, u1, u2, v1, v2]; ring
  have hcross : u1 * v2 - u2 * v1 ≠ 0 := by rwa [← hcross_eq]
  have hu : (u1, u2) ≠ (0 : ℝ × ℝ) := by
    intro h0
    apply hcross
    have hu1 : u1 = 0 := (Prod.ext_iff.mp h0).1
    have hu2 : u2 = 0 := (Prod.ext_iff.mp h0).2
    simp [hu1, hu2]
  have hv : (v1, v2) ≠ (0 : ℝ × ℝ) := by
    intro h0
    apply hcross
    have hv1 : v1 = 0 := (Prod.ext_iff.mp h0).1
    have hv2 : v2 = 0 := (Prod.ext_iff.mp h0).2
    simp [hv1, hv2]
  have h1 : u1 * (X.2 - A.2) - u2 * (X.1 - A.1) = 0 := by
    simpa [detR, u1, u2] using hAB
  have h2 : v1 * (X.2 - B.2) - v2 * (X.1 - B.1) = 0 := by
    simpa [detR, v1, v2] using hBC
  obtain ⟨t, ht⟩ := exists_smul_of_cross_eq_zero (u1, u2) (X.1 - A.1, X.2 - A.2) hu h1
  obtain ⟨s, hs⟩ := exists_smul_of_cross_eq_zero (v1, v2) (X.1 - B.1, X.2 - B.2) hv h2
  have hx1' : X.1 - A.1 = t * u1 := by simpa [smul_eq_mul] using congrArg Prod.fst ht
  have hx2' : X.2 - A.2 = t * u2 := by simpa [smul_eq_mul] using congrArg Prod.snd ht
  have hy1' : X.1 - B.1 = s * v1 := by simpa [smul_eq_mul] using congrArg Prod.fst hs
  have hy2' : X.2 - B.2 = s * v2 := by simpa [smul_eq_mul] using congrArg Prod.snd hs
  have hrel1 : (t - 1) * u1 = s * v1 := by
    have e1 : X.1 = A.1 + t * u1 := by
      have h := sub_eq_iff_eq_add.mp hx1'; rwa [add_comm]
    have e2 : X.1 = A.1 + u1 + s * v1 := by
      have hB : B.1 = A.1 + u1 := by dsimp [u1]; ring
      have eB : X.1 = B.1 + s * v1 := by
        have h := sub_eq_iff_eq_add.mp hy1'; rwa [add_comm]
      rw [eB, hB]
    linarith
  have hrel2 : (t - 1) * u2 = s * v2 := by
    have e1 : X.2 = A.2 + t * u2 := by
      have h := sub_eq_iff_eq_add.mp hx2'; rwa [add_comm]
    have e2 : X.2 = A.2 + u2 + s * v2 := by
      have hB : B.2 = A.2 + u2 := by dsimp [u2]; ring
      have eB : X.2 = B.2 + s * v2 := by
        have h := sub_eq_iff_eq_add.mp hy2'; rwa [add_comm]
      rw [eB, hB]
    linarith
  have hs0 : s = 0 := by
    have : s * (u1 * v2 - u2 * v1) = 0 :=
      calc s * (u1 * v2 - u2 * v1)
          = u1 * (s * v2) - u2 * (s * v1) := by ring
        _ = u1 * ((t - 1) * u2) - u2 * ((t - 1) * u1) := by rw [← hrel2, ← hrel1]
        _ = 0 := by ring
    exact (mul_eq_zero.mp this).resolve_right hcross
  apply Prod.ext
  · have eB : X.1 = B.1 + s * v1 := by
      have h := sub_eq_iff_eq_add.mp hy1'; rwa [add_comm]
    simp [eB, hs0]
  · have eB : X.2 = B.2 + s * v2 := by
      have h := sub_eq_iff_eq_add.mp hy2'; rwa [add_comm]
    simp [eB, hs0]

/-! ## Geometric fan on a `LatticePolygon` -/

variable (P : LatticePolygon)

def vertNat (k : ℕ) : ℤ × ℤ :=
  if h : k < P.nVertices then P.vertex ⟨k, h⟩ else (0, 0)

def fanTriangle (i : ℕ) (hi : i < P.nVertices - 2) : Triangle :=
  ⟨P.vertex ⟨0, P.nVertices_pos⟩,
    P.vertex ⟨i + 1, by have := P.length_ge; omega⟩,
    P.vertex ⟨i + 2, by have := P.length_ge; omega⟩⟩

def fanDet (i : ℕ) (hi : i < P.nVertices - 2) : ℤ :=
  (fanTriangle P i hi).det

def fanDetNat (i : ℕ) : ℤ :=
  if h : i < P.nVertices - 2 then fanDet P i h else 0

def sumFanDet : ℤ :=
  ∑ i ∈ Finset.range (P.nVertices - 2), fanDetNat P i

def fanTriangles : Finset Triangle := by
  classical
  exact (Finset.range (P.nVertices - 2)).attach.image fun i =>
    fanTriangle P i.1 (Finset.mem_range.mp i.2)

lemma mem_fanTriangles {t : Triangle} :
    t ∈ fanTriangles P ↔
      ∃ (i : ℕ) (hi : i < P.nVertices - 2), t = fanTriangle P i hi := by
  classical
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨⟨i, hi⟩, _, rfl⟩
    exact ⟨i, Finset.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_range.mpr hi⟩, by simp⟩

lemma fanTriangle_eq_of_eq {i j : ℕ}
    (hi : i < P.nVertices - 2) (hj : j < P.nVertices - 2)
    (hverts : Function.Injective P.vertex)
    (h : fanTriangle P i hi = fanTriangle P j hj) : i = j := by
  have hb := congrArg Triangle.b h
  have hij := hverts hb
  exact Nat.add_right_cancel (Fin.val_eq_of_eq hij)

lemma card_fanTriangles (hverts : Function.Injective P.vertex) :
    (fanTriangles P).card = P.nVertices - 2 := by
  classical
  dsimp [fanTriangles]
  rw [Finset.card_image_of_injective _ (fun a b h =>
    Subtype.ext (fanTriangle_eq_of_eq P (Finset.mem_range.mp a.2)
      (Finset.mem_range.mp b.2) hverts h))]
  simp [Finset.card_attach, Finset.card_range]

lemma shoelaceSum_eq_sum_cross :
    P.shoelaceSum =
      ∑ i : Fin P.nVertices, cross (P.vertex i) (P.vertex (P.nextIdx i)) := by
  simp only [LatticePolygon.shoelaceSum, edgePair, cross]
  refine Finset.sum_congr rfl fun i _ => ?_; ring

lemma shoelaceSum_as_nat_sum :
    P.shoelaceSum =
      ∑ i ∈ Finset.range P.nVertices,
        cross (vertNat P i) (vertNat P ((i + 1) % P.nVertices)) := by
  rw [shoelaceSum_eq_sum_cross]
  refine Eq.trans ?_ (Fin.sum_univ_eq_sum_range (fun i =>
    cross (vertNat P i) (vertNat P ((i + 1) % P.nVertices))) P.nVertices)
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : i.val < P.nVertices := i.isLt
  have hmod : (i.val + 1) % P.nVertices < P.nVertices := Nat.mod_lt _ P.nVertices_pos
  simp only [vertNat, hi, hmod, ↓reduceDIte]
  cases i with
  | mk val isLt =>
    rfl

lemma fanDetNat_eq_latDet (i : ℕ) (hi : i ∈ Finset.range (P.nVertices - 2)) :
    fanDetNat P i =
      latDet (vertNat P 0) (vertNat P (i + 1)) (vertNat P (i + 2)) := by
  have hi' : i < P.nVertices - 2 := Finset.mem_range.mp hi
  have h0 : 0 < P.nVertices := P.nVertices_pos
  have h1 : i + 1 < P.nVertices := by omega
  have h2 : i + 2 < P.nVertices := by omega
  simp only [fanDetNat, hi', ↓reduceDIte, fanDet, Triangle.det, fanTriangle,
    vertNat, h0, h1, h2, latDet_eq_latticeDet]

/-- **Polygon algebraic fan identity.** -/
theorem shoelaceSum_eq_sumFanDet : P.shoelaceSum = sumFanDet P := by
  classical
  have hn : 3 ≤ P.nVertices := P.length_ge
  have h1 := shoelaceSum_as_nat_sum P
  have h2 := fan_shoelace_identity P.nVertices hn (vertNat P)
  have h3 :
      sumFanDet P =
        ∑ i ∈ Finset.range (P.nVertices - 2),
          latDet (vertNat P 0) (vertNat P (i + 1)) (vertNat P (i + 2)) := by
    refine Finset.sum_congr rfl fun i hi => fanDetNat_eq_latDet P i hi
  exact h1.trans (h2.trans h3.symm)

/-! ## Oriented area additivity + empty-interior Pick-form -/

def FanDetsNonneg : Prop :=
  ∀ (i : ℕ) (hi : i < P.nVertices - 2), 0 ≤ fanDet P i hi

def FanDetPrimitive : Prop :=
  ∀ (i : ℕ) (hi : i < P.nVertices - 2),
    (fanTriangle P i hi).IsDetPrimitive

lemma sumFanDet_eq_sum_natAbs_of_nonneg (hnn : FanDetsNonneg P) :
    sumFanDet P =
      ∑ i ∈ Finset.range (P.nVertices - 2), (Int.natAbs (fanDetNat P i) : ℤ) := by
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < P.nVertices - 2 := Finset.mem_range.mp hi
  have hge : 0 ≤ fanDet P i hi' := hnn i hi'
  simp only [fanDetNat, hi', ↓reduceDIte]
  exact (Int.natAbs_of_nonneg hge).symm

theorem shoelace_eq_sum_fan_shoelace
    (hnn : FanDetsNonneg P) (hverts : Function.Injective P.vertex) :
    P.shoelace = ∑ t ∈ fanTriangles P, t.shoelace := by
  classical
  have hsum := shoelaceSum_eq_sumFanDet P
  have hnn' := sumFanDet_eq_sum_natAbs_of_nonneg P hnn
  have hge : 0 ≤ sumFanDet P := by
    rw [hnn']; exact Finset.sum_nonneg fun _ _ => by exact_mod_cast Nat.zero_le _
  have hnat : (Int.natAbs P.shoelaceSum : ℤ) = sumFanDet P := by
    rw [hsum, Int.natAbs_of_nonneg hge]
  have hrhs :
      ∑ t ∈ fanTriangles P, t.shoelace =
        (∑ i ∈ Finset.range (P.nVertices - 2),
          (Int.natAbs (fanDetNat P i) : ℚ)) / 2 := by
    dsimp [fanTriangles]
    rw [Finset.sum_image (fun a _ha b _hb h =>
      Subtype.ext (fanTriangle_eq_of_eq P (Finset.mem_range.mp a.2)
        (Finset.mem_range.mp b.2) hverts h))]
    have h1 :
        ∑ i ∈ (Finset.range (P.nVertices - 2)).attach,
            (fanTriangle P i.1 (Finset.mem_range.mp i.2)).shoelace =
          ∑ i ∈ (Finset.range (P.nVertices - 2)).attach,
            ((Int.natAbs (fanDet P i.1 (Finset.mem_range.mp i.2)) : ℚ) / 2) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Triangle.shoelace, triangleShoelace, fanDet, Triangle.det]
    rw [h1]
    have h2 :
        ∑ i ∈ (Finset.range (P.nVertices - 2)).attach,
            (Int.natAbs (fanDet P i.1 (Finset.mem_range.mp i.2)) : ℚ) =
          ∑ i ∈ Finset.range (P.nVertices - 2),
            (Int.natAbs (fanDetNat P i) : ℚ) := by
      have hattach := Finset.sum_attach (Finset.range (P.nVertices - 2))
        (fun i => (Int.natAbs (fanDetNat P i) : ℚ))
      refine Eq.trans ?_ hattach
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi' : i.1 < P.nVertices - 2 := Finset.mem_range.mp i.2
      simp [fanDetNat, hi']
    rw [← Finset.sum_div, h2]
  have hlhs :
      (Int.natAbs P.shoelaceSum : ℚ) / 2 =
        (∑ i ∈ Finset.range (P.nVertices - 2),
          (Int.natAbs (fanDetNat P i) : ℚ)) / 2 := by
    have hx : (Int.natAbs P.shoelaceSum : ℚ) = (sumFanDet P : ℚ) := by
      exact congrArg (fun z : ℤ => (z : ℚ)) hnat
    have hy : (sumFanDet P : ℚ) =
        ∑ i ∈ Finset.range (P.nVertices - 2), (Int.natAbs (fanDetNat P i) : ℚ) := by
      have := congrArg (fun z : ℤ => (z : ℚ)) hnn'
      simpa [Int.cast_sum] using this
    rw [hx, hy]
  calc
    P.shoelace = (Int.natAbs P.shoelaceSum : ℚ) / 2 := rfl
    _ = ∑ t ∈ fanTriangles P, t.shoelace := by rw [hlhs, hrhs]

theorem shoelace_eq_n_sub_two_div_two
    (hnn : FanDetsNonneg P) (hprim : FanDetPrimitive P)
    (hverts : Function.Injective P.vertex) :
    P.shoelace = ((P.nVertices - 2 : ℕ) : ℚ) / 2 := by
  classical
  have hadd := shoelace_eq_sum_fan_shoelace P hnn hverts
  have hprim' : ∀ t ∈ fanTriangles P, t.IsDetPrimitive := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := (mem_fanTriangles P).mp ht
    exact hprim i hi
  have hsum := sum_shoelace_eq_card_div_two (fanTriangles P) hprim'
  have hcard := card_fanTriangles P hverts
  calc
    P.shoelace = ∑ t ∈ fanTriangles P, t.shoelace := hadd
    _ = ((fanTriangles P).card : ℚ) / 2 := hsum
    _ = ((P.nVertices - 2 : ℕ) : ℚ) / 2 := by rw [hcard]

/-! ## Primitive edges ⇒ `B = n` -/

def PrimitiveEdges : Prop :=
  ∀ i : Fin P.nVertices, edgeGcd (P.edgePair i).1 (P.edgePair i).2 = 1

private lemma edgeLatticePoints_eq_endpoints (p q : ℤ × ℤ) (h : edgeGcd p q = 1) :
    edgeLatticePoints p q = {p, q} := by
  classical
  have hcard := card_edgeLatticePoints p q
  simp only [h] at hcard
  -- card = 2, and {p,q} ⊆ edgeLatticePoints
  have hp := self_mem_edgeLatticePoints p q
  have hq := other_mem_edgeLatticePoints p q
  have hsub : ({p, q} : Finset (ℤ × ℤ)) ⊆ edgeLatticePoints p q := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hne : p ≠ q := by
    intro hpq
    have : edgeGcd p q = 0 := (edgeGcd_eq_zero_iff p q).mpr hpq
    omega
  have hcard2 : ({p, q} : Finset (ℤ × ℤ)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hsub (by omega : (edgeLatticePoints p q).card ≤ ({p, q} : Finset (ℤ × ℤ)).card)).symm

theorem B_eq_nVertices_of_primitive_edges
    (hprim : PrimitiveEdges P) (hverts : Function.Injective P.vertex) :
    P.B = P.nVertices := by
  classical
  unfold LatticePolygon.B LatticePolygon.boundaryLatticePoints
  have hedge : ∀ i : Fin P.nVertices,
      edgeLatticePoints (P.edgePair i).1 (P.edgePair i).2 =
        {(P.edgePair i).1, (P.edgePair i).2} :=
    fun i => edgeLatticePoints_eq_endpoints _ _ (hprim i)
  have hrew :
      (Finset.univ.biUnion fun i : Fin P.nVertices =>
          edgeLatticePoints (P.edgePair i).1 (P.edgePair i).2) =
        Finset.univ.biUnion fun i : Fin P.nVertices =>
          {(P.edgePair i).1, (P.edgePair i).2} :=
    Finset.biUnion_congr rfl fun i _ => by rw [hedge i]
  rw [hrew]
  have hsub :
      (Finset.univ.biUnion fun i : Fin P.nVertices =>
          {(P.edgePair i).1, (P.edgePair i).2}) =
        Finset.univ.image P.vertex := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and, edgePair]
    constructor
    · rintro ⟨i, h | h⟩
      · exact ⟨i, h.symm⟩
      · exact ⟨P.nextIdx i, h.symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, Or.inl rfl⟩
  rw [hsub, Finset.card_image_of_injective _ hverts, Finset.card_univ,
    Fintype.card_fin]

/-- **Empty-interior shoelace identity** under primitive fan + primitive edges
(not classical Pick). -/
theorem shoelace_eq_B_div_two_sub_one_of_primitive_fan
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hnn : FanDetsNonneg P)
    (hprim : FanDetPrimitive P) :
    P.shoelace = (P.B : ℚ) / 2 - 1 := by
  have hB := B_eq_nVertices_of_primitive_edges P hedge hverts
  have harea := shoelace_eq_n_sub_two_div_two P hnn hprim hverts
  have hn : 3 ≤ P.nVertices := P.length_ge
  have : ((P.nVertices - 2 : ℕ) : ℚ) / 2 = (P.nVertices : ℚ) / 2 - 1 := by
    have : ((P.nVertices - 2 : ℕ) : ℚ) = (P.nVertices : ℚ) - 2 := by
      exact_mod_cast (Nat.cast_sub (by omega : 2 ≤ P.nVertices))
    rw [this]; ring
  rw [harea, this, hB]

theorem shoelace_pick_form_empty_interior_of_primitive_fan
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hnn : FanDetsNonneg P)
    (hprim : FanDetPrimitive P) :
    P.shoelace = (0 : ℚ) + (P.B : ℚ) / 2 - 1 := by
  simpa using shoelace_eq_B_div_two_sub_one_of_primitive_fan P hverts hedge hnn hprim

/-! ## Discharge `FanDetPrimitive` from empty fan triangles -/

/-- Each fan triangle contains no lattice points other than its three vertices. -/
def FanTrianglesEmpty : Prop :=
  ∀ (i : ℕ) (hi : i < P.nVertices - 2),
    ∀ p, MemClosedTriangle (fanTriangle P i hi).a (fanTriangle P i hi).b
        (fanTriangle P i hi).c p →
      p = (fanTriangle P i hi).a ∨ p = (fanTriangle P i hi).b ∨
        p = (fanTriangle P i hi).c

/-- Strictly positive oriented fan dets (nondegenerate + CCW). -/
def FanDetsPos : Prop :=
  ∀ (i : ℕ) (hi : i < P.nVertices - 2), 0 < fanDet P i hi

lemma FanDetsNonneg_of_pos (h : FanDetsPos P) : FanDetsNonneg P :=
  fun i hi => le_of_lt (h i hi)

/-- **Discharge fan-primitivity** from empty fan ears + nondegeneracy.
Uses `natAbs_det_eq_one_of_memClosedTriangle_eq_vertices`. -/
theorem FanDetPrimitive_of_empty_fan_triangles
    (hpos : FanDetsPos P) (hempty : FanTrianglesEmpty P) :
    FanDetPrimitive P := by
  intro i hi
  exact IsDetPrimitive_of_memClosedTriangle_eq_vertices
    (fanTriangle P i hi) (ne_of_gt (hpos i hi)) (hempty i hi)

/-- Empty-interior shoelace Pick-form with `FanDetPrimitive` discharged from
empty fan triangles (not classical Pick). -/
theorem shoelace_eq_B_div_two_sub_one_of_empty_fan
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hpos : FanDetsPos P)
    (hempty : FanTrianglesEmpty P) :
    P.shoelace = (P.B : ℚ) / 2 - 1 :=
  shoelace_eq_B_div_two_sub_one_of_primitive_fan P hverts hedge
    (FanDetsNonneg_of_pos P hpos)
    (FanDetPrimitive_of_empty_fan_triangles P hpos hempty)

/-! ## Empty polygon interior ⇒ empty fan triangles (convex / extreme vertices) -/

/-- Geometric empty-interior: no lattice points in the convex hull off the cyclic boundary.
Matches classical Pick `I = 0` when the polygon is convex (listed vertices extreme). -/
def EmptyInterior : Prop := P.interiorLatticePoints = ∅

/-- Every listed vertex is extreme in the convex hull of the vertex set.
True for convex lattice polygons in vertex order; rules out “foreign” vertices
inside fan ears. (`toReal` = `LatticeTriangle.toReal` = polygon embedding.) -/
def VerticesExtreme : Prop :=
  ∀ i : Fin P.nVertices,
    toReal (P.vertex i) ∉
      convexHull ℝ (toReal '' ((P.vertexFinset.erase (P.vertex i) : Set (ℤ × ℤ))))

lemma vertexFinset_eq_univ_image :
    P.vertexFinset = (Finset.univ : Finset (Fin P.nVertices)).image P.vertex := by
  ext p
  constructor
  · intro hp
    have hp' : p ∈ P.vertices := List.mem_toFinset.mp hp
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp'
    refine Finset.mem_image.mpr ⟨⟨i.1, ?_⟩, Finset.mem_univ _, rfl⟩
    simp [LatticePolygon.nVertices]
  · intro hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact List.mem_toFinset.mpr (List.get_mem P.vertices i)

/-- Primitive edges + distinct vertices ⇒ constructive boundary equals the vertex set. -/
theorem boundaryLatticePoints_eq_vertexFinset
    (hprim : PrimitiveEdges P) (_hverts : Function.Injective P.vertex) :
    P.boundaryLatticePoints = P.vertexFinset := by
  classical
  have hedge : ∀ i : Fin P.nVertices,
      edgeLatticePoints (P.edgePair i).1 (P.edgePair i).2 =
        {(P.edgePair i).1, (P.edgePair i).2} :=
    fun i => edgeLatticePoints_eq_endpoints _ _ (hprim i)
  have hrew :
      P.boundaryLatticePoints =
        Finset.univ.biUnion fun i : Fin P.nVertices =>
          {(P.edgePair i).1, (P.edgePair i).2} := by
    unfold LatticePolygon.boundaryLatticePoints
    exact Finset.biUnion_congr rfl fun i _ => by rw [hedge i]
  have hsub :
      (Finset.univ.biUnion fun i : Fin P.nVertices =>
          {(P.edgePair i).1, (P.edgePair i).2}) =
        Finset.univ.image P.vertex := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and, LatticePolygon.edgePair]
    constructor
    · rintro ⟨i, h | h⟩
      · exact ⟨i, h.symm⟩
      · exact ⟨P.nextIdx i, h.symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, Or.inl rfl⟩
  rw [hrew, hsub, vertexFinset_eq_univ_image P]

/-- Fan-triangle vertices lie among the polygon vertices. -/
lemma fanTriangle_vertices_mem_vertexFinset
    (i : ℕ) (hi : i < P.nVertices - 2) :
    (fanTriangle P i hi).a ∈ P.vertexFinset ∧
      (fanTriangle P i hi).b ∈ P.vertexFinset ∧
        (fanTriangle P i hi).c ∈ P.vertexFinset := by
  rw [vertexFinset_eq_univ_image]
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨⟨0, P.nVertices_pos⟩, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨⟨i + 1, by have := P.length_ge; omega⟩, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨⟨i + 2, by have := P.length_ge; omega⟩, Finset.mem_univ _, rfl⟩

/-- Closed fan triangle (barycentric) sits inside the polygon convex hull. -/
theorem mem_convexHullRegion_of_memClosedTriangle_fan
    (i : ℕ) (hi : i < P.nVertices - 2) {p : ℤ × ℤ}
    (hp : MemClosedTriangle (fanTriangle P i hi).a (fanTriangle P i hi).b
      (fanTriangle P i hi).c p) :
    toReal p ∈ P.convexHullRegion := by
  have htrip := mem_convexHull_of_memClosedTriangle _ _ _ _ hp
  have hv := fanTriangle_vertices_mem_vertexFinset P i hi
  have hsub : ({toReal (fanTriangle P i hi).a,
        toReal (fanTriangle P i hi).b,
        toReal (fanTriangle P i hi).c} : Set (ℝ × ℝ)) ⊆
      toReal '' (P.vertexFinset : Set (ℤ × ℤ)) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Set.mem_image_of_mem toReal hv.1
    · exact Set.mem_image_of_mem toReal hv.2.1
    · exact Set.mem_image_of_mem toReal hv.2.2
  have hmono := (convexHull_mono hsub) htrip
  simpa [LatticePolygon.convexHullRegion] using hmono

/-- **Prize (partial):** empty interior + primitive edges + extreme vertices ⇒
each fan ear meets lattice points only at its three vertices.

Key geometry: fan triangles ⊂ convex hull; with `PrimitiveEdges` the constructive
boundary is exactly the vertex set, so `I = ∅` leaves only listed vertices as
candidate lattice points in the hull; extremality rules out foreign vertices in
an ear. Not classical Pick (no Haar; triangulation existence still open). -/
theorem FanTrianglesEmpty_of_empty_interior
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hI : EmptyInterior P)
    (hext : VerticesExtreme P) :
    FanTrianglesEmpty P := by
  classical
  intro i hi p hp
  have hhull : toReal p ∈ P.convexHullRegion :=
    mem_convexHullRegion_of_memClosedTriangle_fan P i hi hp
  by_cases hb : p ∈ P.boundaryLatticePoints
  · have hbound := boundaryLatticePoints_eq_vertexFinset P hedge hverts
    have hpV : p ∈ P.vertexFinset := by simpa [hbound] using hb
    have hpV' : p ∈ (Finset.univ : Finset (Fin P.nVertices)).image P.vertex := by
      rwa [← vertexFinset_eq_univ_image P]
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hpV'
    subst hj
    by_cases hA : P.vertex j = (fanTriangle P i hi).a
    · exact Or.inl hA
    · by_cases hB : P.vertex j = (fanTriangle P i hi).b
      · exact Or.inr (Or.inl hB)
      · by_cases hC : P.vertex j = (fanTriangle P i hi).c
        · exact Or.inr (Or.inr hC)
        · exfalso
          have hv := fanTriangle_vertices_mem_vertexFinset P i hi
          have hae : (fanTriangle P i hi).a ∈ P.vertexFinset.erase (P.vertex j) :=
            Finset.mem_erase.mpr ⟨Ne.symm hA, hv.1⟩
          have hbe : (fanTriangle P i hi).b ∈ P.vertexFinset.erase (P.vertex j) :=
            Finset.mem_erase.mpr ⟨Ne.symm hB, hv.2.1⟩
          have hce : (fanTriangle P i hi).c ∈ P.vertexFinset.erase (P.vertex j) :=
            Finset.mem_erase.mpr ⟨Ne.symm hC, hv.2.2⟩
          have htrip := mem_convexHull_of_memClosedTriangle _ _ _ _ hp
          have hsub :
              ({toReal (fanTriangle P i hi).a,
                  toReal (fanTriangle P i hi).b,
                  toReal (fanTriangle P i hi).c} : Set (ℝ × ℝ)) ⊆
                toReal '' ((P.vertexFinset.erase (P.vertex j) : Set (ℤ × ℤ))) := by
            intro x hx
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
            rcases hx with rfl | rfl | rfl
            · exact Set.mem_image_of_mem toReal hae
            · exact Set.mem_image_of_mem toReal hbe
            · exact Set.mem_image_of_mem toReal hce
          exact hext j ((convexHull_mono hsub) htrip)
  · have hint : p ∈ P.interiorLatticePoints := by
      refine ⟨?_, hb⟩
      -- align `LatticeTriangle.toReal` with `Picks.toReal` in the region def
      simpa [LatticePolygon.convexHullRegion,
        show (toReal : ℤ × ℤ → ℝ × ℝ) = Picks.toReal from rfl] using hhull
    have : P.interiorLatticePoints = ∅ := hI
    exact (this ▸ hint).elim

/-- Empty-interior shoelace Pick-form under CCW fan + primitive edges + extreme
vertices (discharges `FanTrianglesEmpty` / fan-primitivity). Not classical Pick. -/
theorem shoelace_eq_B_div_two_sub_one_of_empty_interior
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hpos : FanDetsPos P)
    (hI : EmptyInterior P)
    (hext : VerticesExtreme P) :
    P.shoelace = (P.B : ℚ) / 2 - 1 :=
  shoelace_eq_B_div_two_sub_one_of_empty_fan P hverts hedge hpos
    (FanTrianglesEmpty_of_empty_interior P hverts hedge hI hext)

/-- Every listed vertex lies weakly left of every directed edge (CCW convex). -/
def ConvexCCW : Prop :=
  ∀ i j : Fin P.nVertices,
    0 ≤ latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j)

/-- Strict local left turn at every vertex (no three consecutive collinear). -/
def LocalCCWTurns : Prop :=
  ∀ i : Fin P.nVertices,
    0 < latticeDet (P.vertex (P.prevIdx i)) (P.vertex i) (P.vertex (P.nextIdx i))

/-- Strict CCW convexity: edge half-plane conditions + strict local turns. -/
def StrictlyConvexCCW : Prop := ConvexCCW P ∧ LocalCCWTurns P

lemma det_nonneg_prev_of_ConvexCCW (h : ConvexCCW P) (i j : Fin P.nVertices) :
    0 ≤ latticeDet (P.vertex (P.prevIdx i)) (P.vertex i) (P.vertex j) := by
  simpa [P.nextIdx_prevIdx i] using h (P.prevIdx i) j

/-- **Discharge:** strict CCW convexity ⇒ every listed vertex is extreme in the
vertex convex hull. -/
theorem VerticesExtreme_of_strictlyConvexCCW
    (hsc : StrictlyConvexCCW P) (_hinj : Function.Injective P.vertex) :
    VerticesExtreme P := by
  classical
  intro i hi
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ :=
    (mem_convexHull_iff_exists_fintype (R := ℝ) (E := ℝ × ℝ)).1 hi
  set A := toReal (P.vertex (P.prevIdx i))
  set B := toReal (P.vertex i)
  set C := toReal (P.vertex (P.nextIdx i))
  have hturn : 0 < latticeDet (P.vertex (P.prevIdx i)) (P.vertex i) (P.vertex (P.nextIdx i)) :=
    hsc.2 i
  have hne : detR A B C ≠ 0 := by
    intro h0
    have : (latticeDet (P.vertex (P.prevIdx i)) (P.vertex i)
        (P.vertex (P.nextIdx i)) : ℝ) = 0 := by
      simpa [A, B, C, detR_toReal] using h0
    exact (ne_of_gt hturn) (Int.cast_eq_zero.mp this)
  have hφ_nonneg : ∀ j : Fin P.nVertices, 0 ≤ detR A B (toReal (P.vertex j)) := by
    intro j
    have hZ := det_nonneg_prev_of_ConvexCCW P hsc.1 i j
    have : (0 : ℝ) ≤ (latticeDet (P.vertex (P.prevIdx i)) (P.vertex i) (P.vertex j) : ℝ) :=
      Int.cast_nonneg hZ
    simpa [A, B, detR_toReal] using this
  have hψ_nonneg : ∀ j : Fin P.nVertices, 0 ≤ detR B C (toReal (P.vertex j)) := by
    intro j
    have hZ := hsc.1 i j
    have : (0 : ℝ) ≤ (latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j) : ℝ) :=
      Int.cast_nonneg hZ
    simpa [B, C, detR_toReal] using this
  have hφB : detR A B B = 0 := by dsimp [detR]; ring
  have hψB : detR B C B = 0 := by dsimp [detR]; ring
  have hsum' : ∑ k, w k • z k = B := by simpa [B] using hsum
  have hφ_sum : ∑ k, w k * detR A B (z k) = 0 := by
    have := detR_sum_smul A B w z hw1
    simpa [hsum', hφB] using this.symm
  have hψ_sum : ∑ k, w k * detR B C (z k) = 0 := by
    have := detR_sum_smul B C w z hw1
    simpa [hsum', hψB] using this.symm
  have hz' : ∀ k, ∃ j : Fin P.nVertices,
      z k = toReal (P.vertex j) ∧ P.vertex j ≠ P.vertex i := by
    intro k
    obtain ⟨p, hp, heq⟩ := (Set.mem_image _ _ _).1 (hz k)
    have hpE := Finset.mem_erase.mp hp
    have hpV : p ∈ (Finset.univ : Finset (Fin P.nVertices)).image P.vertex := by
      rw [← vertexFinset_eq_univ_image P]
      exact hpE.2
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hpV
    refine ⟨j, ?_, ?_⟩
    · rw [← heq, ← hj]
    · intro hvji
      exact hpE.1 (by rw [← hj, hvji])
  have hφz : ∀ k, 0 ≤ detR A B (z k) := by
    intro k; obtain ⟨j, hj, _⟩ := hz' k; simpa [hj] using hφ_nonneg j
  have hψz : ∀ k, 0 ≤ detR B C (z k) := by
    intro k; obtain ⟨j, hj, _⟩ := hz' k; simpa [hj] using hψ_nonneg j
  have hφ_term : ∀ k, w k * detR A B (z k) = 0 := by
    intro k
    have hnn : ∀ k ∈ (Finset.univ : Finset ι), 0 ≤ w k * detR A B (z k) :=
      fun k _ => mul_nonneg (hw0 k) (hφz k)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hφ_sum k (Finset.mem_univ k)
  have hψ_term : ∀ k, w k * detR B C (z k) = 0 := by
    intro k
    have hnn : ∀ k ∈ (Finset.univ : Finset ι), 0 ≤ w k * detR B C (z k) :=
      fun k _ => mul_nonneg (hw0 k) (hψz k)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hψ_sum k (Finset.mem_univ k)
  obtain ⟨k0, hk0⟩ : ∃ k, 0 < w k := by
    by_contra h
    push Not at h
    have hz0 : ∀ k, w k = 0 := fun k => le_antisymm (h k) (hw0 k)
    have : (∑ k, w k) = 0 := by simp [hz0]
    linarith [hw1]
  have hφ0 : detR A B (z k0) = 0 :=
    (mul_eq_zero.mp (hφ_term k0)).resolve_left (ne_of_gt hk0)
  have hψ0 : detR B C (z k0) = 0 :=
    (mul_eq_zero.mp (hψ_term k0)).resolve_left (ne_of_gt hk0)
  have hzB : z k0 = B := eq_of_detR_corner A B C (z k0) hne hφ0 hψ0
  obtain ⟨j, hj, hne_j⟩ := hz' k0
  have : P.vertex j = P.vertex i :=
    toReal_injective (by simpa [hj, B] using hzB)
  exact hne_j this

/-- Fan dets are nonnegative for a CCW-convex polygon. -/
theorem FanDetsNonneg_of_ConvexCCW (h : ConvexCCW P) : FanDetsNonneg P := by
  intro i hi
  have hidx1 : i + 1 < P.nVertices := by have := P.length_ge; omega
  have hidx2 : i + 2 < P.nVertices := by have := P.length_ge; omega
  have hnext : P.nextIdx ⟨i + 1, hidx1⟩ = ⟨i + 2, hidx2⟩ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt hidx2
  have hge : 0 ≤ latticeDet (P.vertex ⟨i + 1, hidx1⟩) (P.vertex ⟨i + 2, hidx2⟩)
      (P.vertex ⟨0, P.nVertices_pos⟩) := by
    simpa [hnext] using h ⟨i + 1, hidx1⟩ ⟨0, P.nVertices_pos⟩
  have hcyc :
      latticeDet (P.vertex ⟨0, P.nVertices_pos⟩) (P.vertex ⟨i + 1, hidx1⟩)
        (P.vertex ⟨i + 2, hidx2⟩) =
      latticeDet (P.vertex ⟨i + 1, hidx1⟩) (P.vertex ⟨i + 2, hidx2⟩)
        (P.vertex ⟨0, P.nVertices_pos⟩) := by
    unfold latticeDet; ring
  -- fanDet = Triangle.det = latticeDet a b c
  simpa [fanDet, fanTriangle, Triangle.det, hcyc] using hge

/-- Empty-interior shoelace Pick-form with `VerticesExtreme` discharged from
`StrictlyConvexCCW` (not classical Pick). -/
theorem shoelace_eq_B_div_two_sub_one_of_empty_interior_convex
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hpos : FanDetsPos P)
    (hI : EmptyInterior P)
    (hsc : StrictlyConvexCCW P) :
    P.shoelace = (P.B : ℚ) / 2 - 1 :=
  shoelace_eq_B_div_two_sub_one_of_empty_interior P hverts hedge hpos hI
    (VerticesExtreme_of_strictlyConvexCCW P hsc hverts)


end LatticeFan

end Picks
end EulersGem
