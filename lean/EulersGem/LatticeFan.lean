/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.Tactic
import Mathlib.Data.Rat.Defs
import EulersGem.LatticeTriangle
import EulersGem.LatticePolygon
import EulersGem.Picks

/-!
# Geometric fan triangulation of a lattice polygon

Algebraic shoelace fan identity + empty-interior Pick-form under fan
primitivity / primitive edges.

**Honesty / not classical Pick:**
* Fan primitivity is a hypothesis (`empty ⇒ |det|=1` still open).
* Shoelace ≠ Haar/Lebesgue.
* Consistent orientation is a hyp (`0 ≤ fanDet`).
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

end LatticeFan
end Picks
end EulersGem
