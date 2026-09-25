/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.LatticeFanInduction

/-!
# Edge-split substrate for triangle Pick without `PrimitiveEdges` (not classical Pick)

`edgeStep` + shoelace/B additivity + empty-interior ⇒ `edgeGcd(edgeStep, c) = 1`.
Intended next: empty-interior triangle Pick by `|det|` induction, then I ≤ 2
general ears, then hyp-light I = 4 (drop spokes-empty apex).

Shoelace ≠ Haar. Classical Pick FAIL. See `PICKS_CLAUDE_AUDIT.md`.
-/

namespace EulersGem
namespace Picks
namespace LatticeFan
namespace InteriorFan

open LatticeTriangle
open LatticePolygon
open BigOperators

/-! ## Edge step (first open lattice point on a non-primitive edge) -/

/-- First open lattice point on `a—b` (`k = 1` in the edge parametrization). -/
def edgeStep (a b : ℤ × ℤ) : ℤ × ℤ :=
  (a.1 + (b.1 - a.1) / (edgeGcd a b : ℤ),
   a.2 + (b.2 - a.2) / (edgeGcd a b : ℤ))

private lemma mul_edgeGcd_edgeStep_sub (a b : ℤ × ℤ) :
    (edgeGcd a b : ℤ) * ((edgeStep a b).1 - a.1) = b.1 - a.1 ∧
      (edgeGcd a b : ℤ) * ((edgeStep a b).2 - a.2) = b.2 - a.2 := by
  have hdx : (edgeGcd a b : ℤ) ∣ (b.1 - a.1) := by
    simpa [edgeGcd] using Int.gcd_dvd_left (b.1 - a.1) (b.2 - a.2)
  have hdy : (edgeGcd a b : ℤ) ∣ (b.2 - a.2) := by
    simpa [edgeGcd] using Int.gcd_dvd_right (b.1 - a.1) (b.2 - a.2)
  constructor
  · have := Int.mul_ediv_cancel' hdx
    simp only [edgeStep]
    convert this using 1
    ring
  · have := Int.mul_ediv_cancel' hdy
    simp only [edgeStep]
    convert this using 1
    ring

lemma edgeStep_mem_edgeLatticePoints (a b : ℤ × ℤ) (hd : 1 ≤ edgeGcd a b) :
    edgeStep a b ∈ edgeLatticePoints a b := by
  classical
  have hd0 : edgeGcd a b ≠ 0 := by omega
  simp only [edgeLatticePoints, edgeStep, hd0, ↓reduceIte]
  refine Finset.mem_image.mpr ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
  simp

lemma edgeStep_ne_left (a b : ℤ × ℤ) (hd : 1 ≤ edgeGcd a b) :
    edgeStep a b ≠ a := by
  intro h
  obtain ⟨hx, hy⟩ := mul_edgeGcd_edgeStep_sub a b
  simp only [h, sub_self, mul_zero] at hx hy
  have hab : a = b := Prod.ext (by linarith) (by linarith)
  have : edgeGcd a b = 0 := (edgeGcd_eq_zero_iff a b).mpr hab
  omega

lemma edgeStep_ne_right (a b : ℤ × ℤ) (hd : 2 ≤ edgeGcd a b) :
    edgeStep a b ≠ b := by
  intro h
  obtain ⟨hx, hy⟩ := mul_edgeGcd_edgeStep_sub a b
  have h1 : (edgeStep a b).1 = b.1 := congrArg Prod.fst h
  have h2 : (edgeStep a b).2 = b.2 := congrArg Prod.snd h
  rw [h1] at hx
  rw [h2] at hy
  have hx2 : ((edgeGcd a b : ℤ) - 1) * (b.1 - a.1) = 0 := by linarith
  have hy2 : ((edgeGcd a b : ℤ) - 1) * (b.2 - a.2) = 0 := by linarith
  have hne : (edgeGcd a b : ℤ) - 1 ≠ 0 := by
    have : (1 : ℤ) < edgeGcd a b := by exact_mod_cast (by omega : 1 < edgeGcd a b)
    linarith
  have hb1 : b.1 - a.1 = 0 := (mul_eq_zero.mp hx2).resolve_left hne
  have hb2 : b.2 - a.2 = 0 := (mul_eq_zero.mp hy2).resolve_left hne
  have hab : a = b := Prod.ext (by linarith) (by linarith)
  have : edgeGcd a b = 0 := (edgeGcd_eq_zero_iff a b).mpr hab
  omega

/-- Left half of the edge step is primitive. -/
lemma edgeGcd_edgeStep_left (a b : ℤ × ℤ) (hd : 1 ≤ edgeGcd a b) :
    edgeGcd a (edgeStep a b) = 1 := by
  set d := edgeGcd a b
  set p := edgeStep a b
  obtain ⟨hx, hy⟩ := mul_edgeGcd_edgeStep_sub a b
  have hx' : (d : ℤ) * (p.1 - a.1) = b.1 - a.1 := by simpa [d, p] using hx
  have hy' : (d : ℤ) * (p.2 - a.2) = b.2 - a.2 := by simpa [d, p] using hy
  have hgcd_ab : Int.gcd (b.1 - a.1) (b.2 - a.2) = d := by simp [edgeGcd, d]
  have hmul := Int.gcd_mul_left (d : ℤ) (p.1 - a.1) (p.2 - a.2)
  have hcalc :
      d = Int.natAbs (d : ℤ) * Int.gcd (p.1 - a.1) (p.2 - a.2) := by
    calc
      d = Int.gcd (b.1 - a.1) (b.2 - a.2) := hgcd_ab.symm
      _ = Int.gcd ((d : ℤ) * (p.1 - a.1)) ((d : ℤ) * (p.2 - a.2)) := by rw [← hx', ← hy']
      _ = Int.natAbs (d : ℤ) * Int.gcd (p.1 - a.1) (p.2 - a.2) := hmul
  have habs : Int.natAbs (d : ℤ) = d := Int.natAbs_natCast d
  have hgcd : Int.gcd (p.1 - a.1) (p.2 - a.2) = 1 := by
    have : d = d * Int.gcd (p.1 - a.1) (p.2 - a.2) := by simpa [habs] using hcalc
    have hdpos : 0 < d := hd
    exact (Nat.mul_left_cancel_iff hdpos).mp (by linarith)
  simpa [edgeGcd, p] using hgcd

/-- Right residual content after the edge step. -/
lemma edgeGcd_edgeStep_right (a b : ℤ × ℤ) (hd : 2 ≤ edgeGcd a b) :
    edgeGcd (edgeStep a b) b = edgeGcd a b - 1 := by
  set d := edgeGcd a b
  set p := edgeStep a b
  obtain ⟨hx, hy⟩ := mul_edgeGcd_edgeStep_sub a b
  have hx' : (d : ℤ) * (p.1 - a.1) = b.1 - a.1 := by simpa [d, p] using hx
  have hy' : (d : ℤ) * (p.2 - a.2) = b.2 - a.2 := by simpa [d, p] using hy
  have hx2 : b.1 - p.1 = ((d : ℤ) - 1) * (p.1 - a.1) := by
    have : b.1 - p.1 = (b.1 - a.1) - (p.1 - a.1) := by ring
    rw [this, ← hx']; ring
  have hy2 : b.2 - p.2 = ((d : ℤ) - 1) * (p.2 - a.2) := by
    have : b.2 - p.2 = (b.2 - a.2) - (p.2 - a.2) := by ring
    rw [this, ← hy']; ring
  have hleft : Int.gcd (p.1 - a.1) (p.2 - a.2) = 1 := by
    have := edgeGcd_edgeStep_left a b (by omega)
    simpa [edgeGcd, p] using this
  have hmul := Int.gcd_mul_left ((d : ℤ) - 1) (p.1 - a.1) (p.2 - a.2)
  have hcalc :
      Int.gcd (b.1 - p.1) (b.2 - p.2) =
        Int.natAbs ((d : ℤ) - 1) * Int.gcd (p.1 - a.1) (p.2 - a.2) := by
    calc
      Int.gcd (b.1 - p.1) (b.2 - p.2)
          = Int.gcd (((d : ℤ) - 1) * (p.1 - a.1)) (((d : ℤ) - 1) * (p.2 - a.2)) := by
              rw [hx2, hy2]
      _ = _ := hmul
  have hnonneg : (0 : ℤ) ≤ (d : ℤ) - 1 := by
    have : (1 : ℤ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    linarith
  have habs : Int.natAbs ((d : ℤ) - 1) = d - 1 := by omega
  have : Int.gcd (b.1 - p.1) (b.2 - p.2) = d - 1 := by
    rw [hcalc, habs, hleft, mul_one]
  simpa [edgeGcd, p, d] using this

/-- `det(a, edgeStep, c) * edgeGcd = det(a,b,c)`. -/
lemma latticeDet_edgeStep_mul (a b c : ℤ × ℤ) (_hd : 1 ≤ edgeGcd a b) :
    latticeDet a (edgeStep a b) c * (edgeGcd a b : ℤ) = latticeDet a b c := by
  obtain ⟨hx, hy⟩ := mul_edgeGcd_edgeStep_sub a b
  set d := edgeGcd a b
  set p := edgeStep a b
  have hx' : (d : ℤ) * (p.1 - a.1) = b.1 - a.1 := by simpa [d, p] using hx
  have hy' : (d : ℤ) * (p.2 - a.2) = b.2 - a.2 := by simpa [d, p] using hy
  calc
    latticeDet a p c * (d : ℤ)
        = ((p.1 - a.1) * (c.2 - a.2) - (p.2 - a.2) * (c.1 - a.1)) * (d : ℤ) := by
            rfl
    _ = ((d : ℤ) * (p.1 - a.1)) * (c.2 - a.2) -
          ((d : ℤ) * (p.2 - a.2)) * (c.1 - a.1) := by ring
    _ = (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) := by rw [hx', hy']
    _ = latticeDet a b c := by rfl

lemma latticeDet_edgeStep_pos (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 1 ≤ edgeGcd a b) :
    0 < latticeDet a (edgeStep a b) c := by
  have hmul := latticeDet_edgeStep_mul a b c hd
  have hdpos : (0 : ℤ) < edgeGcd a b := by exact_mod_cast hd
  nlinarith

lemma latticeDet_edgeStep_right_pos (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b) :
    0 < latticeDet (edgeStep a b) b c := by
  have hmem := edgeStep_mem_edgeLatticePoints a b (by omega)
  have hadd := latticeDet_add_of_mem_edgeLatticePoints a b c (edgeStep a b) hmem
  have hmul := latticeDet_edgeStep_mul a b c (by omega)
  have h1 : (1 : ℤ) < edgeGcd a b := by exact_mod_cast (by omega : 1 < edgeGcd a b)
  nlinarith [latticeDet_edgeStep_pos a b c hD (by omega : 1 ≤ edgeGcd a b)]


/-! ## Empty-interior triangle Pick without `PrimitiveEdges`

Edge-split induction on `|det|`. Base: `PrimitiveEdges` ⇒ existing empty-interior
convex Pick-form. Step: split along `edgeStep` of a non-primitive edge; both
sub-triangles inherit empty interior and strictly smaller positive det.
-/

lemma shoelace_add_of_edgeStep (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b) :
    (trianglePolygon a b c).shoelace =
      (trianglePolygon a (edgeStep a b) c).shoelace +
        (trianglePolygon (edgeStep a b) b c).shoelace := by
  set p := edgeStep a b
  have hmem := edgeStep_mem_edgeLatticePoints a b (by omega)
  have hadd := latticeDet_add_of_mem_edgeLatticePoints a b c p hmem
  have h1 := latticeDet_edgeStep_pos a b c hD (by omega)
  have h2 := latticeDet_edgeStep_right_pos a b c hD hd
  have hsa := shoelace_trianglePolygon_eq_half_natAbs_det a b c
  have hs1 := shoelace_trianglePolygon_eq_half_natAbs_det a p c
  have hs2 := shoelace_trianglePolygon_eq_half_natAbs_det p b c
  have hnn : 0 ≤ latticeDet a b c := le_of_lt hD
  have e0 : (Int.natAbs (latticeDet a b c) : ℚ) = (latticeDet a b c : ℚ) := by
    rw [← Int.cast_natCast (R := ℚ), Int.natAbs_of_nonneg hnn]
  have e1 : (Int.natAbs (latticeDet a p c) : ℚ) = (latticeDet a p c : ℚ) := by
    rw [← Int.cast_natCast (R := ℚ), Int.natAbs_of_nonneg (le_of_lt h1)]
  have e2 : (Int.natAbs (latticeDet p b c) : ℚ) = (latticeDet p b c : ℚ) := by
    rw [← Int.cast_natCast (R := ℚ), Int.natAbs_of_nonneg (le_of_lt h2)]
  have hsum : (latticeDet a b c : ℚ) = (latticeDet a p c : ℚ) + (latticeDet p b c : ℚ) := by
    exact_mod_cast hadd
  calc
    (trianglePolygon a b c).shoelace
        = (Int.natAbs (latticeDet a b c) : ℚ) / 2 := hsa
    _ = (latticeDet a b c : ℚ) / 2 := by rw [e0]
    _ = ((latticeDet a p c : ℚ) + (latticeDet p b c : ℚ)) / 2 := by rw [hsum]
    _ = (latticeDet a p c : ℚ) / 2 + (latticeDet p b c : ℚ) / 2 := by ring
    _ = (Int.natAbs (latticeDet a p c) : ℚ) / 2 +
          (Int.natAbs (latticeDet p b c) : ℚ) / 2 := by rw [e1, e2]
    _ = (trianglePolygon a p c).shoelace + (trianglePolygon p b c).shoelace := by
          rw [hs1, hs2]

/-- B-additivity across an edge-step split (not classical Pick). -/
lemma B_add_of_edgeStep (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    (hpc : edgeGcd (edgeStep a b) c = 1) :
    (trianglePolygon a (edgeStep a b) c).B + (trianglePolygon (edgeStep a b) b c).B =
      (trianglePolygon a b c).B + 2 := by
  set p := edgeStep a b
  set d := edgeGcd a b
  have hD1 : latticeDet a p c ≠ 0 := ne_of_gt (latticeDet_edgeStep_pos a b c hD (by omega))
  have hD2 : latticeDet p b c ≠ 0 := ne_of_gt (latticeDet_edgeStep_right_pos a b c hD hd)
  have hD0 : latticeDet a b c ≠ 0 := ne_of_gt hD
  have hB := B_trianglePolygon_eq_sum_edgeGcd a b c hD0
  have hB1 := B_trianglePolygon_eq_sum_edgeGcd a p c hD1
  have hB2 := B_trianglePolygon_eq_sum_edgeGcd p b c hD2
  have hL := edgeGcd_edgeStep_left a b (by omega)
  have hR := edgeGcd_edgeStep_right a b hd
  -- B1 = gcd(a,p)+gcd(p,c)+gcd(c,a) = 1 + 1 + gcd(c,a)
  -- B2 = gcd(p,b)+gcd(b,c)+gcd(c,p) = (d-1) + gcd(b,c) + 1
  -- sum = d + gcd(b,c) + gcd(c,a) + 2 = B + 2
  have hpc' : edgeGcd c p = 1 := by simpa [edgeGcd_comm p c] using hpc
  calc
    (trianglePolygon a p c).B + (trianglePolygon p b c).B
        = (edgeGcd a p + edgeGcd p c + edgeGcd c a) +
            (edgeGcd p b + edgeGcd b c + edgeGcd c p) := by
              rw [hB1, hB2]
    _ = (1 + 1 + edgeGcd c a) + ((d - 1) + edgeGcd b c + 1) := by
          simp [p, d, hL, hR, hpc, hpc']
    _ = d + edgeGcd b c + edgeGcd c a + 2 := by
          have : 1 ≤ d := by omega
          omega
    _ = (edgeGcd a b + edgeGcd b c + edgeGcd c a) + 2 := by
          simp [d]
    _ = (trianglePolygon a b c).B + 2 := by rw [hB]



/-- Real expansion of `detR` along `(1-t)•p + t•c`. -/
lemma detR_segment (a b p c : ℝ × ℝ) (t : ℝ) :
    detR a b ((1 - t) • p + t • c) =
      (1 - t) * detR a b p + t * detR a b c := by
  dsimp [detR, Prod.smul_def, smul_eq_mul]
  ring

/-- `latticeDet a b` along a segment from an `ab`-collinear point to `c`. -/
lemma latticeDet_ab_of_segment_from_edge
    (a b c p r : ℤ × ℤ) (t : ℝ)
    (hp0 : latticeDet a b p = 0)
    (hr_eq : (1 - t) • toReal p + t • toReal c = toReal r) :
    (latticeDet a b r : ℝ) = t * (latticeDet a b c : ℝ) := by
  have h0p : detR (toReal a) (toReal b) (toReal p) = 0 := by
    simpa [detR_toReal] using congrArg (Int.cast (R := ℝ)) hp0
  calc
    (latticeDet a b r : ℝ)
        = detR (toReal a) (toReal b) (toReal r) := (detR_toReal a b r).symm
    _ = detR (toReal a) (toReal b) ((1 - t) • toReal p + t • toReal c) := by rw [← hr_eq]
    _ = (1 - t) * detR (toReal a) (toReal b) (toReal p) +
          t * detR (toReal a) (toReal b) (toReal c) := detR_segment _ _ _ _ _
    _ = t * (latticeDet a b c : ℝ) := by rw [h0p, detR_toReal]; ring

/-- Parent-empty ⇒ `edgeGcd (edgeStep a b) c = 1` (not classical Pick). -/
theorem edgeGcd_eq_one_of_empty_interior_edgeStep
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    (hI : EmptyInterior (trianglePolygon a b c)) :
    edgeGcd (edgeStep a b) c = 1 := by
  classical
  set p := edgeStep a b
  by_contra hne
  have hge : 2 ≤ edgeGcd p c := by
    have hz : edgeGcd p c ≠ 0 := by
      intro h0
      have hpc : p = c := (edgeGcd_eq_zero_iff p c).mp h0
      have hp := edgeStep_mem_edgeLatticePoints a b (by omega)
      have : latticeDet a b c = 0 := by
        simpa [hpc] using latticeDet_eq_zero_of_mem_edge_ab a b p hp
      omega
    omega
  obtain ⟨r, hr, hrne_p, hrne_c⟩ :=
    exists_strict_mem_edgeLatticePoints_of_edgeGcd_ge_two p c hge
  have hp := edgeStep_mem_edgeLatticePoints a b (by omega)
  have hp0 : latticeDet a b p = 0 := latticeDet_eq_zero_of_mem_edge_ab a b p hp
  have hr_seg := mem_segment_of_mem_edgeLatticePoints p c r hr
  have ⟨t, ht, hr_eq⟩ : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 1) ∧
      (1 - t) • toReal p + t • toReal c = toReal r := by
    simpa [segment_eq_image] using hr_seg
  have ht0 := ht.1
  have ht1 := ht.2
  have ht_pos : 0 < t := by
    by_contra h
    have ht' : t = 0 := le_antisymm (le_of_not_gt h) ht0
    have : toReal r = toReal p := by simpa [ht'] using hr_eq.symm
    exact hrne_p (toReal_injective this)
  have ht_lt : t < 1 := by
    by_contra h
    have ht' : t = 1 := le_antisymm ht1 (le_of_not_gt h)
    have : toReal r = toReal c := by simpa [ht'] using hr_eq.symm
    exact hrne_c (toReal_injective this)
  set S : Set (ℝ × ℝ) := {toReal a, toReal b, toReal c}
  have hp_seg := mem_segment_of_mem_edgeLatticePoints a b p hp
  have haS : toReal a ∈ S := by simp [S]
  have hbS : toReal b ∈ S := by simp [S]
  have hcS : toReal c ∈ S := by simp [S]
  have hab_sub : segment ℝ (toReal a) (toReal b) ⊆ convexHull ℝ S :=
    segment_subset_convexHull haS hbS
  have hp_hull : toReal p ∈ convexHull ℝ S := hab_sub hp_seg
  have hc_hull : toReal c ∈ convexHull ℝ S := subset_convexHull ℝ S hcS
  have hpc_sub : segment ℝ (toReal p) (toReal c) ⊆ convexHull ℝ S :=
    (convex_convexHull ℝ S).segment_subset hp_hull hc_hull
  have hr_hull : toReal r ∈ convexHull ℝ S := hpc_sub hr_seg
  have hnot_ab : r ∉ edgeLatticePoints a b := by
    intro hab
    have hr0 : latticeDet a b r = 0 := latticeDet_eq_zero_of_mem_edge_ab a b r hab
    have hform := latticeDet_ab_of_segment_from_edge a b c p r t hp0 hr_eq
    have : (0 : ℝ) = t * (latticeDet a b c : ℝ) := by simpa [hr0] using hform
    have hDpos : (0 : ℝ) < latticeDet a b c := by exact_mod_cast hD
    nlinarith
  have hD2 : 0 < latticeDet p b c := latticeDet_edgeStep_right_pos a b c hD hd
  have hnot_bc : r ∉ edgeLatticePoints b c := by
    intro hbc
    have hcp : r ∈ edgeLatticePoints c p := mem_edgeLatticePoints_comm hr
    have := eq_of_mem_edgeLatticePoints_bc_ca p b c r (ne_of_gt hD2) hbc hcp
    exact hrne_c this
  have hD1 : 0 < latticeDet a p c := latticeDet_edgeStep_pos a b c hD (by omega)
  have hnot_ca : r ∉ edgeLatticePoints c a := by
    intro hca
    have hpc : r ∈ edgeLatticePoints p c := hr
    have := eq_of_mem_edgeLatticePoints_bc_ca a p c r (ne_of_gt hD1) hpc hca
    exact hrne_c this
  have hoff : OffTriangleBoundary a b c r := ⟨hnot_ab, hnot_bc, hnot_ca⟩
  have hmem : MemClosedTriangle a b c r :=
    memClosedTriangle_of_mem_convexHull a b c r (by simpa [S, trianglePolygon_convexHullRegion] using
      (show toReal r ∈ (trianglePolygon a b c).convexHullRegion from by
        simpa [trianglePolygon_convexHullRegion, S] using hr_hull))
  have hint : r ∈ (trianglePolygon a b c).interiorLatticePoints :=
    (mem_interiorLatticePoints_trianglePolygon_iff a b c r).mpr ⟨hmem, hoff⟩
  have hempty : (trianglePolygon a b c).interiorLatticePoints = ∅ := hI
  exact (by simp [hempty] : r ∉ (trianglePolygon a b c).interiorLatticePoints) hint



end InteriorFan
end LatticeFan
end Picks
end EulersGem
