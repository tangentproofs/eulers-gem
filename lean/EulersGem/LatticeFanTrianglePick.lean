/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.LatticeFanInduction

/-!
# Empty-interior triangle Pick without `PrimitiveEdges` (not classical Pick)

`edgeStep` split arithmetic + `|det|` induction: empty closed lattice triangle
(no interior points; edges may be non-primitive) satisfies
`shoelace = B/2 − 1`. EmptyInterior inherits across edge-steps; new chord is
primitive under parent-empty.

UniqueInterior substrate without `PrimitiveEdges`: generalized B-add,
chord-interior, `edgeGcd ≤ 2`, half-inheritance, and both-halves-empty when
`edgeGcd(chord)=2`. Full UniqueInterior Pick (g=1 locate-half) / I≤2 / I=4
without spokes-empty still open. Shoelace ≠ Haar. Classical Pick FAIL. See
`PICKS_CLAUDE_AUDIT.md`.
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



/-! ## EmptyInterior / shoelace / B under cyclic rotation -/

lemma trianglePolygon_convexHullRegion_cyclic (a b c : ℤ × ℤ) :
    (trianglePolygon a b c).convexHullRegion =
      (trianglePolygon b c a).convexHullRegion := by
  simp only [trianglePolygon_convexHullRegion]
  congr 1
  ext x
  simp [or_left_comm, or_comm]

lemma boundaryLatticePoints_trianglePolygon_cyclic (a b c : ℤ × ℤ) :
    (trianglePolygon a b c).boundaryLatticePoints =
      (trianglePolygon b c a).boundaryLatticePoints := by
  simp only [boundaryLatticePoints_trianglePolygon]
  ext p
  simp [Finset.mem_union, or_left_comm, or_comm]

lemma interiorLatticePoints_trianglePolygon_cyclic (a b c : ℤ × ℤ) :
    (trianglePolygon a b c).interiorLatticePoints =
      (trianglePolygon b c a).interiorLatticePoints := by
  ext p
  simp only [LatticePolygon.interiorLatticePoints,
    trianglePolygon_convexHullRegion_cyclic a b c,
    boundaryLatticePoints_trianglePolygon_cyclic a b c]

lemma EmptyInterior_trianglePolygon_cyclic (a b c : ℤ × ℤ) :
    EmptyInterior (trianglePolygon a b c) ↔
      EmptyInterior (trianglePolygon b c a) := by
  simp only [EmptyInterior]
  rw [interiorLatticePoints_trianglePolygon_cyclic]

lemma shoelace_trianglePolygon_cyclic (a b c : ℤ × ℤ) :
    (trianglePolygon a b c).shoelace = (trianglePolygon b c a).shoelace := by
  rw [shoelace_trianglePolygon_eq_half_natAbs_det,
      shoelace_trianglePolygon_eq_half_natAbs_det, latticeDet_cyclic]

lemma B_trianglePolygon_cyclic (a b c : ℤ × ℤ) (hne : latticeDet a b c ≠ 0) :
    (trianglePolygon a b c).B = (trianglePolygon b c a).B := by
  have hne' : latticeDet b c a ≠ 0 := by simpa [← latticeDet_cyclic a b c] using hne
  rw [B_trianglePolygon_eq_sum_edgeGcd a b c hne,
      B_trianglePolygon_eq_sum_edgeGcd b c a hne']
  ac_rfl

/-! ## `|det|` decrease across edgeStep -/

lemma natAbs_latticeDet_edgeStep_lt (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b) :
    Int.natAbs (latticeDet a (edgeStep a b) c) < Int.natAbs (latticeDet a b c) ∧
      Int.natAbs (latticeDet (edgeStep a b) b c) < Int.natAbs (latticeDet a b c) := by
  set p := edgeStep a b
  set d := edgeGcd a b
  have hmul : latticeDet a p c * (d : ℤ) = latticeDet a b c := by
    simpa [p, d] using latticeDet_edgeStep_mul a b c (by omega : 1 ≤ d)
  have h1 := latticeDet_edgeStep_pos a b c hD (by omega : 1 ≤ d)
  have h2 := latticeDet_edgeStep_right_pos a b c hD hd
  have hadd : latticeDet a b c = latticeDet a p c + latticeDet p b c :=
    latticeDet_add_of_mem_edgeLatticePoints a b c p
      (edgeStep_mem_edgeLatticePoints a b (by omega))
  have hnn1 : 0 ≤ latticeDet a p c := le_of_lt h1
  have hnn2 : 0 ≤ latticeDet p b c := le_of_lt h2
  have hAbs :
      Int.natAbs (latticeDet a p c) * d = Int.natAbs (latticeDet a b c) := by
    have := congrArg Int.natAbs hmul
    rwa [Int.natAbs_mul, Int.natAbs_natCast d] at this
  have hlt1 : Int.natAbs (latticeDet a p c) < Int.natAbs (latticeDet a b c) := by
    have hpos : 0 < Int.natAbs (latticeDet a p c) := Int.natAbs_pos.mpr (ne_of_gt h1)
    nlinarith [hAbs, (by omega : 1 < d)]
  have hlt2 : Int.natAbs (latticeDet p b c) < Int.natAbs (latticeDet a b c) := by
    have hsum :
        Int.natAbs (latticeDet a b c) =
          Int.natAbs (latticeDet a p c) + Int.natAbs (latticeDet p b c) := by
      rw [hadd, Int.natAbs_add_of_nonneg hnn1 hnn2]
    have hpos1 : 0 < Int.natAbs (latticeDet a p c) := Int.natAbs_pos.mpr (ne_of_gt h1)
    omega
  exact ⟨hlt1, hlt2⟩

/-! ## EmptyInterior inheritance across edgeStep -/

lemma memClosedTriangle_of_memClosedTriangle_edgeStep_left
    (a b c p r : ℤ × ℤ)
    (hp : p ∈ edgeLatticePoints a b)
    (hr : MemClosedTriangle a p c r) :
    MemClosedTriangle a b c r := by
  have hr_hull := mem_convexHull_of_memClosedTriangle a p c r hr
  have hp_seg := mem_segment_of_mem_edgeLatticePoints a b p hp
  set S : Set (ℝ × ℝ) := {toReal a, toReal b, toReal c}
  have haS : toReal a ∈ S := by simp [S]
  have hbS : toReal b ∈ S := by simp [S]
  have hcS : toReal c ∈ S := by simp [S]
  have hp_hull : toReal p ∈ convexHull ℝ S :=
    (segment_subset_convexHull haS hbS) hp_seg
  have hsub :
      convexHull ℝ ({toReal a, toReal p, toReal c} : Set (ℝ × ℝ)) ⊆ convexHull ℝ S := by
    refine convexHull_min ?_ (convex_convexHull ℝ S)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact subset_convexHull ℝ S haS
    · exact hp_hull
    · exact subset_convexHull ℝ S hcS
  exact memClosedTriangle_of_mem_convexHull a b c r (hsub hr_hull)

lemma memClosedTriangle_of_memClosedTriangle_edgeStep_right
    (a b c p r : ℤ × ℤ)
    (hp : p ∈ edgeLatticePoints a b)
    (hr : MemClosedTriangle p b c r) :
    MemClosedTriangle a b c r := by
  have hr_hull := mem_convexHull_of_memClosedTriangle p b c r hr
  have hp_seg := mem_segment_of_mem_edgeLatticePoints a b p hp
  set S : Set (ℝ × ℝ) := {toReal a, toReal b, toReal c}
  have haS : toReal a ∈ S := by simp [S]
  have hbS : toReal b ∈ S := by simp [S]
  have hcS : toReal c ∈ S := by simp [S]
  have hp_hull : toReal p ∈ convexHull ℝ S :=
    (segment_subset_convexHull haS hbS) hp_seg
  have hsub :
      convexHull ℝ ({toReal p, toReal b, toReal c} : Set (ℝ × ℝ)) ⊆ convexHull ℝ S := by
    refine convexHull_min ?_ (convex_convexHull ℝ S)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hp_hull
    · exact subset_convexHull ℝ S hbS
    · exact subset_convexHull ℝ S hcS
  exact memClosedTriangle_of_mem_convexHull a b c r (hsub hr_hull)

private lemma exists_edgeStep_segment_param (a b : ℤ × ℤ)
    (hd : 2 ≤ edgeGcd a b) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      toReal (edgeStep a b) = (1 - t) • toReal a + t • toReal b := by
  have hp_seg := mem_segment_of_mem_edgeLatticePoints a b (edgeStep a b)
    (edgeStep_mem_edgeLatticePoints a b (by omega))
  obtain ⟨t, ⟨ht0, ht1⟩, hp_eq⟩ :
      ∃ t : ℝ, (0 ≤ t ∧ t ≤ 1) ∧
        (1 - t) • toReal a + t • toReal b = toReal (edgeStep a b) := by
    simpa [segment_eq_image] using hp_seg
  refine ⟨t, ?_, ?_, hp_eq.symm⟩
  · by_contra h
    have ht' : t = 0 := le_antisymm (le_of_not_gt h) ht0
    have : toReal (edgeStep a b) = toReal a := by simpa [ht'] using hp_eq.symm
    exact (edgeStep_ne_left a b (by omega)) (toReal_injective this)
  · by_contra h
    have ht' : t = 1 := le_antisymm ht1 (le_of_not_gt h)
    have : toReal (edgeStep a b) = toReal b := by simpa [ht'] using hp_eq.symm
    exact (edgeStep_ne_right a b hd) (toReal_injective this)

lemma OffTriangleBoundary_of_mem_interior_edgeStep_left
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    (r : ℤ × ℤ)
    (hr : MemClosedTriangle a (edgeStep a b) c r)
    (hoff : OffTriangleBoundary a (edgeStep a b) c r) :
    OffTriangleBoundary a b c r := by
  set p := edgeStep a b
  have hD1 : 0 < latticeDet a p c := latticeDet_edgeStep_pos a b c hD (by omega)
  obtain ⟨hα, hβ, hγ⟩ :=
    latticeDet_pos_of_memClosedTriangle_offBoundary a p c r hr hD1 hoff
  obtain ⟨α, β, γ, hα0, hβ0, hγ0, hsum, heq⟩ := hr
  obtain ⟨e_pc, e_ac, e_ap⟩ :=
    latticeDet_eq_bary_mul_of_affine a p c r α β γ hsum heq
  obtain ⟨t, ht_pos, ht_lt, hp_eq⟩ := exists_edgeStep_segment_param a b hd
  have hαpos : (0 : ℝ) < α := by
    have hD1R : (0 : ℝ) < (latticeDet a p c : ℝ) := by exact_mod_cast hD1
    have hpos : (0 : ℝ) < (latticeDet p c r : ℝ) := by exact_mod_cast hα
    nlinarith [e_pc]
  have hβpos : (0 : ℝ) < β := by
    have hD1R : (0 : ℝ) < (latticeDet a p c : ℝ) := by exact_mod_cast hD1
    have hpos : (0 : ℝ) < (latticeDet a r c : ℝ) := by exact_mod_cast hβ
    nlinarith [e_ac]
  have hγpos : (0 : ℝ) < γ := by
    have hD1R : (0 : ℝ) < (latticeDet a p c : ℝ) := by exact_mod_cast hD1
    have hpos : (0 : ℝ) < (latticeDet a p r : ℝ) := by exact_mod_cast hγ
    nlinarith [e_ap]
  have hDR : (0 : ℝ) < (latticeDet a b c : ℝ) := by exact_mod_cast hD
  have hp0 : latticeDet a b p = 0 :=
    latticeDet_eq_zero_of_mem_edge_ab a b p
      (edgeStep_mem_edgeLatticePoints a b (by omega))
  have ha0 : latticeDet a b a = 0 := by unfold latticeDet; ring
  have hr_ab :
      (latticeDet a b r : ℝ) = γ * (latticeDet a b c : ℝ) := by
    have haff :=
      detR_affine_combination3 (toReal a) (toReal b)
        (toReal a) (toReal p) (toReal c) α β γ hsum
    have hz1 : detR (toReal a) (toReal b) (toReal a) = 0 := by
      simpa [detR_toReal] using congrArg (Int.cast (R := ℝ)) ha0
    have hz2 : detR (toReal a) (toReal b) (toReal p) = 0 := by
      simpa [detR_toReal] using congrArg (Int.cast (R := ℝ)) hp0
    have : detR (toReal a) (toReal b) (toReal r) =
        γ * detR (toReal a) (toReal b) (toReal c) := by
      have heq' : toReal r = α • toReal a + β • toReal p + γ • toReal c := by
        simpa [toReal] using heq.symm
      rw [heq', haff, hz1, hz2]; ring
    simpa [detR_toReal] using this
  have hnot_ab : r ∉ edgeLatticePoints a b := by
    intro hab
    have hz : latticeDet a b r = 0 := latticeDet_eq_zero_of_mem_edge_ab a b r hab
    have hzR : (latticeDet a b r : ℝ) = 0 := by exact_mod_cast hz
    have hpos : (0 : ℝ) < (latticeDet a b r : ℝ) := by rw [hr_ab]; nlinarith
    exact (ne_of_gt hpos) hzR
  have hp_bc :
      (latticeDet b c p : ℝ) = (1 - t) * (latticeDet b c a : ℝ) := by
    have hlin :
        detR (toReal b) (toReal c) ((1 - t) • toReal a + t • toReal b) =
          (1 - t) * detR (toReal b) (toReal c) (toReal a) +
            t * detR (toReal b) (toReal c) (toReal b) := by
      simp [detR, Prod.smul_def, smul_eq_mul]; ring
    have hz : detR (toReal b) (toReal c) (toReal b) = 0 := by simp [detR]
    calc
      (latticeDet b c p : ℝ)
          = detR (toReal b) (toReal c) (toReal p) := (detR_toReal b c p).symm
      _ = detR (toReal b) (toReal c) ((1 - t) • toReal a + t • toReal b) := by rw [hp_eq]
      _ = (1 - t) * detR (toReal b) (toReal c) (toReal a) := by rw [hlin, hz]; ring
      _ = (1 - t) * (latticeDet b c a : ℝ) := by rw [detR_toReal]
  have hr_bc :
      (latticeDet b c r : ℝ) =
        α * (latticeDet b c a : ℝ) + β * (latticeDet b c p : ℝ) := by
    have haff :=
      detR_affine_combination3 (toReal b) (toReal c)
        (toReal a) (toReal p) (toReal c) α β γ hsum
    have hz : detR (toReal b) (toReal c) (toReal c) = 0 := by unfold detR; ring
    have heq' : toReal r = α • toReal a + β • toReal p + γ • toReal c := by
      simpa [toReal] using heq.symm
    have : detR (toReal b) (toReal c) (toReal r) =
        α * detR (toReal b) (toReal c) (toReal a) +
          β * detR (toReal b) (toReal c) (toReal p) := by
      rw [heq', haff, hz]; ring
    simpa [detR_toReal] using this
  have hnot_bc : r ∉ edgeLatticePoints b c := by
    intro hbc
    have hz : latticeDet b c r = 0 := latticeDet_eq_zero_of_mem_edge_ab b c r hbc
    have hzR : (latticeDet b c r : ℝ) = 0 := by exact_mod_cast hz
    have hcyc : (latticeDet b c a : ℝ) = (latticeDet a b c : ℝ) := by
      exact_mod_cast (latticeDet_cyclic a b c).symm
    have h1t : (0 : ℝ) < 1 - t := sub_pos.mpr ht_lt
    have hpos : (0 : ℝ) < (latticeDet b c r : ℝ) := by
      have hform : (latticeDet b c r : ℝ) =
          (α + β * (1 - t)) * (latticeDet a b c : ℝ) := by
        calc
          (latticeDet b c r : ℝ)
              = α * (latticeDet b c a : ℝ) + β * (latticeDet b c p : ℝ) := hr_bc
          _ = α * (latticeDet a b c : ℝ) + β * ((1 - t) * (latticeDet a b c : ℝ)) := by
                rw [hp_bc, hcyc]
          _ = (α + β * (1 - t)) * (latticeDet a b c : ℝ) := by ring
      rw [hform]
      exact mul_pos (by nlinarith [hαpos, hβpos, h1t]) hDR
    exact (ne_of_gt hpos) hzR
  exact ⟨hnot_ab, hnot_bc, hoff.2.2⟩

lemma OffTriangleBoundary_of_mem_interior_edgeStep_right
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    (r : ℤ × ℤ)
    (hr : MemClosedTriangle (edgeStep a b) b c r)
    (hoff : OffTriangleBoundary (edgeStep a b) b c r) :
    OffTriangleBoundary a b c r := by
  set p := edgeStep a b
  have hD2 : 0 < latticeDet p b c := latticeDet_edgeStep_right_pos a b c hD hd
  obtain ⟨hα, hβ, hγ⟩ :=
    latticeDet_pos_of_memClosedTriangle_offBoundary p b c r hr hD2 hoff
  obtain ⟨α, β, γ, hα0, hβ0, hγ0, hsum, heq⟩ := hr
  obtain ⟨e_bc, e_pc, e_pb⟩ :=
    latticeDet_eq_bary_mul_of_affine p b c r α β γ hsum heq
  obtain ⟨t, ht_pos, ht_lt, hp_eq⟩ := exists_edgeStep_segment_param a b hd
  have hαpos : (0 : ℝ) < α := by
    have hD2R : (0 : ℝ) < (latticeDet p b c : ℝ) := by exact_mod_cast hD2
    have hpos : (0 : ℝ) < (latticeDet b c r : ℝ) := by exact_mod_cast hα
    nlinarith [e_bc]
  have hβpos : (0 : ℝ) < β := by
    have hD2R : (0 : ℝ) < (latticeDet p b c : ℝ) := by exact_mod_cast hD2
    have hpos : (0 : ℝ) < (latticeDet p r c : ℝ) := by exact_mod_cast hβ
    nlinarith [e_pc]
  have hγpos : (0 : ℝ) < γ := by
    have hD2R : (0 : ℝ) < (latticeDet p b c : ℝ) := by exact_mod_cast hD2
    have hpos : (0 : ℝ) < (latticeDet p b r : ℝ) := by exact_mod_cast hγ
    nlinarith [e_pb]
  have hDR : (0 : ℝ) < (latticeDet a b c : ℝ) := by exact_mod_cast hD
  have hp0 : latticeDet a b p = 0 :=
    latticeDet_eq_zero_of_mem_edge_ab a b p
      (edgeStep_mem_edgeLatticePoints a b (by omega))
  have hb0 : latticeDet a b b = 0 := by unfold latticeDet; ring
  have hr_ab :
      (latticeDet a b r : ℝ) = γ * (latticeDet a b c : ℝ) := by
    have haff :=
      detR_affine_combination3 (toReal a) (toReal b)
        (toReal p) (toReal b) (toReal c) α β γ hsum
    have hz1 : detR (toReal a) (toReal b) (toReal p) = 0 := by
      simpa [detR_toReal] using congrArg (Int.cast (R := ℝ)) hp0
    have hz2 : detR (toReal a) (toReal b) (toReal b) = 0 := by
      simpa [detR_toReal] using congrArg (Int.cast (R := ℝ)) hb0
    have heq' : toReal r = α • toReal p + β • toReal b + γ • toReal c := by
      simpa [toReal] using heq.symm
    have : detR (toReal a) (toReal b) (toReal r) =
        γ * detR (toReal a) (toReal b) (toReal c) := by
      rw [heq', haff, hz1, hz2]; ring
    simpa [detR_toReal] using this
  have hnot_ab : r ∉ edgeLatticePoints a b := by
    intro hab
    have hz : latticeDet a b r = 0 := latticeDet_eq_zero_of_mem_edge_ab a b r hab
    have hzR : (latticeDet a b r : ℝ) = 0 := by exact_mod_cast hz
    have hpos : (0 : ℝ) < (latticeDet a b r : ℝ) := by rw [hr_ab]; nlinarith
    exact (ne_of_gt hpos) hzR
  have hp_ca :
      (latticeDet c a p : ℝ) = t * (latticeDet c a b : ℝ) := by
    have hlin :
        detR (toReal c) (toReal a) ((1 - t) • toReal a + t • toReal b) =
          (1 - t) * detR (toReal c) (toReal a) (toReal a) +
            t * detR (toReal c) (toReal a) (toReal b) := by
      simp [detR, Prod.smul_def, smul_eq_mul]; ring
    have hz : detR (toReal c) (toReal a) (toReal a) = 0 := by unfold detR; ring
    calc
      (latticeDet c a p : ℝ)
          = detR (toReal c) (toReal a) (toReal p) := (detR_toReal c a p).symm
      _ = detR (toReal c) (toReal a) ((1 - t) • toReal a + t • toReal b) := by rw [hp_eq]
      _ = t * detR (toReal c) (toReal a) (toReal b) := by rw [hlin, hz]; ring
      _ = t * (latticeDet c a b : ℝ) := by rw [detR_toReal]
  have hr_ca :
      (latticeDet c a r : ℝ) =
        α * (latticeDet c a p : ℝ) + β * (latticeDet c a b : ℝ) := by
    have haff :=
      detR_affine_combination3 (toReal c) (toReal a)
        (toReal p) (toReal b) (toReal c) α β γ hsum
    have hz : detR (toReal c) (toReal a) (toReal c) = 0 := by unfold detR; ring
    have heq' : toReal r = α • toReal p + β • toReal b + γ • toReal c := by
      simpa [toReal] using heq.symm
    have : detR (toReal c) (toReal a) (toReal r) =
        α * detR (toReal c) (toReal a) (toReal p) +
          β * detR (toReal c) (toReal a) (toReal b) := by
      rw [heq', haff, hz]; ring
    simpa [detR_toReal] using this
  have hnot_ca : r ∉ edgeLatticePoints c a := by
    intro hca
    have hz : latticeDet c a r = 0 := latticeDet_eq_zero_of_mem_edge_ab c a r hca
    have hzR : (latticeDet c a r : ℝ) = 0 := by exact_mod_cast hz
    have hcyc : (latticeDet c a b : ℝ) = (latticeDet a b c : ℝ) := by
      exact_mod_cast (latticeDet_cyclic₂ a b c).symm
    have hpos : (0 : ℝ) < (latticeDet c a r : ℝ) := by
      have hform : (latticeDet c a r : ℝ) =
          (α * t + β) * (latticeDet a b c : ℝ) := by
        calc
          (latticeDet c a r : ℝ)
              = α * (latticeDet c a p : ℝ) + β * (latticeDet c a b : ℝ) := hr_ca
          _ = α * (t * (latticeDet a b c : ℝ)) + β * (latticeDet a b c : ℝ) := by
                rw [hp_ca, hcyc]
          _ = (α * t + β) * (latticeDet a b c : ℝ) := by ring
      rw [hform]
      exact mul_pos (by nlinarith [hαpos, hβpos, ht_pos]) hDR
    exact (ne_of_gt hpos) hzR
  -- hoff.1 is r ∉ edgeLatticePoints p b; need r ∉ edgeLatticePoints b c
  have hnot_bc : r ∉ edgeLatticePoints b c := hoff.2.1
  exact ⟨hnot_ab, hnot_bc, hnot_ca⟩

theorem EmptyInterior_trianglePolygon_of_edgeStep_left
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    (hI : EmptyInterior (trianglePolygon a b c)) :
    EmptyInterior (trianglePolygon a (edgeStep a b) c) := by
  classical
  set p := edgeStep a b
  rw [EmptyInterior] at hI ⊢
  ext r
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hr
  have hr' := (mem_interiorLatticePoints_trianglePolygon_iff a p c r).mp hr
  have hmem := memClosedTriangle_of_memClosedTriangle_edgeStep_left a b c p r
    (edgeStep_mem_edgeLatticePoints a b (by omega)) hr'.1
  have hoff :=
    OffTriangleBoundary_of_mem_interior_edgeStep_left a b c hD hd r hr'.1 hr'.2
  have hint : r ∈ (trianglePolygon a b c).interiorLatticePoints :=
    (mem_interiorLatticePoints_trianglePolygon_iff a b c r).mpr ⟨hmem, hoff⟩
  exact (by simp [hI] : r ∉ (trianglePolygon a b c).interiorLatticePoints) hint

theorem EmptyInterior_trianglePolygon_of_edgeStep_right
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    (hI : EmptyInterior (trianglePolygon a b c)) :
    EmptyInterior (trianglePolygon (edgeStep a b) b c) := by
  classical
  set p := edgeStep a b
  rw [EmptyInterior] at hI ⊢
  ext r
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hr
  have hr' := (mem_interiorLatticePoints_trianglePolygon_iff p b c r).mp hr
  have hmem := memClosedTriangle_of_memClosedTriangle_edgeStep_right a b c p r
    (edgeStep_mem_edgeLatticePoints a b (by omega)) hr'.1
  have hoff :=
    OffTriangleBoundary_of_mem_interior_edgeStep_right a b c hD hd r hr'.1 hr'.2
  have hint : r ∈ (trianglePolygon a b c).interiorLatticePoints :=
    (mem_interiorLatticePoints_trianglePolygon_iff a b c r).mpr ⟨hmem, hoff⟩
  exact (by simp [hI] : r ∉ (trianglePolygon a b c).interiorLatticePoints) hint

/-! ## PrimitiveEdges for triangles + empty-interior Pick by `|det|` induction -/

lemma PrimitiveEdges_trianglePolygon_of_edgeGcds
    (a b c : ℤ × ℤ)
    (hab : edgeGcd a b = 1) (hbc : edgeGcd b c = 1) (hca : edgeGcd c a = 1) :
    PrimitiveEdges (trianglePolygon a b c) := by
  intro i
  fin_cases i
  · simpa [trianglePolygon, LatticePolygon.edgePair, LatticePolygon.vertex,
      LatticePolygon.nextIdx, LatticePolygon.nVertices] using hab
  · simpa [trianglePolygon, LatticePolygon.edgePair, LatticePolygon.vertex,
      LatticePolygon.nextIdx, LatticePolygon.nVertices] using hbc
  · simpa [trianglePolygon, LatticePolygon.edgePair, LatticePolygon.vertex,
      LatticePolygon.nextIdx, LatticePolygon.nVertices] using hca

lemma edgeGcd_pos_of_latticeDet_pos (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) :
    1 ≤ edgeGcd a b ∧ 1 ≤ edgeGcd b c ∧ 1 ≤ edgeGcd c a := by
  refine ⟨?_, ?_, ?_⟩
  · have hne : a ≠ b := by
      intro h; simp [latticeDet, h] at hD
    exact Nat.pos_of_ne_zero fun hz => hne ((edgeGcd_eq_zero_iff a b).mp hz)
  · have hne : b ≠ c := by
      intro h; subst h; unfold latticeDet at hD; linarith
    exact Nat.pos_of_ne_zero fun hz => hne ((edgeGcd_eq_zero_iff b c).mp hz)
  · have hne : c ≠ a := by
      intro h; simp [latticeDet, h] at hD
    exact Nat.pos_of_ne_zero fun hz => hne ((edgeGcd_eq_zero_iff c a).mp hz)

/-- Helper: empty-triangle Pick when a designated edge has `edgeGcd ≥ 2`. -/
theorem shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle_of_edgeStep_ab
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    (hI : EmptyInterior (trianglePolygon a b c))
    (ih : ∀ a' b' c' : ℤ × ℤ,
      0 < latticeDet a' b' c' →
      EmptyInterior (trianglePolygon a' b' c') →
      Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) →
      (trianglePolygon a' b' c').shoelace =
        ((trianglePolygon a' b' c').B : ℚ) / 2 - 1) :
    (trianglePolygon a b c).shoelace =
      ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by
  classical
  set p := edgeStep a b
  have hlt := natAbs_latticeDet_edgeStep_lt a b c hD hd
  have hD1 : 0 < latticeDet a p c := latticeDet_edgeStep_pos a b c hD (by omega)
  have hD2 : 0 < latticeDet p b c := latticeDet_edgeStep_right_pos a b c hD hd
  have hI1 := EmptyInterior_trianglePolygon_of_edgeStep_left a b c hD hd hI
  have hI2 := EmptyInterior_trianglePolygon_of_edgeStep_right a b c hD hd hI
  have ih1 := ih a p c hD1 hI1 hlt.1
  have ih2 := ih p b c hD2 hI2 hlt.2
  have hpc := edgeGcd_eq_one_of_empty_interior_edgeStep a b c hD hd hI
  have hsa := shoelace_add_of_edgeStep a b c hD hd
  have hBa := B_add_of_edgeStep a b c hD hd hpc
  calc
    (trianglePolygon a b c).shoelace
        = (trianglePolygon a p c).shoelace + (trianglePolygon p b c).shoelace := hsa
    _ = (((trianglePolygon a p c).B : ℚ) / 2 - 1) +
          (((trianglePolygon p b c).B : ℚ) / 2 - 1) := by rw [ih1, ih2]
    _ = (((trianglePolygon a p c).B : ℚ) + (trianglePolygon p b c).B) / 2 - 2 := by
          ring
    _ = (((trianglePolygon a p c).B + (trianglePolygon p b c).B : ℕ) : ℚ) / 2 - 2 := by
          push_cast; rfl
    _ = (((trianglePolygon a b c).B + 2 : ℕ) : ℚ) / 2 - 2 := by rw [hBa]
    _ = ((trianglePolygon a b c).B : ℚ) / 2 + 1 - 2 := by push_cast; ring
    _ = ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by ring

/-- Empty closed lattice triangle Pick-form without `PrimitiveEdges`, by induction
on `|det|` via `edgeStep` splits (not classical Pick). -/
theorem shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c)
    (hI : EmptyInterior (trianglePolygon a b c)) :
    (trianglePolygon a b c).shoelace =
      ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by
  classical
  generalize hn : Int.natAbs (latticeDet a b c) = n
  revert a b c
  refine Nat.strong_induction_on n fun n ih a b c hD hI hn => ?_
  have hpos := edgeGcd_pos_of_latticeDet_pos a b c hD
  by_cases hprim : edgeGcd a b = 1 ∧ edgeGcd b c = 1 ∧ edgeGcd c a = 1
  · have hedge :=
      PrimitiveEdges_trianglePolygon_of_edgeGcds a b c hprim.1 hprim.2.1 hprim.2.2
    exact shoelace_eq_B_div_two_sub_one_of_empty_interior_convex
      (trianglePolygon a b c)
      (injective_vertex_trianglePolygon a b c (ne_of_gt hD))
      hedge hI (StrictlyConvexCCW_trianglePolygon a b c hD)
  · have hge : 2 ≤ edgeGcd a b ∨ 2 ≤ edgeGcd b c ∨ 2 ≤ edgeGcd c a := by omega
    have ih' : ∀ a' b' c' : ℤ × ℤ,
        0 < latticeDet a' b' c' →
        EmptyInterior (trianglePolygon a' b' c') →
        Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) →
        (trianglePolygon a' b' c').shoelace =
          ((trianglePolygon a' b' c').B : ℚ) / 2 - 1 := by
      intro a' b' c' hD' hI' hlt'
      have hltn : Int.natAbs (latticeDet a' b' c') < n := by simpa [hn] using hlt'
      exact ih _ hltn a' b' c' hD' hI' rfl
    rcases hge with hab | hbc | hca
    · -- split on a—b
      subst hn
      exact shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle_of_edgeStep_ab
        a b c hD hab hI ih'
    · -- rotate to (b,c,a) and split on b—c
      have hDc : 0 < latticeDet b c a := by simpa [← latticeDet_cyclic a b c] using hD
      have hIc : EmptyInterior (trianglePolygon b c a) :=
        (EmptyInterior_trianglePolygon_cyclic a b c).mp hI
      have ihc : ∀ a' b' c' : ℤ × ℤ,
          0 < latticeDet a' b' c' →
          EmptyInterior (trianglePolygon a' b' c') →
          Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet b c a) →
          (trianglePolygon a' b' c').shoelace =
            ((trianglePolygon a' b' c').B : ℚ) / 2 - 1 := by
        intro a' b' c' hD' hI' hlt'
        have : Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) := by
          simpa [← latticeDet_cyclic a b c] using hlt'
        exact ih' a' b' c' hD' hI' this
      have hpick :=
        shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle_of_edgeStep_ab
          b c a hDc hbc hIc ihc
      rw [shoelace_trianglePolygon_cyclic a b c,
          B_trianglePolygon_cyclic a b c (ne_of_gt hD)]
      exact hpick
    · -- rotate to (c,a,b) and split on c—a
      have hDc : 0 < latticeDet c a b := by simpa [← latticeDet_cyclic₂ a b c] using hD
      have hIc : EmptyInterior (trianglePolygon c a b) := by
        have h1 := (EmptyInterior_trianglePolygon_cyclic a b c).mp hI
        exact (EmptyInterior_trianglePolygon_cyclic b c a).mp h1
      have ihc : ∀ a' b' c' : ℤ × ℤ,
          0 < latticeDet a' b' c' →
          EmptyInterior (trianglePolygon a' b' c') →
          Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet c a b) →
          (trianglePolygon a' b' c').shoelace =
            ((trianglePolygon a' b' c').B : ℚ) / 2 - 1 := by
        intro a' b' c' hD' hI' hlt'
        have : Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) := by
          simpa [← latticeDet_cyclic₂ a b c] using hlt'
        exact ih' a' b' c' hD' hI' this
      have hpick :=
        shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle_of_edgeStep_ab
          c a b hDc hca hIc ihc
      have hs1 := shoelace_trianglePolygon_cyclic a b c
      have hs2 := shoelace_trianglePolygon_cyclic b c a
      have hB1 := B_trianglePolygon_cyclic a b c (ne_of_gt hD)
      have hB2 := B_trianglePolygon_cyclic b c a
        (by simpa [← latticeDet_cyclic a b c] using ne_of_gt hD)
      rw [hs1, hs2, hB1, hB2]
      exact hpick




/-! ## UniqueInterior triangle Pick without `PrimitiveEdges`

`|det|` induction via `edgeStep`. Base: all-primitive edges reuse existing
`UniqueInterior` Pick-form. Step: UniqueInterior ⇒ new chord `edgeGcd ≤ 2`.
If `= 1`, unique interior sits in one half; if `= 2`, it lies on the chord and
both halves are empty. Reassemble via shoelace / B additivity. Not classical Pick.
-/

/-- B-additivity across `edgeStep` for arbitrary new-chord gcd (not classical Pick). -/
lemma B_add_of_edgeStep_of_gcd (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b) :
    (trianglePolygon a (edgeStep a b) c).B + (trianglePolygon (edgeStep a b) b c).B =
      (trianglePolygon a b c).B + 2 * edgeGcd (edgeStep a b) c := by
  set p := edgeStep a b
  set d := edgeGcd a b
  set g := edgeGcd p c
  have hD1 : latticeDet a p c ≠ 0 := ne_of_gt (latticeDet_edgeStep_pos a b c hD (by omega))
  have hD2 : latticeDet p b c ≠ 0 := ne_of_gt (latticeDet_edgeStep_right_pos a b c hD hd)
  have hD0 : latticeDet a b c ≠ 0 := ne_of_gt hD
  have hB := B_trianglePolygon_eq_sum_edgeGcd a b c hD0
  have hB1 := B_trianglePolygon_eq_sum_edgeGcd a p c hD1
  have hB2 := B_trianglePolygon_eq_sum_edgeGcd p b c hD2
  have hL := edgeGcd_edgeStep_left a b (by omega)
  have hR := edgeGcd_edgeStep_right a b hd
  have hgc : edgeGcd c p = g := by simp [g, edgeGcd_comm p c]
  calc
    (trianglePolygon a p c).B + (trianglePolygon p b c).B
        = (edgeGcd a p + edgeGcd p c + edgeGcd c a) +
            (edgeGcd p b + edgeGcd b c + edgeGcd c p) := by
              rw [hB1, hB2]
    _ = (1 + g + edgeGcd c a) + ((d - 1) + edgeGcd b c + g) := by
          simp [p, d, g, hL, hR, hgc]
    _ = d + edgeGcd b c + edgeGcd c a + 2 * g := by
          have : 1 ≤ d := by omega
          omega
    _ = (edgeGcd a b + edgeGcd b c + edgeGcd c a) + 2 * g := by simp [d]
    _ = (trianglePolygon a b c).B + 2 * g := by rw [hB]

theorem mem_interiorLatticePoints_of_strict_mem_edgeStep_chord
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {r : ℤ × ℤ}
    (hr : r ∈ edgeLatticePoints (edgeStep a b) c)
    (hrne_p : r ≠ edgeStep a b) (hrne_c : r ≠ c) :
    r ∈ (trianglePolygon a b c).interiorLatticePoints := by
  classical
  set p := edgeStep a b
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
  exact hint


/-- UniqueInterior ⇒ open chord after `edgeStep` has `edgeGcd ≤ 2`. -/
theorem edgeGcd_le_two_of_uniqueInterior_edgeStep
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q : ℤ × ℤ} (hU : UniqueInterior (trianglePolygon a b c) q) :
    edgeGcd (edgeStep a b) c ≤ 2 := by
  classical
  set p := edgeStep a b
  by_contra hgt
  have hge : 3 ≤ edgeGcd p c := by omega
  have hp_mem : p ∈ edgeLatticePoints p c := self_mem_edgeLatticePoints p c
  have hc_mem : c ∈ edgeLatticePoints p c := other_mem_edgeLatticePoints p c
  have hp_ne_c : p ≠ c := by
    intro hpc
    have hp := edgeStep_mem_edgeLatticePoints a b (by omega)
    have : latticeDet a b c = 0 := by
      simpa [hpc] using latticeDet_eq_zero_of_mem_edge_ab a b p hp
    omega
  have hcard0 : (edgeLatticePoints p c).card = edgeGcd p c + 1 :=
    card_edgeLatticePoints p c
  have hcard1 : ((edgeLatticePoints p c).erase p).card = edgeGcd p c := by
    rw [Finset.card_erase_of_mem hp_mem, hcard0]; omega
  have hc_mem' : c ∈ (edgeLatticePoints p c).erase p :=
    Finset.mem_erase.mpr ⟨fun h => hp_ne_c h.symm, hc_mem⟩
  have hcard2 : (((edgeLatticePoints p c).erase p).erase c).card = edgeGcd p c - 1 := by
    rw [Finset.card_erase_of_mem hc_mem', hcard1]
  have hcard_ge : 2 ≤ (((edgeLatticePoints p c).erase p).erase c).card := by omega
  have hinter : (trianglePolygon a b c).interiorLatticePoints = {q} := by
    ext x
    constructor
    · intro hx; exact hU.2 x hx
    · intro hx
      simp only [Set.mem_singleton_iff] at hx
      exact hx ▸ hU.1
  have hsub :
      ((edgeLatticePoints p c).erase p).erase c ⊆ ({q} : Finset (ℤ × ℤ)) := by
    intro r hr
    have hr' := Finset.mem_erase.mp hr
    have hr'' := Finset.mem_erase.mp hr'.2
    have hint := mem_interiorLatticePoints_of_strict_mem_edgeStep_chord a b c hD hd
      hr''.2 hr''.1 hr'.1
    have hr_eq : r = q := by
      have : r ∈ ({q} : Set (ℤ × ℤ)) := by
        rw [← hinter]; exact hint
      simpa using this
    exact Finset.mem_singleton.mpr hr_eq
  have hcard_le :
      (((edgeLatticePoints p c).erase p).erase c).card ≤ ({q} : Finset (ℤ × ℤ)).card :=
    Finset.card_le_card hsub
  have : (((edgeLatticePoints p c).erase p).erase c).card ≤ 1 := by
    simpa using hcard_le
  omega



/-! ### Inheritance and UniqueInterior Pick without `PrimitiveEdges` -/

lemma mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_left
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {r : ℤ × ℤ}
    (hr : r ∈ (trianglePolygon a (edgeStep a b) c).interiorLatticePoints) :
    r ∈ (trianglePolygon a b c).interiorLatticePoints := by
  set p := edgeStep a b
  have hr' := (mem_interiorLatticePoints_trianglePolygon_iff a p c r).mp hr
  have hmem := memClosedTriangle_of_memClosedTriangle_edgeStep_left a b c p r
    (edgeStep_mem_edgeLatticePoints a b (by omega)) hr'.1
  have hoff :=
    OffTriangleBoundary_of_mem_interior_edgeStep_left a b c hD hd r hr'.1 hr'.2
  exact (mem_interiorLatticePoints_trianglePolygon_iff a b c r).mpr ⟨hmem, hoff⟩

lemma mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_right
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {r : ℤ × ℤ}
    (hr : r ∈ (trianglePolygon (edgeStep a b) b c).interiorLatticePoints) :
    r ∈ (trianglePolygon a b c).interiorLatticePoints := by
  set p := edgeStep a b
  have hr' := (mem_interiorLatticePoints_trianglePolygon_iff p b c r).mp hr
  have hmem := memClosedTriangle_of_memClosedTriangle_edgeStep_right a b c p r
    (edgeStep_mem_edgeLatticePoints a b (by omega)) hr'.1
  have hoff :=
    OffTriangleBoundary_of_mem_interior_edgeStep_right a b c hD hd r hr'.1 hr'.2
  exact (mem_interiorLatticePoints_trianglePolygon_iff a b c r).mpr ⟨hmem, hoff⟩

theorem UniqueInterior_trianglePolygon_of_edgeStep_left
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q : ℤ × ℤ} (hU : UniqueInterior (trianglePolygon a b c) q)
    (hq : q ∈ (trianglePolygon a (edgeStep a b) c).interiorLatticePoints) :
    UniqueInterior (trianglePolygon a (edgeStep a b) c) q :=
  ⟨hq, fun r hr => hU.2 r
    (mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_left a b c hD hd hr)⟩

theorem UniqueInterior_trianglePolygon_of_edgeStep_right
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q : ℤ × ℤ} (hU : UniqueInterior (trianglePolygon a b c) q)
    (hq : q ∈ (trianglePolygon (edgeStep a b) b c).interiorLatticePoints) :
    UniqueInterior (trianglePolygon (edgeStep a b) b c) q :=
  ⟨hq, fun r hr => hU.2 r
    (mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_right a b c hD hd hr)⟩

private lemma latticeDet_pqc_neg (p c q : ℤ × ℤ) :
    latticeDet p q c = -latticeDet p c q := by
  simp [latticeDet]; ring

theorem EmptyInterior_edgeStep_right_of_uniqueInterior_left
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q : ℤ × ℤ} (hU : UniqueInterior (trianglePolygon a b c) q)
    (hq : q ∈ (trianglePolygon a (edgeStep a b) c).interiorLatticePoints) :
    EmptyInterior (trianglePolygon (edgeStep a b) b c) := by
  classical
  set p := edgeStep a b
  rw [EmptyInterior]
  ext r
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hr
  have hint :=
    mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_right a b c hD hd hr
  have rq : r = q := hU.2 r hint
  have hqL := (mem_interiorLatticePoints_trianglePolygon_iff a p c q).mp hq
  have hqR := (mem_interiorLatticePoints_trianglePolygon_iff p b c q).mp (rq ▸ hr)
  have hD1 : 0 < latticeDet a p c := latticeDet_edgeStep_pos a b c hD (by omega)
  have hD2 : 0 < latticeDet p b c := latticeDet_edgeStep_right_pos a b c hD hd
  have hposL := latticeDet_pos_of_memClosedTriangle_offBoundary a p c q hqL.1 hD1 hqL.2
  have hposR := latticeDet_pos_of_memClosedTriangle_offBoundary p b c q hqR.1 hD2 hqR.2
  have h1 : 0 < latticeDet p c q := hposL.1
  have h2 : 0 < latticeDet p q c := hposR.2.1
  have hneg := latticeDet_pqc_neg p c q
  omega

theorem EmptyInterior_edgeStep_left_of_uniqueInterior_right
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q : ℤ × ℤ} (hU : UniqueInterior (trianglePolygon a b c) q)
    (hq : q ∈ (trianglePolygon (edgeStep a b) b c).interiorLatticePoints) :
    EmptyInterior (trianglePolygon a (edgeStep a b) c) := by
  classical
  set p := edgeStep a b
  rw [EmptyInterior]
  ext r
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hr
  have hint :=
    mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_left a b c hD hd hr
  have rq : r = q := hU.2 r hint
  have hqR := (mem_interiorLatticePoints_trianglePolygon_iff p b c q).mp hq
  have hqL := (mem_interiorLatticePoints_trianglePolygon_iff a p c q).mp (rq ▸ hr)
  have hD1 : 0 < latticeDet a p c := latticeDet_edgeStep_pos a b c hD (by omega)
  have hD2 : 0 < latticeDet p b c := latticeDet_edgeStep_right_pos a b c hD hd
  have hposL := latticeDet_pos_of_memClosedTriangle_offBoundary a p c q hqL.1 hD1 hqL.2
  have hposR := latticeDet_pos_of_memClosedTriangle_offBoundary p b c q hqR.1 hD2 hqR.2
  have h1 : 0 < latticeDet p c q := hposL.1
  have h2 : 0 < latticeDet p q c := hposR.2.1
  have hneg := latticeDet_pqc_neg p c q
  omega



/-- Under UniqueInterior, if the unique point lies on the open `edgeStep` chord,
the left sub-triangle is empty (not classical Pick). -/
theorem EmptyInterior_edgeStep_left_of_uniqueInterior_on_chord
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q : ℤ × ℤ} (hU : UniqueInterior (trianglePolygon a b c) q)
    (hq : q ∈ edgeLatticePoints (edgeStep a b) c)
    (_hqne_p : q ≠ edgeStep a b) (_hqne_c : q ≠ c) :
    EmptyInterior (trianglePolygon a (edgeStep a b) c) := by
  classical
  set p := edgeStep a b
  rw [EmptyInterior]
  ext r
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hr
  have hint :=
    mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_left a b c hD hd hr
  have rq : r = q := hU.2 r hint
  have hqL := (mem_interiorLatticePoints_trianglePolygon_iff a p c q).mp (rq ▸ hr)
  -- OffTriangleBoundary a p c q ⇒ q ∉ edgeLatticePoints p c
  exact hqL.2.2.1 hq

/-- Under UniqueInterior, if the unique point lies on the open `edgeStep` chord,
the right sub-triangle is empty (not classical Pick). -/
theorem EmptyInterior_edgeStep_right_of_uniqueInterior_on_chord
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q : ℤ × ℤ} (hU : UniqueInterior (trianglePolygon a b c) q)
    (hq : q ∈ edgeLatticePoints (edgeStep a b) c)
    (_hqne_p : q ≠ edgeStep a b) (_hqne_c : q ≠ c) :
    EmptyInterior (trianglePolygon (edgeStep a b) b c) := by
  classical
  set p := edgeStep a b
  rw [EmptyInterior]
  ext r
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hr
  have hint :=
    mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_right a b c hD hd hr
  have rq : r = q := hU.2 r hint
  have hqR := (mem_interiorLatticePoints_trianglePolygon_iff p b c q).mp (rq ▸ hr)
  -- OffTriangleBoundary p b c q ⇒ q ∉ edgeLatticePoints c p
  have hcp : q ∈ edgeLatticePoints c p := mem_edgeLatticePoints_comm (by simpa [p] using hq)
  exact hqR.2.2.2 hcp

/-- UniqueInterior + `edgeGcd (edgeStep,c) = 2` ⇒ both halves empty (not classical Pick). -/
theorem EmptyInterior_edgeStep_both_of_uniqueInterior_edgeGcd_eq_two
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q : ℤ × ℤ} (hU : UniqueInterior (trianglePolygon a b c) q)
    (hg : edgeGcd (edgeStep a b) c = 2) :
    EmptyInterior (trianglePolygon a (edgeStep a b) c) ∧
      EmptyInterior (trianglePolygon (edgeStep a b) b c) := by
  classical
  set p := edgeStep a b
  obtain ⟨r, hr, hrne_p, hrne_c⟩ :=
    exists_strict_mem_edgeLatticePoints_of_edgeGcd_ge_two p c (by omega)
  have hint := mem_interiorLatticePoints_of_strict_mem_edgeStep_chord a b c hD hd
    hr hrne_p hrne_c
  have rq : r = q := hU.2 r hint
  -- avoid subst on implicit q: rewrite hypotheses
  have hrq : q ∈ edgeLatticePoints p c := by simpa [rq.symm, p] using hr
  have hpq : q ≠ p := by simpa [rq.symm, p] using hrne_p
  have hcq : q ≠ c := by simpa [rq.symm] using hrne_c
  exact ⟨
    EmptyInterior_edgeStep_left_of_uniqueInterior_on_chord a b c hD hd hU hrq hpq hcq,
    EmptyInterior_edgeStep_right_of_uniqueInterior_on_chord a b c hD hd hU hrq hpq hcq⟩


end InteriorFan
end LatticeFan
end Picks
end EulersGem
