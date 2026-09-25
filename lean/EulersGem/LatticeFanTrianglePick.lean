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

UniqueInterior triangle Pick without `PrimitiveEdges`: generalized B-add,
chord-interior, `edgeGcd ≤ 2`, half-inheritance, both-halves-empty when
`edgeGcd(chord)=2`, g=1 locate-half, and `|det|` induction reassembly to
`shoelace = 1 + B/2 − 1`. TwoInterior / I≤2 triangle Pick without
`PrimitiveEdges` via edgeStep locate (empty / UniqueInterior / TwoInterior
halves) and `|det|` induction. I≤3 / I≤4 / I≤5 triangle Pick without `PrimitiveEdges`
by the same `|det|` / edgeStep Finset induction (general pe_ih form).
I=4 / I≤4 / I=5 / I≤5 / I=6 / I≤6 Finset Pick-form without spokes-empty
(ears may have non-primitive sides; use triangle I≤k w/o PE or
PrimitiveEdges inheritance when `#earOff=#S-1`). Strong induction on
Finset card via fan_ear_IH + pe_ih triangle ears green. All-I triangle
Pick without `PrimitiveEdges` via `pe_ih` + PE strong induction.
Parent `B = ∑ edgeGcd` + PE-free hbook arithmetic substrate landed.
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



/-! ### UniqueInterior locate-half + Pick without `PrimitiveEdges` -/

lemma UniqueInterior_trianglePolygon_cyclic (a b c q : ℤ × ℤ) :
    UniqueInterior (trianglePolygon a b c) q ↔
      UniqueInterior (trianglePolygon b c a) q := by
  constructor
  · intro ⟨hq, huniq⟩
    refine ⟨?_, fun p hp => huniq p ?_⟩
    · rw [← interiorLatticePoints_trianglePolygon_cyclic a b c]; exact hq
    · rwa [interiorLatticePoints_trianglePolygon_cyclic a b c]
  · intro ⟨hq, huniq⟩
    refine ⟨?_, fun p hp => huniq p ?_⟩
    · rw [interiorLatticePoints_trianglePolygon_cyclic a b c]; exact hq
    · rwa [← interiorLatticePoints_trianglePolygon_cyclic a b c]

private lemma edgeLatticePoints_eq_endpoints_of_edgeGcd_eq_one
    (p q : ℤ × ℤ) (h : edgeGcd p q = 1) :
    edgeLatticePoints p q = {p, q} := by
  classical
  have hcard := card_edgeLatticePoints p q
  simp only [h] at hcard
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
  exact (Finset.eq_of_subset_of_card_le hsub (by simp [hcard, hcard2])).symm

/-- Under UniqueInterior + chord `edgeGcd = 1`, the unique interior point lies in
one open half after `edgeStep` (not classical Pick). -/
theorem mem_interior_left_or_right_of_uniqueInterior_edgeGcd_eq_one
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    (q : ℤ × ℤ) (hU : UniqueInterior (trianglePolygon a b c) q)
    (hg : edgeGcd (edgeStep a b) c = 1) :
    q ∈ (trianglePolygon a (edgeStep a b) c).interiorLatticePoints ∨
      q ∈ (trianglePolygon (edgeStep a b) b c).interiorLatticePoints := by
  classical
  set p := edgeStep a b
  have hq := (mem_interiorLatticePoints_trianglePolygon_iff a b c q).mp hU.1
  obtain ⟨hmem, hoff⟩ := hq
  obtain ⟨hbc, hac, hab⟩ :=
    latticeDet_pos_of_memClosedTriangle_offBoundary a b c q hmem hD hoff
  have hmul := latticeDet_edgeStep_mul a b q (by omega : 1 ≤ edgeGcd a b)
  have hdpos : (0 : ℤ) < (edgeGcd a b : ℤ) := by exact_mod_cast (by omega : 0 < edgeGcd a b)
  have hap : 0 < latticeDet a p q := by
    have : latticeDet a p q * (edgeGcd a b : ℤ) = latticeDet a b q := by simpa [p] using hmul
    nlinarith
  have hp_mem := edgeStep_mem_edgeLatticePoints a b (by omega)
  have hadd := latticeDet_add_of_mem_edgeLatticePoints a b q p hp_mem
  have hpb : 0 < latticeDet p b q := by
    have : latticeDet a b q = latticeDet a p q + latticeDet p b q := by simpa [p] using hadd
    nlinarith
  have hD1 : 0 < latticeDet a p c := latticeDet_edgeStep_pos a b c hD (by omega)
  have hD2 : 0 < latticeDet p b c := latticeDet_edgeStep_right_pos a b c hD hd
  rcases lt_trichotomy (latticeDet p c q) 0 with hlt | heq | hgt
  · -- right half
    have hprc : 0 ≤ latticeDet p q c := by
      have : latticeDet p q c = -latticeDet p c q := latticeDet_swap_sign p c q
      nlinarith
    have hmemR : MemClosedTriangle p b c q :=
      memClosedTriangle_of_area_weights_nonneg p b c q hD2 (le_of_lt hbc) hprc (le_of_lt hpb)
    have hoffR : OffTriangleBoundary p b c q := by
      refine ⟨?_, ?_, ?_⟩
      · intro hpb_edge
        have : latticeDet p b q = 0 := latticeDet_eq_zero_of_mem_edge_ab p b q hpb_edge
        omega
      · intro hbc_edge
        exact hoff.2.1 hbc_edge
      · intro hcp_edge
        have hpc_edge : q ∈ edgeLatticePoints p c := mem_edgeLatticePoints_comm hcp_edge
        have : latticeDet p c q = 0 := latticeDet_eq_zero_of_mem_edge_ab p c q hpc_edge
        omega
    exact Or.inr ((mem_interiorLatticePoints_trianglePolygon_iff p b c q).mpr ⟨hmemR, hoffR⟩)
  · -- on the chord
    have hmemL : MemClosedTriangle a p c q :=
      memClosedTriangle_of_area_weights_nonneg a p c q hD1 (le_of_eq heq.symm)
        (le_of_lt hac) (le_of_lt hap)
    have hpc_edge : q ∈ edgeLatticePoints p c :=
      mem_edgeLatticePoints_of_weight_zero_bc a p c q hmemL hD1 heq
    have heq_end : edgeLatticePoints p c = {p, c} :=
      edgeLatticePoints_eq_endpoints_of_edgeGcd_eq_one p c hg
    have hq_end : q = p ∨ q = c := by
      have : q ∈ ({p, c} : Finset (ℤ × ℤ)) := by simpa [heq_end] using hpc_edge
      simpa [Finset.mem_insert, Finset.mem_singleton] using this
    rcases hq_end with hqp | hqc
    · exact (hoff.1 (by simpa [hqp, p] using hp_mem)).elim
    · exact (hoff.2.2 (by simpa [hqc] using self_mem_edgeLatticePoints c a)).elim
  · -- left half
    have hmemL : MemClosedTriangle a p c q :=
      memClosedTriangle_of_area_weights_nonneg a p c q hD1 (le_of_lt hgt)
        (le_of_lt hac) (le_of_lt hap)
    have hoffL : OffTriangleBoundary a p c q := by
      refine ⟨?_, ?_, ?_⟩
      · intro hap_edge
        have : latticeDet a p q = 0 := latticeDet_eq_zero_of_mem_edge_ab a p q hap_edge
        omega
      · intro hpc_edge
        have : latticeDet p c q = 0 := latticeDet_eq_zero_of_mem_edge_ab p c q hpc_edge
        omega
      · intro hca_edge
        exact hoff.2.2 hca_edge
    exact Or.inl ((mem_interiorLatticePoints_trianglePolygon_iff a p c q).mpr ⟨hmemL, hoffL⟩)

/-- Helper: UniqueInterior Pick when a designated edge has `edgeGcd ≥ 2`. -/
theorem shoelace_eq_one_add_B_div_two_sub_one_of_unique_interior_triangle_of_edgeStep_ab
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q : ℤ × ℤ} (hU : UniqueInterior (trianglePolygon a b c) q)
    (ih : ∀ a' b' c' : ℤ × ℤ,
      0 < latticeDet a' b' c' →
      UniqueInterior (trianglePolygon a' b' c') q →
      Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) →
      (trianglePolygon a' b' c').shoelace =
        (1 : ℚ) + ((trianglePolygon a' b' c').B : ℚ) / 2 - 1) :
    (trianglePolygon a b c).shoelace =
      (1 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by
  classical
  set p := edgeStep a b
  have hlt := natAbs_latticeDet_edgeStep_lt a b c hD hd
  have hD1 : 0 < latticeDet a p c := latticeDet_edgeStep_pos a b c hD (by omega)
  have hD2 : 0 < latticeDet p b c := latticeDet_edgeStep_right_pos a b c hD hd
  have hg_le : edgeGcd p c ≤ 2 := by
    simpa [p] using edgeGcd_le_two_of_uniqueInterior_edgeStep a b c hD hd hU
  have hsa := shoelace_add_of_edgeStep a b c hD hd
  have hBa := B_add_of_edgeStep_of_gcd a b c hD hd
  have hpne : p ≠ c := by
    intro hpc
    have hp := edgeStep_mem_edgeLatticePoints a b (by omega)
    have : latticeDet a b c = 0 := by
      simpa [hpc] using latticeDet_eq_zero_of_mem_edge_ab a b p hp
    omega
  have hg_pos : 1 ≤ edgeGcd p c :=
    Nat.pos_of_ne_zero fun hz => hpne ((edgeGcd_eq_zero_iff p c).mp hz)
  have hg_cases : edgeGcd p c = 1 ∨ edgeGcd p c = 2 := by omega
  rcases hg_cases with hg1 | hg2
  · have hloc :=
      mem_interior_left_or_right_of_uniqueInterior_edgeGcd_eq_one a b c hD hd q hU
        (by simpa [p] using hg1)
    rcases hloc with hqL | hqR
    · have hUL := UniqueInterior_trianglePolygon_of_edgeStep_left a b c hD hd hU hqL
      have hER := EmptyInterior_edgeStep_right_of_uniqueInterior_left a b c hD hd hU hqL
      have ihL := ih a p c hD1 hUL hlt.1
      have heR := shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle p b c hD2 hER
      have hBsum : (trianglePolygon a p c).B + (trianglePolygon p b c).B =
          (trianglePolygon a b c).B + 2 := by simpa [p, hg1] using hBa
      calc
        (trianglePolygon a b c).shoelace
            = (trianglePolygon a p c).shoelace + (trianglePolygon p b c).shoelace := hsa
        _ = ((1 : ℚ) + ((trianglePolygon a p c).B : ℚ) / 2 - 1) +
              (((trianglePolygon p b c).B : ℚ) / 2 - 1) := by rw [ihL, heR]
        _ = (((trianglePolygon a p c).B : ℚ) + (trianglePolygon p b c).B) / 2 - 1 := by ring
        _ = (((trianglePolygon a p c).B + (trianglePolygon p b c).B : ℕ) : ℚ) / 2 - 1 := by
              push_cast; rfl
        _ = (((trianglePolygon a b c).B + 2 : ℕ) : ℚ) / 2 - 1 := by rw [hBsum]
        _ = ((trianglePolygon a b c).B : ℚ) / 2 + 1 - 1 := by push_cast; ring
        _ = (1 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by ring
    · have hUR := UniqueInterior_trianglePolygon_of_edgeStep_right a b c hD hd hU hqR
      have hEL := EmptyInterior_edgeStep_left_of_uniqueInterior_right a b c hD hd hU hqR
      have ihR := ih p b c hD2 hUR hlt.2
      have heL := shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle a p c hD1 hEL
      have hBsum : (trianglePolygon a p c).B + (trianglePolygon p b c).B =
          (trianglePolygon a b c).B + 2 := by simpa [p, hg1] using hBa
      calc
        (trianglePolygon a b c).shoelace
            = (trianglePolygon a p c).shoelace + (trianglePolygon p b c).shoelace := hsa
        _ = ((((trianglePolygon a p c).B : ℚ) / 2 - 1) +
              ((1 : ℚ) + ((trianglePolygon p b c).B : ℚ) / 2 - 1)) := by rw [heL, ihR]
        _ = (((trianglePolygon a p c).B : ℚ) + (trianglePolygon p b c).B) / 2 - 1 := by ring
        _ = (((trianglePolygon a p c).B + (trianglePolygon p b c).B : ℕ) : ℚ) / 2 - 1 := by
              push_cast; rfl
        _ = (((trianglePolygon a b c).B + 2 : ℕ) : ℚ) / 2 - 1 := by rw [hBsum]
        _ = ((trianglePolygon a b c).B : ℚ) / 2 + 1 - 1 := by push_cast; ring
        _ = (1 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by ring
  · have hboth :=
      EmptyInterior_edgeStep_both_of_uniqueInterior_edgeGcd_eq_two a b c hD hd hU
        (by simpa [p] using hg2)
    have he1 := shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle a p c hD1 hboth.1
    have he2 := shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle p b c hD2 hboth.2
    have hBsum : (trianglePolygon a p c).B + (trianglePolygon p b c).B =
        (trianglePolygon a b c).B + 4 := by
      have hBsum' : (trianglePolygon a p c).B + (trianglePolygon p b c).B =
          (trianglePolygon a b c).B + 2 * edgeGcd p c := by simpa [p] using hBa
      simpa [hg2] using hBsum'
    calc
      (trianglePolygon a b c).shoelace
          = (trianglePolygon a p c).shoelace + (trianglePolygon p b c).shoelace := hsa
      _ = ((((trianglePolygon a p c).B : ℚ) / 2 - 1) +
            (((trianglePolygon p b c).B : ℚ) / 2 - 1)) := by rw [he1, he2]
      _ = (((trianglePolygon a p c).B : ℚ) + (trianglePolygon p b c).B) / 2 - 2 := by ring
      _ = (((trianglePolygon a p c).B + (trianglePolygon p b c).B : ℕ) : ℚ) / 2 - 2 := by
            push_cast; rfl
      _ = (((trianglePolygon a b c).B + 4 : ℕ) : ℚ) / 2 - 2 := by rw [hBsum]
      _ = ((trianglePolygon a b c).B : ℚ) / 2 + 2 - 2 := by push_cast; ring
      _ = (1 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by ring

/-- UniqueInterior closed lattice triangle Pick-form without `PrimitiveEdges`, by
induction on `|det|` via `edgeStep` splits (not classical Pick). -/
theorem shoelace_eq_one_add_B_div_two_sub_one_of_unique_interior_triangle
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c)
    {q : ℤ × ℤ} (hU : UniqueInterior (trianglePolygon a b c) q) :
    (trianglePolygon a b c).shoelace =
      (1 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by
  classical
  generalize hn : Int.natAbs (latticeDet a b c) = n
  revert a b c
  refine Nat.strong_induction_on n fun n ih a b c hD hU hn => ?_
  have _hpos := edgeGcd_pos_of_latticeDet_pos a b c hD
  by_cases hprim : edgeGcd a b = 1 ∧ edgeGcd b c = 1 ∧ edgeGcd c a = 1
  · have hedge :=
      PrimitiveEdges_trianglePolygon_of_edgeGcds a b c hprim.1 hprim.2.1 hprim.2.2
    exact shoelace_eq_I_add_B_div_two_sub_one_of_uniqueInterior
      (trianglePolygon a b c)
      (injective_vertex_trianglePolygon a b c (ne_of_gt hD))
      hedge (StrictlyConvexCCW_trianglePolygon a b c hD) hU
  · have hge : 2 ≤ edgeGcd a b ∨ 2 ≤ edgeGcd b c ∨ 2 ≤ edgeGcd c a := by omega
    have ih' : ∀ a' b' c' : ℤ × ℤ,
        0 < latticeDet a' b' c' →
        UniqueInterior (trianglePolygon a' b' c') q →
        Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) →
        (trianglePolygon a' b' c').shoelace =
          (1 : ℚ) + ((trianglePolygon a' b' c').B : ℚ) / 2 - 1 := by
      intro a' b' c' hD' hU' hlt'
      have hltn : Int.natAbs (latticeDet a' b' c') < n := by simpa [hn] using hlt'
      exact ih _ hltn a' b' c' hD' hU' rfl
    rcases hge with hab | hbc | hca
    · subst hn
      exact shoelace_eq_one_add_B_div_two_sub_one_of_unique_interior_triangle_of_edgeStep_ab
        a b c hD hab hU ih'
    · have hDc : 0 < latticeDet b c a := by simpa [← latticeDet_cyclic a b c] using hD
      have hUc : UniqueInterior (trianglePolygon b c a) q :=
        (UniqueInterior_trianglePolygon_cyclic a b c q).mp hU
      have ihc : ∀ a' b' c' : ℤ × ℤ,
          0 < latticeDet a' b' c' →
          UniqueInterior (trianglePolygon a' b' c') q →
          Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet b c a) →
          (trianglePolygon a' b' c').shoelace =
            (1 : ℚ) + ((trianglePolygon a' b' c').B : ℚ) / 2 - 1 := by
        intro a' b' c' hD' hU' hlt'
        have : Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) := by
          simpa [← latticeDet_cyclic a b c] using hlt'
        exact ih' a' b' c' hD' hU' this
      have hpick :=
        shoelace_eq_one_add_B_div_two_sub_one_of_unique_interior_triangle_of_edgeStep_ab
          b c a hDc hbc hUc ihc
      rw [shoelace_trianglePolygon_cyclic a b c,
          B_trianglePolygon_cyclic a b c (ne_of_gt hD)]
      exact hpick
    · have hDc : 0 < latticeDet c a b := by simpa [← latticeDet_cyclic₂ a b c] using hD
      have hUc : UniqueInterior (trianglePolygon c a b) q := by
        have h1 := (UniqueInterior_trianglePolygon_cyclic a b c q).mp hU
        exact (UniqueInterior_trianglePolygon_cyclic b c a q).mp h1
      have ihc : ∀ a' b' c' : ℤ × ℤ,
          0 < latticeDet a' b' c' →
          UniqueInterior (trianglePolygon a' b' c') q →
          Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet c a b) →
          (trianglePolygon a' b' c').shoelace =
            (1 : ℚ) + ((trianglePolygon a' b' c').B : ℚ) / 2 - 1 := by
        intro a' b' c' hD' hU' hlt'
        have : Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) := by
          simpa [← latticeDet_cyclic₂ a b c] using hlt'
        exact ih' a' b' c' hD' hU' this
      have hpick :=
        shoelace_eq_one_add_B_div_two_sub_one_of_unique_interior_triangle_of_edgeStep_ab
          c a b hDc hca hUc ihc
      have hs1 := shoelace_trianglePolygon_cyclic a b c
      have hs2 := shoelace_trianglePolygon_cyclic b c a
      have hB1 := B_trianglePolygon_cyclic a b c (ne_of_gt hD)
      have hB2 := B_trianglePolygon_cyclic b c a
        (by simpa [← latticeDet_cyclic a b c] using ne_of_gt hD)
      rw [hs1, hs2, hB1, hB2]
      exact hpick

/-! ### I ≤ 1 triangle Pick without `PrimitiveEdges` (not classical Pick) -/

/-- I ∈ {0,1} shoelace Pick-form for a closed lattice triangle without
`PrimitiveEdges` (not classical Pick). -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_one_triangle
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c)
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = (trianglePolygon a b c).interiorLatticePoints)
    (hcard : S.card ≤ 1) :
    (trianglePolygon a b c).shoelace =
      (S.card : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by
  classical
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · have hSempty : S = ∅ := Finset.card_eq_zero.mp h0
    have hI : EmptyInterior (trianglePolygon a b c) := by
      simpa [EmptyInterior, hSempty] using hS.symm
    have harea :=
      shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle a b c hD hI
    calc
      (trianglePolygon a b c).shoelace
          = ((trianglePolygon a b c).B : ℚ) / 2 - 1 := harea
      _ = (0 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by ring
      _ = (S.card : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by simp [h0]
  · have h1 : S.card = 1 := by omega
    obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp h1
    have hU : UniqueInterior (trianglePolygon a b c) q := by
      refine ⟨?_, ?_⟩
      · have : q ∈ (({q} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by simp
        rwa [← hS]
      · intro p hp
        have hpS : p ∈ ({q} : Finset (ℤ × ℤ)) := by
          change p ∈ (({q} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))
          rwa [hS]
        simpa using hpS
    have harea :=
      shoelace_eq_one_add_B_div_two_sub_one_of_unique_interior_triangle a b c hD hU
    simpa [h1] using harea



/-! ### TwoInterior triangle substrate without `PrimitiveEdges` -/

lemma TwoInterior_trianglePolygon_cyclic (a b c q r : ℤ × ℤ) :
    TwoInterior (trianglePolygon a b c) q r ↔
      TwoInterior (trianglePolygon b c a) q r := by
  constructor
  · intro ⟨hne, hset⟩
    refine ⟨hne, ?_⟩
    rw [← interiorLatticePoints_trianglePolygon_cyclic a b c, hset]
  · intro ⟨hne, hset⟩
    refine ⟨hne, ?_⟩
    rw [interiorLatticePoints_trianglePolygon_cyclic a b c, hset]

/-- Any interior point after `edgeStep` lies in the left half, right half, or open
chord (not classical Pick). -/
theorem mem_interior_left_or_right_or_chord_of_mem_interior_edgeStep
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q : ℤ × ℤ}
    (hq : q ∈ (trianglePolygon a b c).interiorLatticePoints) :
    q ∈ (trianglePolygon a (edgeStep a b) c).interiorLatticePoints ∨
      q ∈ (trianglePolygon (edgeStep a b) b c).interiorLatticePoints ∨
        (q ∈ edgeLatticePoints (edgeStep a b) c ∧ q ≠ edgeStep a b ∧ q ≠ c) := by
  classical
  set p := edgeStep a b
  have hq' := (mem_interiorLatticePoints_trianglePolygon_iff a b c q).mp hq
  obtain ⟨hmem, hoff⟩ := hq'
  obtain ⟨hbc, hac, hab⟩ :=
    latticeDet_pos_of_memClosedTriangle_offBoundary a b c q hmem hD hoff
  have hmul := latticeDet_edgeStep_mul a b q (by omega : 1 ≤ edgeGcd a b)
  have hdpos : (0 : ℤ) < (edgeGcd a b : ℤ) := by exact_mod_cast (by omega : 0 < edgeGcd a b)
  have hap : 0 < latticeDet a p q := by
    have : latticeDet a p q * (edgeGcd a b : ℤ) = latticeDet a b q := by simpa [p] using hmul
    nlinarith
  have hp_mem := edgeStep_mem_edgeLatticePoints a b (by omega)
  have hadd := latticeDet_add_of_mem_edgeLatticePoints a b q p hp_mem
  have hpb : 0 < latticeDet p b q := by
    have : latticeDet a b q = latticeDet a p q + latticeDet p b q := by simpa [p] using hadd
    nlinarith
  have hD1 : 0 < latticeDet a p c := latticeDet_edgeStep_pos a b c hD (by omega)
  have hD2 : 0 < latticeDet p b c := latticeDet_edgeStep_right_pos a b c hD hd
  rcases lt_trichotomy (latticeDet p c q) 0 with hlt | heq | hgt
  · have hprc : 0 ≤ latticeDet p q c := by
      have : latticeDet p q c = -latticeDet p c q := latticeDet_swap_sign p c q
      nlinarith
    have hmemR : MemClosedTriangle p b c q :=
      memClosedTriangle_of_area_weights_nonneg p b c q hD2 (le_of_lt hbc) hprc (le_of_lt hpb)
    have hoffR : OffTriangleBoundary p b c q := by
      refine ⟨?_, ?_, ?_⟩
      · intro hpb_edge
        have : latticeDet p b q = 0 := latticeDet_eq_zero_of_mem_edge_ab p b q hpb_edge
        omega
      · intro hbc_edge
        exact hoff.2.1 hbc_edge
      · intro hcp_edge
        have hpc_edge : q ∈ edgeLatticePoints p c := mem_edgeLatticePoints_comm hcp_edge
        have : latticeDet p c q = 0 := latticeDet_eq_zero_of_mem_edge_ab p c q hpc_edge
        omega
    exact Or.inr (Or.inl
      ((mem_interiorLatticePoints_trianglePolygon_iff p b c q).mpr ⟨hmemR, hoffR⟩))
  · have hmemL : MemClosedTriangle a p c q :=
      memClosedTriangle_of_area_weights_nonneg a p c q hD1 (le_of_eq heq.symm)
        (le_of_lt hac) (le_of_lt hap)
    have hpc_edge : q ∈ edgeLatticePoints p c :=
      mem_edgeLatticePoints_of_weight_zero_bc a p c q hmemL hD1 heq
    have hqne_p : q ≠ p := by
      intro hqp
      exact hoff.1 (by simpa [hqp, p] using hp_mem)
    have hqne_c : q ≠ c := by
      intro hqc
      exact hoff.2.2 (by simpa [hqc] using self_mem_edgeLatticePoints c a)
    exact Or.inr (Or.inr ⟨by simpa [p] using hpc_edge, by simpa [p] using hqne_p, hqne_c⟩)
  · have hmemL : MemClosedTriangle a p c q :=
      memClosedTriangle_of_area_weights_nonneg a p c q hD1 (le_of_lt hgt)
        (le_of_lt hac) (le_of_lt hap)
    have hoffL : OffTriangleBoundary a p c q := by
      refine ⟨?_, ?_, ?_⟩
      · intro hap_edge
        have : latticeDet a p q = 0 := latticeDet_eq_zero_of_mem_edge_ab a p q hap_edge
        omega
      · intro hpc_edge
        have : latticeDet p c q = 0 := latticeDet_eq_zero_of_mem_edge_ab p c q hpc_edge
        omega
      · intro hca_edge
        exact hoff.2.2 hca_edge
    exact Or.inl ((mem_interiorLatticePoints_trianglePolygon_iff a p c q).mpr ⟨hmemL, hoffL⟩)

/-- TwoInterior ⇒ open chord after `edgeStep` has `edgeGcd ≤ 3`. -/
theorem edgeGcd_le_three_of_twoInterior_edgeStep
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q r : ℤ × ℤ} (hT : TwoInterior (trianglePolygon a b c) q r) :
    edgeGcd (edgeStep a b) c ≤ 3 := by
  classical
  set p := edgeStep a b
  by_contra hgt
  have hge : 4 ≤ edgeGcd p c := by omega
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
  have hcard_ge : 3 ≤ (((edgeLatticePoints p c).erase p).erase c).card := by omega
  have hinter : (trianglePolygon a b c).interiorLatticePoints = ({q, r} : Set (ℤ × ℤ)) :=
    hT.2
  have hsub :
      ((edgeLatticePoints p c).erase p).erase c ⊆ ({q, r} : Finset (ℤ × ℤ)) := by
    intro x hx
    have hx' := Finset.mem_erase.mp hx
    have hx'' := Finset.mem_erase.mp hx'.2
    have hint := mem_interiorLatticePoints_of_strict_mem_edgeStep_chord a b c hD hd
      hx''.2 hx''.1 hx'.1
    have hx_eq : x = q ∨ x = r := by
      have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
        rw [← hinter]; exact hint
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    exact Finset.mem_insert.mpr (by simpa [Finset.mem_singleton] using hx_eq)
  have hcard_le :
      (((edgeLatticePoints p c).erase p).erase c).card ≤ ({q, r} : Finset (ℤ × ℤ)).card :=
    Finset.card_le_card hsub
  have hne : q ≠ r := hT.1
  have hcard_qr : ({q, r} : Finset (ℤ × ℤ)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have : (((edgeLatticePoints p c).erase p).erase c).card ≤ 2 := by
    simpa [hcard_qr] using hcard_le
  omega

theorem TwoInterior_trianglePolygon_of_edgeStep_left
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q r : ℤ × ℤ} (hT : TwoInterior (trianglePolygon a b c) q r)
    (hq : q ∈ (trianglePolygon a (edgeStep a b) c).interiorLatticePoints)
    (hr : r ∈ (trianglePolygon a (edgeStep a b) c).interiorLatticePoints) :
    TwoInterior (trianglePolygon a (edgeStep a b) c) q r := by
  refine ⟨hT.1, ?_⟩
  ext x
  constructor
  · intro hx
    have hint :=
      mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_left a b c hD hd hx
    have hxqr : x = q ∨ x = r := by
      have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
        rw [← hT.2]; exact hint
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hxqr
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption

theorem TwoInterior_trianglePolygon_of_edgeStep_right
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q r : ℤ × ℤ} (hT : TwoInterior (trianglePolygon a b c) q r)
    (hq : q ∈ (trianglePolygon (edgeStep a b) b c).interiorLatticePoints)
    (hr : r ∈ (trianglePolygon (edgeStep a b) b c).interiorLatticePoints) :
    TwoInterior (trianglePolygon (edgeStep a b) b c) q r := by
  refine ⟨hT.1, ?_⟩
  ext x
  constructor
  · intro hx
    have hint :=
      mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_right a b c hD hd hx
    have hxqr : x = q ∨ x = r := by
      have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
        rw [← hT.2]; exact hint
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hxqr
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption

theorem EmptyInterior_edgeStep_right_of_twoInterior_left
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q r : ℤ × ℤ} (hT : TwoInterior (trianglePolygon a b c) q r)
    (hq : q ∈ (trianglePolygon a (edgeStep a b) c).interiorLatticePoints)
    (hr : r ∈ (trianglePolygon a (edgeStep a b) c).interiorLatticePoints) :
    EmptyInterior (trianglePolygon (edgeStep a b) b c) := by
  classical
  set p := edgeStep a b
  rw [EmptyInterior]
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hint :=
    mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_right a b c hD hd hx
  have hxqr : x = q ∨ x = r := by
    have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
      rw [← hT.2]; exact hint
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have hD1 : 0 < latticeDet a p c := latticeDet_edgeStep_pos a b c hD (by omega)
  have hD2 : 0 < latticeDet p b c := latticeDet_edgeStep_right_pos a b c hD hd
  rcases hxqr with rfl | rfl
  · -- subst gave x = q
    have hL := (mem_interiorLatticePoints_trianglePolygon_iff a p c x).mp hq
    have hR := (mem_interiorLatticePoints_trianglePolygon_iff p b c x).mp hx
    have hposL := latticeDet_pos_of_memClosedTriangle_offBoundary a p c x hL.1 hD1 hL.2
    have hposR := latticeDet_pos_of_memClosedTriangle_offBoundary p b c x hR.1 hD2 hR.2
    have h1 : 0 < latticeDet p c x := hposL.1
    have h2 : 0 < latticeDet p x c := hposR.2.1
    have hneg := latticeDet_pqc_neg p c x
    omega
  · -- subst gave x = r
    have hL := (mem_interiorLatticePoints_trianglePolygon_iff a p c x).mp hr
    have hR := (mem_interiorLatticePoints_trianglePolygon_iff p b c x).mp hx
    have hposL := latticeDet_pos_of_memClosedTriangle_offBoundary a p c x hL.1 hD1 hL.2
    have hposR := latticeDet_pos_of_memClosedTriangle_offBoundary p b c x hR.1 hD2 hR.2
    have h1 : 0 < latticeDet p c x := hposL.1
    have h2 : 0 < latticeDet p x c := hposR.2.1
    have hneg := latticeDet_pqc_neg p c x
    omega

theorem EmptyInterior_edgeStep_left_of_twoInterior_right
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q r : ℤ × ℤ} (hT : TwoInterior (trianglePolygon a b c) q r)
    (hq : q ∈ (trianglePolygon (edgeStep a b) b c).interiorLatticePoints)
    (hr : r ∈ (trianglePolygon (edgeStep a b) b c).interiorLatticePoints) :
    EmptyInterior (trianglePolygon a (edgeStep a b) c) := by
  classical
  set p := edgeStep a b
  rw [EmptyInterior]
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hint :=
    mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_left a b c hD hd hx
  have hxqr : x = q ∨ x = r := by
    have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
      rw [← hT.2]; exact hint
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have hD1 : 0 < latticeDet a p c := latticeDet_edgeStep_pos a b c hD (by omega)
  have hD2 : 0 < latticeDet p b c := latticeDet_edgeStep_right_pos a b c hD hd
  rcases hxqr with rfl | rfl
  · have hR := (mem_interiorLatticePoints_trianglePolygon_iff p b c x).mp hq
    have hL := (mem_interiorLatticePoints_trianglePolygon_iff a p c x).mp hx
    have hposL := latticeDet_pos_of_memClosedTriangle_offBoundary a p c x hL.1 hD1 hL.2
    have hposR := latticeDet_pos_of_memClosedTriangle_offBoundary p b c x hR.1 hD2 hR.2
    have h1 : 0 < latticeDet p c x := hposL.1
    have h2 : 0 < latticeDet p x c := hposR.2.1
    have hneg := latticeDet_pqc_neg p c x
    omega
  · have hR := (mem_interiorLatticePoints_trianglePolygon_iff p b c x).mp hr
    have hL := (mem_interiorLatticePoints_trianglePolygon_iff a p c x).mp hx
    have hposL := latticeDet_pos_of_memClosedTriangle_offBoundary a p c x hL.1 hD1 hL.2
    have hposR := latticeDet_pos_of_memClosedTriangle_offBoundary p b c x hR.1 hD2 hR.2
    have h1 : 0 < latticeDet p c x := hposL.1
    have h2 : 0 < latticeDet p x c := hposR.2.1
    have hneg := latticeDet_pqc_neg p c x
    omega

/-- Under TwoInterior + chord `edgeGcd = 3`, both halves are empty (both interiors
lie on the open chord; not classical Pick). -/
theorem EmptyInterior_edgeStep_both_of_twoInterior_edgeGcd_eq_three
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q r : ℤ × ℤ} (hT : TwoInterior (trianglePolygon a b c) q r)
    (hg : edgeGcd (edgeStep a b) c = 3) :
    EmptyInterior (trianglePolygon a (edgeStep a b) c) ∧
      EmptyInterior (trianglePolygon (edgeStep a b) b c) := by
  classical
  set p := edgeStep a b
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
  have hcard_eq : (((edgeLatticePoints p c).erase p).erase c).card = 2 := by
    simpa [hg] using hcard2
  have hne : q ≠ r := hT.1
  have hsub :
      ((edgeLatticePoints p c).erase p).erase c ⊆ ({q, r} : Finset (ℤ × ℤ)) := by
    intro x hx
    have hx' := Finset.mem_erase.mp hx
    have hx'' := Finset.mem_erase.mp hx'.2
    have hint := mem_interiorLatticePoints_of_strict_mem_edgeStep_chord a b c hD hd
      hx''.2 hx''.1 hx'.1
    have hx_eq : x = q ∨ x = r := by
      have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
        rw [← hT.2]; exact hint
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    exact Finset.mem_insert.mpr (by simpa [Finset.mem_singleton] using hx_eq)
  have hcard_qr : ({q, r} : Finset (ℤ × ℤ)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have heq_set :
      ((edgeLatticePoints p c).erase p).erase c = ({q, r} : Finset (ℤ × ℤ)) :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hcard_eq, hcard_qr])
  have hq_on : q ∈ ((edgeLatticePoints p c).erase p).erase c := by
    simp [heq_set]
  have hq_chord : q ∈ edgeLatticePoints p c :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hq_on).2).2
  have hr_on : r ∈ ((edgeLatticePoints p c).erase p).erase c := by
    simp [heq_set]
  have hr_chord : r ∈ edgeLatticePoints p c :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hr_on).2).2
  refine ⟨?_, ?_⟩
  · rw [EmptyInterior]
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have hint :=
      mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_left a b c hD hd hx
    have hxqr : x = q ∨ x = r := by
      have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
        rw [← hT.2]; exact hint
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    have hx' := (mem_interiorLatticePoints_trianglePolygon_iff a p c x).mp hx
    have hnot : x ∉ edgeLatticePoints p c := hx'.2.2.1
    rcases hxqr with rfl | rfl
    · exact hnot hq_chord
    · exact hnot hr_chord
  · rw [EmptyInterior]
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have hint :=
      mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_right a b c hD hd hx
    have hxqr : x = q ∨ x = r := by
      have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
        rw [← hT.2]; exact hint
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    have hx' := (mem_interiorLatticePoints_trianglePolygon_iff p b c x).mp hx
    have hnot : x ∉ edgeLatticePoints c p := hx'.2.2.2
    have hnot' : x ∉ edgeLatticePoints p c := fun h => hnot (mem_edgeLatticePoints_comm h)
    rcases hxqr with rfl | rfl
    · exact hnot' hq_chord
    · exact hnot' hr_chord



/-! ### TwoInterior / I≤2 triangle Pick without `PrimitiveEdges` -/

/-- Under TwoInterior + chord `edgeGcd = 1`, each interior point lies in an open half. -/
theorem mem_interior_left_or_right_of_twoInterior_edgeGcd_eq_one
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q r : ℤ × ℤ} (hT : TwoInterior (trianglePolygon a b c) q r)
    (hg : edgeGcd (edgeStep a b) c = 1)
    {s : ℤ × ℤ} (hs : s = q ∨ s = r) :
    s ∈ (trianglePolygon a (edgeStep a b) c).interiorLatticePoints ∨
      s ∈ (trianglePolygon (edgeStep a b) b c).interiorLatticePoints := by
  classical
  have hs_int : s ∈ (trianglePolygon a b c).interiorLatticePoints := by
    rw [hT.2]
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hs
  rcases mem_interior_left_or_right_or_chord_of_mem_interior_edgeStep a b c hD hd hs_int with
    hL | hR | hch
  · exact Or.inl hL
  · exact Or.inr hR
  · -- chord impossible when gcd = 1
    set p := edgeStep a b
    have heq_end : edgeLatticePoints p c = {p, c} :=
      edgeLatticePoints_eq_endpoints_of_edgeGcd_eq_one p c (by simpa [p] using hg)
    have hs_end : s = p ∨ s = c := by
      have : s ∈ ({p, c} : Finset (ℤ × ℤ)) := by
        simpa [heq_end] using hch.1
      simpa [Finset.mem_insert, Finset.mem_singleton] using this
    rcases hs_end with hsp | hsc
    · exact (hch.2.1 hsp).elim
    · exact (hch.2.2 hsc).elim

theorem UniqueInterior_trianglePolygon_of_twoInterior_edgeStep_left_of_right_empty
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q r : ℤ × ℤ} (hT : TwoInterior (trianglePolygon a b c) q r)
    (hq : q ∈ (trianglePolygon a (edgeStep a b) c).interiorLatticePoints)
    (hrR : r ∈ (trianglePolygon (edgeStep a b) b c).interiorLatticePoints) :
    UniqueInterior (trianglePolygon a (edgeStep a b) c) q ∧
      UniqueInterior (trianglePolygon (edgeStep a b) b c) r := by
  classical
  set p := edgeStep a b
  have hUL : UniqueInterior (trianglePolygon a p c) q := by
    refine ⟨hq, ?_⟩
    intro x hx
    have hint :=
      mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_left a b c hD hd hx
    have hxqr : x = q ∨ x = r := by
      have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
        rw [← hT.2]; exact hint
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    cases hxqr with
    | inl hxq => exact hxq
    | inr hxr =>
      -- x = r, but r is in the right half ⇒ left/right det contradiction
      have hxr' : x = r := hxr
      have hD1 : 0 < latticeDet a p c := latticeDet_edgeStep_pos a b c hD (by omega)
      have hD2 : 0 < latticeDet p b c := latticeDet_edgeStep_right_pos a b c hD hd
      have hL := (mem_interiorLatticePoints_trianglePolygon_iff a p c x).mp hx
      have hR := (mem_interiorLatticePoints_trianglePolygon_iff p b c r).mp hrR
      have hposL := latticeDet_pos_of_memClosedTriangle_offBoundary a p c x hL.1 hD1 hL.2
      have hposR := latticeDet_pos_of_memClosedTriangle_offBoundary p b c r hR.1 hD2 hR.2
      have h1 : 0 < latticeDet p c x := hposL.1
      have h2 : 0 < latticeDet p r c := hposR.2.1
      have hneg := latticeDet_pqc_neg p c r
      simp [hxr'] at h1
      omega
  have hUR : UniqueInterior (trianglePolygon p b c) r := by
    refine ⟨hrR, ?_⟩
    intro x hx
    have hint :=
      mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_right a b c hD hd hx
    have hxqr : x = q ∨ x = r := by
      have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
        rw [← hT.2]; exact hint
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    cases hxqr with
    | inl hxq =>
      have hxq' : x = q := hxq
      have hD1 : 0 < latticeDet a p c := latticeDet_edgeStep_pos a b c hD (by omega)
      have hD2 : 0 < latticeDet p b c := latticeDet_edgeStep_right_pos a b c hD hd
      have hL := (mem_interiorLatticePoints_trianglePolygon_iff a p c q).mp hq
      have hR := (mem_interiorLatticePoints_trianglePolygon_iff p b c x).mp hx
      have hposL := latticeDet_pos_of_memClosedTriangle_offBoundary a p c q hL.1 hD1 hL.2
      have hposR := latticeDet_pos_of_memClosedTriangle_offBoundary p b c x hR.1 hD2 hR.2
      have h1 : 0 < latticeDet p c q := hposL.1
      have h2 : 0 < latticeDet p x c := hposR.2.1
      have hneg := latticeDet_pqc_neg p c q
      simp [hxq'] at h2
      omega
    | inr hxr => exact hxr
  exact ⟨hUL, hUR⟩

/-- Helper: TwoInterior Pick when a designated edge has `edgeGcd ≥ 2`. -/
theorem shoelace_eq_two_add_B_div_two_sub_one_of_two_interior_triangle_of_edgeStep_ab
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    {q r : ℤ × ℤ} (hT : TwoInterior (trianglePolygon a b c) q r)
    (ih : ∀ a' b' c' : ℤ × ℤ,
      0 < latticeDet a' b' c' →
      TwoInterior (trianglePolygon a' b' c') q r →
      Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) →
      (trianglePolygon a' b' c').shoelace =
        (2 : ℚ) + ((trianglePolygon a' b' c').B : ℚ) / 2 - 1) :
    (trianglePolygon a b c).shoelace =
      (2 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by
  classical
  set p := edgeStep a b
  have hlt := natAbs_latticeDet_edgeStep_lt a b c hD hd
  have hD1 : 0 < latticeDet a p c := latticeDet_edgeStep_pos a b c hD (by omega)
  have hD2 : 0 < latticeDet p b c := latticeDet_edgeStep_right_pos a b c hD hd
  have hg_le : edgeGcd p c ≤ 3 := by
    simpa [p] using edgeGcd_le_three_of_twoInterior_edgeStep a b c hD hd hT
  have hsa := shoelace_add_of_edgeStep a b c hD hd
  have hBa := B_add_of_edgeStep_of_gcd a b c hD hd
  have hpne : p ≠ c := by
    intro hpc
    have hp := edgeStep_mem_edgeLatticePoints a b (by omega)
    have : latticeDet a b c = 0 := by
      simpa [hpc] using latticeDet_eq_zero_of_mem_edge_ab a b p hp
    omega
  have hg_pos : 1 ≤ edgeGcd p c :=
    Nat.pos_of_ne_zero fun hz => hpne ((edgeGcd_eq_zero_iff p c).mp hz)
  have hg_cases : edgeGcd p c = 1 ∨ edgeGcd p c = 2 ∨ edgeGcd p c = 3 := by omega
  -- locate q and r
  have hq_int := (show q ∈ (trianglePolygon a b c).interiorLatticePoints by
    rw [hT.2]; simp)
  have hr_int := (show r ∈ (trianglePolygon a b c).interiorLatticePoints by
    rw [hT.2]; simp)
  rcases hg_cases with hg1 | hg2 | hg3
  · -- g = 1: both in halves
    have hlocq :=
      mem_interior_left_or_right_of_twoInterior_edgeGcd_eq_one a b c hD hd hT
        (by simpa [p] using hg1) (Or.inl rfl)
    have hlocr :=
      mem_interior_left_or_right_of_twoInterior_edgeGcd_eq_one a b c hD hd hT
        (by simpa [p] using hg1) (Or.inr rfl)
    have hBsum : (trianglePolygon a p c).B + (trianglePolygon p b c).B =
        (trianglePolygon a b c).B + 2 := by simpa [p, hg1] using hBa
    rcases hlocq with hqL | hqR
    · rcases hlocr with hrL | hrR
      · -- both left
        have hTL := TwoInterior_trianglePolygon_of_edgeStep_left a b c hD hd hT hqL hrL
        have hER := EmptyInterior_edgeStep_right_of_twoInterior_left a b c hD hd hT hqL hrL
        have ihL := ih a p c hD1 hTL hlt.1
        have heR := shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle p b c hD2 hER
        calc
          (trianglePolygon a b c).shoelace
              = (trianglePolygon a p c).shoelace + (trianglePolygon p b c).shoelace := hsa
          _ = ((2 : ℚ) + ((trianglePolygon a p c).B : ℚ) / 2 - 1) +
                (((trianglePolygon p b c).B : ℚ) / 2 - 1) := by rw [ihL, heR]
          _ = (((trianglePolygon a p c).B : ℚ) + (trianglePolygon p b c).B) / 2 := by ring
          _ = (((trianglePolygon a p c).B + (trianglePolygon p b c).B : ℕ) : ℚ) / 2 := by
                push_cast; rfl
          _ = (((trianglePolygon a b c).B + 2 : ℕ) : ℚ) / 2 := by rw [hBsum]
          _ = ((trianglePolygon a b c).B : ℚ) / 2 + 1 := by push_cast; ring
          _ = (2 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by ring
      · -- q left, r right
        obtain ⟨hUL, hUR⟩ :=
          UniqueInterior_trianglePolygon_of_twoInterior_edgeStep_left_of_right_empty
            a b c hD hd hT hqL hrR
        have ihL :=
          shoelace_eq_one_add_B_div_two_sub_one_of_unique_interior_triangle a p c hD1 hUL
        have ihR :=
          shoelace_eq_one_add_B_div_two_sub_one_of_unique_interior_triangle p b c hD2 hUR
        calc
          (trianglePolygon a b c).shoelace
              = (trianglePolygon a p c).shoelace + (trianglePolygon p b c).shoelace := hsa
          _ = ((1 : ℚ) + ((trianglePolygon a p c).B : ℚ) / 2 - 1) +
                ((1 : ℚ) + ((trianglePolygon p b c).B : ℚ) / 2 - 1) := by rw [ihL, ihR]
          _ = (((trianglePolygon a p c).B : ℚ) + (trianglePolygon p b c).B) / 2 := by ring
          _ = (((trianglePolygon a p c).B + (trianglePolygon p b c).B : ℕ) : ℚ) / 2 := by
                push_cast; rfl
          _ = (((trianglePolygon a b c).B + 2 : ℕ) : ℚ) / 2 := by rw [hBsum]
          _ = ((trianglePolygon a b c).B : ℚ) / 2 + 1 := by push_cast; ring
          _ = (2 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by ring
    · rcases hlocr with hrL | hrR
      · -- q right, r left: swap names via UniqueInterior helper with swapped args
        obtain ⟨hUL, hUR⟩ :=
          UniqueInterior_trianglePolygon_of_twoInterior_edgeStep_left_of_right_empty
            a b c hD hd ⟨hT.1.symm, by simpa [Set.pair_comm] using hT.2⟩ hrL hqR
        -- hUL : UniqueInterior left r, hUR : UniqueInterior right q
        have ihL :=
          shoelace_eq_one_add_B_div_two_sub_one_of_unique_interior_triangle a p c hD1 hUL
        have ihR :=
          shoelace_eq_one_add_B_div_two_sub_one_of_unique_interior_triangle p b c hD2 hUR
        calc
          (trianglePolygon a b c).shoelace
              = (trianglePolygon a p c).shoelace + (trianglePolygon p b c).shoelace := hsa
          _ = ((1 : ℚ) + ((trianglePolygon a p c).B : ℚ) / 2 - 1) +
                ((1 : ℚ) + ((trianglePolygon p b c).B : ℚ) / 2 - 1) := by rw [ihL, ihR]
          _ = (((trianglePolygon a p c).B : ℚ) + (trianglePolygon p b c).B) / 2 := by ring
          _ = (((trianglePolygon a p c).B + (trianglePolygon p b c).B : ℕ) : ℚ) / 2 := by
                push_cast; rfl
          _ = (((trianglePolygon a b c).B + 2 : ℕ) : ℚ) / 2 := by rw [hBsum]
          _ = ((trianglePolygon a b c).B : ℚ) / 2 + 1 := by push_cast; ring
          _ = (2 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by ring
      · -- both right
        have hTR := TwoInterior_trianglePolygon_of_edgeStep_right a b c hD hd hT hqR hrR
        have hEL := EmptyInterior_edgeStep_left_of_twoInterior_right a b c hD hd hT hqR hrR
        have ihR := ih p b c hD2 hTR hlt.2
        have heL := shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle a p c hD1 hEL
        calc
          (trianglePolygon a b c).shoelace
              = (trianglePolygon a p c).shoelace + (trianglePolygon p b c).shoelace := hsa
          _ = ((((trianglePolygon a p c).B : ℚ) / 2 - 1) +
                ((2 : ℚ) + ((trianglePolygon p b c).B : ℚ) / 2 - 1)) := by rw [heL, ihR]
          _ = (((trianglePolygon a p c).B : ℚ) + (trianglePolygon p b c).B) / 2 := by ring
          _ = (((trianglePolygon a p c).B + (trianglePolygon p b c).B : ℕ) : ℚ) / 2 := by
                push_cast; rfl
          _ = (((trianglePolygon a b c).B + 2 : ℕ) : ℚ) / 2 := by rw [hBsum]
          _ = ((trianglePolygon a b c).B : ℚ) / 2 + 1 := by push_cast; ring
          _ = (2 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by ring
  · -- g = 2: one on chord, one in a half
    have hBsum : (trianglePolygon a p c).B + (trianglePolygon p b c).B =
        (trianglePolygon a b c).B + 4 := by
      have hBsum' : (trianglePolygon a p c).B + (trianglePolygon p b c).B =
          (trianglePolygon a b c).B + 2 * edgeGcd p c := by simpa [p] using hBa
      simpa [hg2] using hBsum'
    have hlocq :=
      mem_interior_left_or_right_or_chord_of_mem_interior_edgeStep a b c hD hd hq_int
    have hlocr :=
      mem_interior_left_or_right_or_chord_of_mem_interior_edgeStep a b c hD hd hr_int
    -- Exactly one of q,r on chord: exclusive cases by exhaustion with omega/contradiction
    -- Use: if both on chord, open-chord card ≥ 2 but g-1 = 1
    have hopen_card :
        (((edgeLatticePoints p c).erase p).erase c).card = 1 := by
      have hp_mem : p ∈ edgeLatticePoints p c := self_mem_edgeLatticePoints p c
      have hc_mem : c ∈ edgeLatticePoints p c := other_mem_edgeLatticePoints p c
      have hcard0 : (edgeLatticePoints p c).card = edgeGcd p c + 1 :=
        card_edgeLatticePoints p c
      have hcard1 : ((edgeLatticePoints p c).erase p).card = edgeGcd p c := by
        rw [Finset.card_erase_of_mem hp_mem, hcard0]; omega
      have hc_mem' : c ∈ (edgeLatticePoints p c).erase p :=
        Finset.mem_erase.mpr ⟨fun h => hpne (h.symm), hc_mem⟩
      have hcard2 : (((edgeLatticePoints p c).erase p).erase c).card = edgeGcd p c - 1 := by
        rw [Finset.card_erase_of_mem hc_mem', hcard1]
      simpa [hg2] using hcard2
    rcases hlocq with hqL | hqR | hqC
    · -- q left ⇒ r on chord (r cannot be left: would be TwoInterior left + Empty right,
      -- but then open chord point is a third interior)
      rcases hlocr with hrL | hrR | hrC
      · -- both left: chord open point is third interior — contradiction
        obtain ⟨s, hs, hsne_p, hsne_c⟩ :=
          exists_strict_mem_edgeLatticePoints_of_edgeGcd_ge_two p c (by omega)
        have hint := mem_interiorLatticePoints_of_strict_mem_edgeStep_chord a b c hD hd
          hs hsne_p hsne_c
        have hs_qr : s = q ∨ s = r := by
          have : s ∈ ({q, r} : Set (ℤ × ℤ)) := by
            rw [← hT.2]; exact hint
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
        -- s on chord cannot equal q or r which are left-interior (off chord)
        have hq' := (mem_interiorLatticePoints_trianglePolygon_iff a p c q).mp hqL
        have hr' := (mem_interiorLatticePoints_trianglePolygon_iff a p c r).mp hrL
        have hnotq : q ∉ edgeLatticePoints p c := hq'.2.2.1
        have hnotr : r ∉ edgeLatticePoints p c := hr'.2.2.1
        rcases hs_qr with rfl | rfl
        · exact (hnotq hs).elim
        · exact (hnotr hs).elim
      · -- q left, r right: open chord point is third — contradiction
        obtain ⟨s, hs, hsne_p, hsne_c⟩ :=
          exists_strict_mem_edgeLatticePoints_of_edgeGcd_ge_two p c (by omega)
        have hint := mem_interiorLatticePoints_of_strict_mem_edgeStep_chord a b c hD hd
          hs hsne_p hsne_c
        have hs_qr : s = q ∨ s = r := by
          have : s ∈ ({q, r} : Set (ℤ × ℤ)) := by
            rw [← hT.2]; exact hint
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
        have hq' := (mem_interiorLatticePoints_trianglePolygon_iff a p c q).mp hqL
        have hr' := (mem_interiorLatticePoints_trianglePolygon_iff p b c r).mp hrR
        have hnotq : q ∉ edgeLatticePoints p c := hq'.2.2.1
        have hnotr : r ∉ edgeLatticePoints p c := fun h => hr'.2.2.2 (mem_edgeLatticePoints_comm h)
        rcases hs_qr with rfl | rfl
        · exact (hnotq hs).elim
        · exact (hnotr hs).elim
      · -- q left, r on chord
        have hUL : UniqueInterior (trianglePolygon a p c) q := by
          refine ⟨hqL, ?_⟩
          intro x hx
          have hint :=
            mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_left a b c hD hd hx
          have hxqr : x = q ∨ x = r := by
            have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
              rw [← hT.2]; exact hint
            simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
          cases hxqr with
          | inl hxq => exact hxq
          | inr hxr =>
            have hx' := (mem_interiorLatticePoints_trianglePolygon_iff a p c x).mp hx
            have : x ∈ edgeLatticePoints p c := by simpa [hxr] using hrC.1
            exact (hx'.2.2.1 this).elim
        have hER : EmptyInterior (trianglePolygon p b c) := by
          rw [EmptyInterior]
          ext x
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hx
          have hint :=
            mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_right a b c hD hd hx
          have hxqr : x = q ∨ x = r := by
            have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
              rw [← hT.2]; exact hint
            simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
          have hx' := (mem_interiorLatticePoints_trianglePolygon_iff p b c x).mp hx
          have hnot : x ∉ edgeLatticePoints c p := hx'.2.2.2
          have hnot' : x ∉ edgeLatticePoints p c := fun h => hnot (mem_edgeLatticePoints_comm h)
          cases hxqr with
          | inl hxq =>
            have hL := (mem_interiorLatticePoints_trianglePolygon_iff a p c q).mp hqL
            have hR := hx'
            have hposL := latticeDet_pos_of_memClosedTriangle_offBoundary a p c q hL.1 hD1 hL.2
            have hposR := latticeDet_pos_of_memClosedTriangle_offBoundary p b c x hR.1 hD2 hR.2
            have h1 : 0 < latticeDet p c q := hposL.1
            have h2 : 0 < latticeDet p x c := hposR.2.1
            have hneg := latticeDet_pqc_neg p c q
            simp [hxq] at h2
            omega
          | inr hxr =>
            have : x ∈ edgeLatticePoints p c := by simpa [hxr] using hrC.1
            exact hnot' this
        have ihL :=
          shoelace_eq_one_add_B_div_two_sub_one_of_unique_interior_triangle a p c hD1 hUL
        have heR := shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle p b c hD2 hER
        calc
          (trianglePolygon a b c).shoelace
              = (trianglePolygon a p c).shoelace + (trianglePolygon p b c).shoelace := hsa
          _ = ((1 : ℚ) + ((trianglePolygon a p c).B : ℚ) / 2 - 1) +
                (((trianglePolygon p b c).B : ℚ) / 2 - 1) := by rw [ihL, heR]
          _ = (((trianglePolygon a p c).B : ℚ) + (trianglePolygon p b c).B) / 2 - 1 := by ring
          _ = (((trianglePolygon a p c).B + (trianglePolygon p b c).B : ℕ) : ℚ) / 2 - 1 := by
                push_cast; rfl
          _ = (((trianglePolygon a b c).B + 4 : ℕ) : ℚ) / 2 - 1 := by rw [hBsum]
          _ = ((trianglePolygon a b c).B : ℚ) / 2 + 2 - 1 := by push_cast; ring
          _ = (2 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by ring
    · -- q right
      rcases hlocr with hrL | hrR | hrC
      · -- q right, r left: chord third — contradiction
        obtain ⟨s, hs, hsne_p, hsne_c⟩ :=
          exists_strict_mem_edgeLatticePoints_of_edgeGcd_ge_two p c (by omega)
        have hint := mem_interiorLatticePoints_of_strict_mem_edgeStep_chord a b c hD hd
          hs hsne_p hsne_c
        have hs_qr : s = q ∨ s = r := by
          have : s ∈ ({q, r} : Set (ℤ × ℤ)) := by
            rw [← hT.2]; exact hint
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
        have hq' := (mem_interiorLatticePoints_trianglePolygon_iff p b c q).mp hqR
        have hr' := (mem_interiorLatticePoints_trianglePolygon_iff a p c r).mp hrL
        have hnotq : q ∉ edgeLatticePoints p c := fun h => hq'.2.2.2 (mem_edgeLatticePoints_comm h)
        have hnotr : r ∉ edgeLatticePoints p c := hr'.2.2.1
        rcases hs_qr with rfl | rfl
        · exact (hnotq hs).elim
        · exact (hnotr hs).elim
      · -- both right: chord third — contradiction
        obtain ⟨s, hs, hsne_p, hsne_c⟩ :=
          exists_strict_mem_edgeLatticePoints_of_edgeGcd_ge_two p c (by omega)
        have hint := mem_interiorLatticePoints_of_strict_mem_edgeStep_chord a b c hD hd
          hs hsne_p hsne_c
        have hs_qr : s = q ∨ s = r := by
          have : s ∈ ({q, r} : Set (ℤ × ℤ)) := by
            rw [← hT.2]; exact hint
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
        have hq' := (mem_interiorLatticePoints_trianglePolygon_iff p b c q).mp hqR
        have hr' := (mem_interiorLatticePoints_trianglePolygon_iff p b c r).mp hrR
        have hnotq : q ∉ edgeLatticePoints p c := fun h => hq'.2.2.2 (mem_edgeLatticePoints_comm h)
        have hnotr : r ∉ edgeLatticePoints p c := fun h => hr'.2.2.2 (mem_edgeLatticePoints_comm h)
        rcases hs_qr with rfl | rfl
        · exact (hnotq hs).elim
        · exact (hnotr hs).elim
      · -- q right, r on chord
        have hUR : UniqueInterior (trianglePolygon p b c) q := by
          refine ⟨hqR, ?_⟩
          intro x hx
          have hint :=
            mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_right a b c hD hd hx
          have hxqr : x = q ∨ x = r := by
            have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
              rw [← hT.2]; exact hint
            simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
          cases hxqr with
          | inl hxq => exact hxq
          | inr hxr =>
            have hx' := (mem_interiorLatticePoints_trianglePolygon_iff p b c x).mp hx
            have : x ∈ edgeLatticePoints p c := by simpa [hxr] using hrC.1
            exact (hx'.2.2.2 (mem_edgeLatticePoints_comm this)).elim
        have hEL : EmptyInterior (trianglePolygon a p c) := by
          rw [EmptyInterior]
          ext x
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hx
          have hint :=
            mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_left a b c hD hd hx
          have hxqr : x = q ∨ x = r := by
            have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
              rw [← hT.2]; exact hint
            simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
          have hx' := (mem_interiorLatticePoints_trianglePolygon_iff a p c x).mp hx
          have hnot : x ∉ edgeLatticePoints p c := hx'.2.2.1
          cases hxqr with
          | inl hxq =>
            have hL := hx'
            have hR := (mem_interiorLatticePoints_trianglePolygon_iff p b c q).mp hqR
            have hposL := latticeDet_pos_of_memClosedTriangle_offBoundary a p c x hL.1 hD1 hL.2
            have hposR := latticeDet_pos_of_memClosedTriangle_offBoundary p b c q hR.1 hD2 hR.2
            have h1 : 0 < latticeDet p c x := hposL.1
            have h2 : 0 < latticeDet p q c := hposR.2.1
            have hneg := latticeDet_pqc_neg p c q
            simp [hxq] at h1
            omega
          | inr hxr =>
            have : x ∈ edgeLatticePoints p c := by simpa [hxr] using hrC.1
            exact hnot this
        have ihR :=
          shoelace_eq_one_add_B_div_two_sub_one_of_unique_interior_triangle p b c hD2 hUR
        have heL := shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle a p c hD1 hEL
        calc
          (trianglePolygon a b c).shoelace
              = (trianglePolygon a p c).shoelace + (trianglePolygon p b c).shoelace := hsa
          _ = ((((trianglePolygon a p c).B : ℚ) / 2 - 1) +
                ((1 : ℚ) + ((trianglePolygon p b c).B : ℚ) / 2 - 1)) := by rw [heL, ihR]
          _ = (((trianglePolygon a p c).B : ℚ) + (trianglePolygon p b c).B) / 2 - 1 := by ring
          _ = (((trianglePolygon a p c).B + (trianglePolygon p b c).B : ℕ) : ℚ) / 2 - 1 := by
                push_cast; rfl
          _ = (((trianglePolygon a b c).B + 4 : ℕ) : ℚ) / 2 - 1 := by rw [hBsum]
          _ = ((trianglePolygon a b c).B : ℚ) / 2 + 2 - 1 := by push_cast; ring
          _ = (2 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by ring
    · -- q on chord
      rcases hlocr with hrL | hrR | hrC
      · -- q chord, r left
        have hUL : UniqueInterior (trianglePolygon a p c) r := by
          refine ⟨hrL, ?_⟩
          intro x hx
          have hint :=
            mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_left a b c hD hd hx
          have hxqr : x = q ∨ x = r := by
            have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
              rw [← hT.2]; exact hint
            simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
          cases hxqr with
          | inl hxq =>
            have hx' := (mem_interiorLatticePoints_trianglePolygon_iff a p c x).mp hx
            have : x ∈ edgeLatticePoints p c := by simpa [hxq] using hqC.1
            exact (hx'.2.2.1 this).elim
          | inr hxr => exact hxr
        have hER : EmptyInterior (trianglePolygon p b c) := by
          rw [EmptyInterior]
          ext x
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hx
          have hint :=
            mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_right a b c hD hd hx
          have hxqr : x = q ∨ x = r := by
            have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
              rw [← hT.2]; exact hint
            simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
          have hx' := (mem_interiorLatticePoints_trianglePolygon_iff p b c x).mp hx
          have hnot : x ∉ edgeLatticePoints c p := hx'.2.2.2
          have hnot' : x ∉ edgeLatticePoints p c := fun h => hnot (mem_edgeLatticePoints_comm h)
          cases hxqr with
          | inl hxq =>
            have : x ∈ edgeLatticePoints p c := by simpa [hxq] using hqC.1
            exact hnot' this
          | inr hxr =>
            have hL := (mem_interiorLatticePoints_trianglePolygon_iff a p c r).mp hrL
            have hR := hx'
            have hposL := latticeDet_pos_of_memClosedTriangle_offBoundary a p c r hL.1 hD1 hL.2
            have hposR := latticeDet_pos_of_memClosedTriangle_offBoundary p b c x hR.1 hD2 hR.2
            have h1 : 0 < latticeDet p c r := hposL.1
            have h2 : 0 < latticeDet p x c := hposR.2.1
            have hneg := latticeDet_pqc_neg p c r
            simp [hxr] at h2
            omega
        have ihL :=
          shoelace_eq_one_add_B_div_two_sub_one_of_unique_interior_triangle a p c hD1 hUL
        have heR := shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle p b c hD2 hER
        calc
          (trianglePolygon a b c).shoelace
              = (trianglePolygon a p c).shoelace + (trianglePolygon p b c).shoelace := hsa
          _ = ((1 : ℚ) + ((trianglePolygon a p c).B : ℚ) / 2 - 1) +
                (((trianglePolygon p b c).B : ℚ) / 2 - 1) := by rw [ihL, heR]
          _ = (((trianglePolygon a p c).B : ℚ) + (trianglePolygon p b c).B) / 2 - 1 := by ring
          _ = (((trianglePolygon a p c).B + (trianglePolygon p b c).B : ℕ) : ℚ) / 2 - 1 := by
                push_cast; rfl
          _ = (((trianglePolygon a b c).B + 4 : ℕ) : ℚ) / 2 - 1 := by rw [hBsum]
          _ = ((trianglePolygon a b c).B : ℚ) / 2 + 2 - 1 := by push_cast; ring
          _ = (2 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by ring
      · -- q chord, r right
        have hUR : UniqueInterior (trianglePolygon p b c) r := by
          refine ⟨hrR, ?_⟩
          intro x hx
          have hint :=
            mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_right a b c hD hd hx
          have hxqr : x = q ∨ x = r := by
            have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
              rw [← hT.2]; exact hint
            simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
          cases hxqr with
          | inl hxq =>
            have hx' := (mem_interiorLatticePoints_trianglePolygon_iff p b c x).mp hx
            have : x ∈ edgeLatticePoints p c := by simpa [hxq] using hqC.1
            exact (hx'.2.2.2 (mem_edgeLatticePoints_comm this)).elim
          | inr hxr => exact hxr
        have hEL : EmptyInterior (trianglePolygon a p c) := by
          rw [EmptyInterior]
          ext x
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hx
          have hint :=
            mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_left a b c hD hd hx
          have hxqr : x = q ∨ x = r := by
            have : x ∈ ({q, r} : Set (ℤ × ℤ)) := by
              rw [← hT.2]; exact hint
            simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
          have hx' := (mem_interiorLatticePoints_trianglePolygon_iff a p c x).mp hx
          have hnot : x ∉ edgeLatticePoints p c := hx'.2.2.1
          cases hxqr with
          | inl hxq =>
            have : x ∈ edgeLatticePoints p c := by simpa [hxq] using hqC.1
            exact hnot this
          | inr hxr =>
            have hL := hx'
            have hR := (mem_interiorLatticePoints_trianglePolygon_iff p b c r).mp hrR
            have hposL := latticeDet_pos_of_memClosedTriangle_offBoundary a p c x hL.1 hD1 hL.2
            have hposR := latticeDet_pos_of_memClosedTriangle_offBoundary p b c r hR.1 hD2 hR.2
            have h1 : 0 < latticeDet p c x := hposL.1
            have h2 : 0 < latticeDet p r c := hposR.2.1
            have hneg := latticeDet_pqc_neg p c r
            simp [hxr] at h1
            omega
        have ihR :=
          shoelace_eq_one_add_B_div_two_sub_one_of_unique_interior_triangle p b c hD2 hUR
        have heL := shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle a p c hD1 hEL
        calc
          (trianglePolygon a b c).shoelace
              = (trianglePolygon a p c).shoelace + (trianglePolygon p b c).shoelace := hsa
          _ = ((((trianglePolygon a p c).B : ℚ) / 2 - 1) +
                ((1 : ℚ) + ((trianglePolygon p b c).B : ℚ) / 2 - 1)) := by rw [heL, ihR]
          _ = (((trianglePolygon a p c).B : ℚ) + (trianglePolygon p b c).B) / 2 - 1 := by ring
          _ = (((trianglePolygon a p c).B + (trianglePolygon p b c).B : ℕ) : ℚ) / 2 - 1 := by
                push_cast; rfl
          _ = (((trianglePolygon a b c).B + 4 : ℕ) : ℚ) / 2 - 1 := by rw [hBsum]
          _ = ((trianglePolygon a b c).B : ℚ) / 2 + 2 - 1 := by push_cast; ring
          _ = (2 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by ring
      · -- both on chord: open card = 1 but q ≠ r — contradiction with card
        have hsub :
            ({q, r} : Finset (ℤ × ℤ)) ⊆ ((edgeLatticePoints p c).erase p).erase c := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_erase.mpr ⟨hqC.2.2, Finset.mem_erase.mpr ⟨hqC.2.1, hqC.1⟩⟩
          · exact Finset.mem_erase.mpr ⟨hrC.2.2, Finset.mem_erase.mpr ⟨hrC.2.1, hrC.1⟩⟩
        have hcard_qr : ({q, r} : Finset (ℤ × ℤ)).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simp [hT.1]), Finset.card_singleton]
        have hle := Finset.card_le_card hsub
        have : 2 ≤ (((edgeLatticePoints p c).erase p).erase c).card := by
          simpa [hcard_qr] using hle
        omega
  · -- g = 3: both halves empty
    have hboth :=
      EmptyInterior_edgeStep_both_of_twoInterior_edgeGcd_eq_three a b c hD hd hT
        (by simpa [p] using hg3)
    have he1 := shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle a p c hD1 hboth.1
    have he2 := shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle p b c hD2 hboth.2
    have hBsum : (trianglePolygon a p c).B + (trianglePolygon p b c).B =
        (trianglePolygon a b c).B + 6 := by
      have hBsum' : (trianglePolygon a p c).B + (trianglePolygon p b c).B =
          (trianglePolygon a b c).B + 2 * edgeGcd p c := by simpa [p] using hBa
      simpa [hg3] using hBsum'
    calc
      (trianglePolygon a b c).shoelace
          = (trianglePolygon a p c).shoelace + (trianglePolygon p b c).shoelace := hsa
      _ = ((((trianglePolygon a p c).B : ℚ) / 2 - 1) +
            (((trianglePolygon p b c).B : ℚ) / 2 - 1)) := by rw [he1, he2]
      _ = (((trianglePolygon a p c).B : ℚ) + (trianglePolygon p b c).B) / 2 - 2 := by ring
      _ = (((trianglePolygon a p c).B + (trianglePolygon p b c).B : ℕ) : ℚ) / 2 - 2 := by
            push_cast; rfl
      _ = (((trianglePolygon a b c).B + 6 : ℕ) : ℚ) / 2 - 2 := by rw [hBsum]
      _ = ((trianglePolygon a b c).B : ℚ) / 2 + 3 - 2 := by push_cast; ring
      _ = (2 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by ring

/-- TwoInterior closed lattice triangle Pick-form without `PrimitiveEdges`, by
induction on `|det|` via `edgeStep` splits (not classical Pick). -/
theorem shoelace_eq_two_add_B_div_two_sub_one_of_two_interior_triangle
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c)
    {q r : ℤ × ℤ} (hT : TwoInterior (trianglePolygon a b c) q r) :
    (trianglePolygon a b c).shoelace =
      (2 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by
  classical
  generalize hn : Int.natAbs (latticeDet a b c) = n
  revert a b c
  refine Nat.strong_induction_on n fun n ih a b c hD hT hn => ?_
  have _hpos := edgeGcd_pos_of_latticeDet_pos a b c hD
  by_cases hprim : edgeGcd a b = 1 ∧ edgeGcd b c = 1 ∧ edgeGcd c a = 1
  · have hedge :=
      PrimitiveEdges_trianglePolygon_of_edgeGcds a b c hprim.1 hprim.2.1 hprim.2.2
    exact shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior
      (trianglePolygon a b c)
      (StrictlyConvexCCW_trianglePolygon a b c hD)
      (injective_vertex_trianglePolygon a b c (ne_of_gt hD))
      hedge hT
  · have hge : 2 ≤ edgeGcd a b ∨ 2 ≤ edgeGcd b c ∨ 2 ≤ edgeGcd c a := by omega
    have ih' : ∀ a' b' c' : ℤ × ℤ,
        0 < latticeDet a' b' c' →
        TwoInterior (trianglePolygon a' b' c') q r →
        Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) →
        (trianglePolygon a' b' c').shoelace =
          (2 : ℚ) + ((trianglePolygon a' b' c').B : ℚ) / 2 - 1 := by
      intro a' b' c' hD' hT' hlt'
      have hltn : Int.natAbs (latticeDet a' b' c') < n := by simpa [hn] using hlt'
      exact ih _ hltn a' b' c' hD' hT' rfl
    rcases hge with hab | hbc | hca
    · subst hn
      exact shoelace_eq_two_add_B_div_two_sub_one_of_two_interior_triangle_of_edgeStep_ab
        a b c hD hab hT ih'
    · have hDc : 0 < latticeDet b c a := by simpa [← latticeDet_cyclic a b c] using hD
      have hTc : TwoInterior (trianglePolygon b c a) q r :=
        (TwoInterior_trianglePolygon_cyclic a b c q r).mp hT
      have ihc : ∀ a' b' c' : ℤ × ℤ,
          0 < latticeDet a' b' c' →
          TwoInterior (trianglePolygon a' b' c') q r →
          Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet b c a) →
          (trianglePolygon a' b' c').shoelace =
            (2 : ℚ) + ((trianglePolygon a' b' c').B : ℚ) / 2 - 1 := by
        intro a' b' c' hD' hT' hlt'
        have : Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) := by
          simpa [← latticeDet_cyclic a b c] using hlt'
        exact ih' a' b' c' hD' hT' this
      have hpick :=
        shoelace_eq_two_add_B_div_two_sub_one_of_two_interior_triangle_of_edgeStep_ab
          b c a hDc hbc hTc ihc
      rw [shoelace_trianglePolygon_cyclic a b c,
          B_trianglePolygon_cyclic a b c (ne_of_gt hD)]
      exact hpick
    · have hDc : 0 < latticeDet c a b := by simpa [← latticeDet_cyclic₂ a b c] using hD
      have hTc : TwoInterior (trianglePolygon c a b) q r := by
        have h1 := (TwoInterior_trianglePolygon_cyclic a b c q r).mp hT
        exact (TwoInterior_trianglePolygon_cyclic b c a q r).mp h1
      have ihc : ∀ a' b' c' : ℤ × ℤ,
          0 < latticeDet a' b' c' →
          TwoInterior (trianglePolygon a' b' c') q r →
          Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet c a b) →
          (trianglePolygon a' b' c').shoelace =
            (2 : ℚ) + ((trianglePolygon a' b' c').B : ℚ) / 2 - 1 := by
        intro a' b' c' hD' hT' hlt'
        have : Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) := by
          simpa [← latticeDet_cyclic₂ a b c] using hlt'
        exact ih' a' b' c' hD' hT' this
      have hpick :=
        shoelace_eq_two_add_B_div_two_sub_one_of_two_interior_triangle_of_edgeStep_ab
          c a b hDc hca hTc ihc
      have hs1 := shoelace_trianglePolygon_cyclic a b c
      have hs2 := shoelace_trianglePolygon_cyclic b c a
      have hB1 := B_trianglePolygon_cyclic a b c (ne_of_gt hD)
      have hB2 := B_trianglePolygon_cyclic b c a
        (by simpa [← latticeDet_cyclic a b c] using ne_of_gt hD)
      rw [hs1, hs2, hB1, hB2]
      exact hpick

/-- I ∈ {0,1,2} shoelace Pick-form for a closed lattice triangle without
`PrimitiveEdges` (not classical Pick). -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_two_triangle
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c)
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = (trianglePolygon a b c).interiorLatticePoints)
    (hcard : S.card ≤ 2) :
    (trianglePolygon a b c).shoelace =
      (S.card : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by
  classical
  by_cases hle1 : S.card ≤ 1
  · exact shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_one_triangle a b c hD S hS hle1
  · have h2 : S.card = 2 := by omega
    obtain ⟨q, r, hT, hSeq⟩ := twoInterior_of_finset_card_two (trianglePolygon a b c) S hS h2
    have harea :=
      shoelace_eq_two_add_B_div_two_sub_one_of_two_interior_triangle a b c hD hT
    calc
      (trianglePolygon a b c).shoelace
          = (2 : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := harea
      _ = (S.card : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by simp [h2]



/-! ## I ≤ 3 triangle Pick without `PrimitiveEdges` (not classical Pick)

Finset `|det|` induction via `edgeStep`: base all-primitive ⇒ existing I≤3
with `PrimitiveEdges`; step splits a non-primitive edge, partitions interior
into left / right / open-chord, applies IH on halves (strictly smaller
`|det|`, card ≤ 3), reassembles via shoelace/B additivity.
`#openChord = edgeGcd(chord) − 1` cancels the B-chord contribution.
Shoelace ≠ Haar. Classical Pick FAIL.
-/

/-- Parent `#I ≤ 3` ⇒ open chord after `edgeStep` has `edgeGcd ≤ 4`. -/
theorem edgeGcd_le_four_of_card_le_three_edgeStep
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = (trianglePolygon a b c).interiorLatticePoints)
    (hcard : S.card ≤ 3) :
    edgeGcd (edgeStep a b) c ≤ 4 := by
  classical
  set p := edgeStep a b
  by_contra hgt
  have hge : 5 ≤ edgeGcd p c := by omega
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
  have hcard_ge : 4 ≤ (((edgeLatticePoints p c).erase p).erase c).card := by omega
  have hsub :
      ((edgeLatticePoints p c).erase p).erase c ⊆ S := by
    intro x hx
    have hx' := Finset.mem_erase.mp hx
    have hx'' := Finset.mem_erase.mp hx'.2
    have hint := mem_interiorLatticePoints_of_strict_mem_edgeStep_chord a b c hD hd
      hx''.2 hx''.1 hx'.1
    have : x ∈ (S : Set (ℤ × ℤ)) := by simpa [hS] using hint
    exact this
  have hcard_le :
      (((edgeLatticePoints p c).erase p).erase c).card ≤ S.card :=
    Finset.card_le_card hsub
  omega

/-- Open chord Finset after `edgeStep` (excluding endpoints). -/
noncomputable def openChordEdgeStep (a b c : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  ((edgeLatticePoints (edgeStep a b) c).erase (edgeStep a b)).erase c

lemma card_openChordEdgeStep (a b c : ℤ × ℤ)
    (hpne : edgeStep a b ≠ c) :
    (openChordEdgeStep a b c).card = edgeGcd (edgeStep a b) c - 1 ∨
      edgeGcd (edgeStep a b) c = 0 := by
  classical
  set p := edgeStep a b
  set g := edgeGcd p c
  by_cases hg0 : g = 0
  · exact Or.inr hg0
  · left
    have hp_mem : p ∈ edgeLatticePoints p c := self_mem_edgeLatticePoints p c
    have hc_mem : c ∈ edgeLatticePoints p c := other_mem_edgeLatticePoints p c
    have hcard0 : (edgeLatticePoints p c).card = g + 1 := by
      simpa [g] using card_edgeLatticePoints p c
    have hcard1 : ((edgeLatticePoints p c).erase p).card = g := by
      rw [Finset.card_erase_of_mem hp_mem, hcard0]; omega
    have hc_mem' : c ∈ (edgeLatticePoints p c).erase p :=
      Finset.mem_erase.mpr ⟨fun h => hpne h.symm, hc_mem⟩
    simpa [openChordEdgeStep, p, g] using
      (by rw [Finset.card_erase_of_mem hc_mem', hcard1] : (((edgeLatticePoints p c).erase p).erase c).card = g - 1)

lemma openChordEdgeStep_subset_interior
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b) :
    ↑(openChordEdgeStep a b c) ⊆ (trianglePolygon a b c).interiorLatticePoints := by
  classical
  intro x hx
  simp only [openChordEdgeStep] at hx
  have hx1 := Finset.mem_erase.mp hx
  have hx2 := Finset.mem_erase.mp hx1.2
  exact mem_interiorLatticePoints_of_strict_mem_edgeStep_chord a b c hD hd
    hx2.2 hx2.1 hx1.1

/-- Helper: I≤3 triangle Pick when a designated edge has `edgeGcd ≥ 2`. -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_three_triangle_of_edgeStep_ab
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = (trianglePolygon a b c).interiorLatticePoints)
    (hcard : S.card ≤ 3)
    (ih : ∀ a' b' c' : ℤ × ℤ, ∀ S' : Finset (ℤ × ℤ),
      0 < latticeDet a' b' c' →
      (S' : Set (ℤ × ℤ)) = (trianglePolygon a' b' c').interiorLatticePoints →
      S'.card ≤ 3 →
      Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) →
      (trianglePolygon a' b' c').shoelace =
        (S'.card : ℚ) + ((trianglePolygon a' b' c').B : ℚ) / 2 - 1) :
    (trianglePolygon a b c).shoelace =
      (S.card : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by
  classical
  set p := edgeStep a b
  set T := trianglePolygon a b c
  set TL := trianglePolygon a p c
  set TR := trianglePolygon p b c
  have hlt := natAbs_latticeDet_edgeStep_lt a b c hD hd
  have hD1 : 0 < latticeDet a p c := latticeDet_edgeStep_pos a b c hD (by omega)
  have hD2 : 0 < latticeDet p b c := latticeDet_edgeStep_right_pos a b c hD hd
  have hg_le : edgeGcd p c ≤ 4 := by
    simpa [p] using edgeGcd_le_four_of_card_le_three_edgeStep a b c hD hd S hS hcard
  have hsa := shoelace_add_of_edgeStep a b c hD hd
  have hBa := B_add_of_edgeStep_of_gcd a b c hD hd
  have hpne : p ≠ c := by
    intro hpc
    have hp := edgeStep_mem_edgeLatticePoints a b (by omega)
    have : latticeDet a b c = 0 := by
      simpa [hpc] using latticeDet_eq_zero_of_mem_edge_ab a b p hp
    omega
  have hg_pos : 1 ≤ edgeGcd p c :=
    Nat.pos_of_ne_zero fun hz => hpne ((edgeGcd_eq_zero_iff p c).mp hz)
  set g := edgeGcd p c
  set S_L : Finset (ℤ × ℤ) := S.filter (fun x => x ∈ TL.interiorLatticePoints)
  set S_R : Finset (ℤ × ℤ) := S.filter (fun x => x ∈ TR.interiorLatticePoints)
  set S_C : Finset (ℤ × ℤ) := openChordEdgeStep a b c
  have hSL_set : (S_L : Set (ℤ × ℤ)) = TL.interiorLatticePoints := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp (by simpa [S_L] using hx)).2
    · intro hx
      have hxP := mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_left a b c hD hd
        (by simpa [p, TL] using hx)
      have hxS : x ∈ S := by
        have : x ∈ (S : Set (ℤ × ℤ)) := by simpa [hS] using hxP
        exact this
      exact Finset.mem_filter.mpr ⟨hxS, by simpa [TL] using hx⟩
  have hSR_set : (S_R : Set (ℤ × ℤ)) = TR.interiorLatticePoints := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp (by simpa [S_R] using hx)).2
    · intro hx
      have hxP := mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_right a b c hD hd
        (by simpa [p, TR] using hx)
      have hxS : x ∈ S := by
        have : x ∈ (S : Set (ℤ × ℤ)) := by simpa [hS] using hxP
        exact this
      exact Finset.mem_filter.mpr ⟨hxS, by simpa [TR] using hx⟩
  have hSC_sub : (S_C : Set (ℤ × ℤ)) ⊆ T.interiorLatticePoints := by
    simpa [S_C, T] using openChordEdgeStep_subset_interior a b c hD hd
  have hSC_S : S_C ⊆ S := by
    intro x hx
    have : x ∈ (S : Set (ℤ × ℤ)) := by
      have hxI : x ∈ T.interiorLatticePoints := hSC_sub hx
      simpa [hS, T] using hxI
    exact this
  have hcard_C : S_C.card = g - 1 := by
    have h := card_openChordEdgeStep a b c (by simpa [p] using hpne)
    rcases h with h' | hg0
    · simpa [S_C, g, p] using h'
    · exact (Nat.ne_of_gt hg_pos (by simpa [g, p] using hg0)).elim
  -- Disjointness
  have hdisj_LR : Disjoint S_L S_R := by
    refine Finset.disjoint_left.mpr fun x hxL hxR => ?_
    have hxL' : x ∈ TL.interiorLatticePoints := (Finset.mem_filter.mp (by simpa [S_L] using hxL)).2
    have hxR' : x ∈ TR.interiorLatticePoints := (Finset.mem_filter.mp (by simpa [S_R] using hxR)).2
    have hL := (mem_interiorLatticePoints_trianglePolygon_iff a p c x).mp (by simpa [TL] using hxL')
    have hR := (mem_interiorLatticePoints_trianglePolygon_iff p b c x).mp (by simpa [TR] using hxR')
    have hposL := latticeDet_pos_of_memClosedTriangle_offBoundary a p c x hL.1 hD1 hL.2
    have hposR := latticeDet_pos_of_memClosedTriangle_offBoundary p b c x hR.1 hD2 hR.2
    have h1 : 0 < latticeDet p c x := hposL.1
    have h2 : 0 < latticeDet p x c := hposR.2.1
    have hneg := latticeDet_pqc_neg p c x
    omega
  have hdisj_LC : Disjoint S_L S_C := by
    refine Finset.disjoint_left.mpr fun x hxL hxC => ?_
    have hxL' : x ∈ TL.interiorLatticePoints := (Finset.mem_filter.mp (by simpa [S_L] using hxL)).2
    have hL := (mem_interiorLatticePoints_trianglePolygon_iff a p c x).mp (by simpa [TL] using hxL')
    have hxC' : x ∈ ((edgeLatticePoints p c).erase p).erase c := by
      simpa [S_C, openChordEdgeStep, p] using hxC
    have hx_edge : x ∈ edgeLatticePoints p c := (Finset.mem_erase.mp (Finset.mem_erase.mp hxC').2).2
    exact hL.2.2.1 hx_edge
  have hdisj_RC : Disjoint S_R S_C := by
    refine Finset.disjoint_left.mpr fun x hxR hxC => ?_
    have hxR' : x ∈ TR.interiorLatticePoints := (Finset.mem_filter.mp (by simpa [S_R] using hxR)).2
    have hR := (mem_interiorLatticePoints_trianglePolygon_iff p b c x).mp (by simpa [TR] using hxR')
    have hxC' : x ∈ ((edgeLatticePoints p c).erase p).erase c := by
      simpa [S_C, openChordEdgeStep, p] using hxC
    have hx_edge : x ∈ edgeLatticePoints p c := (Finset.mem_erase.mp (Finset.mem_erase.mp hxC').2).2
    have hx_edge' : x ∈ edgeLatticePoints c p := mem_edgeLatticePoints_comm hx_edge
    exact hR.2.2.2 hx_edge'
  have hunion : S = S_L ∪ S_R ∪ S_C := by
    ext x
    constructor
    · intro hx
      have hxI : x ∈ T.interiorLatticePoints := by
        have : x ∈ (S : Set (ℤ × ℤ)) := hx
        simpa [hS, T] using this
      rcases mem_interior_left_or_right_or_chord_of_mem_interior_edgeStep a b c hD hd
          (by simpa [T] using hxI) with hL | hR | hC
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr ⟨hx, by simpa [TL, p] using hL⟩))))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨hx, by simpa [TR, p] using hR⟩))))
      · exact Finset.mem_union.mpr (Or.inr (by
          simpa [S_C, openChordEdgeStep, p, Finset.mem_erase] using
            ⟨hC.2.2, ⟨hC.2.1, hC.1⟩⟩))
    · intro hx
      rcases Finset.mem_union.mp hx with hLR | hC
      · rcases Finset.mem_union.mp hLR with hL | hR
        · exact (Finset.mem_filter.mp (by simpa [S_L] using hL)).1
        · exact (Finset.mem_filter.mp (by simpa [S_R] using hR)).1
      · exact hSC_S (by simpa [S_C] using hC)
  have hcard_sum : S.card = S_L.card + S_R.card + S_C.card := by
    have h1 : (S_L ∪ S_R ∪ S_C).card = S_L.card + S_R.card + S_C.card := by
      have d1 := hdisj_LR
      have d2 : Disjoint (S_L ∪ S_R) S_C :=
        Finset.disjoint_union_left.mpr ⟨hdisj_LC, hdisj_RC⟩
      rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1]
    simpa [hunion] using h1
  have hcardL : S_L.card ≤ 3 := by omega
  have hcardR : S_R.card ≤ 3 := by omega
  have ihL := ih a p c S_L hD1 hSL_set hcardL hlt.1
  have ihR := ih p b c S_R hD2 hSR_set hcardR hlt.2
  have hBsum : TL.B + TR.B = T.B + 2 * g := by simpa [TL, TR, T, p, g] using hBa
  calc
    T.shoelace
        = TL.shoelace + TR.shoelace := by simpa [T, TL, TR, p] using hsa
    _ = ((S_L.card : ℚ) + (TL.B : ℚ) / 2 - 1) +
          ((S_R.card : ℚ) + (TR.B : ℚ) / 2 - 1) := by rw [ihL, ihR]
    _ = (S_L.card : ℚ) + (S_R.card : ℚ) + ((TL.B : ℚ) + (TR.B : ℚ)) / 2 - 2 := by ring
    _ = (S_L.card : ℚ) + (S_R.card : ℚ) + ((T.B + 2 * g : ℕ) : ℚ) / 2 - 2 := by
          rw [← hBsum]; push_cast; rfl
    _ = (S_L.card : ℚ) + (S_R.card : ℚ) + (T.B : ℚ) / 2 + (g : ℚ) - 2 := by
          push_cast; ring
    _ = (S.card : ℚ) + (T.B : ℚ) / 2 - 1 := by
          have hsum' : (S.card : ℚ) = (S_L.card : ℚ) + (S_R.card : ℚ) + (S_C.card : ℚ) := by
            exact_mod_cast hcard_sum
          have hC' : (S_C.card : ℚ) = (g : ℚ) - 1 := by
            have : S_C.card + 1 = g := by omega
            exact_mod_cast (by omega : (S_C.card : ℤ) = (g : ℤ) - 1)
          rw [hsum', hC']
          ring

/-- I ∈ {0,1,2,3} shoelace Pick-form for a closed lattice triangle without
`PrimitiveEdges` (not classical Pick). -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_three_triangle
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c)
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = (trianglePolygon a b c).interiorLatticePoints)
    (hcard : S.card ≤ 3) :
    (trianglePolygon a b c).shoelace =
      (S.card : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by
  classical
  generalize hn : Int.natAbs (latticeDet a b c) = n
  revert a b c S
  refine Nat.strong_induction_on n fun n ih a b c hD S hS hcard hn => ?_
  have _hpos := edgeGcd_pos_of_latticeDet_pos a b c hD
  by_cases hprim : edgeGcd a b = 1 ∧ edgeGcd b c = 1 ∧ edgeGcd c a = 1
  · have hedge :=
      PrimitiveEdges_trianglePolygon_of_edgeGcds a b c hprim.1 hprim.2.1 hprim.2.2
    exact shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_three
      (trianglePolygon a b c) S hS hcard
      (injective_vertex_trianglePolygon a b c (ne_of_gt hD))
      hedge
      (StrictlyConvexCCW_trianglePolygon a b c hD)
  · have hge : 2 ≤ edgeGcd a b ∨ 2 ≤ edgeGcd b c ∨ 2 ≤ edgeGcd c a := by omega
    have ih' : ∀ a' b' c' : ℤ × ℤ, ∀ S' : Finset (ℤ × ℤ),
        0 < latticeDet a' b' c' →
        (S' : Set (ℤ × ℤ)) = (trianglePolygon a' b' c').interiorLatticePoints →
        S'.card ≤ 3 →
        Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) →
        (trianglePolygon a' b' c').shoelace =
          (S'.card : ℚ) + ((trianglePolygon a' b' c').B : ℚ) / 2 - 1 := by
      intro a' b' c' S' hD' hS' hcard' hlt'
      have hltn : Int.natAbs (latticeDet a' b' c') < n := by simpa [hn] using hlt'
      exact ih _ hltn a' b' c' hD' S' hS' hcard' rfl
    rcases hge with hab | hbc | hca
    · subst hn
      exact shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_three_triangle_of_edgeStep_ab
        a b c hD hab S hS hcard ih'
    · have hDc : 0 < latticeDet b c a := by simpa [← latticeDet_cyclic a b c] using hD
      have hSc : (S : Set (ℤ × ℤ)) = (trianglePolygon b c a).interiorLatticePoints := by
        simpa [← interiorLatticePoints_trianglePolygon_cyclic a b c] using hS
      have ihc : ∀ a' b' c' : ℤ × ℤ, ∀ S' : Finset (ℤ × ℤ),
          0 < latticeDet a' b' c' →
          (S' : Set (ℤ × ℤ)) = (trianglePolygon a' b' c').interiorLatticePoints →
          S'.card ≤ 3 →
          Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet b c a) →
          (trianglePolygon a' b' c').shoelace =
            (S'.card : ℚ) + ((trianglePolygon a' b' c').B : ℚ) / 2 - 1 := by
        intro a' b' c' S' hD' hS' hcard' hlt'
        have : Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) := by
          simpa [← latticeDet_cyclic a b c] using hlt'
        exact ih' a' b' c' S' hD' hS' hcard' this
      have hpick :=
        shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_three_triangle_of_edgeStep_ab
          b c a hDc hbc S hSc hcard ihc
      rw [shoelace_trianglePolygon_cyclic a b c,
          B_trianglePolygon_cyclic a b c (ne_of_gt hD)]
      exact hpick
    · have hDc : 0 < latticeDet c a b := by simpa [← latticeDet_cyclic₂ a b c] using hD
      have hSc : (S : Set (ℤ × ℤ)) = (trianglePolygon c a b).interiorLatticePoints := by
        have h1 := interiorLatticePoints_trianglePolygon_cyclic a b c
        have h2 := interiorLatticePoints_trianglePolygon_cyclic b c a
        simpa [← h2, ← h1] using hS
      have ihc : ∀ a' b' c' : ℤ × ℤ, ∀ S' : Finset (ℤ × ℤ),
          0 < latticeDet a' b' c' →
          (S' : Set (ℤ × ℤ)) = (trianglePolygon a' b' c').interiorLatticePoints →
          S'.card ≤ 3 →
          Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet c a b) →
          (trianglePolygon a' b' c').shoelace =
            (S'.card : ℚ) + ((trianglePolygon a' b' c').B : ℚ) / 2 - 1 := by
        intro a' b' c' S' hD' hS' hcard' hlt'
        have : Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) := by
          simpa [← latticeDet_cyclic₂ a b c] using hlt'
        exact ih' a' b' c' S' hD' hS' hcard' this
      have hpick :=
        shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_three_triangle_of_edgeStep_ab
          c a b hDc hca S hSc hcard ihc
      have hs1 := shoelace_trianglePolygon_cyclic a b c
      have hs2 := shoelace_trianglePolygon_cyclic b c a
      have hB1 := B_trianglePolygon_cyclic a b c (ne_of_gt hD)
      have hB2 := B_trianglePolygon_cyclic b c a
        (by simpa [← latticeDet_cyclic a b c] using ne_of_gt hD)
      rw [hs1, hs2, hB1, hB2]
      exact hpick


/-! ## I = 4 geometric fan-ear without spokes-empty (not classical Pick)

Parent `#S = 4`: pick any apex `q ∈ S`, fan into ears. Each `#earOff ≤ 3`.
* `#earOff ≤ 2` ⇒ triangle I≤2 Pick without `PrimitiveEdges` on ear sides.
* `#earOff = 3` ⇒ the three non-apex interior points all lie Off in that ear, so
  every spoke from `q` is empty; ear inherits `PrimitiveEdges` and I≤3 applies.
Discharged hbook closes the fan-ear step. Shoelace ≠ Haar. Classical Pick FAIL.
-/

variable (P : LatticePolygon)

/-- Parent `#S = 4` and `#earOff = 3` ⇒ every spoke from the apex is empty
(all three remaining interior points lie Off in that ear). -/
theorem spokeInterior_eq_empty_of_earOffInterior_card_eq_three_of_card_eq_four
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q : ℤ × ℤ}
    (hq : q ∈ S) (i : Fin P.nVertices)
    (hcardS : S.card = 4)
    (hcardE : (earOffInterior P q i S).card = 3)
    (k : Fin P.nVertices) :
    spokeInterior P q k S = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
  have hqI : q ∈ P.interiorLatticePoints := by
    have : q ∈ (S : Set (ℤ × ℤ)) := hq
    rwa [hS] at this
  have hp' : p ∈ S ∧ p ≠ q ∧ p ≠ P.vertex k ∧ p ∈ edgeLatticePoints q (P.vertex k) := by
    simpa [spokeInterior] using hp
  have hsub : earOffInterior P q i S ⊆ S.erase q := by
    intro r hr
    have hr' : r ∈ S ∧ r ≠ q ∧
        MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r ∧
          OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r := by
      simpa [earOffInterior] using hr
    exact Finset.mem_erase.mpr ⟨hr'.2.1, hr'.1⟩
  have herase : (S.erase q).card = 3 := by
    rw [Finset.card_erase_of_mem hq, hcardS]
  have heq : earOffInterior P q i S = S.erase q :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hp_ear : p ∈ earOffInterior P q i S := by
    have : p ∈ S.erase q := Finset.mem_erase.mpr ⟨hp'.2.1, hp'.1⟩
    simpa [heq] using this
  exact false_of_mem_earOffInterior_of_mem_spokeInterior
    P hsc hinj hedge hqI S hp_ear hp

/-- Ear Pick-form for parent `#S = 4` without a spokes-empty hyp
(not classical Pick).

Uses triangle I≤2 when `#earOff ≤ 2` (no `PrimitiveEdges` on ear sides); when
`#earOff = 3`, adjacent spokes are empty so the existing I≤3 ear lemma applies. -/
theorem shoelace_trianglePolygon_ear_eq_card_earOff_add_B_div_two_sub_one_of_I_le_three_of_card_eq_four
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q : ℤ × ℤ}
    (hq : q ∈ S) (i : Fin P.nVertices)
    (hcardS : S.card = 4)
    (hcard : (earOffInterior P q i S).card ≤ 3) :
    (trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))).shoelace =
      ((earOffInterior P q i S).card : ℚ) +
        ((trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))).B : ℚ) / 2 - 1 := by
  classical
  set T := trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))
  set S_ear := earOffInterior P q i S
  have hqI : q ∈ P.interiorLatticePoints := by
    have : q ∈ (S : Set (ℤ × ℤ)) := hq
    rwa [hS] at this
  have hpos := InteriorFanDetsPos_of_mem_interior P hsc hinj hedge hqI
  have hD : 0 < latticeDet q (P.vertex i) (P.vertex (P.nextIdx i)) := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hpos i
  have hS_ear : (S_ear : Set (ℤ × ℤ)) = T.interiorLatticePoints :=
    coe_earOffInterior_eq_interiorLatticePoints_trianglePolygon
      P S hS hsc hinj hedge hq i
  by_cases hle2 : S_ear.card ≤ 2
  · simpa [T, S_ear] using
      (shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_two_triangle
        q (P.vertex i) (P.vertex (P.nextIdx i)) hD S_ear hS_ear hle2)
  · have h3 : S_ear.card = 3 := by omega
    have h3' : (earOffInterior P q i S).card = 3 := by simpa [S_ear] using h3
    have hL : spokeInterior P q i S = ∅ :=
      spokeInterior_eq_empty_of_earOffInterior_card_eq_three_of_card_eq_four
        P S hS hsc hinj hedge hq i hcardS h3' i
    have hR : spokeInterior P q (P.nextIdx i) S = ∅ :=
      spokeInterior_eq_empty_of_earOffInterior_card_eq_three_of_card_eq_four
        P S hS hsc hinj hedge hq i hcardS h3' (P.nextIdx i)
    simpa [T, S_ear] using
      (shoelace_trianglePolygon_ear_eq_card_earOff_add_B_div_two_sub_one_of_I_le_three
        P S hS hsc hinj hedge hq i hL hR hcard)

/-- **I = 4 shoelace Pick-form** without spokes-empty hyp (not classical Pick).

Hyps: geometric polygon (`StrictlyConvexCCW`, injective, parent `PrimitiveEdges`),
interior Finset `#S = 4`. Any apex works: fan-ear IH with triangle I≤2 /
PrimitiveEdges-on-`#earOff=3` ears and discharged hbook. Ears may have
non-primitive sides. Shoelace ≠ Haar. Classical Pick FAIL. -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_four
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hcard : S.card = 4)
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hsc : StrictlyConvexCCW P) :
    P.shoelace = (S.card : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q, hq⟩ := hne
  refine shoelace_eq_cardI_add_B_div_two_sub_one_of_fan_ear_IH
    P S hS q hq hverts hedge hsc ?hIH
    (hbook_of_fan_ear_partition_of_interior P S hS hsc hverts hedge hq)
  intro i
  exact shoelace_trianglePolygon_ear_eq_card_earOff_add_B_div_two_sub_one_of_I_le_three_of_card_eq_four
    P S hS hsc hverts hedge hq i hcard
    (card_earOffInterior_le_three_of_card_eq_four P q i S hq hcard)

/-- **I ≤ 4 shoelace Pick-form** without spokes-empty hyp (not classical Pick).

Combines geometric I ≤ 3 with I = 4. Shoelace ≠ Haar. Classical Pick FAIL. -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_four
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hcard : S.card ≤ 4)
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hsc : StrictlyConvexCCW P) :
    P.shoelace = (S.card : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  by_cases hle3 : S.card ≤ 3
  · exact shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_three
      P S hS hle3 hverts hedge hsc
  · have h4 : S.card = 4 := by omega
    exact shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_four
      P S hS h4 hverts hedge hsc


/-! ## I = 5 geometric fan-ear without spokes-empty (not classical Pick)

Parent `#S = 5`: pick any apex `q ∈ S`, fan into ears. Each `#earOff ≤ 4`.
* `#earOff ≤ 3` ⇒ triangle I≤3 Pick without `PrimitiveEdges` on ear sides.
* `#earOff = 4` ⇒ the four non-apex interior points all lie Off in that ear, so
  every spoke from `q` is empty; ear inherits `PrimitiveEdges` and I≤4 applies.
Discharged hbook closes the fan-ear IH. Shoelace ≠ Haar. Classical Pick FAIL.
-/

/-- Parent `#S = 5` ⇒ `#earOff ≤ 4`. -/
theorem card_earOffInterior_le_four_of_card_eq_five
    (q : ℤ × ℤ) (i : Fin P.nVertices) (S : Finset (ℤ × ℤ))
    (hq : q ∈ S) (hcard : S.card = 5) :
    (earOffInterior P q i S).card ≤ 4 := by
  have hlt := card_earOffInterior_lt P q i S hq
  omega

/-- Parent `#S = 5` and `#earOff = 4` ⇒ every spoke from the apex is empty
(all four remaining interior points lie Off in that ear). -/
theorem spokeInterior_eq_empty_of_earOffInterior_card_eq_four_of_card_eq_five
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q : ℤ × ℤ}
    (hq : q ∈ S) (i : Fin P.nVertices)
    (hcardS : S.card = 5)
    (hcardE : (earOffInterior P q i S).card = 4)
    (k : Fin P.nVertices) :
    spokeInterior P q k S = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
  have hqI : q ∈ P.interiorLatticePoints := by
    have : q ∈ (S : Set (ℤ × ℤ)) := hq
    rwa [hS] at this
  have hp' : p ∈ S ∧ p ≠ q ∧ p ≠ P.vertex k ∧ p ∈ edgeLatticePoints q (P.vertex k) := by
    simpa [spokeInterior] using hp
  have hsub : earOffInterior P q i S ⊆ S.erase q := by
    intro r hr
    have hr' : r ∈ S ∧ r ≠ q ∧
        MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r ∧
          OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r := by
      simpa [earOffInterior] using hr
    exact Finset.mem_erase.mpr ⟨hr'.2.1, hr'.1⟩
  have herase : (S.erase q).card = 4 := by
    rw [Finset.card_erase_of_mem hq, hcardS]
  have heq : earOffInterior P q i S = S.erase q :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hp_ear : p ∈ earOffInterior P q i S := by
    have : p ∈ S.erase q := Finset.mem_erase.mpr ⟨hp'.2.1, hp'.1⟩
    simpa [heq] using this
  exact false_of_mem_earOffInterior_of_mem_spokeInterior
    P hsc hinj hedge hqI S hp_ear hp

/-- Ear Pick-form for parent `#S = 5` without a spokes-empty hyp
(not classical Pick).

Uses triangle I≤3 when `#earOff ≤ 3` (no `PrimitiveEdges` on ear sides); when
`#earOff = 4`, adjacent spokes are empty so the ear inherits `PrimitiveEdges`
and I≤4 applies. -/
theorem shoelace_trianglePolygon_ear_eq_card_earOff_add_B_div_two_sub_one_of_I_le_four_of_card_eq_five
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q : ℤ × ℤ}
    (hq : q ∈ S) (i : Fin P.nVertices)
    (hcardS : S.card = 5)
    (hcard : (earOffInterior P q i S).card ≤ 4) :
    (trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))).shoelace =
      ((earOffInterior P q i S).card : ℚ) +
        ((trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))).B : ℚ) / 2 - 1 := by
  classical
  set T := trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))
  set S_ear := earOffInterior P q i S
  have hqI : q ∈ P.interiorLatticePoints := by
    have : q ∈ (S : Set (ℤ × ℤ)) := hq
    rwa [hS] at this
  have hpos := InteriorFanDetsPos_of_mem_interior P hsc hinj hedge hqI
  have hD : 0 < latticeDet q (P.vertex i) (P.vertex (P.nextIdx i)) := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hpos i
  have hS_ear : (S_ear : Set (ℤ × ℤ)) = T.interiorLatticePoints :=
    coe_earOffInterior_eq_interiorLatticePoints_trianglePolygon
      P S hS hsc hinj hedge hq i
  by_cases hle3 : S_ear.card ≤ 3
  · simpa [T, S_ear] using
      (shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_three_triangle
        q (P.vertex i) (P.vertex (P.nextIdx i)) hD S_ear hS_ear hle3)
  · have h4 : S_ear.card = 4 := by omega
    have h4' : (earOffInterior P q i S).card = 4 := by simpa [S_ear] using h4
    have hL : spokeInterior P q i S = ∅ :=
      spokeInterior_eq_empty_of_earOffInterior_card_eq_four_of_card_eq_five
        P S hS hsc hinj hedge hq i hcardS h4' i
    have hR : spokeInterior P q (P.nextIdx i) S = ∅ :=
      spokeInterior_eq_empty_of_earOffInterior_card_eq_four_of_card_eq_five
        P S hS hsc hinj hedge hq i hcardS h4' (P.nextIdx i)
    have hscT : StrictlyConvexCCW T := StrictlyConvexCCW_trianglePolygon _ _ _ hD
    have hinjT : Function.Injective T.vertex :=
      injective_vertex_trianglePolygon _ _ _ (ne_of_gt hD)
    have hedgeT : PrimitiveEdges T :=
      PrimitiveEdges_trianglePolygon_ear_of_spokeInterior_empty
        P S hS hsc hinj hedge hq i hL hR
    simpa [T, S_ear] using
      (shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_four
        T S_ear hS_ear (by omega : S_ear.card ≤ 4) hinjT hedgeT hscT)

/-- **I = 5 shoelace Pick-form** without spokes-empty hyp (not classical Pick).

Hyps: geometric polygon (`StrictlyConvexCCW`, injective, parent `PrimitiveEdges`),
interior Finset `#S = 5`. Any apex works: fan-ear IH with triangle I≤3 /
PrimitiveEdges-on-`#earOff=4` ears and discharged hbook. Ears may have
non-primitive sides. Shoelace ≠ Haar. Classical Pick FAIL. -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_five
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hcard : S.card = 5)
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hsc : StrictlyConvexCCW P) :
    P.shoelace = (S.card : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q, hq⟩ := hne
  refine shoelace_eq_cardI_add_B_div_two_sub_one_of_fan_ear_IH
    P S hS q hq hverts hedge hsc ?hIH
    (hbook_of_fan_ear_partition_of_interior P S hS hsc hverts hedge hq)
  intro i
  exact shoelace_trianglePolygon_ear_eq_card_earOff_add_B_div_two_sub_one_of_I_le_four_of_card_eq_five
    P S hS hsc hverts hedge hq i hcard
    (card_earOffInterior_le_four_of_card_eq_five P q i S hq hcard)

/-- **I ≤ 5 shoelace Pick-form** without spokes-empty hyp (not classical Pick).

Combines geometric I ≤ 4 with I = 5. Shoelace ≠ Haar. Classical Pick FAIL. -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_five
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hcard : S.card ≤ 5)
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hsc : StrictlyConvexCCW P) :
    P.shoelace = (S.card : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  by_cases hle4 : S.card ≤ 4
  · exact shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_four
      P S hS hle4 hverts hedge hsc
  · have h5 : S.card = 5 := by omega
    exact shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_five
      P S hS h5 hverts hedge hsc



/-! ## I ≤ k triangle without PrimitiveEdges via pe_ih (not classical Pick)

Generalizes the I≤3 Finset `|det|` / edgeStep induction: given Pick for all
polygons with `PrimitiveEdges` and `#S ≤ k`, conclude Pick for closed lattice
triangles with `#S ≤ k` and **no** `PrimitiveEdges` hyp. Fuel for fan-ear /
strong induction on ears that may have non-primitive sides. Shoelace ≠ Haar.
Classical Pick FAIL.
-/

/-- Helper: I≤k triangle Pick when a designated edge has `edgeGcd ≥ 2`,
conditional on IH for strictly smaller `|det|`. -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_triangle_of_edgeStep_ab
    (k : ℕ) (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = (trianglePolygon a b c).interiorLatticePoints)
    (hcard : S.card ≤ k)
    (ih : ∀ a' b' c' : ℤ × ℤ, ∀ S' : Finset (ℤ × ℤ),
      0 < latticeDet a' b' c' →
      (S' : Set (ℤ × ℤ)) = (trianglePolygon a' b' c').interiorLatticePoints →
      S'.card ≤ k →
      Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) →
      (trianglePolygon a' b' c').shoelace =
        (S'.card : ℚ) + ((trianglePolygon a' b' c').B : ℚ) / 2 - 1) :
    (trianglePolygon a b c).shoelace =
      (S.card : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by
  classical
  set p := edgeStep a b
  set T := trianglePolygon a b c
  set TL := trianglePolygon a p c
  set TR := trianglePolygon p b c
  have hlt := natAbs_latticeDet_edgeStep_lt a b c hD hd
  have hD1 : 0 < latticeDet a p c := latticeDet_edgeStep_pos a b c hD (by omega)
  have hD2 : 0 < latticeDet p b c := latticeDet_edgeStep_right_pos a b c hD hd
  have hsa := shoelace_add_of_edgeStep a b c hD hd
  have hBa := B_add_of_edgeStep_of_gcd a b c hD hd
  have hpne : p ≠ c := by
    intro hpc
    have hp := edgeStep_mem_edgeLatticePoints a b (by omega)
    have : latticeDet a b c = 0 := by
      simpa [hpc] using latticeDet_eq_zero_of_mem_edge_ab a b p hp
    omega
  have hg_pos : 1 ≤ edgeGcd p c :=
    Nat.pos_of_ne_zero fun hz => hpne ((edgeGcd_eq_zero_iff p c).mp hz)
  set g := edgeGcd p c
  set S_L : Finset (ℤ × ℤ) := S.filter (fun x => x ∈ TL.interiorLatticePoints)
  set S_R : Finset (ℤ × ℤ) := S.filter (fun x => x ∈ TR.interiorLatticePoints)
  set S_C : Finset (ℤ × ℤ) := openChordEdgeStep a b c
  have hSL_set : (S_L : Set (ℤ × ℤ)) = TL.interiorLatticePoints := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp (by simpa [S_L] using hx)).2
    · intro hx
      have hxP := mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_left a b c hD hd
        (by simpa [p, TL] using hx)
      have hxS : x ∈ S := by
        have : x ∈ (S : Set (ℤ × ℤ)) := by simpa [hS] using hxP
        exact this
      exact Finset.mem_filter.mpr ⟨hxS, by simpa [TL] using hx⟩
  have hSR_set : (S_R : Set (ℤ × ℤ)) = TR.interiorLatticePoints := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp (by simpa [S_R] using hx)).2
    · intro hx
      have hxP := mem_interiorLatticePoints_parent_of_mem_interior_edgeStep_right a b c hD hd
        (by simpa [p, TR] using hx)
      have hxS : x ∈ S := by
        have : x ∈ (S : Set (ℤ × ℤ)) := by simpa [hS] using hxP
        exact this
      exact Finset.mem_filter.mpr ⟨hxS, by simpa [TR] using hx⟩
  have hSC_sub : (S_C : Set (ℤ × ℤ)) ⊆ T.interiorLatticePoints := by
    simpa [S_C, T] using openChordEdgeStep_subset_interior a b c hD hd
  have hSC_S : S_C ⊆ S := by
    intro x hx
    have : x ∈ (S : Set (ℤ × ℤ)) := by
      have hxI : x ∈ T.interiorLatticePoints := hSC_sub hx
      simpa [hS, T] using hxI
    exact this
  have hcard_C : S_C.card = g - 1 := by
    have h := card_openChordEdgeStep a b c (by simpa [p] using hpne)
    rcases h with h' | hg0
    · simpa [S_C, g, p] using h'
    · exact (Nat.ne_of_gt hg_pos (by simpa [g, p] using hg0)).elim
  have hdisj_LR : Disjoint S_L S_R := by
    refine Finset.disjoint_left.mpr fun x hxL hxR => ?_
    have hxL' : x ∈ TL.interiorLatticePoints := (Finset.mem_filter.mp (by simpa [S_L] using hxL)).2
    have hxR' : x ∈ TR.interiorLatticePoints := (Finset.mem_filter.mp (by simpa [S_R] using hxR)).2
    have hL := (mem_interiorLatticePoints_trianglePolygon_iff a p c x).mp (by simpa [TL] using hxL')
    have hR := (mem_interiorLatticePoints_trianglePolygon_iff p b c x).mp (by simpa [TR] using hxR')
    have hposL := latticeDet_pos_of_memClosedTriangle_offBoundary a p c x hL.1 hD1 hL.2
    have hposR := latticeDet_pos_of_memClosedTriangle_offBoundary p b c x hR.1 hD2 hR.2
    have h1 : 0 < latticeDet p c x := hposL.1
    have h2 : 0 < latticeDet p x c := hposR.2.1
    have hneg := latticeDet_pqc_neg p c x
    omega
  have hdisj_LC : Disjoint S_L S_C := by
    refine Finset.disjoint_left.mpr fun x hxL hxC => ?_
    have hxL' : x ∈ TL.interiorLatticePoints := (Finset.mem_filter.mp (by simpa [S_L] using hxL)).2
    have hL := (mem_interiorLatticePoints_trianglePolygon_iff a p c x).mp (by simpa [TL] using hxL')
    have hxC' : x ∈ ((edgeLatticePoints p c).erase p).erase c := by
      simpa [S_C, openChordEdgeStep, p] using hxC
    have hx_edge : x ∈ edgeLatticePoints p c := (Finset.mem_erase.mp (Finset.mem_erase.mp hxC').2).2
    exact hL.2.2.1 hx_edge
  have hdisj_RC : Disjoint S_R S_C := by
    refine Finset.disjoint_left.mpr fun x hxR hxC => ?_
    have hxR' : x ∈ TR.interiorLatticePoints := (Finset.mem_filter.mp (by simpa [S_R] using hxR)).2
    have hR := (mem_interiorLatticePoints_trianglePolygon_iff p b c x).mp (by simpa [TR] using hxR')
    have hxC' : x ∈ ((edgeLatticePoints p c).erase p).erase c := by
      simpa [S_C, openChordEdgeStep, p] using hxC
    have hx_edge : x ∈ edgeLatticePoints p c := (Finset.mem_erase.mp (Finset.mem_erase.mp hxC').2).2
    have hx_edge' : x ∈ edgeLatticePoints c p := mem_edgeLatticePoints_comm hx_edge
    exact hR.2.2.2 hx_edge'
  have hunion : S = S_L ∪ S_R ∪ S_C := by
    ext x
    constructor
    · intro hx
      have hxI : x ∈ T.interiorLatticePoints := by
        have : x ∈ (S : Set (ℤ × ℤ)) := hx
        simpa [hS, T] using this
      rcases mem_interior_left_or_right_or_chord_of_mem_interior_edgeStep a b c hD hd
          (by simpa [T] using hxI) with hL | hR | hC
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr ⟨hx, by simpa [TL, p] using hL⟩))))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨hx, by simpa [TR, p] using hR⟩))))
      · exact Finset.mem_union.mpr (Or.inr (by
          simpa [S_C, openChordEdgeStep, p, Finset.mem_erase] using
            ⟨hC.2.2, ⟨hC.2.1, hC.1⟩⟩))
    · intro hx
      rcases Finset.mem_union.mp hx with hLR | hC
      · rcases Finset.mem_union.mp hLR with hL | hR
        · exact (Finset.mem_filter.mp (by simpa [S_L] using hL)).1
        · exact (Finset.mem_filter.mp (by simpa [S_R] using hR)).1
      · exact hSC_S (by simpa [S_C] using hC)
  have hcard_sum : S.card = S_L.card + S_R.card + S_C.card := by
    have h1 : (S_L ∪ S_R ∪ S_C).card = S_L.card + S_R.card + S_C.card := by
      have d1 := hdisj_LR
      have d2 : Disjoint (S_L ∪ S_R) S_C :=
        Finset.disjoint_union_left.mpr ⟨hdisj_LC, hdisj_RC⟩
      rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1]
    simpa [hunion] using h1
  have hcardL : S_L.card ≤ k := by omega
  have hcardR : S_R.card ≤ k := by omega
  have ihL := ih a p c S_L hD1 hSL_set hcardL hlt.1
  have ihR := ih p b c S_R hD2 hSR_set hcardR hlt.2
  have hBsum : TL.B + TR.B = T.B + 2 * g := by simpa [TL, TR, T, p, g] using hBa
  calc
    T.shoelace
        = TL.shoelace + TR.shoelace := by simpa [T, TL, TR, p] using hsa
    _ = ((S_L.card : ℚ) + (TL.B : ℚ) / 2 - 1) +
          ((S_R.card : ℚ) + (TR.B : ℚ) / 2 - 1) := by rw [ihL, ihR]
    _ = (S_L.card : ℚ) + (S_R.card : ℚ) + ((TL.B : ℚ) + (TR.B : ℚ)) / 2 - 2 := by ring
    _ = (S_L.card : ℚ) + (S_R.card : ℚ) + ((T.B + 2 * g : ℕ) : ℚ) / 2 - 2 := by
          rw [← hBsum]; push_cast; rfl
    _ = (S_L.card : ℚ) + (S_R.card : ℚ) + (T.B : ℚ) / 2 + (g : ℚ) - 2 := by
          push_cast; ring
    _ = (S.card : ℚ) + (T.B : ℚ) / 2 - 1 := by
          have hsum' : (S.card : ℚ) = (S_L.card : ℚ) + (S_R.card : ℚ) + (S_C.card : ℚ) := by
            exact_mod_cast hcard_sum
          have hC' : (S_C.card : ℚ) = (g : ℚ) - 1 := by
            have : S_C.card + 1 = g := by omega
            exact_mod_cast (by omega : (S_C.card : ℤ) = (g : ℤ) - 1)
          rw [hsum', hC']
          ring

/-- I≤k shoelace Pick-form for a closed lattice triangle without `PrimitiveEdges`,
conditional on Pick for all `PrimitiveEdges` polygons with `#S ≤ k`
(not classical Pick). -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_triangle_of_pe_ih
    (k : ℕ)
    (pe_ih : ∀ (Q : LatticePolygon) (S : Finset (ℤ × ℤ)),
      (S : Set (ℤ × ℤ)) = Q.interiorLatticePoints →
      S.card ≤ k →
      Function.Injective Q.vertex →
      PrimitiveEdges Q →
      StrictlyConvexCCW Q →
      Q.shoelace = (S.card : ℚ) + (Q.B : ℚ) / 2 - 1)
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c)
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = (trianglePolygon a b c).interiorLatticePoints)
    (hcard : S.card ≤ k) :
    (trianglePolygon a b c).shoelace =
      (S.card : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 := by
  classical
  generalize hn : Int.natAbs (latticeDet a b c) = n
  revert a b c S
  refine Nat.strong_induction_on n fun n ih a b c hD S hS hcard hn => ?_
  have _hpos := edgeGcd_pos_of_latticeDet_pos a b c hD
  by_cases hprim : edgeGcd a b = 1 ∧ edgeGcd b c = 1 ∧ edgeGcd c a = 1
  · have hedge :=
      PrimitiveEdges_trianglePolygon_of_edgeGcds a b c hprim.1 hprim.2.1 hprim.2.2
    exact pe_ih (trianglePolygon a b c) S hS hcard
      (injective_vertex_trianglePolygon a b c (ne_of_gt hD))
      hedge
      (StrictlyConvexCCW_trianglePolygon a b c hD)
  · have hge : 2 ≤ edgeGcd a b ∨ 2 ≤ edgeGcd b c ∨ 2 ≤ edgeGcd c a := by omega
    have ih' : ∀ a' b' c' : ℤ × ℤ, ∀ S' : Finset (ℤ × ℤ),
        0 < latticeDet a' b' c' →
        (S' : Set (ℤ × ℤ)) = (trianglePolygon a' b' c').interiorLatticePoints →
        S'.card ≤ k →
        Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) →
        (trianglePolygon a' b' c').shoelace =
          (S'.card : ℚ) + ((trianglePolygon a' b' c').B : ℚ) / 2 - 1 := by
      intro a' b' c' S' hD' hS' hcard' hlt'
      have hltn : Int.natAbs (latticeDet a' b' c') < n := by simpa [hn] using hlt'
      exact ih _ hltn a' b' c' hD' S' hS' hcard' rfl
    rcases hge with hab | hbc | hca
    · subst hn
      exact shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_triangle_of_edgeStep_ab
        k a b c hD hab S hS hcard ih'
    · have hDc : 0 < latticeDet b c a := by simpa [← latticeDet_cyclic a b c] using hD
      have hSc : (S : Set (ℤ × ℤ)) = (trianglePolygon b c a).interiorLatticePoints := by
        simpa [← interiorLatticePoints_trianglePolygon_cyclic a b c] using hS
      have ihc : ∀ a' b' c' : ℤ × ℤ, ∀ S' : Finset (ℤ × ℤ),
          0 < latticeDet a' b' c' →
          (S' : Set (ℤ × ℤ)) = (trianglePolygon a' b' c').interiorLatticePoints →
          S'.card ≤ k →
          Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet b c a) →
          (trianglePolygon a' b' c').shoelace =
            (S'.card : ℚ) + ((trianglePolygon a' b' c').B : ℚ) / 2 - 1 := by
        intro a' b' c' S' hD' hS' hcard' hlt'
        have : Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) := by
          simpa [← latticeDet_cyclic a b c] using hlt'
        exact ih' a' b' c' S' hD' hS' hcard' this
      have hpick :=
        shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_triangle_of_edgeStep_ab
          k b c a hDc hbc S hSc hcard ihc
      rw [shoelace_trianglePolygon_cyclic a b c,
          B_trianglePolygon_cyclic a b c (ne_of_gt hD)]
      exact hpick
    · have hDc : 0 < latticeDet c a b := by simpa [← latticeDet_cyclic₂ a b c] using hD
      have hSc : (S : Set (ℤ × ℤ)) = (trianglePolygon c a b).interiorLatticePoints := by
        have h1 := interiorLatticePoints_trianglePolygon_cyclic a b c
        have h2 := interiorLatticePoints_trianglePolygon_cyclic b c a
        simpa [← h2, ← h1] using hS
      have ihc : ∀ a' b' c' : ℤ × ℤ, ∀ S' : Finset (ℤ × ℤ),
          0 < latticeDet a' b' c' →
          (S' : Set (ℤ × ℤ)) = (trianglePolygon a' b' c').interiorLatticePoints →
          S'.card ≤ k →
          Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet c a b) →
          (trianglePolygon a' b' c').shoelace =
            (S'.card : ℚ) + ((trianglePolygon a' b' c').B : ℚ) / 2 - 1 := by
        intro a' b' c' S' hD' hS' hcard' hlt'
        have : Int.natAbs (latticeDet a' b' c') < Int.natAbs (latticeDet a b c) := by
          simpa [← latticeDet_cyclic₂ a b c] using hlt'
        exact ih' a' b' c' S' hD' hS' hcard' this
      have hpick :=
        shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_triangle_of_edgeStep_ab
          k c a b hDc hca S hSc hcard ihc
      have hs1 := shoelace_trianglePolygon_cyclic a b c
      have hs2 := shoelace_trianglePolygon_cyclic b c a
      have hB1 := B_trianglePolygon_cyclic a b c (ne_of_gt hD)
      have hB2 := B_trianglePolygon_cyclic b c a
        (by simpa [← latticeDet_cyclic a b c] using ne_of_gt hD)
      rw [hs1, hs2, hB1, hB2]
      exact hpick

/-- I ∈ {0..4} shoelace Pick-form for a closed lattice triangle without
`PrimitiveEdges` (not classical Pick). -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_four_triangle
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c)
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = (trianglePolygon a b c).interiorLatticePoints)
    (hcard : S.card ≤ 4) :
    (trianglePolygon a b c).shoelace =
      (S.card : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 :=
  shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_triangle_of_pe_ih 4
    (fun Q S hS hcard hverts hedge hsc =>
      shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_four
        Q S hS hcard hverts hedge hsc)
    a b c hD S hS hcard

/-- I ∈ {0..5} shoelace Pick-form for a closed lattice triangle without
`PrimitiveEdges` (not classical Pick). -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_five_triangle
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c)
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = (trianglePolygon a b c).interiorLatticePoints)
    (hcard : S.card ≤ 5) :
    (trianglePolygon a b c).shoelace =
      (S.card : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 :=
  shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_triangle_of_pe_ih 5
    (fun Q S hS hcard hverts hedge hsc =>
      shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_five
        Q S hS hcard hverts hedge hsc)
    a b c hD S hS hcard


/-! ## I = 6 geometric fan-ear without spokes-empty (not classical Pick)

Parent `#S = 6`: pick any apex `q ∈ S`, fan into ears. Each `#earOff ≤ 5`.
Apply triangle I≤5 Pick without `PrimitiveEdges` on every ear (no PE
inheritance branch needed). Discharged hbook closes the fan-ear IH.
Shoelace ≠ Haar. Classical Pick FAIL.
-/

/-- Parent `#S = 6` ⇒ `#earOff ≤ 5`. -/
theorem card_earOffInterior_le_five_of_card_eq_six
    (q : ℤ × ℤ) (i : Fin P.nVertices) (S : Finset (ℤ × ℤ))
    (hq : q ∈ S) (hcard : S.card = 6) :
    (earOffInterior P q i S).card ≤ 5 := by
  have hlt := card_earOffInterior_lt P q i S hq
  omega

/-- Ear Pick-form for parent `#S = 6` without a spokes-empty hyp
(not classical Pick). Uses triangle I≤5 without `PrimitiveEdges`. -/
theorem shoelace_trianglePolygon_ear_eq_card_earOff_add_B_div_two_sub_one_of_I_le_five_of_card_eq_six
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q : ℤ × ℤ}
    (hq : q ∈ S) (i : Fin P.nVertices)
    (_hcardS : S.card = 6)
    (hcard : (earOffInterior P q i S).card ≤ 5) :
    (trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))).shoelace =
      ((earOffInterior P q i S).card : ℚ) +
        ((trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))).B : ℚ) / 2 - 1 := by
  classical
  set T := trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))
  set S_ear := earOffInterior P q i S
  have hqI : q ∈ P.interiorLatticePoints := by
    have : q ∈ (S : Set (ℤ × ℤ)) := hq
    rwa [hS] at this
  have hpos := InteriorFanDetsPos_of_mem_interior P hsc hinj hedge hqI
  have hD : 0 < latticeDet q (P.vertex i) (P.vertex (P.nextIdx i)) := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hpos i
  have hS_ear : (S_ear : Set (ℤ × ℤ)) = T.interiorLatticePoints :=
    coe_earOffInterior_eq_interiorLatticePoints_trianglePolygon
      P S hS hsc hinj hedge hq i
  simpa [T, S_ear] using
    (shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_five_triangle
      q (P.vertex i) (P.vertex (P.nextIdx i)) hD S_ear hS_ear hcard)

/-- **I = 6 shoelace Pick-form** without spokes-empty hyp (not classical Pick).

Hyps: geometric polygon (`StrictlyConvexCCW`, injective, parent `PrimitiveEdges`),
interior Finset `#S = 6`. Any apex works: fan-ear IH with triangle I≤5 ears
and discharged hbook. Ears may have non-primitive sides. Shoelace ≠ Haar.
Classical Pick FAIL. -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_six
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hcard : S.card = 6)
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hsc : StrictlyConvexCCW P) :
    P.shoelace = (S.card : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q, hq⟩ := hne
  refine shoelace_eq_cardI_add_B_div_two_sub_one_of_fan_ear_IH
    P S hS q hq hverts hedge hsc ?hIH
    (hbook_of_fan_ear_partition_of_interior P S hS hsc hverts hedge hq)
  intro i
  exact shoelace_trianglePolygon_ear_eq_card_earOff_add_B_div_two_sub_one_of_I_le_five_of_card_eq_six
    P S hS hsc hverts hedge hq i hcard
    (card_earOffInterior_le_five_of_card_eq_six P q i S hq hcard)

/-- **I ≤ 6 shoelace Pick-form** without spokes-empty hyp (not classical Pick).

Combines geometric I ≤ 5 with I = 6. Shoelace ≠ Haar. Classical Pick FAIL. -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_six
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hcard : S.card ≤ 6)
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hsc : StrictlyConvexCCW P) :
    P.shoelace = (S.card : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  by_cases hle5 : S.card ≤ 5
  · exact shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_five
      P S hS hle5 hverts hedge hsc
  · have h6 : S.card = 6 := by omega
    exact shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_six
      P S hS h6 hverts hedge hsc


/-! ## Strong induction on Finset card (not classical Pick)

`∀ S, geometric hyps → shoelace = #S + B/2 − 1`, by strong induction on
`S.card`. Base `card ≤ 5` via `I_le_five`. Step: fan from any apex; each ear
has strictly smaller card, so triangle Pick without `PrimitiveEdges` via
`pe_ih` fed by the induction hypothesis; discharged hbook closes
`fan_ear_IH`. PE inheritance on large ears is avoided: ears are triangles
handled by `|det|` induction with PE Pick as primitive-edge base.
Shoelace ≠ Haar. Classical Pick FAIL.
-/

/-- **Geometric Finset shoelace Pick-form** by strong induction on `#S`
(not classical Pick).

Hyps: `StrictlyConvexCCW`, injective vertices, parent `PrimitiveEdges`,
`S` exactly the interior lattice points. Concludes
`P.shoelace = #S + B/2 − 1`. Shoelace ≠ Haar. Classical Pick FAIL. -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hsc : StrictlyConvexCCW P) :
    P.shoelace = (S.card : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  have hmain :
      ∀ (n : ℕ) (Q : LatticePolygon) (T : Finset (ℤ × ℤ)),
        (T : Set (ℤ × ℤ)) = Q.interiorLatticePoints →
        T.card = n →
        Function.Injective Q.vertex →
        PrimitiveEdges Q →
        StrictlyConvexCCW Q →
        Q.shoelace = (T.card : ℚ) + (Q.B : ℚ) / 2 - 1 := by
    intro n
    refine Nat.strong_induction_on n fun n ih Q T hT hn hverts' hedge' hsc' => ?_
    by_cases hle5 : n ≤ 5
    · subst hn
      exact shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_five
        Q T hT (by omega) hverts' hedge' hsc'
    · have hne : T.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨q, hq⟩ := hne
      refine shoelace_eq_cardI_add_B_div_two_sub_one_of_fan_ear_IH
        Q T hT q hq hverts' hedge' hsc' ?hIH
        (hbook_of_fan_ear_partition_of_interior Q T hT hsc' hverts' hedge' hq)
      intro i
      set Tri := trianglePolygon q (Q.vertex i) (Q.vertex (Q.nextIdx i))
      set S_ear := earOffInterior Q q i T
      have hqI : q ∈ Q.interiorLatticePoints := by
        have : q ∈ (T : Set (ℤ × ℤ)) := hq
        rwa [hT] at this
      have hpos := InteriorFanDetsPos_of_mem_interior Q hsc' hverts' hedge' hqI
      have hD : 0 < latticeDet q (Q.vertex i) (Q.vertex (Q.nextIdx i)) := by
        simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hpos i
      have hS_ear : (S_ear : Set (ℤ × ℤ)) = Tri.interiorLatticePoints :=
        coe_earOffInterior_eq_interiorLatticePoints_trianglePolygon
          Q T hT hsc' hverts' hedge' hq i
      have hlt_ear : S_ear.card < n := by
        simpa [S_ear, hn] using card_earOffInterior_lt Q q i T hq
      have hcard_ear : S_ear.card ≤ n - 1 := by omega
      refine shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_triangle_of_pe_ih
        (n - 1) ?pe_ih q (Q.vertex i) (Q.vertex (Q.nextIdx i)) hD S_ear hS_ear
        hcard_ear
      intro Q' S' hS' hcard' hverts'' hedge'' hsc''
      have hlt' : S'.card < n := by omega
      exact ih S'.card hlt' Q' S' hS' rfl hverts'' hedge'' hsc''
  exact hmain S.card P S hS rfl hverts hedge hsc

/-! ## All-I triangle without PrimitiveEdges (not classical Pick)

Package `pe_ih` at `#S` against the PE strong induction, so every closed lattice
triangle (any `#I`) satisfies the shoelace Pick-form with no `PrimitiveEdges` hyp.
Fuel for PE-free parent fan / ear-clip. Classical Pick FAIL.
-/

/-- Closed lattice triangle shoelace Pick-form for arbitrary `#S`, without
`PrimitiveEdges` (not classical Pick). -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_triangle
    (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c)
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = (trianglePolygon a b c).interiorLatticePoints) :
    (trianglePolygon a b c).shoelace =
      (S.card : ℚ) + ((trianglePolygon a b c).B : ℚ) / 2 - 1 :=
  shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_triangle_of_pe_ih S.card
    (fun Q T hT _hcard hverts hedge hsc =>
      shoelace_eq_cardI_add_B_div_two_sub_one Q T hT hverts hedge hsc)
    a b c hD S hS le_rfl

/-! ## Empty-interior StrictlyConvexCCW without PrimitiveEdges (not classical Pick)

Vertex fan from `v₀` + empty PE-free triangles + chord `edgeGcd = 1` + `B = ∑ edgeGcd`
telescoping. Classical Pick FAIL.
-/

/-- Three points each collinear with edge `(A,B)` are themselves collinear. -/
lemma latticeDet_eq_zero_of_edge_dets_eq_zero
    (A B X Y Z : ℤ × ℤ) (hAB : A ≠ B)
    (hx : latticeDet A B X = 0) (hy : latticeDet A B Y = 0)
    (hz : latticeDet A B Z = 0) :
    latticeDet X Y Z = 0 := by
  set w : ℤ × ℤ := (B.1 - A.1, B.2 - A.2)
  set u : ℤ × ℤ := (Y.1 - X.1, Y.2 - X.2)
  set v : ℤ × ℤ := (Z.1 - X.1, Z.2 - X.2)
  have hw : w ≠ 0 := by
    intro h
    have h1 : B.1 - A.1 = 0 := by simpa [w] using congrArg Prod.fst h
    have h2 : B.2 - A.2 = 0 := by simpa [w] using congrArg Prod.snd h
    exact hAB (Prod.ext (by linarith) (by linarith))
  -- latticeDet A B W = w × (W-A); cross lemma wants (W-A) × w = -(w × (W-A))
  have hx' : (X.1 - A.1) * w.2 - (X.2 - A.2) * w.1 = 0 := by
    have : w.1 * (X.2 - A.2) - w.2 * (X.1 - A.1) = 0 := by
      simpa [latticeDet, w] using hx
    linarith
  have hy' : (Y.1 - A.1) * w.2 - (Y.2 - A.2) * w.1 = 0 := by
    have : w.1 * (Y.2 - A.2) - w.2 * (Y.1 - A.1) = 0 := by
      simpa [latticeDet, w] using hy
    linarith
  have hz' : (Z.1 - A.1) * w.2 - (Z.2 - A.2) * w.1 = 0 := by
    have : w.1 * (Z.2 - A.2) - w.2 * (Z.1 - A.1) = 0 := by
      simpa [latticeDet, w] using hz
    linarith
  have hu : u.1 * w.2 - u.2 * w.1 = 0 := by
    have : ((Y.1 - A.1) - (X.1 - A.1)) * w.2 -
        ((Y.2 - A.2) - (X.2 - A.2)) * w.1 = 0 := by
      linear_combination hy' - hx'
    simpa [u] using this
  have hv : v.1 * w.2 - v.2 * w.1 = 0 := by
    have : ((Z.1 - A.1) - (X.1 - A.1)) * w.2 -
        ((Z.2 - A.2) - (X.2 - A.2)) * w.1 = 0 := by
      linear_combination hz' - hx'
    simpa [v] using this
  have hcross := cross_eq_zero_of_cross_eq_zero_both u v w hu hv hw
  simpa [latticeDet, u, v] using hcross

/-- An OffBoundary lattice point of a vertex-fan ear is a parent-interior point,
without `PrimitiveEdges`. -/
theorem mem_interiorLatticePoints_of_memClosedTriangle_off_fan_no_pe
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (i : ℕ) (hi : i < P.nVertices - 2) {p : ℤ × ℤ}
    (hmem : MemClosedTriangle (fanTriangle P i hi).a (fanTriangle P i hi).b
      (fanTriangle P i hi).c p)
    (hoff : OffTriangleBoundary (fanTriangle P i hi).a (fanTriangle P i hi).b
      (fanTriangle P i hi).c p) :
    p ∈ P.interiorLatticePoints := by
  classical
  set a := (fanTriangle P i hi).a
  set b := (fanTriangle P i hi).b
  set c := (fanTriangle P i hi).c
  have hposFan := FanDetsPos_of_strictlyConvexCCW P hsc hinj
  have hD : 0 < latticeDet a b c := by
    simpa [a, b, c, fanDet, fanTriangle, Triangle.det] using hposFan i hi
  obtain ⟨hd_bc, hd_ac, hd_ab⟩ :=
    latticeDet_pos_of_memClosedTriangle_offBoundary a b c p
      (by simpa [a, b, c] using hmem) hD (by simpa [a, b, c] using hoff)
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, heq⟩ := (by simpa [a, b, c] using hmem)
  obtain ⟨e1, e2, e3⟩ := latticeDet_eq_bary_mul_of_affine a b c p α β γ hsum heq
  have hD0 : (0 : ℝ) < (latticeDet a b c : ℝ) := by exact_mod_cast hD
  have hαpos : 0 < α := by
    have hposR : (0 : ℝ) < (latticeDet b c p : ℝ) := by exact_mod_cast hd_bc
    nlinarith [e1, hposR, hD0]
  have hβpos : 0 < β := by
    have hposR : (0 : ℝ) < (latticeDet a p c : ℝ) := by exact_mod_cast hd_ac
    nlinarith [e2, hposR, hD0]
  have hγpos : 0 < γ := by
    have hposR : (0 : ℝ) < (latticeDet a b p : ℝ) := by exact_mod_cast hd_ab
    nlinarith [e3, hposR, hD0]
  have hedge_det_pos : ∀ j : Fin P.nVertices,
      0 < latticeDet (P.vertex j) (P.vertex (P.nextIdx j)) p := by
    intro j
    set A := toReal (P.vertex j)
    set B := toReal (P.vertex (P.nextIdx j))
    have haff :=
      detR_affine_combination3 A B (toReal a) (toReal b) (toReal c) α β γ hsum
    have hdetR :
        detR A B (toReal p) =
          α * detR A B (toReal a) + β * detR A B (toReal b) +
            γ * detR A B (toReal c) := by
      have hp_eq : toReal p = α • toReal a + β • toReal b + γ • toReal c := heq.symm
      rw [hp_eq, haff]
    have ha_nn : 0 ≤ latticeDet (P.vertex j) (P.vertex (P.nextIdx j)) a := by
      have ha0 : a = P.vertex ⟨0, P.nVertices_pos⟩ := by simp [a, fanTriangle]
      simpa [ha0] using hsc.1 j ⟨0, P.nVertices_pos⟩
    have hb_nn : 0 ≤ latticeDet (P.vertex j) (P.vertex (P.nextIdx j)) b := by
      have hb0 : b = P.vertex ⟨i + 1, by have := P.length_ge; omega⟩ := by
        simp [b, fanTriangle]
      simpa [hb0] using hsc.1 j ⟨i + 1, by have := P.length_ge; omega⟩
    have hc_nn : 0 ≤ latticeDet (P.vertex j) (P.vertex (P.nextIdx j)) c := by
      have hc0 : c = P.vertex ⟨i + 2, by have := P.length_ge; omega⟩ := by
        simp [c, fanTriangle]
      simpa [hc0] using hsc.1 j ⟨i + 2, by have := P.length_ge; omega⟩
    have haR : (0 : ℝ) ≤ detR A B (toReal a) := by
      have : (0 : ℝ) ≤ (latticeDet (P.vertex j) (P.vertex (P.nextIdx j)) a : ℝ) :=
        Int.cast_nonneg ha_nn
      simpa [A, B, detR_toReal] using this
    have hbR : (0 : ℝ) ≤ detR A B (toReal b) := by
      have : (0 : ℝ) ≤ (latticeDet (P.vertex j) (P.vertex (P.nextIdx j)) b : ℝ) :=
        Int.cast_nonneg hb_nn
      simpa [A, B, detR_toReal] using this
    have hcR : (0 : ℝ) ≤ detR A B (toReal c) := by
      have : (0 : ℝ) ≤ (latticeDet (P.vertex j) (P.vertex (P.nextIdx j)) c : ℝ) :=
        Int.cast_nonneg hc_nn
      simpa [A, B, detR_toReal] using this
    have hne_edge : P.vertex j ≠ P.vertex (P.nextIdx j) :=
      fun h => (nextIdx_ne P j) (hinj h).symm
    refine lt_of_le_of_ne ?hnn ?hne0
    · have hposR : (0 : ℝ) ≤ detR A B (toReal p) := by
        have h1 : 0 ≤ α * detR A B (toReal a) := mul_nonneg (le_of_lt hαpos) haR
        have h2 : 0 ≤ β * detR A B (toReal b) := mul_nonneg (le_of_lt hβpos) hbR
        have h3 : 0 ≤ γ * detR A B (toReal c) := mul_nonneg (le_of_lt hγpos) hcR
        linarith [hdetR]
      have : (0 : ℝ) ≤ (latticeDet (P.vertex j) (P.vertex (P.nextIdx j)) p : ℝ) := by
        simpa [A, B, detR_toReal] using hposR
      exact_mod_cast this
    · intro hz
      have hsum0 : detR A B (toReal p) = 0 := by
        have : (latticeDet (P.vertex j) (P.vertex (P.nextIdx j)) p : ℝ) = 0 := by
          exact_mod_cast hz.symm
        simpa [A, B, detR_toReal] using this
      have ha0 : latticeDet (P.vertex j) (P.vertex (P.nextIdx j)) a = 0 := by
        have hR : detR A B (toReal a) = 0 := by
          nlinarith [hdetR, hsum0,
            mul_nonneg (le_of_lt hαpos) haR,
            mul_nonneg (le_of_lt hβpos) hbR,
            mul_nonneg (le_of_lt hγpos) hcR, hαpos, haR]
        have : (latticeDet (P.vertex j) (P.vertex (P.nextIdx j)) a : ℝ) = 0 := by
          simpa [A, B, detR_toReal] using hR
        exact_mod_cast this
      have hb0 : latticeDet (P.vertex j) (P.vertex (P.nextIdx j)) b = 0 := by
        have hR : detR A B (toReal b) = 0 := by
          nlinarith [hdetR, hsum0,
            mul_nonneg (le_of_lt hαpos) haR,
            mul_nonneg (le_of_lt hβpos) hbR,
            mul_nonneg (le_of_lt hγpos) hcR, hβpos, hbR]
        have : (latticeDet (P.vertex j) (P.vertex (P.nextIdx j)) b : ℝ) = 0 := by
          simpa [A, B, detR_toReal] using hR
        exact_mod_cast this
      have hc0 : latticeDet (P.vertex j) (P.vertex (P.nextIdx j)) c = 0 := by
        have hR : detR A B (toReal c) = 0 := by
          nlinarith [hdetR, hsum0,
            mul_nonneg (le_of_lt hαpos) haR,
            mul_nonneg (le_of_lt hβpos) hbR,
            mul_nonneg (le_of_lt hγpos) hcR, hγpos, hcR]
        have : (latticeDet (P.vertex j) (P.vertex (P.nextIdx j)) c : ℝ) = 0 := by
          simpa [A, B, detR_toReal] using hR
        exact_mod_cast this
      have hcoll :=
        latticeDet_eq_zero_of_edge_dets_eq_zero
          (P.vertex j) (P.vertex (P.nextIdx j)) a b c hne_edge ha0 hb0 hc0
      exact (ne_of_gt hD) hcoll
  have hnb : p ∉ P.boundaryLatticePoints := by
    intro hb
    obtain ⟨j, hj⟩ := (mem_boundaryLatticePoints_iff P p).mp hb
    have hz : latticeDet (P.vertex j) (P.vertex (P.nextIdx j)) p = 0 :=
      latticeDet_eq_zero_of_mem_edge_ab (P.vertex j) (P.vertex (P.nextIdx j)) p
        (by simpa [LatticePolygon.edgePair] using hj)
    exact (ne_of_gt (hedge_det_pos j)) hz
  have hhull :=
    mem_convexHullRegion_of_memClosedTriangle_fan P i hi
      (by simpa [a, b, c] using hmem)
  refine ⟨?_, hnb⟩
  simpa [LatticePolygon.convexHullRegion] using hhull

/-- Fan ear `trianglePolygon` is empty-interior when the parent is (no PE). -/
theorem EmptyInterior_trianglePolygon_fanTriangle
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hI : EmptyInterior P)
    (i : ℕ) (hi : i < P.nVertices - 2) :
    EmptyInterior
      (trianglePolygon (fanTriangle P i hi).a (fanTriangle P i hi).b
        (fanTriangle P i hi).c) := by
  classical
  set a := (fanTriangle P i hi).a
  set b := (fanTriangle P i hi).b
  set c := (fanTriangle P i hi).c
  change (trianglePolygon a b c).interiorLatticePoints = ∅
  refine Set.eq_empty_of_forall_notMem fun p hp => ?_
  have hp' := (mem_interiorLatticePoints_trianglePolygon_iff a b c p).mp hp
  have hpI :=
    mem_interiorLatticePoints_of_memClosedTriangle_off_fan_no_pe P hsc hinj i hi
      (by simpa [a, b, c] using hp'.1) (by simpa [a, b, c] using hp'.2)
  have hEmpty : P.interiorLatticePoints = ∅ := hI
  exact (hEmpty ▸ hpI).elim


/-! ## Chord primitivity under EmptyInterior (not classical Pick)

Fan chord `(v₀, vₖ)` for `2 ≤ k ≤ nVertices-2`: an open lattice point on the chord
is in the hull and off the constructive boundary (else three listed vertices are
collinear under `VerticesExtreme`), hence parent-interior. EmptyInterior forces
`edgeGcd = 1`. Explicit `Fin` indices. Classical Pick FAIL.
-/

/-- Open lattice point on a non-adjacent fan chord from `v₀` is parent-interior. -/
theorem mem_interiorLatticePoints_of_strict_mem_fan_chord
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (k : Fin P.nVertices)
    (hk : 2 ≤ k.val ∧ k.val + 1 < P.nVertices)
    {p : ℤ × ℤ}
    (hp : p ∈ edgeLatticePoints (P.vertex ⟨0, P.nVertices_pos⟩) (P.vertex k))
    (hp0 : p ≠ P.vertex ⟨0, P.nVertices_pos⟩)
    (hpk : p ≠ P.vertex k) :
    p ∈ P.interiorLatticePoints := by
  classical
  set v0 : ℤ × ℤ := P.vertex ⟨0, P.nVertices_pos⟩
  set vk : ℤ × ℤ := P.vertex k
  have hext := VerticesExtreme_of_strictlyConvexCCW P hsc hinj
  have hseg := mem_segment_of_mem_edgeLatticePoints v0 vk p hp
  have ⟨t, ht, hp_eq⟩ : ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧
      (1 - t) • toReal v0 + t • toReal vk = toReal p := by
    simpa [segment_eq_image] using hseg
  have ht0 := ht.1
  have ht1 := ht.2
  have ht_pos : 0 < t := by
    by_contra h
    have ht' : t = 0 := le_antisymm (le_of_not_gt h) ht0
    have : toReal p = toReal v0 := by simpa [ht'] using hp_eq.symm
    exact hp0 (toReal_injective this)
  have ht_lt : t < 1 := by
    by_contra h
    have ht' : t = 1 := le_antisymm ht1 (le_of_not_gt h)
    have : toReal p = toReal vk := by simpa [ht'] using hp_eq.symm
    exact hpk (toReal_injective this)
  have hv0S : toReal v0 ∈ toReal '' (P.vertexFinset : Set (ℤ × ℤ)) := by
    refine ⟨v0, ?_, rfl⟩
    rw [vertexFinset_eq_univ_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hvkS : toReal vk ∈ toReal '' (P.vertexFinset : Set (ℤ × ℤ)) := by
    refine ⟨vk, ?_, rfl⟩
    rw [vertexFinset_eq_univ_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hseg_sub :
      segment ℝ (toReal v0) (toReal vk) ⊆
        convexHull ℝ (toReal '' (P.vertexFinset : Set (ℤ × ℤ))) :=
    (convex_convexHull ℝ _).segment_subset
      (subset_convexHull _ _ hv0S) (subset_convexHull _ _ hvkS)
  have hhull : toReal p ∈ P.convexHullRegion := by
    simpa [LatticePolygon.convexHullRegion] using hseg_sub hseg
  have hnb : p ∉ P.boundaryLatticePoints := by
    intro hb
    obtain ⟨j, hj⟩ := (mem_boundaryLatticePoints_iff P p).mp hb
    set A := P.vertex j
    set B := P.vertex (P.nextIdx j)
    have hp_edge : p ∈ edgeLatticePoints A B := by
      simpa [LatticePolygon.edgePair, A, B] using hj
    have hdet_p : latticeDet A B p = 0 :=
      latticeDet_eq_zero_of_mem_edge_ab A B p hp_edge
    have hnn0 : 0 ≤ latticeDet A B v0 := by
      simpa [A, B, v0] using hsc.1 j ⟨0, P.nVertices_pos⟩
    have hnnk : 0 ≤ latticeDet A B vk := by
      simpa [A, B, vk] using hsc.1 j k
    have hform :
        (latticeDet A B p : ℝ) =
          (1 - t) * (latticeDet A B v0 : ℝ) + t * (latticeDet A B vk : ℝ) := by
      have h0 :
          detR (toReal A) (toReal B) (toReal p) =
            (1 - t) * detR (toReal A) (toReal B) (toReal v0) +
              t * detR (toReal A) (toReal B) (toReal vk) := by
        have := detR_segment (toReal A) (toReal B) (toReal v0) (toReal vk) t
        simpa [← hp_eq] using this
      simpa [detR_toReal] using h0
    have hsum0 :
        (1 - t) * (latticeDet A B v0 : ℝ) + t * (latticeDet A B vk : ℝ) = 0 := by
      have : (latticeDet A B p : ℝ) = 0 := by exact_mod_cast hdet_p
      linarith [hform]
    have h0R : (0 : ℝ) ≤ (latticeDet A B v0 : ℝ) := by exact_mod_cast hnn0
    have hkR : (0 : ℝ) ≤ (latticeDet A B vk : ℝ) := by exact_mod_cast hnnk
    have ht0' : 0 ≤ 1 - t := by linarith
    have hm0 : (1 - t) * (latticeDet A B v0 : ℝ) = 0 := by
      nlinarith [hsum0, mul_nonneg ht0' h0R, mul_nonneg (le_of_lt ht_pos) hkR]
    have hmk : t * (latticeDet A B vk : ℝ) = 0 := by
      nlinarith [hsum0, mul_nonneg ht0' h0R, mul_nonneg (le_of_lt ht_pos) hkR]
    have hdet0 : latticeDet A B v0 = 0 := by
      have : (latticeDet A B v0 : ℝ) = 0 :=
        (mul_eq_zero.mp hm0).resolve_left (ne_of_gt (show 0 < 1 - t by linarith))
      exact_mod_cast this
    have hdetk : latticeDet A B vk = 0 := by
      have : (latticeDet A B vk : ℝ) = 0 :=
        (mul_eq_zero.mp hmk).resolve_left (ne_of_gt ht_pos)
      exact_mod_cast this
    have hj_ne_next : j ≠ P.nextIdx j := Ne.symm (nextIdx_ne P j)
    have h0_ne_k : (⟨0, P.nVertices_pos⟩ : Fin P.nVertices) ≠ k := by
      intro h; exact (by omega : (0 : ℕ) ≠ k.val) (congrArg Fin.val h)
    -- Always get three distinct collinear vertices among {j, nextIdx j, 0, k}
    by_cases h0_eq_j : (⟨0, P.nVertices_pos⟩ : Fin P.nVertices) = j
    · have hnext0 : P.nextIdx j = ⟨1, by have := P.length_ge; omega⟩ := by
        have hj0 : j = ⟨0, P.nVertices_pos⟩ := h0_eq_j.symm
        subst hj0
        apply Fin.ext
        simp [LatticePolygon.nextIdx]
        exact Nat.mod_eq_of_lt (by have := P.length_ge; omega)
      have h1_ne_k : (⟨1, by have := P.length_ge; omega⟩ : Fin P.nVertices) ≠ k := by
        intro h; exact (by omega : (1 : ℕ) ≠ k.val) (congrArg Fin.val h)
      have h01 : (⟨0, P.nVertices_pos⟩ : Fin P.nVertices) ≠
          ⟨1, by have := P.length_ge; omega⟩ := by
        intro h; exact (by decide : (0 : ℕ) ≠ 1) (congrArg Fin.val h)
      refine not_collinear_of_VerticesExtreme P hext hinj
        ⟨0, P.nVertices_pos⟩ ⟨1, by have := P.length_ge; omega⟩ k h01 h0_ne_k h1_ne_k ?_
      simpa [A, B, v0, vk, h0_eq_j, hnext0] using hdetk
    · by_cases h0_eq_n : (⟨0, P.nVertices_pos⟩ : Fin P.nVertices) = P.nextIdx j
      · have hj_last : j.val = P.nVertices - 1 := by
          have hnext : (j.val + 1) % P.nVertices = 0 := by
            simpa [LatticePolygon.nextIdx] using congrArg Fin.val h0_eq_n.symm
          have hlt : j.val + 1 ≤ P.nVertices := Nat.succ_le_of_lt j.isLt
          have hne0 : j.val + 1 ≠ 0 := Nat.succ_ne_zero _
          -- If j.val+1 < n then mod = j.val+1 ≠ 0
          by_cases hlt' : j.val + 1 < P.nVertices
          · have : (j.val + 1) % P.nVertices = j.val + 1 := Nat.mod_eq_of_lt hlt'
            omega
          · have : j.val + 1 = P.nVertices := le_antisymm hlt (Nat.le_of_not_gt hlt')
            omega
        have hj_ne_k : j ≠ k := by
          intro h
          have : j.val = k.val := congrArg Fin.val h
          have : k.val + 1 < P.nVertices := hk.2
          omega
        refine not_collinear_of_VerticesExtreme P hext hinj j ⟨0, P.nVertices_pos⟩ k
          (Ne.symm h0_eq_j) hj_ne_k h0_ne_k ?_
        · have hB0 : B = v0 := by simp [B, v0, h0_eq_n]
          simpa [A, hB0, v0, vk] using hdetk
      · exact not_collinear_of_VerticesExtreme P hext hinj j (P.nextIdx j)
          ⟨0, P.nVertices_pos⟩ hj_ne_next (Ne.symm h0_eq_j) (Ne.symm h0_eq_n) hdet0
  exact ⟨hhull, hnb⟩

/-- Fan chord `(v₀, vₖ)` is primitive under EmptyInterior (`2 ≤ k ≤ n-2`). -/
theorem edgeGcd_eq_one_of_empty_interior_fan_chord
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hI : EmptyInterior P)
    (k : Fin P.nVertices)
    (hk : 2 ≤ k.val ∧ k.val + 1 < P.nVertices) :
    edgeGcd (P.vertex ⟨0, P.nVertices_pos⟩) (P.vertex k) = 1 := by
  classical
  set v0 := P.vertex ⟨0, P.nVertices_pos⟩
  set vk := P.vertex k
  by_contra hne
  have hne0 : edgeGcd v0 vk ≠ 0 := by
    intro h0
    have : v0 = vk := (edgeGcd_eq_zero_iff v0 vk).mp h0
    exact (by omega : (0 : ℕ) ≠ k.val) (congrArg Fin.val (hinj this))
  have hge : 2 ≤ edgeGcd v0 vk := by omega
  obtain ⟨p, hp, hp0, hpk⟩ :=
    exists_strict_mem_edgeLatticePoints_of_edgeGcd_ge_two v0 vk hge
  have hint :=
    mem_interiorLatticePoints_of_strict_mem_fan_chord P hsc hinj k hk hp hp0 hpk
  have hEmpty : P.interiorLatticePoints = ∅ := hI
  exact (hEmpty ▸ hint).elim






/-! ## Empty-interior parent shoelace without PrimitiveEdges (not classical Pick)

Vertex fan from `v₀` + empty PE-free triangles + chord `edgeGcd = 1` + `B = ∑ edgeGcd`
telescoping: `∑ᵢ B(earᵢ) = B + 2(n−3)`, hence `∑(Bᵢ/2−1) = B/2−1`, and with
`shoelace_eq_sum_fan_shoelace` the empty StrictlyConvexCCW parent has
`shoelace = B/2 − 1` without `PrimitiveEdges`. Classical Pick FAIL.
-/

/-- Fan ear empty-interior Pick-form (feeds PE-free empty parent). -/
theorem shoelace_fanTriangle_eq_B_div_two_sub_one_of_empty
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hI : EmptyInterior P)
    (i : ℕ) (hi : i < P.nVertices - 2) :
    (fanTriangle P i hi).shoelace =
      ((trianglePolygon (fanTriangle P i hi).a (fanTriangle P i hi).b
          (fanTriangle P i hi).c).B : ℚ) / 2 - 1 := by
  set a := (fanTriangle P i hi).a
  set b := (fanTriangle P i hi).b
  set c := (fanTriangle P i hi).c
  have hpos := FanDetsPos_of_strictlyConvexCCW P hsc hinj
  have hD : 0 < latticeDet a b c := by
    simpa [a, b, c, fanDet, fanTriangle, Triangle.det] using hpos i hi
  have hIe := EmptyInterior_trianglePolygon_fanTriangle P hsc hinj hI i hi
  have hpick :=
    shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle a b c hD
      (by simpa [a, b, c] using hIe)
  have hT : (fanTriangle P i hi).shoelace = (trianglePolygon a b c).shoelace := by
    simp [Triangle.shoelace, a, b, c, fanTriangle,
      shoelace_trianglePolygon_eq_half_natAbs_det, triangleShoelace]
  simpa [hT, a, b, c] using hpick

/-- Fan-ear triangle `B` as sum of its three edge gcds (no PE). -/
theorem B_fanTriangle_eq_sum_edgeGcd
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (i : ℕ) (hi : i < P.nVertices - 2) :
    (trianglePolygon (fanTriangle P i hi).a (fanTriangle P i hi).b
        (fanTriangle P i hi).c).B =
      edgeGcd (fanTriangle P i hi).a (fanTriangle P i hi).b +
        edgeGcd (fanTriangle P i hi).b (fanTriangle P i hi).c +
          edgeGcd (fanTriangle P i hi).c (fanTriangle P i hi).a := by
  have hpos := FanDetsPos_of_strictlyConvexCCW P hsc hinj
  have hD : latticeDet (fanTriangle P i hi).a (fanTriangle P i hi).b
      (fanTriangle P i hi).c ≠ 0 :=
    ne_of_gt (by simpa [fanDet, fanTriangle, Triangle.det] using hpos i hi)
  exact B_trianglePolygon_eq_sum_edgeGcd _ _ _ hD

/-- Pure ℕ telescope used by fan-ear B bookkeeping. -/
private lemma sum_spoke_base_spoke_telescope
    (n : ℕ) (hn : 3 ≤ n) (spoke : ℕ → ℕ) (base : ℕ → ℕ)
    (hspoke : ∀ k, 2 ≤ k → k ≤ n - 2 → spoke k = 1) :
    (∑ i ∈ Finset.range (n - 2), (spoke (i + 1) + base (i + 1) + spoke (i + 2))) =
      spoke 1 + (∑ i ∈ Finset.range (n - 2), base (i + 1)) + spoke (n - 1) +
        2 * (n - 3) := by
  classical
  have hlen : n - 2 = n - 3 + 1 := by omega
  have hone_mid : ∀ i ∈ Finset.range (n - 3), spoke (i + 2) = 1 := by
    intro i hi
    have hi' : i < n - 3 := Finset.mem_range.mp hi
    exact hspoke (i + 2) (by omega) (by omega)
  have hsum_ones : (∑ i ∈ Finset.range (n - 3), spoke (i + 2)) = n - 3 := by
    refine Eq.trans (Finset.sum_congr rfl hone_mid) ?_
    simp [Finset.sum_const, Finset.card_range]
  have hsplit :
      (∑ i ∈ Finset.range (n - 2), (spoke (i + 1) + base (i + 1) + spoke (i + 2))) =
        (∑ i ∈ Finset.range (n - 2), spoke (i + 1)) +
          (∑ i ∈ Finset.range (n - 2), base (i + 1)) +
            (∑ i ∈ Finset.range (n - 2), spoke (i + 2)) := by
    simp_rw [add_assoc]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hleft :
      (∑ i ∈ Finset.range (n - 2), spoke (i + 1)) = spoke 1 + (n - 3) := by
    rw [hlen]
    -- sum_range_succ' : ∑ range (m+1) f = ∑ range m (f∘succ) + f 0
    rw [Finset.sum_range_succ' (fun i => spoke (i + 1)) (n - 3)]
    change (∑ i ∈ Finset.range (n - 3), spoke (i + 1 + 1)) + spoke (0 + 1) =
      spoke 1 + (n - 3)
    simp only [Nat.add_assoc, Nat.zero_add]
    -- spoke (i+2) sum
    change (∑ i ∈ Finset.range (n - 3), spoke (i + 2)) + spoke 1 = spoke 1 + (n - 3)
    rw [hsum_ones, add_comm]
  have hright :
      (∑ i ∈ Finset.range (n - 2), spoke (i + 2)) =
        (n - 3) + spoke (n - 1) := by
    rw [hlen]
    rw [Finset.sum_range_succ (fun i => spoke (i + 2)) (n - 3)]
    change (∑ i ∈ Finset.range (n - 3), spoke (i + 2)) + spoke (n - 3 + 2) =
      (n - 3) + spoke (n - 1)
    rw [hsum_ones]
    congr 2
    omega
  rw [hsplit, hleft, hright]
  ring

private lemma nVertices_ge_three : 3 ≤ P.nVertices := by
  simpa [LatticePolygon.nVertices] using P.length_ge

private lemma nextIdx_ofNat_lt
    (k : ℕ) (hk : k + 1 < P.nVertices) :
    P.nextIdx ⟨k, Nat.lt_of_succ_lt hk⟩ = ⟨k + 1, hk⟩ :=
  Fin.ext (Nat.mod_eq_of_lt hk)

private lemma nextIdx_last_eq_zero :
    P.nextIdx ⟨P.nVertices - 1, Nat.sub_lt P.nVertices_pos (Nat.succ_pos 0)⟩ =
      ⟨0, P.nVertices_pos⟩ := by
  apply Fin.ext
  have hpos : 0 < P.nVertices := P.nVertices_pos
  have : P.nVertices - 1 + 1 = P.nVertices :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
  change (P.nVertices - 1 + 1) % P.nVertices = 0
  rw [this, Nat.mod_self]

/-- **B-telescope**: `∑ᵢ B(earᵢ) = B(P) + 2(n−3)` under EmptyInterior.
Audit name `sum_B_fan_ears_eq_B_add_two_mul_n_sub_three`. -/
theorem sum_B_fan_ears_eq_B_add_two_mul_n_sub_three
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hI : EmptyInterior P) :
    (∑ i : Fin (P.nVertices - 2),
        (trianglePolygon (fanTriangle P i.val i.isLt).a
          (fanTriangle P i.val i.isLt).b
          (fanTriangle P i.val i.isLt).c).B) =
      P.B + 2 * (P.nVertices - 3) := by
  classical
  have hn := nVertices_ge_three (P := P)
  set n := P.nVertices with hn_def
  -- Boundary edge gcd function
  let bound : ℕ → ℕ := fun k =>
    if h : k < n then
      edgeGcd (P.vertex ⟨k, h⟩) (P.vertex (P.nextIdx ⟨k, h⟩)) else 0
  -- Spoke gcd from v0 to vk
  let spoke : ℕ → ℕ := fun k =>
    if h : k < n then
      edgeGcd (P.vertex ⟨0, P.nVertices_pos⟩) (P.vertex ⟨k, h⟩) else 0
  have hspoke_one : ∀ k, 2 ≤ k → k ≤ n - 2 → spoke k = 1 := by
    intro k hk2 hk_le
    have hk_lt : k < n := by omega
    have hk_succ : k + 1 < n := by omega
    simp only [spoke, dif_pos hk_lt]
    exact edgeGcd_eq_one_of_empty_interior_fan_chord P hsc hinj hI
      ⟨k, hk_lt⟩ ⟨hk2, hk_succ⟩
  have hBear : ∀ i : Fin (n - 2),
      (trianglePolygon (fanTriangle P i.val i.isLt).a
          (fanTriangle P i.val i.isLt).b
          (fanTriangle P i.val i.isLt).c).B =
        spoke (i.val + 1) + bound (i.val + 1) + spoke (i.val + 2) := by
    intro i
    have hi : i.val < n - 2 := by simpa [n] using i.isLt
    have h1 : i.val + 1 < n := by omega
    have h2 : i.val + 2 < n := by omega
    have hB := B_fanTriangle_eq_sum_edgeGcd P hsc hinj i.val (by simpa [n] using hi)
    have hnext : P.nextIdx ⟨i.val + 1, h1⟩ = ⟨i.val + 2, h2⟩ :=
      nextIdx_ofNat_lt P (i.val + 1) h2
    -- fanTriangle edges: (v0,v_{i+1}), (v_{i+1},v_{i+2}), (v_{i+2},v0)
    simp only [fanTriangle, spoke, bound, dif_pos h1, dif_pos h2, hnext,
      edgeGcd_comm (P.vertex ⟨i.val + 2, h2⟩) (P.vertex ⟨0, P.nVertices_pos⟩)] at hB ⊢
    -- Need to match edgeGcd c a with spoke (i+2) via edgeGcd_comm
    simpa [fanTriangle, n] using hB
  -- Actually rewrite more carefully
  clear hBear
  have hBear : ∀ i : Fin (n - 2),
      (trianglePolygon (fanTriangle P i.val i.isLt).a
          (fanTriangle P i.val i.isLt).b
          (fanTriangle P i.val i.isLt).c).B =
        spoke (i.val + 1) + bound (i.val + 1) + spoke (i.val + 2) := by
    intro i
    have hi : i.val < n - 2 := by simpa [n] using i.isLt
    have h1 : i.val + 1 < n := by omega
    have h2 : i.val + 2 < n := by omega
    have hB := B_fanTriangle_eq_sum_edgeGcd P hsc hinj i.val (by simpa [n] using hi)
    have hnext : P.nextIdx ⟨i.val + 1, Nat.lt_of_succ_lt h2⟩ = ⟨i.val + 2, h2⟩ :=
      nextIdx_ofNat_lt P (i.val + 1) h2
    have hs1 : spoke (i.val + 1) =
        edgeGcd (P.vertex ⟨0, P.nVertices_pos⟩) (P.vertex ⟨i.val + 1, h1⟩) := by
      simp [spoke, dif_pos h1]
    have hs2 : spoke (i.val + 2) =
        edgeGcd (P.vertex ⟨0, P.nVertices_pos⟩) (P.vertex ⟨i.val + 2, h2⟩) := by
      simp [spoke, dif_pos h2]
    have hb : bound (i.val + 1) =
        edgeGcd (P.vertex ⟨i.val + 1, h1⟩) (P.vertex ⟨i.val + 2, h2⟩) := by
      simp [bound, dif_pos h1, hnext]
    have hca : edgeGcd (P.vertex ⟨i.val + 2, h2⟩) (P.vertex ⟨0, P.nVertices_pos⟩) =
        spoke (i.val + 2) := by
      rw [hs2, edgeGcd_comm]
    -- fanTriangle a,b,c = v0, v_{i+1}, v_{i+2}
    change (trianglePolygon (P.vertex ⟨0, P.nVertices_pos⟩)
        (P.vertex ⟨i.val + 1, by omega⟩)
        (P.vertex ⟨i.val + 2, by omega⟩)).B =
      spoke (i.val + 1) + bound (i.val + 1) + spoke (i.val + 2)
    have hB' :
        (trianglePolygon (P.vertex ⟨0, P.nVertices_pos⟩)
            (P.vertex ⟨i.val + 1, by omega⟩)
            (P.vertex ⟨i.val + 2, by omega⟩)).B =
          edgeGcd (P.vertex ⟨0, P.nVertices_pos⟩) (P.vertex ⟨i.val + 1, by omega⟩) +
            edgeGcd (P.vertex ⟨i.val + 1, by omega⟩) (P.vertex ⟨i.val + 2, by omega⟩) +
              edgeGcd (P.vertex ⟨i.val + 2, by omega⟩) (P.vertex ⟨0, P.nVertices_pos⟩) := by
      simpa [fanTriangle, n] using hB
    rw [hB', hs1, hb, hca]
  have hsum_ears :
      (∑ i : Fin (n - 2),
          (trianglePolygon (fanTriangle P i.val i.isLt).a
            (fanTriangle P i.val i.isLt).b
            (fanTriangle P i.val i.isLt).c).B) =
        ∑ i ∈ Finset.range (n - 2),
          (spoke (i + 1) + bound (i + 1) + spoke (i + 2)) := by
    simp_rw [hBear]
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < n - 2 := Finset.mem_range.mp hk
    simp [hk']
  have htel :=
    sum_spoke_base_spoke_telescope n hn spoke (fun k => bound k) hspoke_one
  -- bound (i+1) in telescope matches
  have htel' :
      (∑ i ∈ Finset.range (n - 2), (spoke (i + 1) + bound (i + 1) + spoke (i + 2))) =
        spoke 1 + (∑ i ∈ Finset.range (n - 2), bound (i + 1)) + spoke (n - 1) +
          2 * (n - 3) := htel
  -- Identify B(P) with spoke 1 + ∑ bound(i+1) + spoke(n-1)
  have hB := B_eq_sum_edgeGcd P hsc hinj
  have hB_expand :
      P.B = spoke 1 + (∑ i ∈ Finset.range (n - 2), bound (i + 1)) + spoke (n - 1) := by
    let f : ℕ → ℕ := fun k =>
      if h : k < n then
        edgeGcd (P.vertex ⟨k, h⟩) (P.vertex (P.nextIdx ⟨k, h⟩)) else 0
    have hf_bound : ∀ k, f k = bound k := fun k => rfl
    have hfin :
        (∑ i : Fin n, edgeGcd (P.vertex i) (P.vertex (P.nextIdx i))) =
          ∑ k ∈ Finset.range n, f k := by
      refine Eq.trans (Finset.sum_fin_eq_sum_range
        (fun i : Fin n => edgeGcd (P.vertex i) (P.vertex (P.nextIdx i)))) ?_
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < n := Finset.mem_range.mp hk
      simp [f, hk']
    have hsucc0 :
        ∑ k ∈ Finset.range n, f k =
          f 0 + ∑ k ∈ Finset.range (n - 1), f (k + 1) := by
      have hlen : n = (n - 1) + 1 := by omega
      rw [hlen]
      simpa [add_comm] using Finset.sum_range_succ' f (n - 1)
    have hsuccL :
        ∑ k ∈ Finset.range (n - 1), f (k + 1) =
          (∑ k ∈ Finset.range (n - 2), f (k + 1)) + f (n - 1) := by
      have hlen2 : n - 1 = n - 2 + 1 := by
        have : 1 ≤ n := by omega
        omega
      rw [hlen2]
      simpa using Finset.sum_range_succ (fun k => f (k + 1)) (n - 2)
    have hf0 : f 0 = spoke 1 := by
      have h0 : (0 : ℕ) < n := by omega
      have h1 : (1 : ℕ) < n := by omega
      simp only [f, dif_pos h0, spoke, dif_pos h1]
      rw [nextIdx_ofNat_lt P 0 (by omega)]
    have hfL : f (n - 1) = spoke (n - 1) := by
      have hlt : n - 1 < n := Nat.sub_lt P.nVertices_pos (Nat.succ_pos 0)
      simp only [f, dif_pos hlt, spoke, dif_pos hlt]
      have hnext := nextIdx_last_eq_zero (P := P)
      have : P.nextIdx ⟨n - 1, hlt⟩ = ⟨0, P.nVertices_pos⟩ := hnext
      rw [this, edgeGcd_comm]
    have hmid :
        (∑ k ∈ Finset.range (n - 2), f (k + 1)) =
          ∑ i ∈ Finset.range (n - 2), bound (i + 1) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rfl
    calc
      P.B = ∑ i : Fin n, edgeGcd (P.vertex i) (P.vertex (P.nextIdx i)) := by
            simpa [n] using hB
      _ = ∑ k ∈ Finset.range n, f k := hfin
      _ = f 0 + ∑ k ∈ Finset.range (n - 1), f (k + 1) := hsucc0
      _ = f 0 + ((∑ k ∈ Finset.range (n - 2), f (k + 1)) + f (n - 1)) := by
            rw [hsuccL]
      _ = spoke 1 + (∑ i ∈ Finset.range (n - 2), bound (i + 1)) + spoke (n - 1) := by
            rw [hf0, hfL, hmid]; abel
  calc
    (∑ i : Fin (n - 2),
        (trianglePolygon (fanTriangle P i.val i.isLt).a
          (fanTriangle P i.val i.isLt).b
          (fanTriangle P i.val i.isLt).c).B)
        = ∑ i ∈ Finset.range (n - 2),
            (spoke (i + 1) + bound (i + 1) + spoke (i + 2)) := hsum_ears
    _ = spoke 1 + (∑ i ∈ Finset.range (n - 2), bound (i + 1)) + spoke (n - 1) +
          2 * (n - 3) := htel'
    _ = P.B + 2 * (n - 3) := by rw [← hB_expand]

/-- From B-telescope: `∑(Bᵢ/2 − 1) = B/2 − 1`. -/
theorem sum_B_div_two_sub_one_fan_ears_eq_B_div_two_sub_one
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hI : EmptyInterior P) :
    (∑ i : Fin (P.nVertices - 2),
        (((trianglePolygon (fanTriangle P i.val i.isLt).a
            (fanTriangle P i.val i.isLt).b
            (fanTriangle P i.val i.isLt).c).B : ℚ) / 2 - 1)) =
      (P.B : ℚ) / 2 - 1 := by
  classical
  have hn := nVertices_ge_three (P := P)
  set n := P.nVertices
  have htel := sum_B_fan_ears_eq_B_add_two_mul_n_sub_three P hsc hinj hI
  have hcard : (Fintype.card (Fin (n - 2)) : ℚ) = (n - 2 : ℕ) := by
    simp [Fintype.card_fin]
  have hn2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := Nat.cast_sub (by omega : 2 ≤ n)
  have hn3 : ((n - 3 : ℕ) : ℚ) = (n : ℚ) - 3 := Nat.cast_sub (by omega : 3 ≤ n)
  have hsumB :
      (∑ i : Fin (n - 2),
          ((trianglePolygon (fanTriangle P i.val i.isLt).a
              (fanTriangle P i.val i.isLt).b
              (fanTriangle P i.val i.isLt).c).B : ℚ)) =
        (P.B : ℚ) + 2 * ((n - 3 : ℕ) : ℚ) := by
    have := congrArg (fun m : ℕ => (m : ℚ)) (by simpa [n] using htel)
    simpa [Nat.cast_sum, Nat.cast_add, Nat.cast_mul] using this
  calc
    (∑ i : Fin (n - 2),
        (((trianglePolygon (fanTriangle P i.val i.isLt).a
            (fanTriangle P i.val i.isLt).b
            (fanTriangle P i.val i.isLt).c).B : ℚ) / 2 - 1))
        = (∑ i : Fin (n - 2),
            ((trianglePolygon (fanTriangle P i.val i.isLt).a
                (fanTriangle P i.val i.isLt).b
                (fanTriangle P i.val i.isLt).c).B : ℚ) / 2) -
          ∑ _i : Fin (n - 2), (1 : ℚ) := by
          simp [Finset.sum_sub_distrib]
    _ = (∑ i : Fin (n - 2),
            ((trianglePolygon (fanTriangle P i.val i.isLt).a
                (fanTriangle P i.val i.isLt).b
                (fanTriangle P i.val i.isLt).c).B : ℚ)) / 2 -
          (n - 2 : ℕ) := by
          rw [← Finset.sum_div]
          simp [Finset.card_univ, hcard]
    _ = ((P.B : ℚ) + 2 * ((n - 3 : ℕ) : ℚ)) / 2 - ((n - 2 : ℕ) : ℚ) := by
          rw [hsumB]
    _ = (P.B : ℚ) / 2 - 1 := by
          rw [hn2, hn3]; ring

theorem shoelace_eq_B_div_two_sub_one_of_empty_interior_no_pe
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hI : EmptyInterior P) :
    P.shoelace = (P.B : ℚ) / 2 - 1 := by
  classical
  have hn := nVertices_ge_three (P := P)
  set n := P.nVertices
  have hnn := FanDetsNonneg_of_pos P (FanDetsPos_of_strictlyConvexCCW P hsc hinj)
  have hadd := shoelace_eq_sum_fan_shoelace P hnn hinj
  have hre :
      ∑ t ∈ fanTriangles P, t.shoelace =
        ∑ i : Fin (n - 2), (fanTriangle P i.val i.isLt).shoelace := by
    dsimp [fanTriangles]
    have hinjImg : Function.Injective
        (fun i : { x // x ∈ Finset.range (n - 2) } =>
          fanTriangle P i.1 (Finset.mem_range.mp i.2)) := fun a b h =>
      Subtype.ext (fanTriangle_eq_of_eq P (Finset.mem_range.mp a.2)
        (Finset.mem_range.mp b.2) hinj h)
    rw [Finset.sum_image (fun _ _ _ _ h => hinjImg h)]
    let e : Fin (n - 2) ≃ { x // x ∈ Finset.range (n - 2) } :=
      { toFun := fun i => ⟨i.val, Finset.mem_range.mpr i.isLt⟩
        invFun := fun ⟨i, hi⟩ => ⟨i, Finset.mem_range.mp hi⟩
        left_inv := fun _ => Fin.ext rfl
        right_inv := fun _ => rfl }
    exact (Fintype.sum_equiv e
      (fun i => (fanTriangle P i.val i.isLt).shoelace)
      (fun i => (fanTriangle P i.1 (Finset.mem_range.mp i.2)).shoelace)
      (fun _ => rfl)).symm
  have hear : ∀ i : Fin (n - 2),
      (fanTriangle P i.val i.isLt).shoelace =
        ((trianglePolygon (fanTriangle P i.val i.isLt).a
          (fanTriangle P i.val i.isLt).b
          (fanTriangle P i.val i.isLt).c).B : ℚ) / 2 - 1 :=
    fun i => shoelace_fanTriangle_eq_B_div_two_sub_one_of_empty P hsc hinj hI i.val
      (by simpa [n] using i.isLt)
  have hsumB := sum_B_div_two_sub_one_fan_ears_eq_B_div_two_sub_one P hsc hinj hI
  calc
    P.shoelace = ∑ t ∈ fanTriangles P, t.shoelace := hadd
    _ = ∑ i : Fin (n - 2), (fanTriangle P i.val i.isLt).shoelace := hre
    _ = ∑ i : Fin (n - 2),
          (((trianglePolygon (fanTriangle P i.val i.isLt).a
            (fanTriangle P i.val i.isLt).b
            (fanTriangle P i.val i.isLt).c).B : ℚ) / 2 - 1) := by
          simp_rw [hear]
    _ = (P.B : ℚ) / 2 - 1 := by simpa [n] using hsumB

end InteriorFan
end LatticeFan
end Picks
end EulersGem
