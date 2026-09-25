/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.LatticeFanInterior

/-!
# Ear-uniqueness under OffTriangleBoundary (not classical Pick)

Plücker identity, segment ↔ `edgeLatticePoints`, then area-weight signs and
cone-disjointness uniqueness of an Off occupied ear from any interior apex.
Specializes to I = 2 (`TwoInterior`) and discharges I = 3 uniqueness hyps.
-/

namespace EulersGem
namespace Picks
namespace LatticeFan
namespace InteriorFan

open LatticeTriangle
open LatticePolygon

variable (P : LatticePolygon)

lemma latticeDet_plucker (q a b c r : ℤ × ℤ) :
    latticeDet q a b * latticeDet q c r
      - latticeDet q a c * latticeDet q b r
      + latticeDet q a r * latticeDet q b c = 0 := by
  simp only [latticeDet]; ring

lemma mem_edgeLatticePoints_of_mem_segment
    (a b p : ℤ × ℤ)
    (h : toReal p ∈ segment ℝ (toReal a) (toReal b)) :
    p ∈ edgeLatticePoints a b := by
  classical
  by_cases hd0 : edgeGcd a b = 0
  · have hab : a = b := (edgeGcd_eq_zero_iff a b).mp hd0
    have hp : toReal p = toReal a := by simpa [hab, segment_same] using h
    have : p = a := toReal_injective hp
    simp [edgeLatticePoints, hd0, this]
  · set d := edgeGcd a b with hd_def
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    rcases h with ⟨sa, sb, hsa, hsb, hsab, hr⟩
    have hr' : toReal p = toReal a + sb • (toReal b - toReal a) := by
      have hsb_split :
          sb • toReal b = sb • toReal a + sb • (toReal b - toReal a) := by
        rw [← smul_add, add_sub_cancel]
      calc
        toReal p = sa • toReal a + sb • toReal b := hr.symm
        _ = sa • toReal a + (sb • toReal a + sb • (toReal b - toReal a)) := by
              rw [hsb_split]
        _ = (sa + sb) • toReal a + sb • (toReal b - toReal a) := by
              rw [add_smul]; abel
        _ = toReal a + sb • (toReal b - toReal a) := by
              rw [hsab, one_smul]
    have hx : ((p.1 - a.1 : ℤ) : ℝ) = sb * ((b.1 - a.1 : ℤ) : ℝ) := by
      have hfst := congrArg Prod.fst hr'
      change (p.1 : ℝ) = (a.1 : ℝ) + sb * ((b.1 : ℝ) - (a.1 : ℝ)) at hfst
      have : (p.1 : ℝ) - (a.1 : ℝ) = sb * ((b.1 : ℝ) - (a.1 : ℝ)) := by linarith
      simpa [Int.cast_sub] using this
    have hy : ((p.2 - a.2 : ℤ) : ℝ) = sb * ((b.2 - a.2 : ℤ) : ℝ) := by
      have hsnd := congrArg Prod.snd hr'
      change (p.2 : ℝ) = (a.2 : ℝ) + sb * ((b.2 : ℝ) - (a.2 : ℝ)) at hsnd
      have : (p.2 : ℝ) - (a.2 : ℝ) = sb * ((b.2 : ℝ) - (a.2 : ℝ)) := by linarith
      simpa [Int.cast_sub] using this
    set n : ℤ :=
      Int.gcdA (b.1 - a.1) (b.2 - a.2) * (p.1 - a.1) +
        Int.gcdB (b.1 - a.1) (b.2 - a.2) * (p.2 - a.2)
    have hbez : (d : ℝ) =
        ((b.1 - a.1 : ℤ) : ℝ) * (Int.gcdA (b.1 - a.1) (b.2 - a.2) : ℝ) +
          ((b.2 - a.2 : ℤ) : ℝ) * (Int.gcdB (b.1 - a.1) (b.2 - a.2) : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) (Int.gcd_eq_gcd_ab (b.1 - a.1) (b.2 - a.2))
      simpa [d, edgeGcd] using this
    have hsbd : sb * (d : ℝ) = (n : ℝ) := by
      have hexp :
          sb * (d : ℝ) =
            (Int.gcdA (b.1 - a.1) (b.2 - a.2) : ℝ) * ((p.1 - a.1 : ℤ) : ℝ) +
              (Int.gcdB (b.1 - a.1) (b.2 - a.2) : ℝ) * ((p.2 - a.2 : ℤ) : ℝ) := by
        calc
          sb * (d : ℝ)
              = sb *
                  (((b.1 - a.1 : ℤ) : ℝ) * (Int.gcdA (b.1 - a.1) (b.2 - a.2) : ℝ) +
                    ((b.2 - a.2 : ℤ) : ℝ) * (Int.gcdB (b.1 - a.1) (b.2 - a.2) : ℝ)) := by
                      rw [hbez]
          _ = (Int.gcdA (b.1 - a.1) (b.2 - a.2) : ℝ) * (sb * ((b.1 - a.1 : ℤ) : ℝ)) +
                (Int.gcdB (b.1 - a.1) (b.2 - a.2) : ℝ) * (sb * ((b.2 - a.2 : ℤ) : ℝ)) := by
                      ring
          _ = (Int.gcdA (b.1 - a.1) (b.2 - a.2) : ℝ) * ((p.1 - a.1 : ℤ) : ℝ) +
                (Int.gcdB (b.1 - a.1) (b.2 - a.2) : ℝ) * ((p.2 - a.2 : ℤ) : ℝ) := by
                      rw [hx, hy]
      have : (Int.gcdA (b.1 - a.1) (b.2 - a.2) : ℝ) * ((p.1 - a.1 : ℤ) : ℝ) +
            (Int.gcdB (b.1 - a.1) (b.2 - a.2) : ℝ) * ((p.2 - a.2 : ℤ) : ℝ) = (n : ℝ) := by
        dsimp [n]; push_cast; ring
      linarith
    have hn0 : (0 : ℤ) ≤ n := by
      have : (0 : ℝ) ≤ sb * (d : ℝ) :=
        mul_nonneg hsb (by exact_mod_cast (Nat.zero_le d))
      exact_mod_cast (by simpa [hsbd] using this : (0 : ℝ) ≤ (n : ℝ))
    have hn_le : n ≤ (d : ℤ) := by
      have hsb1 : sb ≤ (1 : ℝ) := by linarith [hsab, hsa]
      have : sb * (d : ℝ) ≤ (d : ℝ) := by nlinarith
      have : (n : ℝ) ≤ (d : ℝ) := by simpa [hsbd] using this
      exact_mod_cast this
    set k : ℕ := n.toNat
    have hk_eq : (k : ℤ) = n := Int.toNat_of_nonneg hn0
    have hk_le : k ≤ d := by
      have : (k : ℤ) ≤ (d : ℤ) := by simpa [hk_eq] using hn_le
      exact Nat.cast_le.mp this
    have hdx : (d : ℤ) ∣ (b.1 - a.1) := by
      simpa [edgeGcd, d] using Int.gcd_dvd_left (b.1 - a.1) (b.2 - a.2)
    have hdy : (d : ℤ) ∣ (b.2 - a.2) := by
      simpa [edgeGcd, d] using Int.gcd_dvd_right (b.1 - a.1) (b.2 - a.2)
    set sx : ℤ := (b.1 - a.1) / (d : ℤ)
    set sy : ℤ := (b.2 - a.2) / (d : ℤ)
    have hsx : sx * (d : ℤ) = b.1 - a.1 := by simpa [sx] using Int.ediv_mul_cancel hdx
    have hsy : sy * (d : ℤ) = b.2 - a.2 := by simpa [sy] using Int.ediv_mul_cancel hdy
    have hxZ : p.1 - a.1 = n * sx := by
      have : ((p.1 - a.1 : ℤ) : ℝ) = (n : ℝ) * (sx : ℝ) := by
        have hsxR : (sx : ℝ) * (d : ℝ) = ((b.1 - a.1 : ℤ) : ℝ) := by exact_mod_cast hsx
        calc
          ((p.1 - a.1 : ℤ) : ℝ) = sb * ((b.1 - a.1 : ℤ) : ℝ) := hx
          _ = sb * ((sx : ℝ) * (d : ℝ)) := by rw [← hsxR]
          _ = (sb * (d : ℝ)) * (sx : ℝ) := by ring
          _ = (n : ℝ) * (sx : ℝ) := by rw [hsbd]
      exact_mod_cast this
    have hyZ : p.2 - a.2 = n * sy := by
      have : ((p.2 - a.2 : ℤ) : ℝ) = (n : ℝ) * (sy : ℝ) := by
        have hsyR : (sy : ℝ) * (d : ℝ) = ((b.2 - a.2 : ℤ) : ℝ) := by exact_mod_cast hsy
        calc
          ((p.2 - a.2 : ℤ) : ℝ) = sb * ((b.2 - a.2 : ℤ) : ℝ) := hy
          _ = sb * ((sy : ℝ) * (d : ℝ)) := by rw [← hsyR]
          _ = (sb * (d : ℝ)) * (sy : ℝ) := by ring
          _ = (n : ℝ) * (sy : ℝ) := by rw [hsbd]
      exact_mod_cast this
    
    let f : ℕ → ℤ × ℤ := fun t =>
      (a.1 + (t : ℤ) * ((b.1 - a.1) / (d : ℤ)),
       a.2 + (t : ℤ) * ((b.2 - a.2) / (d : ℤ)))
    have hk_range : k ∈ Finset.range (d + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le)
    have hf : f k = p := by
      apply Prod.ext
      · have : p.1 = a.1 + n * sx := by linarith [hxZ]
        simp [f, sx, hk_eq, this]
      · have : p.2 = a.2 + n * sy := by linarith [hyZ]
        simp [f, sy, hk_eq, this]
    -- Conclude membership via constructive image.
    have hmem : p ∈
        (Finset.range (d + 1)).image fun t : ℕ =>
          (a.1 + (t : ℤ) * ((b.1 - a.1) / (d : ℤ)),
           a.2 + (t : ℤ) * ((b.2 - a.2) / (d : ℤ))) := by
      have : f = fun t : ℕ =>
          (a.1 + (t : ℤ) * ((b.1 - a.1) / (d : ℤ)),
           a.2 + (t : ℤ) * ((b.2 - a.2) / (d : ℤ))) := rfl
      rw [← this, ← hf]
      exact Finset.mem_image_of_mem f hk_range
    -- Match edgeLatticePoints definition under d ≠ 0.
    have hdef :
        edgeLatticePoints a b =
          (Finset.range (d + 1)).image fun t : ℕ =>
            (a.1 + (t : ℤ) * ((b.1 - a.1) / (d : ℤ)),
             a.2 + (t : ℤ) * ((b.2 - a.2) / (d : ℤ))) := by
      -- `edgeLatticePoints` is `let d' := edgeGcd a b; if d' = 0 then {a} else image ...`
      have hne : edgeGcd a b ≠ 0 := by simpa [hd_def] using hd0
      -- Evaluate the definition
      simp only [edgeLatticePoints]
      -- Now: let d' := edgeGcd a b; if ...
      -- Use `rw` after showing the let equals d
      change (let d' := edgeGcd a b;
          if d' = 0 then ({a} : Finset (ℤ × ℤ))
          else (Finset.range (d' + 1)).image fun t : ℕ =>
            (a.1 + (t : ℤ) * ((b.1 - a.1) / (d' : ℤ)),
             a.2 + (t : ℤ) * ((b.2 - a.2) / (d' : ℤ)))) =
        (Finset.range (d + 1)).image fun t : ℕ =>
          (a.1 + (t : ℤ) * ((b.1 - a.1) / (d : ℤ)),
           a.2 + (t : ℤ) * ((b.2 - a.2) / (d : ℤ)))
      have hd0' : ¬ d = 0 := by simpa [hd_def] using hd0
      rw [ite_eq_right (by simpa [hd_def] using hd0)]
    rwa [← hdef] at hmem


/-- Barycentric area-weight identities (third-argument affinity + swap). -/
lemma latticeDet_eq_bary_mul_of_affine
    (q v w p : ℤ × ℤ) (α β γ : ℝ)
    (hsum : α + β + γ = 1)
    (heq : α • toReal q + β • toReal v + γ • toReal w = toReal p) :
    (latticeDet v w p : ℝ) = α * (latticeDet q v w : ℝ) ∧
      (latticeDet q p w : ℝ) = β * (latticeDet q v w : ℝ) ∧
      (latticeDet q v p : ℝ) = γ * (latticeDet q v w : ℝ) := by
  have hα : (latticeDet v w p : ℝ) = α * (latticeDet q v w : ℝ) := by
    have haff :=
      detR_affine_combination3 (toReal v) (toReal w) (toReal q) (toReal v) (toReal w)
        α β γ hsum
    have : detR (toReal v) (toReal w) (toReal p) =
        α * detR (toReal v) (toReal w) (toReal q) := by
      have hz1 : detR (toReal v) (toReal w) (toReal v) = 0 := by simp [detR]
      have hz2 : detR (toReal v) (toReal w) (toReal w) = 0 := by simp [detR]; ring
      calc
        detR (toReal v) (toReal w) (toReal p)
            = detR (toReal v) (toReal w)
                (α • toReal q + β • toReal v + γ • toReal w) := by rw [← heq]
        _ = α * detR (toReal v) (toReal w) (toReal q) +
              β * detR (toReal v) (toReal w) (toReal v) +
                γ * detR (toReal v) (toReal w) (toReal w) := haff
        _ = α * detR (toReal v) (toReal w) (toReal q) := by simp [hz1, hz2]
    have hcyc : latticeDet v w q = latticeDet q v w := (latticeDet_cyclic q v w).symm
    simpa [detR_toReal, hcyc] using this
  have hγ : (latticeDet q v p : ℝ) = γ * (latticeDet q v w : ℝ) := by
    have haff :=
      detR_affine_combination3 (toReal q) (toReal v) (toReal q) (toReal v) (toReal w)
        α β γ hsum
    have : detR (toReal q) (toReal v) (toReal p) =
        γ * detR (toReal q) (toReal v) (toReal w) := by
      have hz1 : detR (toReal q) (toReal v) (toReal q) = 0 := by simp [detR]
      have hz2 : detR (toReal q) (toReal v) (toReal v) = 0 := by simp [detR]; ring
      calc
        detR (toReal q) (toReal v) (toReal p)
            = detR (toReal q) (toReal v)
                (α • toReal q + β • toReal v + γ • toReal w) := by rw [← heq]
        _ = α * detR (toReal q) (toReal v) (toReal q) +
              β * detR (toReal q) (toReal v) (toReal v) +
                γ * detR (toReal q) (toReal v) (toReal w) := haff
        _ = γ * detR (toReal q) (toReal v) (toReal w) := by simp [hz1, hz2]
    simpa [detR_toReal] using this
  have hβ : (latticeDet q p w : ℝ) = β * (latticeDet q v w : ℝ) := by
    have haff :=
      detR_affine_combination3 (toReal q) (toReal w) (toReal q) (toReal v) (toReal w)
        α β γ hsum
    have hqw : (latticeDet q w p : ℝ) = β * (latticeDet q w v : ℝ) := by
      have : detR (toReal q) (toReal w) (toReal p) =
          β * detR (toReal q) (toReal w) (toReal v) := by
        have hz1 : detR (toReal q) (toReal w) (toReal q) = 0 := by simp [detR]
        have hz2 : detR (toReal q) (toReal w) (toReal w) = 0 := by simp [detR]; ring
        calc
          detR (toReal q) (toReal w) (toReal p)
              = detR (toReal q) (toReal w)
                  (α • toReal q + β • toReal v + γ • toReal w) := by rw [← heq]
          _ = α * detR (toReal q) (toReal w) (toReal q) +
                β * detR (toReal q) (toReal w) (toReal v) +
                  γ * detR (toReal q) (toReal w) (toReal w) := haff
          _ = β * detR (toReal q) (toReal w) (toReal v) := by simp [hz1, hz2]
      simpa [detR_toReal] using this
    have hswap : latticeDet q p w = -latticeDet q w p :=
      latticeDet_swap_sign q w p
    have hswapv : latticeDet q w v = -latticeDet q v w :=
      latticeDet_swap_sign q v w
    have hswapR : (latticeDet q p w : ℝ) = - (latticeDet q w p : ℝ) := by exact_mod_cast hswap
    have hswapvR : (latticeDet q w v : ℝ) = - (latticeDet q v w : ℝ) := by exact_mod_cast hswapv
    calc
      (latticeDet q p w : ℝ) = - (latticeDet q w p : ℝ) := hswapR
      _ = - (β * (latticeDet q w v : ℝ)) := by rw [hqw]
      _ = - (β * (- (latticeDet q v w : ℝ))) := by rw [hswapvR]
      _ = β * (latticeDet q v w : ℝ) := by ring
  exact ⟨hα, hβ, hγ⟩

lemma latticeDet_nonneg_of_memClosedTriangle
    (q v w p : ℤ × ℤ) (hp : MemClosedTriangle q v w p)
    (hD : 0 < latticeDet q v w) :
    0 ≤ latticeDet v w p ∧ 0 ≤ latticeDet q p w ∧ 0 ≤ latticeDet q v p := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, heq⟩ := hp
  obtain ⟨e1, e2, e3⟩ := latticeDet_eq_bary_mul_of_affine q v w p α β γ hsum heq
  have hD0 : (0 : ℝ) ≤ (latticeDet q v w : ℝ) := by exact_mod_cast (le_of_lt hD)
  refine ⟨?_, ?_, ?_⟩
  · have : (0 : ℝ) ≤ (latticeDet v w p : ℝ) := by rw [e1]; exact mul_nonneg hα hD0
    exact_mod_cast this
  · have : (0 : ℝ) ≤ (latticeDet q p w : ℝ) := by rw [e2]; exact mul_nonneg hβ hD0
    exact_mod_cast this
  · have : (0 : ℝ) ≤ (latticeDet q v p : ℝ) := by rw [e3]; exact mul_nonneg hγ hD0
    exact_mod_cast this



lemma mem_edgeLatticePoints_of_weight_zero_bc
    (q v w p : ℤ × ℤ) (hp : MemClosedTriangle q v w p)
    (hD : 0 < latticeDet q v w) (hz : latticeDet v w p = 0) :
    p ∈ edgeLatticePoints v w := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, heq⟩ := hp
  obtain ⟨e1, _, _⟩ := latticeDet_eq_bary_mul_of_affine q v w p α β γ hsum heq
  have hα0 : α = 0 := by
    have heqα : α * (latticeDet q v w : ℝ) = 0 := by
      rw [← e1]; exact_mod_cast hz
    rcases mul_eq_zero.mp heqα with h | h
    · exact h
    · exact absurd h (by exact_mod_cast (ne_of_gt hD))
  have hseg : toReal p ∈ segment ℝ (toReal v) (toReal w) := by
    refine ⟨β, γ, hβ, hγ, ?_, ?_⟩
    · linarith [hsum, hα0]
    · simpa [hα0, zero_smul, zero_add] using heq
  exact mem_edgeLatticePoints_of_mem_segment v w p hseg

lemma mem_edgeLatticePoints_of_weight_zero_ca
    (q v w p : ℤ × ℤ) (hp : MemClosedTriangle q v w p)
    (hD : 0 < latticeDet q v w) (hz : latticeDet q p w = 0) :
    p ∈ edgeLatticePoints w q := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, heq⟩ := hp
  obtain ⟨_, e2, _⟩ := latticeDet_eq_bary_mul_of_affine q v w p α β γ hsum heq
  have hβ0 : β = 0 := by
    have heqβ : β * (latticeDet q v w : ℝ) = 0 := by
      rw [← e2]; exact_mod_cast hz
    rcases mul_eq_zero.mp heqβ with h | h
    · exact h
    · exact absurd h (by exact_mod_cast (ne_of_gt hD))
  have hseg : toReal p ∈ segment ℝ (toReal w) (toReal q) := by
    rw [segment_symm]
    refine ⟨α, γ, hα, hγ, ?_, ?_⟩
    · linarith [hsum, hβ0]
    · have h' : α • toReal q + γ • toReal w = toReal p := by
        calc
          α • toReal q + γ • toReal w
              = α • toReal q + (0 : ℝ) • toReal v + γ • toReal w := by
                  simp [zero_smul]
          _ = α • toReal q + β • toReal v + γ • toReal w := by rw [← hβ0]
          _ = toReal p := heq
      exact h'
  exact mem_edgeLatticePoints_of_mem_segment w q p hseg

lemma mem_edgeLatticePoints_of_weight_zero_ab
    (q v w p : ℤ × ℤ) (hp : MemClosedTriangle q v w p)
    (hD : 0 < latticeDet q v w) (hz : latticeDet q v p = 0) :
    p ∈ edgeLatticePoints q v := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, heq⟩ := hp
  obtain ⟨_, _, e3⟩ := latticeDet_eq_bary_mul_of_affine q v w p α β γ hsum heq
  have hγ0 : γ = 0 := by
    have heqγ : γ * (latticeDet q v w : ℝ) = 0 := by
      rw [← e3]; exact_mod_cast hz
    rcases mul_eq_zero.mp heqγ with h | h
    · exact h
    · exact absurd h (by exact_mod_cast (ne_of_gt hD))
  have hseg : toReal p ∈ segment ℝ (toReal q) (toReal v) := by
    refine ⟨α, β, hα, hβ, ?_, ?_⟩
    · linarith [hsum, hγ0]
    · have h' : α • toReal q + β • toReal v = toReal p := by
        have := heq
        simpa [hγ0, zero_smul, add_zero] using this
      exact h'
  exact mem_edgeLatticePoints_of_mem_segment q v p hseg

/-- `OffTriangleBoundary` ⇒ strict positive area weights. -/
theorem latticeDet_pos_of_memClosedTriangle_offBoundary
    (q v w r : ℤ × ℤ) (hr : MemClosedTriangle q v w r)
    (hD : 0 < latticeDet q v w) (hoff : OffTriangleBoundary q v w r) :
    0 < latticeDet v w r ∧ 0 < latticeDet q r w ∧ 0 < latticeDet q v r := by
  obtain ⟨hα0, hβ0, hγ0⟩ := latticeDet_nonneg_of_memClosedTriangle q v w r hr hD
  refine ⟨lt_of_le_of_ne hα0 ?_, lt_of_le_of_ne hβ0 ?_, lt_of_le_of_ne hγ0 ?_⟩
  · intro hz
    exact hoff.2.1 (mem_edgeLatticePoints_of_weight_zero_bc q v w r hr hD hz.symm)
  · intro hz
    exact hoff.2.2 (mem_edgeLatticePoints_of_weight_zero_ca q v w r hr hD hz.symm)
  · intro hz
    exact hoff.1 (mem_edgeLatticePoints_of_weight_zero_ab q v w r hr hD hz.symm)

lemma latticeDet_swap_middle (a b c : ℤ × ℤ) :
    latticeDet a b c = -latticeDet a c b :=
  latticeDet_swap_sign a c b

/-- Foreign vertex in an interior-fan ear contradicts supporting half-plane at that
vertex (works for any interior apex; not classical Pick). -/
lemma false_of_vertex_mem_interiorFan_ear_ne_of_mem_interior
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q : ℤ × ℤ}
    (hq : q ∈ P.interiorLatticePoints) (i j : Fin P.nVertices)
    (hne_i : P.vertex j ≠ P.vertex i)
    (hne_n : P.vertex j ≠ P.vertex (P.nextIdx i))
    (hvj : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j)) :
    False := by
  classical
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, heq⟩ := hvj
  set A := toReal (P.vertex (P.prevIdx j))
  set B := toReal (P.vertex j)
  have hpos := InteriorFanDetsPos_of_mem_interior P hsc hinj hedge hq
  have hφq : 0 < detR A B (toReal q) := by
    simpa [A, B] using detR_prev_apex_pos_of_InteriorFanDetsPos P hpos j
  have hφvi : 0 ≤ detR A B (toReal (P.vertex i)) := by
    simpa [A, B] using detR_prev_vertex_nonneg_of_ConvexCCW P hsc.1 j i
  have hφvn : 0 ≤ detR A B (toReal (P.vertex (P.nextIdx i))) := by
    simpa [A, B] using
      detR_prev_vertex_nonneg_of_ConvexCCW P hsc.1 j (P.nextIdx i)
  have hφj : detR A B (toReal (P.vertex j)) = 0 := by
    simpa [A, B] using detR_prev_vertex_eq_zero P j
  have hcomb :
      detR A B (toReal (P.vertex j)) =
        α * detR A B (toReal q) +
          β * detR A B (toReal (P.vertex i)) +
            γ * detR A B (toReal (P.vertex (P.nextIdx i))) := by
    have heq' :
        toReal (P.vertex j) =
          α • toReal q + β • toReal (P.vertex i) +
            γ • toReal (P.vertex (P.nextIdx i)) := heq.symm
    have haff := detR_affine_combination3 A B
      (toReal q) (toReal (P.vertex i)) (toReal (P.vertex (P.nextIdx i)))
      α β γ hsum
    rw [heq', haff]
  have hα0 : α = 0 := by
    have hge :
        α * detR A B (toReal q) ≤
          α * detR A B (toReal q) +
            β * detR A B (toReal (P.vertex i)) +
              γ * detR A B (toReal (P.vertex (P.nextIdx i))) := by
      have h1 : 0 ≤ β * detR A B (toReal (P.vertex i)) :=
        mul_nonneg hβ hφvi
      have h2 : 0 ≤ γ * detR A B (toReal (P.vertex (P.nextIdx i))) :=
        mul_nonneg hγ hφvn
      linarith
    have hαφ : α * detR A B (toReal q) ≤ 0 := by
      have : α * detR A B (toReal q) +
            β * detR A B (toReal (P.vertex i)) +
              γ * detR A B (toReal (P.vertex (P.nextIdx i))) = 0 := by
        simpa [hφj] using hcomb.symm
      linarith
    have hαφ' : 0 ≤ α * detR A B (toReal q) :=
      mul_nonneg hα (le_of_lt hφq)
    have hαφ0 : α * detR A B (toReal q) = 0 := le_antisymm hαφ hαφ'
    exact (mul_eq_zero.mp hαφ0).resolve_right (ne_of_gt hφq)
  have hseg :
      toReal (P.vertex j) ∈
        segment ℝ (toReal (P.vertex i))
          (toReal (P.vertex (P.nextIdx i))) := by
    refine ⟨β, γ, hβ, hγ, ?_, ?_⟩
    · linarith [hsum, hα0]
    · simpa [hα0, zero_smul, zero_add] using heq
  have hprim : edgeGcd (P.vertex i) (P.vertex (P.nextIdx i)) = 1 := by
    simpa [LatticePolygon.edgePair] using hedge i
  have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one
    (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j) hprim hseg
  exact hend.elim (fun h => hne_i h) (fun h => hne_n h)

/-- Foreign-vertex / interior contradiction for a polygon vertex in an ear
under `TwoInterior` (delegates to the general half-plane form). -/
lemma false_of_vertex_mem_interiorFan_ear_ne
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) (i j : Fin P.nVertices)
    (hne_i : P.vertex j ≠ P.vertex i)
    (hne_n : P.vertex j ≠ P.vertex (P.nextIdx i))
    (hvj : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j)) :
    False :=
  false_of_vertex_mem_interiorFan_ear_ne_of_mem_interior P hsc hinj hedge
    (mem_interior_of_twoInterior_left P h) i j hne_i hne_n hvj

/-- At most one closed interior-fan ear contains an Off-boundary point `r`
from an interior apex (cone / half-plane disjointness; not classical Pick).

Works for any interior cardinality: only `q ∈ interior` + `OffTriangleBoundary`
on the occupied ear. -/
theorem eq_of_mem_interiorFan_of_offBoundary
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (hq : q ∈ P.interiorLatticePoints) (i j : Fin P.nVertices)
    (hri : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hoff : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hrj : MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) r) :
    j = i := by
  classical
  have hpos := InteriorFanDetsPos_of_mem_interior P hsc hinj hedge hq
  have hDi : 0 < latticeDet q (P.vertex i) (P.vertex (P.nextIdx i)) := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hpos i
  have hDj : 0 < latticeDet q (P.vertex j) (P.vertex (P.nextIdx j)) := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hpos j
  obtain ⟨hαi, hβi, hγi⟩ :=
    latticeDet_pos_of_memClosedTriangle_offBoundary q (P.vertex i)
      (P.vertex (P.nextIdx i)) r hri hDi hoff
  obtain ⟨hαj0, hβj0, hγj0⟩ :=
    latticeDet_nonneg_of_memClosedTriangle q (P.vertex j)
      (P.vertex (P.nextIdx j)) r hrj hDj
  -- f(k) := latticeDet q (vertex k) r
  have hfi : 0 < latticeDet q (P.vertex i) r := hγi
  have hfinext : latticeDet q (P.vertex (P.nextIdx i)) r < 0 := by
    have h' : latticeDet q (P.vertex (P.nextIdx i)) r =
        -latticeDet q r (P.vertex (P.nextIdx i)) :=
      latticeDet_swap_middle q (P.vertex (P.nextIdx i)) r
    linarith [h', hβi]
  have hfj : 0 ≤ latticeDet q (P.vertex j) r := hγj0
  have hfjnext : latticeDet q (P.vertex (P.nextIdx j)) r ≤ 0 := by
    have h' : latticeDet q (P.vertex (P.nextIdx j)) r =
        -latticeDet q r (P.vertex (P.nextIdx j)) :=
      latticeDet_swap_middle q (P.vertex (P.nextIdx j)) r
    linarith [h', hβj0]
  by_cases hji : j = i
  · exact hji
  · by_cases hadj1 : j = P.nextIdx i
    · subst hadj1
      exact absurd hfj (not_le.mpr hfinext)
    · by_cases hadj2 : i = P.nextIdx j
      · have : latticeDet q (P.vertex (P.nextIdx j)) r =
            latticeDet q (P.vertex i) r := by rw [← hadj2]
        exact absurd (this ▸ hfjnext) (not_le.mpr hfi)
      · -- Non-adjacent
        set vi := P.vertex i
        set wi := P.vertex (P.nextIdx i)
        set vj := P.vertex j
        set wj := P.vertex (P.nextIdx j)
        set dac : ℤ := latticeDet q vi vj
        set dbc : ℤ := latticeDet q wi vj
        have hpluck :
            latticeDet q vi wi * latticeDet q vj r
              - latticeDet q vi vj * latticeDet q wi r
              + latticeDet q vi r * latticeDet q wi vj = 0 :=
          latticeDet_plucker q vi wi vj r
        have hConvex_ij : 0 ≤ latticeDet vi wi vj := hsc.1 i j
        by_cases hdac : 0 < dac
        · by_cases hdbc : 0 < dbc
          · have hfwi : latticeDet q wi r < 0 := hfinext
            have hform :
                latticeDet q vi wi * latticeDet q vj r
                  + latticeDet q vi vj * (-latticeDet q wi r)
                  + latticeDet q vi r * latticeDet q wi vj = 0 := by
              linarith [hpluck]
            have ht1 : 0 ≤ latticeDet q vi wi * latticeDet q vj r :=
              mul_nonneg (le_of_lt hDi) hfj
            have ht2 : 0 < latticeDet q vi vj * (-latticeDet q wi r) :=
              mul_pos hdac (neg_pos.mpr hfwi)
            have ht3 : 0 < latticeDet q vi r * latticeDet q wi vj :=
              mul_pos hfi hdbc
            have : (0 : ℤ) < 0 := by nlinarith [hform, ht1, ht2, ht3]
            exact (lt_irrefl (0 : ℤ) this).elim
          · -- dac > 0, dbc ≤ 0 ⇒ vj ∈ closed ear i
            push Not at hdbc
            have hβvj : 0 ≤ latticeDet q vj wi := by
              have : latticeDet q vj wi = -dbc := by
                simpa [dbc] using latticeDet_swap_sign q wi vj
              linarith
            have hvj : MemClosedTriangle q vi wi vj :=
              memClosedTriangle_of_area_weights_nonneg q vi wi vj hDi
                hConvex_ij hβvj (le_of_lt hdac)
            have hne_i : vj ≠ vi := by
              intro heq; exact hji (hinj heq)
            have hne_n : vj ≠ wi := by
              intro heq; exact hadj1 (hinj heq)
            exact (false_of_vertex_mem_interiorFan_ear_ne_of_mem_interior P hsc hinj hedge hq i j
              hne_i hne_n (by simpa [vi, wi, vj] using hvj)).elim
        · -- dac ≤ 0 ⇒ vi ∈ closed ear j (via Plücker)
          push Not at hdac
          have hpluckj :
              latticeDet q vj wj * latticeDet q vi r
                - latticeDet q vj vi * latticeDet q wj r
                + latticeDet q vj r * latticeDet q wj vi = 0 :=
            latticeDet_plucker q vj wj vi r
          have hdap : 0 ≤ latticeDet q vj vi := by
            have : latticeDet q vj vi = -dac := by
              simpa [dac] using latticeDet_swap_sign q vi vj
            linarith
          have hConvex_ji : 0 ≤ latticeDet vj wj vi := hsc.1 j i
          by_cases hfj0 : latticeDet q vj r = 0
          · have hL : 0 < latticeDet q vj wj * latticeDet q vi r :=
              mul_pos hDj hfi
            have hR : latticeDet q vj vi * latticeDet q wj r ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos hdap hfjnext
            have hdiff :
                latticeDet q vj wj * latticeDet q vi r
                  - latticeDet q vj vi * latticeDet q wj r = 0 := by
              have h := hpluckj
              simp [hfj0] at h
              exact h
            have hposdiff :
                0 < latticeDet q vj wj * latticeDet q vi r
                  - latticeDet q vj vi * latticeDet q wj r := by
              linarith [hL, hR]
            exact absurd hdiff (ne_of_gt hposdiff)
          · have hfjpos : 0 < latticeDet q vj r :=
              lt_of_le_of_ne hfj (Ne.symm hfj0)
            have hmid : 0 < latticeDet q vi wj := by
              have hswap : latticeDet q vi wj = -latticeDet q wj vi :=
                latticeDet_swap_sign q wj vi
              have hL : 0 < latticeDet q vj wj * latticeDet q vi r :=
                mul_pos hDj hfi
              have hR : latticeDet q vj vi * latticeDet q wj r ≤ 0 :=
                mul_nonpos_of_nonneg_of_nonpos hdap hfjnext
              -- Plücker: L - R + f(j)*det(q,wj,vi) = 0
              -- ⇒ f(j)*det(q,wj,vi) = R - L < 0
              have hprod :
                  latticeDet q vj r * latticeDet q wj vi =
                    latticeDet q vj vi * latticeDet q wj r
                      - latticeDet q vj wj * latticeDet q vi r := by
                linarith [hpluckj]
              have hprod_neg : latticeDet q vj r * latticeDet q wj vi < 0 := by
                linarith [hprod, hL, hR]
              have hneg : latticeDet q wj vi < 0 := by
                nlinarith [hprod_neg, hfjpos]
              linarith [hswap]
            have hvi : MemClosedTriangle q vj wj vi :=
              memClosedTriangle_of_area_weights_nonneg q vj wj vi hDj
                hConvex_ji (le_of_lt hmid) hdap
            have hne_j : vi ≠ vj := by
              intro heq; exact hji (hinj heq.symm)
            have hne_jn : vi ≠ wj := by
              intro heq; exact hadj2 (hinj heq)
            exact (false_of_vertex_mem_interiorFan_ear_ne_of_mem_interior P hsc hinj hedge hq j i
              hne_j hne_jn (by simpa [vj, wj, vi] using hvi)).elim

/-- At most one closed interior-fan ear contains `r` under `TwoInterior` +
`OffTriangleBoundary` (specializes `eq_of_mem_interiorFan_of_offBoundary`). -/
theorem eq_of_mem_interiorFan_of_twoInterior_offBoundary
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) (i j : Fin P.nVertices)
    (hri : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hoff : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hrj : MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) r) :
    j = i :=
  eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge
    (mem_interior_of_twoInterior_left P h) i j hri hoff hrj

/-- **I = 2 shoelace Pick-form** without uniqueness hyp (still needs
`OffTriangleBoundary`; not classical Pick). -/
theorem shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior_occupied_offBoundary
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) (i : Fin P.nVertices)
    (hr : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hoff : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r) :
    P.shoelace = (2 : ℚ) + (P.B : ℚ) / 2 - 1 := by
  refine shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior_occupied
    P hsc hinj hedge h i hr hoff ?_
  intro j hj
  exact eq_of_mem_interiorFan_of_twoInterior_offBoundary
    P hsc hinj hedge h i j hr hoff hj


end InteriorFan
end LatticeFan
end Picks
end EulersGem
