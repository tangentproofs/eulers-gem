/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.LatticeTriangle
import EulersGem.LatticePolygon

/-!
# Empty closed lattice triangle ⇒ `|det|=1` (nondegenerate)

Converse of `memClosedTriangle_eq_vertices_of_natAbs_det_eq_one`.

**Honesty:** requires `det ≠ 0` (degenerate collinear triples can be vertex-only
with `det = 0`). Not Haar; not classical Pick. See `PICKS_CLAUDE_AUDIT.md`.
-/

namespace EulersGem
namespace Picks
namespace LatticeTriangle

open scoped BigOperators

/-- Companion vector: if `gcd(u₁,u₂)=1` then `det(u, companion u)=1`. -/
def companion (u : ℤ × ℤ) : ℤ × ℤ :=
  (-Int.gcdB u.1 u.2, Int.gcdA u.1 u.2)

lemma latticeDet_companion (u : ℤ × ℤ) (h : Int.gcd u.1 u.2 = 1) :
    latticeDet (0, 0) u (companion u) = 1 := by
  unfold latticeDet companion
  have hb : (Int.gcd u.1 u.2 : ℤ) = u.1 * Int.gcdA u.1 u.2 + u.2 * Int.gcdB u.1 u.2 :=
    Int.gcd_eq_gcd_ab u.1 u.2
  simp only [h, Nat.cast_one] at hb ⊢
  linarith

/-- Coefficient `α` of `u` in the `{u, companion u}` expansion of `v`. -/
def basisCoeffα (u v : ℤ × ℤ) : ℤ :=
  latticeDet (0, 0) v (companion u)

lemma eq_basisCoeff_smul_of_gcd_eq_one (u v : ℤ × ℤ)
    (h : Int.gcd u.1 u.2 = 1) :
    v = basisCoeffα u v • u + latticeDet (0, 0) u v • companion u := by
  have hw : latticeDet (0, 0) u (companion u) = 1 := latticeDet_companion u h
  have hα : cramerα u (companion u) v = basisCoeffα u v := by
    unfold cramerα basisCoeffα latticeDet companion; ring
  have hβ : cramerβ u (companion u) v = latticeDet (0, 0) u v := by
    unfold cramerβ latticeDet; ring
  apply Prod.ext
  · have hmul := (cramer_mul_det u (companion u) v).1
    simp only [hα, hβ, hw, one_mul] at hmul
    -- hmul: u.1 * α + w.1 * β = v.1; goal uses opposite mul order
    simp [Prod.smul_def, mul_comm]
    linarith
  · have hmul := (cramer_mul_det u (companion u) v).2
    simp only [hα, hβ, hw, one_mul] at hmul
    simp [Prod.smul_def, mul_comm]
    linarith

theorem exists_strict_mem_edgeLatticePoints_of_edgeGcd_ge_two
    (p q : ℤ × ℤ) (h : 2 ≤ edgeGcd p q) :
    ∃ r ∈ edgeLatticePoints p q, r ≠ p ∧ r ≠ q := by
  classical
  have hcard := card_edgeLatticePoints p q
  have hne : p ≠ q := by
    intro hpq
    have : edgeGcd p q = 0 := (edgeGcd_eq_zero_iff p q).mpr hpq
    omega
  have hcard2 : ({p, q} : Finset (ℤ × ℤ)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have hlt : ({p, q} : Finset (ℤ × ℤ)).card < (edgeLatticePoints p q).card := by
    omega
  obtain ⟨r, hr, hrnq⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨r, hr, fun hrp => hrnq (by simp [hrp]), fun hrq => hrnq (by simp [hrq])⟩

lemma memClosedTriangle_of_edge_convexComb
    (a b c : ℤ × ℤ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (p : ℤ × ℤ)
    (hx : (p.1 : ℝ) = (1 - t) * a.1 + t * b.1)
    (hy : (p.2 : ℝ) = (1 - t) * a.2 + t * b.2) :
    MemClosedTriangle a b c p := by
  refine ⟨1 - t, t, 0, by linarith, ht0, le_rfl, by ring, ?_⟩
  apply Prod.ext
  · simpa [toReal, Prod.smul_def, smul_eq_mul] using hx.symm
  · simpa [toReal, Prod.smul_def, smul_eq_mul] using hy.symm

lemma memClosedTriangle_of_mem_edgeLatticePoints_ab
    (a b c p : ℤ × ℤ) (hp : p ∈ edgeLatticePoints a b) :
    MemClosedTriangle a b c p := by
  classical
  simp only [edgeLatticePoints] at hp
  split_ifs at hp with hd
  · simp only [Finset.mem_singleton] at hp
    exact memClosedTriangle_of_edge_convexComb a b c 0 (by norm_num) (by norm_num) p
      (by simp [hp]) (by simp [hp])
  · rcases Finset.mem_image.mp hp with ⟨k, hk, rfl⟩
    set d := edgeGcd a b
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hdx : (d : ℤ) ∣ (b.1 - a.1) := by
      simpa [edgeGcd, d] using Int.gcd_dvd_left (b.1 - a.1) (b.2 - a.2)
    have hdy : (d : ℤ) ∣ (b.2 - a.2) := by
      simpa [edgeGcd, d] using Int.gcd_dvd_right (b.1 - a.1) (b.2 - a.2)
    set sx : ℤ := (b.1 - a.1) / (d : ℤ)
    set sy : ℤ := (b.2 - a.2) / (d : ℤ)
    have hsx : sx * (d : ℤ) = b.1 - a.1 := by simpa [sx] using Int.ediv_mul_cancel hdx
    have hsy : sy * (d : ℤ) = b.2 - a.2 := by simpa [sy] using Int.ediv_mul_cancel hdy
    set t : ℝ := (k : ℝ) / d
    have ht0 : 0 ≤ t :=
      div_nonneg (by exact_mod_cast Nat.zero_le k) (by exact_mod_cast Nat.zero_le d)
    have ht1 : t ≤ 1 := (div_le_one hdpos).mpr (by exact_mod_cast hk')
    refine memClosedTriangle_of_edge_convexComb a b c t ht0 ht1
      (a.1 + (k : ℤ) * sx, a.2 + (k : ℤ) * sy) ?hx ?hy
    · have hb1 : (b.1 : ℝ) = a.1 + (d : ℝ) * sx := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hsx
        push_cast at this ⊢; linarith
      have hkdiv : (k : ℝ) * (sx : ℝ) = t * ((d : ℝ) * sx) := by
        dsimp [t]; field_simp
      show (↑(a.1 + (k : ℤ) * sx) : ℝ) = (1 - t) * a.1 + t * b.1
      calc
        (↑(a.1 + (k : ℤ) * sx) : ℝ)
            = (a.1 : ℝ) + (k : ℝ) * sx := by push_cast; rfl
        _ = (a.1 : ℝ) + t * ((d : ℝ) * sx) := by rw [hkdiv]
        _ = (1 - t) * a.1 + t * b.1 := by rw [hb1]; ring
    · have hb2 : (b.2 : ℝ) = a.2 + (d : ℝ) * sy := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hsy
        push_cast at this ⊢; linarith
      have hkdiv : (k : ℝ) * (sy : ℝ) = t * ((d : ℝ) * sy) := by
        dsimp [t]; field_simp
      show (↑(a.2 + (k : ℤ) * sy) : ℝ) = (1 - t) * a.2 + t * b.2
      calc
        (↑(a.2 + (k : ℤ) * sy) : ℝ)
            = (a.2 : ℝ) + (k : ℝ) * sy := by push_cast; rfl
        _ = (a.2 : ℝ) + t * ((d : ℝ) * sy) := by rw [hkdiv]
        _ = (1 - t) * a.2 + t * b.2 := by rw [hb2]; ring


/-! ### Helpers for the companion basis -/

private lemma latticeDet_smul_right (u w : ℤ × ℤ) (k : ℤ) :
    latticeDet (0, 0) u (k • w) = k * latticeDet (0, 0) u w := by
  unfold latticeDet; simp [Prod.smul_def]; ring

private lemma latticeDet_add_right (u w z : ℤ × ℤ) :
    latticeDet (0, 0) u (w + z) =
      latticeDet (0, 0) u w + latticeDet (0, 0) u z := by
  unfold latticeDet; simp [Prod.add_def]; ring

private lemma latticeDet_self_smul (u : ℤ × ℤ) (k : ℤ) :
    latticeDet (0, 0) u (k • u) = 0 := by
  unfold latticeDet; simp [Prod.smul_def]; ring

lemma latticeDet_companion_smul_add (u : ℤ × ℤ) (h : Int.gcd u.1 u.2 = 1)
    (k : ℤ) :
    latticeDet (0, 0) u (k • u + companion u) = 1 := by
  rw [latticeDet_add_right, latticeDet_self_smul, latticeDet_companion u h, zero_add]

lemma latticeDet_neg_companion_smul_add (u : ℤ × ℤ) (h : Int.gcd u.1 u.2 = 1)
    (k : ℤ) :
    latticeDet (0, 0) u (k • u + -companion u) = -1 := by
  rw [latticeDet_add_right, latticeDet_self_smul, zero_add, show (-companion u) = (-1 : ℤ) • companion u by simp]
  rw [latticeDet_smul_right, latticeDet_companion u h]; ring

/-- Oriented companion so the `v`-coefficient is positive `|det|`. -/
def orientedCompanion (u v : ℤ × ℤ) : ℤ × ℤ :=
  if 0 < latticeDet (0, 0) u v then companion u else -companion u

/-- Same as `basisCoeffα`: flipping the companion absorbs the det sign, not `α`. -/
def orientedα (u v : ℤ × ℤ) : ℤ :=
  basisCoeffα u v

lemma oriented_β_eq_natAbs (u v : ℤ × ℤ) :
    (if 0 < latticeDet (0, 0) u v then latticeDet (0, 0) u v
      else -latticeDet (0, 0) u v) =
      (Int.natAbs (latticeDet (0, 0) u v) : ℤ) := by
  split_ifs with h
  · exact (Int.natAbs_of_nonneg (le_of_lt h)).symm
  · have hle : latticeDet (0, 0) u v ≤ 0 := le_of_not_gt h
    rw [← Int.natAbs_neg]
    exact (Int.natAbs_of_nonneg (neg_nonneg.mpr hle)).symm

lemma eq_oriented_basis (u v : ℤ × ℤ) (h : Int.gcd u.1 u.2 = 1) :
    v = orientedα u v • u +
      (Int.natAbs (latticeDet (0, 0) u v) : ℤ) • orientedCompanion u v := by
  unfold orientedα orientedCompanion
  have hv := eq_basisCoeff_smul_of_gcd_eq_one u v h
  split_ifs with hpos
  · have : (Int.natAbs (latticeDet (0, 0) u v) : ℤ) = latticeDet (0, 0) u v :=
      Int.natAbs_of_nonneg (le_of_lt hpos)
    simpa [this] using hv
  · have hle : latticeDet (0, 0) u v ≤ 0 := le_of_not_gt hpos
    have habs : (Int.natAbs (latticeDet (0, 0) u v) : ℤ) = -latticeDet (0, 0) u v := by
      rw [← Int.natAbs_neg]
      exact Int.natAbs_of_nonneg (neg_nonneg.mpr hle)
    -- v = α•u + β•w = α•u + (-β)•(-w)
    calc
      v = basisCoeffα u v • u + latticeDet (0, 0) u v • companion u := hv
      _ = basisCoeffα u v • u + (-latticeDet (0, 0) u v) • (-companion u) := by
          simp [smul_neg, neg_smul]
      _ = basisCoeffα u v • u +
            (Int.natAbs (latticeDet (0, 0) u v) : ℤ) • (-companion u) := by
          rw [habs]

lemma latticeDet_orientedCompanion (u v : ℤ × ℤ) (h : Int.gcd u.1 u.2 = 1) :
    latticeDet (0, 0) u (orientedCompanion u v) =
      if 0 < latticeDet (0, 0) u v then (1 : ℤ) else (-1 : ℤ) := by
  unfold orientedCompanion
  split_ifs
  · exact latticeDet_companion u h
  · simpa using (latticeDet_smul_right u (companion u) (-1)).trans
      (by rw [latticeDet_companion u h]; ring)

/-! ### Extra lattice point when `|det| ≥ 2` -/

private lemma memClosedTriangle_origin_of_smul_eq
    (u v p : ℤ × ℤ) (β : ℕ) (hβ : 2 ≤ β)
    (hv : v = (β : ℤ) • p) :
    MemClosedTriangle (0, 0) u v p := by
  have hbR : (0 : ℝ) < β := by exact_mod_cast (by omega : 0 < β)
  refine ⟨(1 : ℝ) - 1 / (β : ℝ), 0, 1 / (β : ℝ), ?_, le_rfl, ?_, by ring, ?_⟩
  · have : (1 : ℝ) / β ≤ 1 :=
      (div_le_one hbR).mpr (by exact_mod_cast (by omega : (1 : ℕ) ≤ β))
    linarith
  · exact div_nonneg (by norm_num) (le_of_lt hbR)
  · have hvR : toReal v = (β : ℝ) • toReal p := by
      calc toReal v = toReal ((β : ℤ) • p) := by rw [hv]
        _ = (β : ℝ) • toReal p := toReal_smul _ _
    have hscale : ((1 : ℝ) / β) • toReal v = toReal p := by
      rw [hvR]
      -- (1/β) • (β • toReal p) = toReal p
      have : ((1 : ℝ) / β) * β = 1 := by field_simp
      rw [smul_smul, this, one_smul]
    -- goal: (1-1/β)•0 + 0•u + (1/β)•v = p
    convert hscale using 1
    simp [toReal_zero]

private lemma ne_zero_of_det_u_pm_one (u p : ℤ × ℤ)
    (h : latticeDet (0, 0) u p = 1 ∨ latticeDet (0, 0) u p = -1) :
    p ≠ (0, 0) := by
  intro hp; simp [hp, latticeDet] at h

private lemma det_u_eq_det_w_of_smul_add (u w : ℤ × ℤ) (k : ℤ) :
    latticeDet (0, 0) u (k • u + w) = latticeDet (0, 0) u w := by
  rw [latticeDet_add_right, latticeDet_self_smul, zero_add]

private lemma latticeDet_u_u (u : ℤ × ℤ) : latticeDet (0, 0) u u = 0 := by
  unfold latticeDet; ring

/-- If `|det(u,v)| ≥ 2` and edge `0--u` is primitive, an extra closed-triangle
lattice point exists. -/
theorem exists_extra_lattice_point_of_natAbs_det_ge_two_origin
    (u v : ℤ × ℤ)
    (hu : Int.gcd u.1 u.2 = 1)
    (hge : 2 ≤ Int.natAbs (latticeDet (0, 0) u v)) :
    ∃ p, MemClosedTriangle (0, 0) u v p ∧ p ≠ (0, 0) ∧ p ≠ u ∧ p ≠ v := by
  set α := orientedα u v
  set w := orientedCompanion u v
  set β : ℕ := Int.natAbs (latticeDet (0, 0) u v)
  have hv : v = α • u + (β : ℤ) • w := eq_oriented_basis u v hu
  have hβge : 2 ≤ β := hge
  have hβpos : 0 < (β : ℤ) := by exact_mod_cast (by omega : 0 < β)
  have hwε : latticeDet (0, 0) u w = 1 ∨ latticeDet (0, 0) u w = -1 := by
    dsimp only [w, orientedCompanion]
    split_ifs with hpos
    · exact Or.inl (latticeDet_companion u hu)
    · refine Or.inr ?_
      have hneg : latticeDet (0, 0) u (-companion u) =
          -latticeDet (0, 0) u (companion u) := by
        simpa using latticeDet_smul_right u (companion u) (-1)
      rw [hneg, latticeDet_companion u hu]
  set q : ℤ := α / (β : ℤ)
  set r : ℤ := α % (β : ℤ)
  have hdiv : (β : ℤ) * q + r = α := Int.mul_ediv_add_emod α β
  have hr0 : 0 ≤ r := Int.emod_nonneg α (by omega)
  have hr1 : r < (β : ℤ) := Int.emod_lt_of_pos α hβpos
  by_cases hr : r = 0
  · set p : ℤ × ℤ := q • u + w
    have hv' : v = (β : ℤ) • p := by
      have hv1 : v = ((β : ℤ) * q + r) • u + (β : ℤ) • w := by
        simpa [hdiv] using hv
      rw [hr, add_zero] at hv1
      calc
        v = ((β : ℤ) * q) • u + (β : ℤ) • w := hv1
        _ = (β : ℤ) • (q • u) + (β : ℤ) • w := by rw [mul_zsmul]
        _ = (β : ℤ) • (q • u + w) := (smul_add _ _ _).symm
    refine ⟨p, memClosedTriangle_origin_of_smul_eq u v p β hβge hv', ?_, ?_, ?_⟩
    · exact ne_zero_of_det_u_pm_one u p (by
        rw [det_u_eq_det_w_of_smul_add]; exact hwε)
    · intro hu'
      have hdet := det_u_eq_det_w_of_smul_add u w q
      rw [← show p = q • u + w from rfl, hu', latticeDet_u_u] at hdet
      rcases hwε with h1 | h1 <;> omega
    · intro hvEq
      have : (β : ℤ) • p = p := by rw [← hv', hvEq]
      have hx : ((β : ℤ) - 1) * p.1 = 0 := by
        have := congrArg Prod.fst this; simp [Prod.smul_def] at this; linarith
      have hy : ((β : ℤ) - 1) * p.2 = 0 := by
        have := congrArg Prod.snd this; simp [Prod.smul_def] at this; linarith
      have hp0 := ne_zero_of_det_u_pm_one u p (by
        rw [det_u_eq_det_w_of_smul_add]; exact hwε)
      have hβ1 : (β : ℤ) - 1 ≠ 0 := by omega
      exact hp0 (Prod.ext ((mul_eq_zero.mp hx).resolve_left hβ1)
        ((mul_eq_zero.mp hy).resolve_left hβ1))
  · have hrpos : (0 : ℤ) < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    set p : ℤ × ℤ := (q + 1) • u + w
    have hbR : (0 : ℝ) < β := by exact_mod_cast (by omega : 0 < β)
    -- Barycentric: G = (r-1)/β, A = (β-r)/β, Bv = 1/β
    have hm : MemClosedTriangle (0, 0) u v p := by
      set A : ℝ := ((β : ℝ) - (r : ℝ)) / (β : ℝ)
      set Bv : ℝ := (1 : ℝ) / (β : ℝ)
      set G : ℝ := ((r : ℝ) - 1) / (β : ℝ)
      have hsum : G + A + Bv = 1 := by
        dsimp [A, Bv, G]; field_simp; ring
      refine ⟨G, A, Bv,
        div_nonneg (by exact_mod_cast (by omega : (0:ℤ) ≤ r-1)) (le_of_lt hbR),
        div_nonneg (by exact_mod_cast (by omega : (0:ℤ) ≤ (β:ℤ)-r)) (le_of_lt hbR),
        div_nonneg (by norm_num) (le_of_lt hbR), hsum, ?_⟩
      have hαR : (α : ℝ) = (β : ℝ) * (q : ℝ) + (r : ℝ) := by exact_mod_cast hdiv.symm
      have hv1 : (v.1 : ℝ) = (α : ℝ) * u.1 + (β : ℝ) * w.1 := by
        have := congrArg Prod.fst (congrArg toReal hv)
        -- toReal (α•u + β•w)
        have ht : toReal v = toReal (α • u + (β : ℤ) • w) := by rw [hv]
        have := congrArg Prod.fst ht
        simp [toReal, Prod.smul_def, Prod.add_def] at this
        exact this
      have hv2 : (v.2 : ℝ) = (α : ℝ) * u.2 + (β : ℝ) * w.2 := by
        have ht : toReal v = toReal (α • u + (β : ℤ) • w) := by rw [hv]
        have := congrArg Prod.snd ht
        simp [toReal, Prod.smul_def, Prod.add_def] at this
        exact this
      apply Prod.ext
      · have calc1 : A * (u.1 : ℝ) + Bv * (v.1 : ℝ) = ((q : ℝ) + 1) * u.1 + w.1 := by
          dsimp [A, Bv]; rw [hv1, hαR]; field_simp; ring
        have lhs :
            (G • toReal (0, 0) + A • toReal u + Bv • toReal v).1 =
              A * (u.1 : ℝ) + Bv * (v.1 : ℝ) := by
          simp [toReal, Prod.smul_def]
        have rhs : (toReal p).1 = ((q : ℝ) + 1) * u.1 + w.1 := by
          simp [p, toReal, Prod.smul_def, Prod.add_def]
        rw [lhs, calc1, rhs]
      · have calc2 : A * (u.2 : ℝ) + Bv * (v.2 : ℝ) = ((q : ℝ) + 1) * u.2 + w.2 := by
          dsimp [A, Bv]; rw [hv2, hαR]; field_simp; ring
        have lhs :
            (G • toReal (0, 0) + A • toReal u + Bv • toReal v).2 =
              A * (u.2 : ℝ) + Bv * (v.2 : ℝ) := by
          simp [toReal, Prod.smul_def]
        have rhs : (toReal p).2 = ((q : ℝ) + 1) * u.2 + w.2 := by
          simp [p, toReal, Prod.smul_def, Prod.add_def]
        rw [lhs, calc2, rhs]
    refine ⟨p, hm, ?_, ?_, ?_⟩
    · exact ne_zero_of_det_u_pm_one u p (by
        rw [det_u_eq_det_w_of_smul_add]; exact hwε)
    · intro hu'
      have hdet := det_u_eq_det_w_of_smul_add u w (q + 1)
      -- hdet: det(u, (q+1)u+w) = det(u,w); p = (q+1)u+w = u
      change latticeDet (0, 0) u p = latticeDet (0, 0) u w at hdet
      rw [hu', latticeDet_u_u] at hdet
      rcases hwε with h1 | h1 <;> omega
    · intro hvEq
      have hdp : latticeDet (0, 0) u p = latticeDet (0, 0) u w :=
        det_u_eq_det_w_of_smul_add u w (q + 1)
      have : latticeDet (0, 0) u v = latticeDet (0, 0) u w := by
        rw [← hvEq, hdp]
      have : Int.natAbs (latticeDet (0, 0) u v) = 1 := by
        rcases hwε with h1 | h1 <;> simp [this, h1]
      omega

/-- Origin form of the converse. -/
theorem natAbs_det_eq_one_of_memClosedTriangle_eq_vertices_origin
    (u v : ℤ × ℤ)
    (hne : latticeDet (0, 0) u v ≠ 0)
    (hu : Int.gcd u.1 u.2 = 1)
    (h : ∀ p, MemClosedTriangle (0, 0) u v p → p = (0, 0) ∨ p = u ∨ p = v) :
    Int.natAbs (latticeDet (0, 0) u v) = 1 := by
  by_contra hne1
  have hge : 2 ≤ Int.natAbs (latticeDet (0, 0) u v) := by
    have : 0 < Int.natAbs (latticeDet (0, 0) u v) := Int.natAbs_pos.mpr hne
    omega
  obtain ⟨p, hp, hp0, hpu, hpv⟩ :=
    exists_extra_lattice_point_of_natAbs_det_ge_two_origin u v hu hge
  rcases h p hp with h0 | hu' | hv'
  · exact hp0 h0
  · exact hpu hu'
  · exact hpv hv'

/-- Translated form: nondegenerate empty closed triangle ⇒ `|det|=1`,
assuming the edge `a--b` is primitive. -/
theorem natAbs_det_eq_one_of_memClosedTriangle_eq_vertices_of_edgeGcd
    (a b c : ℤ × ℤ)
    (hne : latticeDet a b c ≠ 0)
    (hab : edgeGcd a b = 1)
    (h : ∀ p, MemClosedTriangle a b c p → p = a ∨ p = b ∨ p = c) :
    Int.natAbs (latticeDet a b c) = 1 := by
  set u := b - a
  set v := c - a
  have hne' : latticeDet (0, 0) u v ≠ 0 := by
    simpa [u, v, ← latticeDet_translate] using hne
  have hu : Int.gcd u.1 u.2 = 1 := by
    simpa [u, edgeGcd, Prod.sub_def] using hab
  have h' : ∀ p, MemClosedTriangle (0, 0) u v p →
      p = (0, 0) ∨ p = u ∨ p = v := by
    intro p hp
    -- translate membership back
    -- MemClosed (0,u,v) p ⇒ MemClosed (a,b,c) (p+a)
    have hp' : MemClosedTriangle a b c (p + a) := by
      obtain ⟨α, β, γ, hα, hβ, hγ, hsum, heq⟩ := hp
      refine ⟨α, β, γ, hα, hβ, hγ, hsum, ?_⟩
      -- α•0 + β•u + γ•v = p  ⇒  α•a + β•b + γ•c = p+a
      apply Prod.ext
      · have h1 := congrArg Prod.fst heq
        simp [toReal, Prod.smul_def, u, v, Prod.sub_def] at h1 ⊢
        -- β*(b-a) + γ*(c-a) = p  and α+β+γ=1 ⇒ α a + β b + γ c = p+a
        have : (α : ℝ) * a.1 + β * b.1 + γ * c.1 = (p.1 : ℝ) + a.1 := by
          have : β * ((b.1 : ℝ) - a.1) + γ * ((c.1 : ℝ) - a.1) = p.1 := by
            simpa [smul_eq_mul] using h1
          calc
            (α : ℝ) * a.1 + β * b.1 + γ * c.1
                = α * a.1 + β * (a.1 + (b.1 - a.1)) + γ * (a.1 + (c.1 - a.1)) := by ring
            _ = (α + β + γ) * a.1 + (β * (b.1 - a.1) + γ * (c.1 - a.1)) := by ring
            _ = 1 * a.1 + p.1 := by rw [hsum, this]
            _ = p.1 + a.1 := by ring
        simpa [toReal, Prod.smul_def, Prod.add_def] using this
      · have h2 := congrArg Prod.snd heq
        simp [toReal, Prod.smul_def, u, v, Prod.sub_def] at h2 ⊢
        have : (α : ℝ) * a.2 + β * b.2 + γ * c.2 = (p.2 : ℝ) + a.2 := by
          have : β * ((b.2 : ℝ) - a.2) + γ * ((c.2 : ℝ) - a.2) = p.2 := by
            simpa [smul_eq_mul] using h2
          calc
            (α : ℝ) * a.2 + β * b.2 + γ * c.2
                = α * a.2 + β * (a.2 + (b.2 - a.2)) + γ * (a.2 + (c.2 - a.2)) := by ring
            _ = (α + β + γ) * a.2 + (β * (b.2 - a.2) + γ * (c.2 - a.2)) := by ring
            _ = 1 * a.2 + p.2 := by rw [hsum, this]
            _ = p.2 + a.2 := by ring
        simpa [toReal, Prod.smul_def, Prod.add_def] using this
    rcases h (p + a) hp' with h1 | h2 | h3
    · left; exact (add_eq_right).mp h1
    · right; left
      -- p + a = b = u + a
      have : p + a = u + a := by simpa [u] using h2
      exact (add_left_inj a).mp this
    · right; right
      have : p + a = v + a := by simpa [v] using h3
      exact (add_left_inj a).mp this
  have := natAbs_det_eq_one_of_memClosedTriangle_eq_vertices_origin u v hne' hu h'
  simpa [u, v, ← latticeDet_translate] using this

/-! ### Edge primitivity from emptiness + nondegeneracy -/

lemma memClosedTriangle_permute_acb
    {a b c p : ℤ × ℤ} (h : MemClosedTriangle a c b p) :
    MemClosedTriangle a b c p := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, heq⟩ := h
  refine ⟨α, γ, β, hα, hγ, hβ, by linarith, ?_⟩
  -- heq: α•a + β•c + γ•b = p; goal: α•a + γ•b + β•c = p
  convert heq using 1
  abel

lemma memClosedTriangle_permute_bca
    {a b c p : ℤ × ℤ} (h : MemClosedTriangle b c a p) :
    MemClosedTriangle a b c p := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, heq⟩ := h
  refine ⟨γ, α, β, hγ, hα, hβ, by linarith, ?_⟩
  convert heq using 1
  abel

lemma memClosedTriangle_permute_cab
    {a b c p : ℤ × ℤ} (h : MemClosedTriangle c a b p) :
    MemClosedTriangle a b c p := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, heq⟩ := h
  refine ⟨β, γ, α, hβ, hγ, hα, by linarith, ?_⟩
  convert heq using 1
  abel

lemma memClosedTriangle_of_mem_edgeLatticePoints_bc
    (a b c p : ℤ × ℤ) (hp : p ∈ edgeLatticePoints b c) :
    MemClosedTriangle a b c p :=
  memClosedTriangle_permute_bca
    (memClosedTriangle_of_mem_edgeLatticePoints_ab b c a p hp)

lemma memClosedTriangle_of_mem_edgeLatticePoints_ca
    (a b c p : ℤ × ℤ) (hp : p ∈ edgeLatticePoints c a) :
    MemClosedTriangle a b c p :=
  memClosedTriangle_permute_cab
    (memClosedTriangle_of_mem_edgeLatticePoints_ab c a b p hp)

lemma latticeDet_eq_zero_of_mem_edge_ab
    (a b c : ℤ × ℤ) (hc : c ∈ edgeLatticePoints a b) :
    latticeDet a b c = 0 := by
  classical
  simp only [edgeLatticePoints] at hc
  split_ifs at hc with hd
  · -- d=0 ⇒ a=b ⇒ det=0
    have hab : a = b := (edgeGcd_eq_zero_iff a b).mp hd
    simp [latticeDet, hab]
  · rcases Finset.mem_image.mp hc with ⟨k, hk, hkEq⟩
    set d := edgeGcd a b
    set sx : ℤ := (b.1 - a.1) / (d : ℤ)
    set sy : ℤ := (b.2 - a.2) / (d : ℤ)
    have hdx : (d : ℤ) ∣ (b.1 - a.1) := by
      simpa [edgeGcd, d] using Int.gcd_dvd_left (b.1 - a.1) (b.2 - a.2)
    have hdy : (d : ℤ) ∣ (b.2 - a.2) := by
      simpa [edgeGcd, d] using Int.gcd_dvd_right (b.1 - a.1) (b.2 - a.2)
    have hsx : sx * (d : ℤ) = b.1 - a.1 := by simpa [sx] using Int.ediv_mul_cancel hdx
    have hsy : sy * (d : ℤ) = b.2 - a.2 := by simpa [sy] using Int.ediv_mul_cancel hdy
    have eqc : c = (a.1 + (k : ℤ) * sx, a.2 + (k : ℤ) * sy) := hkEq.symm
    have hx : c.1 - a.1 = (k : ℤ) * sx := by have := congrArg Prod.fst eqc; omega
    have hy : c.2 - a.2 = (k : ℤ) * sy := by have := congrArg Prod.snd eqc; omega
    unfold latticeDet
    have : (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) =
        (sx * d) * (k * sy) - (sy * d) * (k * sx) := by
      rw [← hsx, ← hsy, hx, hy]
    rw [this]; ring

/-- Under nondegeneracy, emptiness ⇒ edge `a--b` is primitive. -/
theorem edgeGcd_eq_one_of_memClosedTriangle_eq_vertices_of_det_ne_zero
    (a b c : ℤ × ℤ)
    (hne : latticeDet a b c ≠ 0)
    (h : ∀ p, MemClosedTriangle a b c p → p = a ∨ p = b ∨ p = c) :
    edgeGcd a b = 1 := by
  have hab : a ≠ b := by
    intro hab
    have : latticeDet a b c = 0 := by simp [latticeDet, hab]
    exact hne this
  have hge0 : edgeGcd a b ≠ 0 := fun hz => hab ((edgeGcd_eq_zero_iff a b).mp hz)
  by_contra hne1
  have h2 : 2 ≤ edgeGcd a b := by omega
  obtain ⟨r, hr, hrne⟩ := exists_strict_mem_edgeLatticePoints_of_edgeGcd_ge_two a b h2
  have hm := h r (memClosedTriangle_of_mem_edgeLatticePoints_ab a b c r hr)
  rcases hm with rfl | rfl | rfl
  · exact hrne.1 rfl
  · exact hrne.2 rfl
  · -- third case: r = c (via rfl), so c is gone; use r
    exact hne (latticeDet_eq_zero_of_mem_edge_ab a b r hr)

/-- **Main prize (triangle form):** nondegenerate empty closed lattice triangle
⇒ `|det|=1`. Converse of `memClosedTriangle_eq_vertices_of_natAbs_det_eq_one`. -/
theorem natAbs_det_eq_one_of_memClosedTriangle_eq_vertices
    (a b c : ℤ × ℤ)
    (hne : latticeDet a b c ≠ 0)
    (h : ∀ p, MemClosedTriangle a b c p → p = a ∨ p = b ∨ p = c) :
    Int.natAbs (latticeDet a b c) = 1 :=
  natAbs_det_eq_one_of_memClosedTriangle_eq_vertices_of_edgeGcd a b c hne
    (edgeGcd_eq_one_of_memClosedTriangle_eq_vertices_of_det_ne_zero a b c hne h) h

/-- Bundled triangle form. -/
theorem IsDetPrimitive_of_memClosedTriangle_eq_vertices
    (t : Triangle)
    (hne : t.det ≠ 0)
    (h : ∀ p, MemClosedTriangle t.a t.b t.c p → p = t.a ∨ p = t.b ∨ p = t.c) :
    t.IsDetPrimitive :=
  natAbs_det_eq_one_of_memClosedTriangle_eq_vertices t.a t.b t.c hne h

end LatticeTriangle
end Picks
end EulersGem
