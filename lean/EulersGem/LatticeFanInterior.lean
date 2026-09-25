/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.Tactic
import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Segment
import EulersGem.LatticeTriangle
import EulersGem.LatticeTriangleEmpty
import EulersGem.LatticePolygon
import EulersGem.LatticeFan

/-!
# Interior-point fan (I = 1 Pick-form substrate)

Fan triangulation from an **interior** lattice point `q` to each boundary edge:
triangles `(q, vᵢ, vᵢ₊₁)`.

**Algebra:** for any apex `q`,
`∑ᵢ latticeDet(q, vᵢ, vᵢ₊₁) = shoelaceSum(P)`.

**I = 1 route (not classical Pick):**
if the fan triangles are positively oriented and empty of extra lattice points,
and boundary edges are primitive, then each `|det| = 1`, hence
`shoelace = n/2 = B/2 = 1 + B/2 − 1`.

**Geometric discharge (I = 1):**
`InteriorFanDetsPos` and `InteriorFanTrianglesEmpty` discharge from
`UniqueInterior q` + `StrictlyConvexCCW` + injective vertices + `PrimitiveEdges`.
Foreign vertices in an ear contradict the supporting half-plane at that vertex
(CCW edge functional strictly positive at the unique interior apex).

**I ∈ {0,1} Finset unification:**
`shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_one` packages empty + unique
interior into one Finset statement (`card ≤ 1`).

**I = 2 scaffold:** `TwoInterior`, fan positivity from either apex.
Fan covering of the second interior point + `InteriorFanTrianglesEmpty` failure
for I=2 are green. Ear inheritance / B-bookkeeping still open.

**Honesty / not classical Pick:**
Shoelace ≠ Haar/Lebesgue. General I > 1 triangulation existence open. EP→planar open.
See `PICKS_CLAUDE_AUDIT.md`.
-/

namespace EulersGem
namespace Picks
namespace LatticeFan
namespace InteriorFan

open LatticeTriangle
open LatticePolygon
open BigOperators

variable (P : LatticePolygon)

/-! ## Triangles from an apex -/

/-- Fan triangle from apex `q` across edge `i`. -/
def interiorFanTriangle (q : ℤ × ℤ) (i : Fin P.nVertices) : Triangle :=
  ⟨q, P.vertex i, P.vertex (P.nextIdx i)⟩

def interiorFanDet (q : ℤ × ℤ) (i : Fin P.nVertices) : ℤ :=
  (interiorFanTriangle P q i).det

/-- Strictly positive oriented interior-fan dets. -/
def InteriorFanDetsPos (q : ℤ × ℤ) : Prop :=
  ∀ i : Fin P.nVertices, 0 < interiorFanDet P q i

def InteriorFanDetsNonneg (q : ℤ × ℤ) : Prop :=
  ∀ i : Fin P.nVertices, 0 ≤ interiorFanDet P q i

lemma InteriorFanDetsNonneg_of_pos {q : ℤ × ℤ}
    (h : InteriorFanDetsPos P q) : InteriorFanDetsNonneg P q :=
  fun i => le_of_lt (h i)

/-- Each interior-fan triangle meets lattice points only at its three vertices. -/
def InteriorFanTrianglesEmpty (q : ℤ × ℤ) : Prop :=
  ∀ (i : Fin P.nVertices) (p : ℤ × ℤ),
    MemClosedTriangle (interiorFanTriangle P q i).a
      (interiorFanTriangle P q i).b (interiorFanTriangle P q i).c p →
    p = (interiorFanTriangle P q i).a ∨
      p = (interiorFanTriangle P q i).b ∨
        p = (interiorFanTriangle P q i).c

/-- Unique interior lattice point `q` (convex-hull interpretation of `I = 1`). -/
def UniqueInterior (q : ℤ × ℤ) : Prop :=
  q ∈ P.interiorLatticePoints ∧
    ∀ p ∈ P.interiorLatticePoints, p = q

/-! ## Algebraic identity: sum of interior-fan dets = shoelace sum -/

/-- **Any-apex algebraic fan identity.**
`∑ᵢ latticeDet(q, vᵢ, vᵢ₊₁) = shoelaceSum(P)`. -/
theorem sum_interiorFanDet_eq_shoelaceSum (q : ℤ × ℤ) :
    (∑ i : Fin P.nVertices, interiorFanDet P q i) = P.shoelaceSum := by
  classical
  have hcross := shoelaceSum_eq_sum_cross P
  have hexpand :
      ∀ i : Fin P.nVertices,
        interiorFanDet P q i =
          cross q (P.vertex i) + cross (P.vertex i) (P.vertex (P.nextIdx i)) +
            cross (P.vertex (P.nextIdx i)) q := by
    intro i
    simp only [interiorFanDet, interiorFanTriangle, Triangle.det]
    exact latticeDet_eq_cross_cycle q (P.vertex i) (P.vertex (P.nextIdx i))
  have hsum :
      (∑ i : Fin P.nVertices, interiorFanDet P q i) =
        (∑ i : Fin P.nVertices, cross q (P.vertex i)) +
          (∑ i : Fin P.nVertices, cross (P.vertex i) (P.vertex (P.nextIdx i))) +
            (∑ i : Fin P.nVertices, cross (P.vertex (P.nextIdx i)) q) := by
    simp only [hexpand, Finset.sum_add_distrib]
  have hshift :
      (∑ i : Fin P.nVertices, cross (P.vertex (P.nextIdx i)) q) =
        ∑ i : Fin P.nVertices, cross (P.vertex i) q := by
    -- Reindex by `nextIdx`, which is a bijection (inverse = `prevIdx`).
    refine Finset.sum_bij (fun i _ => P.nextIdx i) (fun _ _ => Finset.mem_univ _)
      (fun i _ j _ h => ?inj) (fun j _ => ?surj) (fun i _ => rfl)
    · -- injectivity of nextIdx
      have := congrArg P.prevIdx h
      simpa [P.prevIdx_nextIdx] using this
    · exact ⟨P.prevIdx j, Finset.mem_univ _, P.nextIdx_prevIdx j⟩
  have hcancel :
      (∑ i : Fin P.nVertices, cross q (P.vertex i)) +
        (∑ i : Fin P.nVertices, cross (P.vertex (P.nextIdx i)) q) = 0 := by
    have hneg : ∀ i, cross (P.vertex i) q = -cross q (P.vertex i) :=
      fun i => cross_anticomm (P.vertex i) q
    calc
      (∑ i : Fin P.nVertices, cross q (P.vertex i)) +
          (∑ i : Fin P.nVertices, cross (P.vertex (P.nextIdx i)) q)
          = (∑ i : Fin P.nVertices, cross q (P.vertex i)) +
              (∑ i : Fin P.nVertices, cross (P.vertex i) q) := by rw [hshift]
      _ = (∑ i : Fin P.nVertices, cross q (P.vertex i)) +
            (∑ i : Fin P.nVertices, -cross q (P.vertex i)) := by
              simp only [hneg]
      _ = (∑ i : Fin P.nVertices, cross q (P.vertex i)) +
            -(∑ i : Fin P.nVertices, cross q (P.vertex i)) := by
              simp only [Finset.sum_neg_distrib]
      _ = 0 := by ring
  calc
    (∑ i : Fin P.nVertices, interiorFanDet P q i)
        = (∑ i : Fin P.nVertices, cross q (P.vertex i)) +
            (∑ i : Fin P.nVertices, cross (P.vertex i) (P.vertex (P.nextIdx i))) +
              (∑ i : Fin P.nVertices, cross (P.vertex (P.nextIdx i)) q) := hsum
    _ = (∑ i : Fin P.nVertices, cross (P.vertex i) (P.vertex (P.nextIdx i))) +
          ((∑ i : Fin P.nVertices, cross q (P.vertex i)) +
            (∑ i : Fin P.nVertices, cross (P.vertex (P.nextIdx i)) q)) := by ring
    _ = (∑ i : Fin P.nVertices, cross (P.vertex i) (P.vertex (P.nextIdx i))) + 0 := by
          rw [hcancel]
    _ = P.shoelaceSum := by
          rw [hcross]; ring

/-! ## Primitivity from empty + positive orientation -/

def InteriorFanDetPrimitive (q : ℤ × ℤ) : Prop :=
  ∀ i : Fin P.nVertices, (interiorFanTriangle P q i).IsDetPrimitive

theorem InteriorFanDetPrimitive_of_empty
    {q : ℤ × ℤ}
    (hpos : InteriorFanDetsPos P q)
    (hempty : InteriorFanTrianglesEmpty P q) :
    InteriorFanDetPrimitive P q := by
  intro i
  exact IsDetPrimitive_of_memClosedTriangle_eq_vertices
    (interiorFanTriangle P q i) (ne_of_gt (hpos i)) (hempty i)

/-! ## Shoelace = n/2 under primitive interior fan -/

theorem sum_interiorFanDet_eq_n_of_primitive
    {q : ℤ × ℤ}
    (hpos : InteriorFanDetsPos P q)
    (hprim : InteriorFanDetPrimitive P q) :
    (∑ i : Fin P.nVertices, interiorFanDet P q i) = (P.nVertices : ℤ) := by
  classical
  have h1 : ∀ i : Fin P.nVertices, interiorFanDet P q i = 1 := by
    intro i
    have hnat : Int.natAbs (interiorFanDet P q i) = 1 := hprim i
    have hnn : 0 ≤ interiorFanDet P q i := le_of_lt (hpos i)
    -- 0 ≤ z and natAbs z = 1 ⇒ z = 1
    have hz : interiorFanDet P q i = (Int.natAbs (interiorFanDet P q i) : ℤ) :=
      (Int.natAbs_of_nonneg hnn).symm
    rw [hz, hnat]; norm_num
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem shoelaceSum_eq_n_of_interior_fan
    {q : ℤ × ℤ}
    (hpos : InteriorFanDetsPos P q)
    (hprim : InteriorFanDetPrimitive P q) :
    P.shoelaceSum = (P.nVertices : ℤ) := by
  rw [← sum_interiorFanDet_eq_shoelaceSum P q]
  exact sum_interiorFanDet_eq_n_of_primitive P hpos hprim

theorem shoelace_eq_n_div_two_of_interior_fan
    {q : ℤ × ℤ}
    (hpos : InteriorFanDetsPos P q)
    (hempty : InteriorFanTrianglesEmpty P q) :
    P.shoelace = (P.nVertices : ℚ) / 2 := by
  have hprim := InteriorFanDetPrimitive_of_empty P hpos hempty
  have hsum := shoelaceSum_eq_n_of_interior_fan P hpos hprim
  have hnat : Int.natAbs P.shoelaceSum = P.nVertices := by
    rw [hsum]; simp [Int.natAbs_natCast]
  change (Int.natAbs P.shoelaceSum : ℚ) / 2 = (P.nVertices : ℚ) / 2
  rw [hnat]

/-- **I = 1 shoelace Pick-form** under interior-fan primitivity hyps
(not classical Pick).

Given unique-interior bookkeeping `I = 1` (via the identity `1 + B/2 − 1 = B/2`),
primitive edges (`B = n`), and an empty positively oriented fan from an
interior apex: `shoelace = 1 + B/2 − 1`. -/
theorem shoelace_eq_one_add_B_div_two_sub_one_of_interior_fan
    {q : ℤ × ℤ}
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hpos : InteriorFanDetsPos P q)
    (hempty : InteriorFanTrianglesEmpty P q) :
    P.shoelace = (1 : ℚ) + (P.B : ℚ) / 2 - 1 := by
  have hB := B_eq_nVertices_of_primitive_edges P hedge hverts
  have harea := shoelace_eq_n_div_two_of_interior_fan P hpos hempty
  have hn : (P.nVertices : ℚ) / 2 = (1 : ℚ) + (P.nVertices : ℚ) / 2 - 1 := by ring
  calc
    P.shoelace = (P.nVertices : ℚ) / 2 := harea
    _ = (1 : ℚ) + (P.nVertices : ℚ) / 2 - 1 := hn
    _ = (1 : ℚ) + (P.B : ℚ) / 2 - 1 := by rw [hB]

/-- Same conclusion written as `I + B/2 − 1` with `I = 1`. -/
theorem shoelace_eq_I_add_B_div_two_sub_one_of_interior_fan
    {q : ℤ × ℤ}
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hpos : InteriorFanDetsPos P q)
    (hempty : InteriorFanTrianglesEmpty P q) :
    P.shoelace = (1 : ℚ) + (P.B : ℚ) / 2 - 1 :=
  shoelace_eq_one_add_B_div_two_sub_one_of_interior_fan P hverts hedge hpos hempty

/-! ## Primitive segment endpoints -/

lemma eq_endpoints_of_mem_segment_of_edgeGcd_eq_one
    (a b r : ℤ × ℤ) (hgcd : edgeGcd a b = 1)
    (h : toReal r ∈ segment ℝ (toReal a) (toReal b)) :
    r = a ∨ r = b := by
  classical
  rcases h with ⟨sa, sb, hsa, hsb, hsab, hr⟩
  have hr' :
      toReal r = toReal a + sb • (toReal b - toReal a) := by
    have hsb_split :
        sb • toReal b = sb • toReal a + sb • (toReal b - toReal a) := by
      rw [← smul_add, add_sub_cancel]
    calc
      toReal r = sa • toReal a + sb • toReal b := hr.symm
      _ = sa • toReal a + (sb • toReal a + sb • (toReal b - toReal a)) := by
            rw [hsb_split]
      _ = (sa + sb) • toReal a + sb • (toReal b - toReal a) := by
            rw [add_smul]; abel
      _ = toReal a + sb • (toReal b - toReal a) := by
            rw [hsab, one_smul]
  have hx : ((r.1 - a.1 : ℤ) : ℝ) = sb * ((b.1 - a.1 : ℤ) : ℝ) := by
    have hfst := congrArg Prod.fst hr'
    -- Unfold coordinate-wise: r = a + sb•(b-a)
    change (r.1 : ℝ) =
        (a.1 : ℝ) + sb * ((b.1 : ℝ) - (a.1 : ℝ)) at hfst
    have h' : (r.1 : ℝ) - (a.1 : ℝ) = sb * ((b.1 : ℝ) - (a.1 : ℝ)) := by linarith [hfst]
    simpa [Int.cast_sub] using h'
  have hy : ((r.2 - a.2 : ℤ) : ℝ) = sb * ((b.2 - a.2 : ℤ) : ℝ) := by
    have hsnd := congrArg Prod.snd hr'
    change (r.2 : ℝ) =
        (a.2 : ℝ) + sb * ((b.2 : ℝ) - (a.2 : ℝ)) at hsnd
    have h' : (r.2 : ℝ) - (a.2 : ℝ) = sb * ((b.2 : ℝ) - (a.2 : ℝ)) := by linarith [hsnd]
    simpa [Int.cast_sub] using h' 
  set n : ℤ :=
    Int.gcdA (b.1 - a.1) (b.2 - a.2) * (r.1 - a.1) +
      Int.gcdB (b.1 - a.1) (b.2 - a.2) * (r.2 - a.2) with hn_def
  have hbez :
      ((edgeGcd a b : ℤ) : ℝ) =
        ((b.1 - a.1 : ℤ) : ℝ) * (Int.gcdA (b.1 - a.1) (b.2 - a.2) : ℝ) +
          ((b.2 - a.2 : ℤ) : ℝ) * (Int.gcdB (b.1 - a.1) (b.2 - a.2) : ℝ) := by
    simpa [edgeGcd] using
      congrArg (fun z : ℤ => (z : ℝ)) (Int.gcd_eq_gcd_ab (b.1 - a.1) (b.2 - a.2))
  have hsb_eq : sb = (n : ℝ) := by
    have h1 : (1 : ℝ) =
        ((b.1 - a.1 : ℤ) : ℝ) * (Int.gcdA (b.1 - a.1) (b.2 - a.2) : ℝ) +
          ((b.2 - a.2 : ℤ) : ℝ) * (Int.gcdB (b.1 - a.1) (b.2 - a.2) : ℝ) := by
      simpa [hgcd] using hbez
    have : sb =
        (Int.gcdA (b.1 - a.1) (b.2 - a.2) : ℝ) * ((r.1 - a.1 : ℤ) : ℝ) +
          (Int.gcdB (b.1 - a.1) (b.2 - a.2) : ℝ) * ((r.2 - a.2 : ℤ) : ℝ) := by
      calc
        sb = sb * (1 : ℝ) := by ring
        _ = sb *
            (((b.1 - a.1 : ℤ) : ℝ) * (Int.gcdA (b.1 - a.1) (b.2 - a.2) : ℝ) +
              ((b.2 - a.2 : ℤ) : ℝ) * (Int.gcdB (b.1 - a.1) (b.2 - a.2) : ℝ)) := by
                  rw [h1]
        _ = (Int.gcdA (b.1 - a.1) (b.2 - a.2) : ℝ) * (sb * ((b.1 - a.1 : ℤ) : ℝ)) +
              (Int.gcdB (b.1 - a.1) (b.2 - a.2) : ℝ) * (sb * ((b.2 - a.2 : ℤ) : ℝ)) := by
                  ring
        _ = (Int.gcdA (b.1 - a.1) (b.2 - a.2) : ℝ) * ((r.1 - a.1 : ℤ) : ℝ) +
              (Int.gcdB (b.1 - a.1) (b.2 - a.2) : ℝ) * ((r.2 - a.2 : ℤ) : ℝ) := by
                  rw [hx, hy]
    have hrhs :
        (Int.gcdA (b.1 - a.1) (b.2 - a.2) : ℝ) * ((r.1 - a.1 : ℤ) : ℝ) +
            (Int.gcdB (b.1 - a.1) (b.2 - a.2) : ℝ) * ((r.2 - a.2 : ℤ) : ℝ) =
          (n : ℝ) := by
      simp only [hn_def]; push_cast; ring
    linarith
  have hn0 : 0 ≤ n := by exact_mod_cast (show (0 : ℝ) ≤ n from by simpa [hsb_eq] using hsb)
  have hn1 : n ≤ 1 := by
    have : sb ≤ 1 := by linarith [hsab, hsa]
    exact_mod_cast (show (n : ℝ) ≤ 1 from by simpa [hsb_eq] using this)
  have hn01 : n = 0 ∨ n = 1 := by
    have : n = 0 ∨ n = 1 ∨ n < 0 ∨ 1 < n := by omega
    rcases this with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (not_lt.mpr hn0 h).elim
    · exact (not_lt.mpr hn1 h).elim
  rcases hn01 with h0 | h1
  · left
    apply toReal_injective
    have hsb0 : sb = 0 := by simp [hsb_eq, h0]
    simpa [hsb0] using hr'
  · right
    apply toReal_injective
    have hsb1 : sb = 1 := by simp [hsb_eq, h1]
    have : toReal r = toReal b := by
      simp only [hr', hsb1, one_smul, add_sub_cancel]
    exact this

lemma latticeDet_eq_zero_of_mem_segment
    (a b p : ℤ × ℤ)
    (h : toReal p ∈ segment ℝ (toReal a) (toReal b)) :
    latticeDet a b p = 0 := by
  rcases h with ⟨sa, sb, hsa, hsb, hsab, hr⟩
  have hAi : detR (toReal a) (toReal b) (toReal a) = 0 := by dsimp [detR]; ring
  have hBi : detR (toReal a) (toReal b) (toReal b) = 0 := by dsimp [detR]; ring
  have hx : toReal p = sa • toReal a + sb • toReal b := hr.symm
  have hlin :
      detR (toReal a) (toReal b) (toReal p) =
        sa * detR (toReal a) (toReal b) (toReal a) +
          sb * detR (toReal a) (toReal b) (toReal b) := by
    have := detR_sum_smul (toReal a) (toReal b)
      (fun i : Fin 2 => ![sa, sb] i)
      (fun i : Fin 2 => ![toReal a, toReal b] i)
      (by simp [Fin.sum_univ_two, hsab])
    -- LHS of detR_sum_smul is detR a b (∑ w•z) = detR a b (sa•a+sb•b)
    have hsumz : ∑ i : Fin 2, ![sa, sb] i • ![toReal a, toReal b] i =
        sa • toReal a + sb • toReal b := by
      simp [Fin.sum_univ_two]
    simpa [hx, hsumz, Fin.sum_univ_two] using this
  have : detR (toReal a) (toReal b) (toReal p) = 0 := by simp [hlin, hAi, hBi]
  have : (latticeDet a b p : ℝ) = 0 := by simpa [detR_toReal] using this
  exact_mod_cast this

lemma latticeDet_cycle (a b c : ℤ × ℤ) :
    latticeDet a b c = latticeDet b c a := by
  unfold latticeDet; ring

lemma nextIdx_ne (i : Fin P.nVertices) : P.nextIdx i ≠ i := by
  intro h
  have hn : 3 ≤ P.nVertices := P.length_ge
  have hval : (i.val + 1) % P.nVertices = i.val := by
    simpa [LatticePolygon.nextIdx] using congrArg Fin.val h
  by_cases hlast : i.val + 1 = P.nVertices
  · rw [hlast, Nat.mod_self] at hval
    -- 0 = i.val and i.val + 1 = n ⇒ n = 1, contradicts n ≥ 3
    omega
  · have hlt : i.val + 1 < P.nVertices := by omega
    rw [Nat.mod_eq_of_lt hlt] at hval
    omega

theorem det_edge_nonneg_of_ConvexCCW_of_mem_hull
    (h : ConvexCCW P) {q : ℤ × ℤ}
    (hq : toReal q ∈ P.convexHullRegion) (i : Fin P.nVertices) :
    0 ≤ latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) q := by
  classical
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ :=
    (mem_convexHull_iff_exists_fintype (R := ℝ) (E := ℝ × ℝ)).1 hq
  set A := toReal (P.vertex i)
  set B := toReal (P.vertex (P.nextIdx i))
  have hφ_nonneg : ∀ j : Fin P.nVertices, 0 ≤ detR A B (toReal (P.vertex j)) := by
    intro j
    have hZ := h i j
    have : (0 : ℝ) ≤ (latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j) : ℝ) :=
      Int.cast_nonneg hZ
    simpa [A, B, detR_toReal] using this
  have hz' : ∀ k, ∃ j : Fin P.nVertices, z k = toReal (P.vertex j) := by
    intro k
    obtain ⟨p, hp, heq⟩ := (Set.mem_image _ _ _).1 (hz k)
    have hpV : p ∈ (Finset.univ : Finset (Fin P.nVertices)).image P.vertex := by
      rw [← vertexFinset_eq_univ_image P]; exact hp
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hpV
    exact ⟨j, by rw [← heq, ← hj]⟩
  have hφz : ∀ k, 0 ≤ detR A B (z k) := by
    intro k; obtain ⟨j, hj⟩ := hz' k; simpa [hj] using hφ_nonneg j
  have hφ_sum : detR A B (toReal q) = ∑ k, w k * detR A B (z k) := by
    have := detR_sum_smul A B w z hw1
    simpa [hsum] using this
  have hnn : 0 ≤ ∑ k, w k * detR A B (z k) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hw0 k) (hφz k)
  have hφq : 0 ≤ detR A B (toReal q) := by simpa [hφ_sum] using hnn
  have : (0 : ℝ) ≤ (latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) q : ℝ) := by
    simpa [A, B, detR_toReal] using hφq
  exact_mod_cast this

theorem mem_segment_of_det_eq_zero_of_mem_hull
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    {q : ℤ × ℤ} (hq : toReal q ∈ P.convexHullRegion) (i : Fin P.nVertices)
    (hdet : latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) q = 0) :
    toReal q ∈ segment ℝ (toReal (P.vertex i)) (toReal (P.vertex (P.nextIdx i))) := by
  classical
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ :=
    (mem_convexHull_iff_exists_fintype (R := ℝ) (E := ℝ × ℝ)).1 hq
  set A := toReal (P.vertex i)
  set B := toReal (P.vertex (P.nextIdx i))
  have hext := VerticesExtreme_of_strictlyConvexCCW P hsc hinj
  have hABne : A ≠ B := by
    intro h
    have hv : P.vertex i = P.vertex (P.nextIdx i) :=
      toReal_injective (by simpa [A, B] using h)
    exact (nextIdx_ne P i) (Eq.symm (hinj hv))
  have hφ_nonneg : ∀ j : Fin P.nVertices, 0 ≤ detR A B (toReal (P.vertex j)) := by
    intro j
    have hZ := hsc.1 i j
    have : (0 : ℝ) ≤ (latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j) : ℝ) :=
      Int.cast_nonneg hZ
    simpa [A, B, detR_toReal] using this
  have hz' : ∀ k, ∃ j : Fin P.nVertices, z k = toReal (P.vertex j) := by
    intro k
    obtain ⟨p, hp, heq⟩ := (Set.mem_image _ _ _).1 (hz k)
    have hpV : p ∈ (Finset.univ : Finset (Fin P.nVertices)).image P.vertex := by
      rw [← vertexFinset_eq_univ_image P]; exact hp
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hpV
    exact ⟨j, by rw [← heq, ← hj]⟩
  have hφz : ∀ k, 0 ≤ detR A B (z k) := by
    intro k; obtain ⟨j, hj⟩ := hz' k; simpa [hj] using hφ_nonneg j
  have hφ_sum : ∑ k, w k * detR A B (z k) = 0 := by
    have := detR_sum_smul A B w z hw1
    have h0 : detR A B (toReal q) = 0 := by
      simpa [A, B, detR_toReal] using congrArg (fun z : ℤ => (z : ℝ)) hdet
    simpa [hsum, h0] using this.symm
  have hφ_term : ∀ k, w k * detR A B (z k) = 0 := by
    intro k
    have hnn : ∀ k ∈ (Finset.univ : Finset ι), 0 ≤ w k * detR A B (z k) :=
      fun k _ => mul_nonneg (hw0 k) (hφz k)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hφ_sum k (Finset.mem_univ k)
  have hsupp : ∀ k, 0 < w k → z k = A ∨ z k = B := by
    intro k hwk
    have hdetz : detR A B (z k) = 0 :=
      (mul_eq_zero.mp (hφ_term k)).resolve_left (ne_of_gt hwk)
    obtain ⟨j, hj⟩ := hz' k
    have hdetj : latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j) = 0 := by
      have : (latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j) : ℝ) = 0 := by
        simpa [A, B, hj, detR_toReal] using hdetz
      exact_mod_cast this
    by_cases hij : j = i
    · exact Or.inl (by simp [hj, hij, A])
    · by_cases hijn : j = P.nextIdx i
      · exact Or.inr (by simp [hj, hijn, B])
      · exact (not_collinear_of_VerticesExtreme P hext hinj i (P.nextIdx i) j
            (nextIdx_ne P i).symm (Ne.symm hij) (Ne.symm hijn) hdetj).elim
  have hterm : ∀ k, w k • z k =
      (if z k = A then w k else 0) • A + (if z k = B then w k else 0) • B := by
    intro k
    by_cases hw : w k = 0
    · simp [hw]
    · have hwp : 0 < w k := lt_of_le_of_ne (hw0 k) (Ne.symm hw)
      rcases hsupp k hwp with hzA | hzB
      · rw [hzA]; simp [hABne]
      · rw [hzB]; simp [show ¬ B = A from fun h => hABne h.symm]
  have hsumAB :
      toReal q =
        (∑ k, if z k = A then w k else 0) • A +
          (∑ k, if z k = B then w k else 0) • B := by
    calc
      toReal q = ∑ k, w k • z k := hsum.symm
      _ = ∑ k, ((if z k = A then w k else 0) • A +
            (if z k = B then w k else 0) • B) := by
              refine Finset.sum_congr rfl fun k _ => hterm k
      _ = (∑ k, (if z k = A then w k else 0) • A) +
            (∑ k, (if z k = B then w k else 0) • B) := by
              simp only [Finset.sum_add_distrib]
      _ = (∑ k, if z k = A then w k else 0) • A +
            (∑ k, if z k = B then w k else 0) • B := by
              simp only [Finset.sum_smul]
  set wA := ∑ k, if z k = A then w k else 0
  set wB := ∑ k, if z k = B then w k else 0
  have hwA0 : 0 ≤ wA :=
    Finset.sum_nonneg fun k _ => by split_ifs <;> simp [hw0 k]
  have hwB0 : 0 ≤ wB :=
    Finset.sum_nonneg fun k _ => by split_ifs <;> simp [hw0 k]
  have hwAB1 : wA + wB = 1 := by
    have : wA + wB = ∑ k, w k := by
      dsimp [wA, wB]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hA : z k = A
      · -- z = A ≠ B
        simp [hA, hABne]
      · by_cases hB : z k = B
        · -- z = B ≠ A
          have hBA : ¬ B = A := fun h => hABne h.symm
          simp [hB, hBA]
        · by_cases hw : 0 < w k
          · exact (hsupp k hw).elim (fun h => (hA h).elim) (fun h => (hB h).elim)
          · have hw0' : w k = 0 := le_antisymm (le_of_not_gt hw) (hw0 k)
            simp [hA, hB, hw0']
    simpa [this] using hw1
  refine ⟨wA, wB, hwA0, hwB0, hwAB1, ?_⟩
  simpa [wA, wB] using hsumAB.symm

/-- **Discharge:** interior lattice point + strict CCW + primitive edges ⇒
positively oriented interior fan. -/
theorem InteriorFanDetsPos_of_mem_interior
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q : ℤ × ℤ}
    (hq : q ∈ P.interiorLatticePoints) :
    InteriorFanDetsPos P q := by
  intro i
  have hq_hull : toReal q ∈ P.convexHullRegion := hq.1
  have hq_not_bd : q ∉ P.boundaryLatticePoints := hq.2
  have hnn := det_edge_nonneg_of_ConvexCCW_of_mem_hull P hsc.1 hq_hull i
  have hcyc : interiorFanDet P q i =
      latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) q := by
    simp only [interiorFanDet, interiorFanTriangle, Triangle.det]
    exact latticeDet_cycle q _ _
  refine lt_of_le_of_ne (by simpa [hcyc] using hnn) ?_
  intro h0
  have hdet : latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) q = 0 := by
    simpa [hcyc] using h0.symm
  have hseg := mem_segment_of_det_eq_zero_of_mem_hull P hsc hinj hq_hull i hdet
  have hprim : edgeGcd (P.vertex i) (P.vertex (P.nextIdx i)) = 1 := by
    simpa [LatticePolygon.edgePair] using hedge i
  have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one
    (P.vertex i) (P.vertex (P.nextIdx i)) q hprim hseg
  have hvi_mem : P.vertex i ∈ P.vertices := by
    have : P.vertex i ∈ P.vertexFinset := by
      rw [vertexFinset_eq_univ_image]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    exact List.mem_toFinset.mp this
  have hvn_mem : P.vertex (P.nextIdx i) ∈ P.vertices := by
    have : P.vertex (P.nextIdx i) ∈ P.vertexFinset := by
      rw [vertexFinset_eq_univ_image]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    exact List.mem_toFinset.mp this
  have hbound : q ∈ P.boundaryLatticePoints := by
    rcases hend with rfl | rfl
    · exact P.vertices_mem_boundary hvi_mem
    · exact P.vertices_mem_boundary hvn_mem
  exact hq_not_bd hbound

theorem InteriorFanDetsPos_of_uniqueInterior
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q : ℤ × ℤ}
    (hU : UniqueInterior P q) :
    InteriorFanDetsPos P q :=
  InteriorFanDetsPos_of_mem_interior P hsc hinj hedge hU.1

/-! ## Partial empty-discharge + geometric I=1 export -/

theorem mem_convexHullRegion_of_memClosedTriangle_interiorFan
    {q : ℤ × ℤ} (hq : toReal q ∈ P.convexHullRegion) (i : Fin P.nVertices)
    {p : ℤ × ℤ}
    (hp : MemClosedTriangle (interiorFanTriangle P q i).a
      (interiorFanTriangle P q i).b (interiorFanTriangle P q i).c p) :
    toReal p ∈ P.convexHullRegion := by
  have htrip := mem_convexHull_of_memClosedTriangle _ _ _ _ hp
  have hvb : toReal (P.vertex i) ∈ P.convexHullRegion := by
    have : P.vertex i ∈ P.vertexFinset := by
      rw [vertexFinset_eq_univ_image]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    exact subset_convexHull ℝ _ (Set.mem_image_of_mem toReal this)
  have hvc : toReal (P.vertex (P.nextIdx i)) ∈ P.convexHullRegion := by
    have : P.vertex (P.nextIdx i) ∈ P.vertexFinset := by
      rw [vertexFinset_eq_univ_image]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    exact subset_convexHull ℝ _ (Set.mem_image_of_mem toReal this)
  have hsub :
      ({toReal (interiorFanTriangle P q i).a,
          toReal (interiorFanTriangle P q i).b,
          toReal (interiorFanTriangle P q i).c} : Set (ℝ × ℝ)) ⊆
        P.convexHullRegion := by
    intro x hx
    simp only [interiorFanTriangle, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hq
    · exact hvb
    · exact hvc
  exact convexHull_min hsub (convex_convexHull ℝ _) htrip

/-- Non-boundary lattice points in an interior-fan ear equal the unique interior
apex. -/
theorem eq_apex_of_mem_interiorFan_of_uniqueInterior
    {q : ℤ × ℤ} (hU : UniqueInterior P q) (i : Fin P.nVertices) {p : ℤ × ℤ}
    (hp : MemClosedTriangle (interiorFanTriangle P q i).a
      (interiorFanTriangle P q i).b (interiorFanTriangle P q i).c p)
    (hnotbd : p ∉ P.boundaryLatticePoints) :
    p = q := by
  have hq_hull : toReal q ∈ P.convexHullRegion := hU.1.1
  have hhull := mem_convexHullRegion_of_memClosedTriangle_interiorFan P hq_hull i hp
  have hint : p ∈ P.interiorLatticePoints := by
    refine ⟨?_, hnotbd⟩
    simpa [LatticePolygon.convexHullRegion,
      show (toReal : ℤ × ℤ → ℝ × ℝ) = Picks.toReal from rfl] using hhull
  exact hU.2 p hint

lemma detR_affine_combination3 (a b x y z : ℝ × ℝ) (α β γ : ℝ)
    (hsum : α + β + γ = 1) :
    detR a b (α • x + β • y + γ • z) =
      α * detR a b x + β * detR a b y + γ * detR a b z := by
  let w : Fin 3 → ℝ := ![α, β, γ]
  let zs : Fin 3 → ℝ × ℝ := ![x, y, z]
  have hw1 : ∑ i : Fin 3, w i = 1 := by
    simp [w, Fin.sum_univ_three, hsum]
  have hpts : ∑ i : Fin 3, w i • zs i = α • x + β • y + γ • z := by
    simp [w, zs, Fin.sum_univ_three]
  have hsum' := detR_sum_smul a b w zs hw1
  -- Rewrite both sides to the expanded form.
  have hrs : ∑ i : Fin 3, w i * detR a b (zs i) =
      α * detR a b x + β * detR a b y + γ * detR a b z := by
    simp [w, zs, Fin.sum_univ_three]
  simpa [hpts, hrs] using hsum'

/-- Supporting half-plane functional at vertex `j` (from the incoming edge). -/
lemma detR_prev_vertex_eq_zero (j : Fin P.nVertices) :
    detR (toReal (P.vertex (P.prevIdx j))) (toReal (P.vertex j))
      (toReal (P.vertex j)) = 0 := by
  simp [detR]; ring

lemma detR_prev_vertex_nonneg_of_ConvexCCW (h : ConvexCCW P)
    (j k : Fin P.nVertices) :
    0 ≤ detR (toReal (P.vertex (P.prevIdx j))) (toReal (P.vertex j))
      (toReal (P.vertex k)) := by
  have hZ := det_nonneg_prev_of_ConvexCCW P h j k
  have : (0 : ℝ) ≤
      (latticeDet (P.vertex (P.prevIdx j)) (P.vertex j) (P.vertex k) : ℝ) :=
    Int.cast_nonneg hZ
  simpa [detR_toReal] using this

lemma detR_prev_apex_pos_of_InteriorFanDetsPos {q : ℤ × ℤ}
    (hpos : InteriorFanDetsPos P q) (j : Fin P.nVertices) :
    0 < detR (toReal (P.vertex (P.prevIdx j))) (toReal (P.vertex j))
      (toReal q) := by
  have hpos' : 0 < interiorFanDet P q (P.prevIdx j) := hpos (P.prevIdx j)
  have hcyc : interiorFanDet P q (P.prevIdx j) =
      latticeDet (P.vertex (P.prevIdx j)) (P.vertex j) q := by
    simp only [interiorFanDet, interiorFanTriangle, Triangle.det, P.nextIdx_prevIdx]
    exact latticeDet_cycle q _ _
  have hZ : 0 < latticeDet (P.vertex (P.prevIdx j)) (P.vertex j) q := by
    simpa [hcyc] using hpos'
  have hR : (0 : ℝ) <
      (latticeDet (P.vertex (P.prevIdx j)) (P.vertex j) q : ℝ) :=
    Int.cast_pos.mpr hZ
  simpa [detR_toReal] using hR

/-- **Prize:** unique interior + strict CCW + primitive edges ⇒ each interior-fan
ear meets lattice points only at its three vertices.

Geometry: ear ⊂ hull; non-boundary points equal the unique apex; boundary points
are listed vertices (`PrimitiveEdges`); a foreign vertex in the ear would be a
convex combination involving `q`, contradicting the supporting half-plane at that
vertex (CCW functional vanishes at the vertex and is strictly positive at `q`). -/
theorem InteriorFanTrianglesEmpty_of_uniqueInterior
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q : ℤ × ℤ}
    (hU : UniqueInterior P q) :
    InteriorFanTrianglesEmpty P q := by
  classical
  intro i p hp
  by_cases hbd : p ∈ P.boundaryLatticePoints
  · -- Boundary: constructive boundary = vertex set under primitivity.
    have hbound := boundaryLatticePoints_eq_vertexFinset P hedge hinj
    have hpV : p ∈ P.vertexFinset := by simpa [hbound] using hbd
    have hpV' : p ∈ (Finset.univ : Finset (Fin P.nVertices)).image P.vertex := by
      rwa [← vertexFinset_eq_univ_image P]
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hpV'
    subst hj
    -- Same as an ear endpoint?
    by_cases hBi : P.vertex j = P.vertex i
    · exact Or.inr (Or.inl (by simpa [interiorFanTriangle] using hBi))
    · by_cases hCi : P.vertex j = P.vertex (P.nextIdx i)
      · exact Or.inr (Or.inr (by simpa [interiorFanTriangle] using hCi))
      · -- Foreign vertex in △(q, vᵢ, vᵢ₊₁): supporting half-plane contradiction.
        exfalso
        obtain ⟨α, β, γ, hα, hβ, hγ, hsum, heq⟩ := hp
        set A := toReal (P.vertex (P.prevIdx j))
        set B := toReal (P.vertex j)
        have hpos := InteriorFanDetsPos_of_uniqueInterior P hsc hinj hedge hU
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
                  γ • toReal (P.vertex (P.nextIdx i)) := by
            simpa [interiorFanTriangle] using heq.symm
          have haff := detR_affine_combination3 A B
            (toReal q) (toReal (P.vertex i)) (toReal (P.vertex (P.nextIdx i)))
            α β γ hsum
          -- heq' : toReal v_j = α•q+β•v_i+γ•v_next
          -- haff : detR A B (α•q+...) = α*detR A B q + ...
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
            -- RHS = φ(j) = 0
            have : α * detR A B (toReal q) +
                  β * detR A B (toReal (P.vertex i)) +
                    γ * detR A B (toReal (P.vertex (P.nextIdx i))) = 0 := by
              simpa [hφj] using hcomb.symm
            linarith
          have hαφ' : 0 ≤ α * detR A B (toReal q) :=
            mul_nonneg hα (le_of_lt hφq)
          have hαφ0 : α * detR A B (toReal q) = 0 := le_antisymm hαφ hαφ'
          exact (mul_eq_zero.mp hαφ0).resolve_right (ne_of_gt hφq)
        -- α = 0 ⇒ vertex j lies on the primitive edge (vᵢ, vᵢ₊₁).
        have hseg :
            toReal (P.vertex j) ∈
              segment ℝ (toReal (P.vertex i))
                (toReal (P.vertex (P.nextIdx i))) := by
          refine ⟨β, γ, hβ, hγ, ?_, ?_⟩
          · linarith [hsum, hα0]
          · have heq' :
                α • toReal (interiorFanTriangle P q i).a +
                    β • toReal (interiorFanTriangle P q i).b +
                      γ • toReal (interiorFanTriangle P q i).c =
                  toReal (P.vertex j) := heq
            simp only [interiorFanTriangle] at heq'
            simpa [hα0, zero_smul, zero_add] using heq' 
        have hprim : edgeGcd (P.vertex i) (P.vertex (P.nextIdx i)) = 1 := by
          simpa [LatticePolygon.edgePair] using hedge i
        have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one
          (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j) hprim hseg
        exact hend.elim (fun h => hBi h) (fun h => hCi h)
  · -- Non-boundary ⇒ unique apex.
    exact Or.inl
      (eq_apex_of_mem_interiorFan_of_uniqueInterior P hU i hp hbd)

/-- **I = 1 shoelace Pick-form** with `InteriorFanDetsPos` discharged from
`UniqueInterior` + `StrictlyConvexCCW` (not classical Pick).

Still takes `InteriorFanTrianglesEmpty` as an optional alternate hyp; prefer the
fully geometric form below. -/
theorem shoelace_eq_I_add_B_div_two_sub_one_of_uniqueInterior_of_empty
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hsc : StrictlyConvexCCW P)
    {q : ℤ × ℤ} (hU : UniqueInterior P q)
    (hempty : InteriorFanTrianglesEmpty P q) :
    P.shoelace = (1 : ℚ) + (P.B : ℚ) / 2 - 1 :=
  shoelace_eq_I_add_B_div_two_sub_one_of_interior_fan P hverts hedge
    (InteriorFanDetsPos_of_uniqueInterior P hsc hverts hedge hU) hempty

/-- **I = 1 shoelace Pick-form** with fan emptiness discharged from geometric hyps
(not classical Pick).

Hyps: injective vertices, primitive edges, `StrictlyConvexCCW`, unique interior
lattice point. Concludes `shoelace = 1 + B/2 − 1`. No `InteriorFanTrianglesEmpty`
hyp. Still shoelace ≠ Haar; classical Pick FAIL. -/
theorem shoelace_eq_I_add_B_div_two_sub_one_of_uniqueInterior
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hsc : StrictlyConvexCCW P)
    {q : ℤ × ℤ} (hU : UniqueInterior P q) :
    P.shoelace = (1 : ℚ) + (P.B : ℚ) / 2 - 1 :=
  shoelace_eq_I_add_B_div_two_sub_one_of_uniqueInterior_of_empty P hverts hedge hsc hU
    (InteriorFanTrianglesEmpty_of_uniqueInterior P hsc hverts hedge hU)

/-! ## I ∈ {0,1} Finset unification (not classical Pick)

Packages the empty-interior and unique-interior geometric discharges into a
single statement whose interior data is a `Finset` with `card ≤ 1`. This is the
API shape needed for a future general-`I` induction; it is **not** classical
Pick (shoelace ≠ Haar; triangulation existence for `I > 1` open).
-/

/-- **I ∈ {0,1} shoelace Pick-form** (not classical Pick).

Hyps: `↑S = interiorLatticePoints`, `S.card ≤ 1`, injective vertices, primitive
edges, `StrictlyConvexCCW`. Concludes `shoelace = #S + B/2 − 1`.

* `#S = 0` ⇒ empty-interior convex discharge.
* `#S = 1` ⇒ unique-interior fan discharge.

Still shoelace ≠ Haar/Lebesgue; classical Pick FAIL. -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_one
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hcard : S.card ≤ 1)
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hsc : StrictlyConvexCCW P) :
    P.shoelace = (S.card : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · -- I = 0
    have hSempty : S = ∅ := Finset.card_eq_zero.mp h0
    have hI : EmptyInterior P := by
      simpa [EmptyInterior, hSempty] using hS.symm
    have harea :=
      shoelace_eq_B_div_two_sub_one_of_empty_interior_convex P hverts hedge hI hsc
    calc
      P.shoelace = (P.B : ℚ) / 2 - 1 := harea
      _ = (0 : ℚ) + (P.B : ℚ) / 2 - 1 := by ring
      _ = (S.card : ℚ) + (P.B : ℚ) / 2 - 1 := by simp [h0]
  · -- I = 1
    have h1 : S.card = 1 := by omega
    obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp h1
    have hU : UniqueInterior P q := by
      refine ⟨?mem, ?uniq⟩
      · -- q is the unique listed interior point
        have : q ∈ (({q} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
          simp
        rwa [← hS]
      · intro p hp
        have hpS : p ∈ ({q} : Finset (ℤ × ℤ)) := by
          change p ∈ (({q} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))
          rwa [hS]
        simpa using hpS
    have harea :=
      shoelace_eq_I_add_B_div_two_sub_one_of_uniqueInterior P hverts hedge hsc hU
    simpa [h1] using harea

/-! ## I = 2 scaffolding (not classical Pick)

`InteriorFanDetsPos` already discharges from mere interior membership (no
uniqueness). For `I = 2`, fanning from one apex leaves the other interior point
inside some fan ear; closing Pick needs that ear’s triangle (or the leftover
polygon) to inherit an `I ≤ 1` statement. Covering / inheritance lemmas below;
full geometric `I = 2` discharge still open.
-/

/-- Exactly two distinct interior lattice points (set form). -/
def TwoInterior (q r : ℤ × ℤ) : Prop :=
  q ≠ r ∧ P.interiorLatticePoints = ({q, r} : Set (ℤ × ℤ))

theorem mem_interior_of_twoInterior_left {q r : ℤ × ℤ}
    (h : TwoInterior P q r) : q ∈ P.interiorLatticePoints := by
  rw [h.2]; simp

theorem mem_interior_of_twoInterior_right {q r : ℤ × ℤ}
    (h : TwoInterior P q r) : r ∈ P.interiorLatticePoints := by
  rw [h.2]; simp

/-- Fan orientation from either apex of a two-point interior (not uniqueness). -/
theorem InteriorFanDetsPos_of_twoInterior_left
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) :
    InteriorFanDetsPos P q :=
  InteriorFanDetsPos_of_mem_interior P hsc hinj hedge
    (mem_interior_of_twoInterior_left P h)

theorem InteriorFanDetsPos_of_twoInterior_right
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) :
    InteriorFanDetsPos P r :=
  InteriorFanDetsPos_of_mem_interior P hsc hinj hedge
    (mem_interior_of_twoInterior_right P h)

/-- Finset form of `TwoInterior` (API for inductive general-`I`). -/
theorem twoInterior_of_finset_card_two
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hcard : S.card = 2) :
    ∃ q r, TwoInterior P q r ∧ S = {q, r} := by
  classical
  obtain ⟨q, r, hne, rfl⟩ := Finset.card_eq_two.mp hcard
  refine ⟨q, r, ⟨hne, ?_⟩, rfl⟩
  -- Finset `{q,r}` coe equals the set `{q,r}` used by `TwoInterior`.
  simpa [Finset.coe_insert, Finset.coe_singleton] using hS.symm

/-! ### Fan covering (I = 2 substrate; not classical Pick)

Any hull lattice point lies in some closed interior-fan ear from an apex with
positive fan dets: sector sign-change around the apex + edge half-plane from
`ConvexCCW`. Specializes to the second point of `TwoInterior`. Consequently
`InteriorFanTrianglesEmpty` fails for `I = 2` (expected — the other interior
point sits in an ear). Ear inheritance / B-bookkeeping still open.
-/

lemma latticeDet_area_sum (q v w p : ℤ × ℤ) :
    latticeDet q v w =
      latticeDet v w p + latticeDet q p w + latticeDet q v p := by
  unfold latticeDet; ring

lemma latticeDet_area_barycentric_x (q v w p : ℤ × ℤ) :
    latticeDet q v w * p.1 =
      latticeDet v w p * q.1 + latticeDet q p w * v.1 + latticeDet q v p * w.1 := by
  simp only [latticeDet]; ring

lemma latticeDet_area_barycentric_y (q v w p : ℤ × ℤ) :
    latticeDet q v w * p.2 =
      latticeDet v w p * q.2 + latticeDet q p w * v.2 + latticeDet q v p * w.2 := by
  simp only [latticeDet]; ring

theorem memClosedTriangle_of_area_weights_nonneg
    (q v w p : ℤ × ℤ)
    (hD : 0 < latticeDet q v w)
    (hα : 0 ≤ latticeDet v w p)
    (hβ : 0 ≤ latticeDet q p w)
    (hγ : 0 ≤ latticeDet q v p) :
    MemClosedTriangle q v w p := by
  set α : ℝ := (latticeDet v w p : ℝ) / (latticeDet q v w : ℝ)
  set β : ℝ := (latticeDet q p w : ℝ) / (latticeDet q v w : ℝ)
  set γ : ℝ := (latticeDet q v p : ℝ) / (latticeDet q v w : ℝ)
  have hD0 : (latticeDet q v w : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  have hα0 : 0 ≤ α :=
    div_nonneg (by exact_mod_cast hα) (by exact_mod_cast (le_of_lt hD))
  have hβ0 : 0 ≤ β :=
    div_nonneg (by exact_mod_cast hβ) (by exact_mod_cast (le_of_lt hD))
  have hγ0 : 0 ≤ γ :=
    div_nonneg (by exact_mod_cast hγ) (by exact_mod_cast (le_of_lt hD))
  have hsum : α + β + γ = 1 := by
    dsimp [α, β, γ]
    have hsumℤ := latticeDet_area_sum q v w p
    have : ((latticeDet v w p : ℝ) + (latticeDet q p w : ℝ) + (latticeDet q v p : ℝ)) /
        (latticeDet q v w : ℝ) = 1 := by
      have rhs : ((latticeDet v w p : ℝ) + (latticeDet q p w : ℝ) + (latticeDet q v p : ℝ)) =
          (latticeDet q v w : ℝ) := by exact_mod_cast hsumℤ.symm
      rw [rhs, div_self hD0]
    convert this using 1; ring
  refine ⟨α, β, γ, hα0, hβ0, hγ0, hsum, ?_⟩
  apply Prod.ext
  · change α * (q.1 : ℝ) + β * (v.1 : ℝ) + γ * (w.1 : ℝ) = (p.1 : ℝ)
    dsimp [α, β, γ]
    have hid := congrArg (fun z : ℤ => (z : ℝ)) (latticeDet_area_barycentric_x q v w p)
    push_cast at hid
    have :
        ((latticeDet v w p : ℝ) * (q.1 : ℝ) + (latticeDet q p w : ℝ) * (v.1 : ℝ) +
          (latticeDet q v p : ℝ) * (w.1 : ℝ)) / (latticeDet q v w : ℝ) = (p.1 : ℝ) := by
      calc
        _ = ((latticeDet q v w : ℝ) * (p.1 : ℝ)) / (latticeDet q v w : ℝ) := by
              congr 1; linarith
        _ = (p.1 : ℝ) := by field_simp [hD0]
    convert this using 1; ring
  · change α * (q.2 : ℝ) + β * (v.2 : ℝ) + γ * (w.2 : ℝ) = (p.2 : ℝ)
    dsimp [α, β, γ]
    have hid := congrArg (fun z : ℤ => (z : ℝ)) (latticeDet_area_barycentric_y q v w p)
    push_cast at hid
    have :
        ((latticeDet v w p : ℝ) * (q.2 : ℝ) + (latticeDet q p w : ℝ) * (v.2 : ℝ) +
          (latticeDet q v p : ℝ) * (w.2 : ℝ)) / (latticeDet q v w : ℝ) = (p.2 : ℝ) := by
      calc
        _ = ((latticeDet q v w : ℝ) * (p.2 : ℝ)) / (latticeDet q v w : ℝ) := by
              congr 1; linarith
        _ = (p.2 : ℝ) := by field_simp [hD0]
    convert this using 1; ring

lemma detR_swap_right (a b c : ℝ × ℝ) : detR a b c = -detR a c b := by
  dsimp [detR]; ring

lemma detR_sum_smul_middle {ι : Type*} [Fintype ι]
    (q p : ℝ × ℝ) (w : ι → ℝ) (z : ι → ℝ × ℝ) (hw1 : ∑ i, w i = 1) :
    detR q (∑ i, w i • z i) p = ∑ i, w i * detR q (z i) p := by
  have h := detR_sum_smul q p w z hw1
  calc
    detR q (∑ i, w i • z i) p
        = -detR q p (∑ i, w i • z i) := by rw [detR_swap_right]
    _ = -∑ i, w i * detR q p (z i) := by rw [h]
    _ = ∑ i, -(w i * detR q p (z i)) := by rw [Finset.sum_neg_distrib]
    _ = ∑ i, w i * (-detR q p (z i)) := by simp only [mul_neg]
    _ = ∑ i, w i * detR q (z i) p := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← detR_swap_right]

lemma nextIdx_iterate_val (i : Fin P.nVertices) (k : ℕ) :
    ((fun j => P.nextIdx j)^[k] i).val = (i.val + k) % P.nVertices := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
      have hnext :
          (P.nextIdx ((fun j => P.nextIdx j)^[k] i)).val =
            (((fun j => P.nextIdx j)^[k] i).val + 1) % P.nVertices := rfl
      rw [Function.iterate_succ_apply', hnext, ih, Nat.mod_add_mod, Nat.add_assoc]

lemma nextIdx_iterate_nVertices (i : Fin P.nVertices) :
    ((fun j => P.nextIdx j)^[P.nVertices] i) = i := by
  apply Fin.ext
  rw [nextIdx_iterate_val, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

lemma nextIdx_iterate_hits (i0 j : Fin P.nVertices) :
    ∃ k < P.nVertices, ((fun t => P.nextIdx t)^[k] i0) = j := by
  refine ⟨(j.val + P.nVertices - i0.val) % P.nVertices,
    Nat.mod_lt _ P.nVertices_pos, Fin.ext ?_⟩
  rw [nextIdx_iterate_val]
  have hj : j.val < P.nVertices := j.isLt
  have hi : i0.val < P.nVertices := i0.isLt
  have hmod := Nat.add_mod_mod i0.val (j.val + P.nVertices - i0.val) P.nVertices
  have hsum : i0.val + (j.val + P.nVertices - i0.val) = j.val + P.nVertices := by omega
  rw [hmod, hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hj]

lemma exists_cyclic_nonneg_nonpos_transition (f : Fin P.nVertices → ℝ)
    (hge : ∃ i, 0 ≤ f i) (hle : ∃ i, f i ≤ 0) :
    ∃ i, 0 ≤ f i ∧ f (P.nextIdx i) ≤ 0 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨i0, hi0⟩ := hge
  have step : ∀ i, 0 ≤ f i → 0 < f (P.nextIdx i) := fun i hi => h i hi
  have grow_pos : ∀ k, 1 ≤ k → 0 < f ((fun j => P.nextIdx j)^[k] i0) := by
    intro k hk
    induction k with
    | zero =>
        exact (Nat.not_succ_le_zero 0 hk).elim
    | succ k ih =>
        cases k with
        | zero =>
            simpa [Function.iterate_succ_apply'] using step i0 hi0
        | succ k' =>
            have hpos := ih (Nat.succ_le_succ (Nat.zero_le _))
            have hnn : 0 ≤ f ((fun j => P.nextIdx j)^[k' + 1] i0) := le_of_lt hpos
            simpa [Function.iterate_succ_apply'] using step _ hnn
  have hi0_pos : 0 < f i0 := by
    have hn : 1 ≤ P.nVertices := Nat.succ_le_of_lt P.nVertices_pos
    simpa [nextIdx_iterate_nVertices] using grow_pos P.nVertices hn
  have all_pos : ∀ j, 0 < f j := by
    intro j
    obtain ⟨k, _, hk⟩ := nextIdx_iterate_hits P i0 j
    by_cases hk0 : k = 0
    · subst hk0
      -- iterate 0 i0 = i0 = j
      have : j = i0 := by simpa using hk.symm
      simpa [this] using hi0_pos
    · have hpos := grow_pos k (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0))
      exact hk ▸ hpos
  obtain ⟨ineg, hineg⟩ := hle
  exact (not_lt.mpr hineg) (all_pos ineg)

theorem exists_mem_interiorFanTriangle_of_mem_hull
    (hsc : StrictlyConvexCCW P)
    {q : ℤ × ℤ} (hpos : InteriorFanDetsPos P q)
    {p : ℤ × ℤ} (hp : toReal p ∈ P.convexHullRegion) :
    ∃ i : Fin P.nVertices,
      MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) p := by
  classical
  set fℤ : Fin P.nVertices → ℤ := fun i => latticeDet q (P.vertex i) p
  set f : Fin P.nVertices → ℝ := fun i => (fℤ i : ℝ)
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ :=
    (mem_convexHull_iff_exists_fintype (R := ℝ) (E := ℝ × ℝ)).1 hp
  have hz' : ∀ k, ∃ j : Fin P.nVertices, z k = toReal (P.vertex j) := by
    intro k
    obtain ⟨pt, hpt, heq⟩ := (Set.mem_image _ _ _).1 (hz k)
    have hpV : pt ∈ (Finset.univ : Finset (Fin P.nVertices)).image P.vertex := by
      rw [← vertexFinset_eq_univ_image P]; exact hpt
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hpV
    exact ⟨j, by rw [← heq, ← hj]⟩
  have hsumf : ∑ k, w k * detR (toReal q) (z k) (toReal p) = 0 := by
    have hlin := detR_sum_smul_middle (toReal q) (toReal p) w z hw1
    have hqp : detR (toReal q) (toReal p) (toReal p) = 0 := by dsimp [detR]; ring
    calc
      ∑ k, w k * detR (toReal q) (z k) (toReal p)
          = detR (toReal q) (∑ k, w k • z k) (toReal p) := hlin.symm
      _ = detR (toReal q) (toReal p) (toReal p) := by rw [hsum]
      _ = 0 := hqp
  have hfz : ∀ k, ∃ j, z k = toReal (P.vertex j) ∧
      detR (toReal q) (z k) (toReal p) = f j := by
    intro k
    obtain ⟨j, hj⟩ := hz' k
    refine ⟨j, hj, ?_⟩
    simp [f, fℤ, hj, detR_toReal]
  have exists_pos_weight : ∃ k, 0 < w k := by
    by_contra hnone
    push Not at hnone
    have : ∑ k, w k = 0 :=
      Finset.sum_eq_zero fun k _ => le_antisymm (hnone k) (hw0 k)
    linarith [hw1]
  have not_all_pos : ¬ ∀ i, 0 < f i := by
    intro hall
    obtain ⟨k0, hk0⟩ := exists_pos_weight
    obtain ⟨j0, _, hjeq⟩ := hfz k0
    set g : ι → ℝ := fun k => w k * detR (toReal q) (z k) (toReal p)
    have hterm : ∀ k, 0 ≤ g k := by
      intro k
      obtain ⟨j, _, heq⟩ := hfz k
      exact mul_nonneg (hw0 k) (le_of_lt (by simpa [heq] using hall j))
    have hg0 : 0 < g k0 :=
      mul_pos hk0 (by simpa [hjeq] using hall j0)
    have hdecomp : ∑ k, g k = ∑ k ∈ Finset.univ.erase k0, g k + g k0 :=
      (Finset.sum_erase_add (s := Finset.univ) g (Finset.mem_univ k0)).symm
    have hrest : 0 ≤ ∑ k ∈ Finset.univ.erase k0, g k :=
      Finset.sum_nonneg fun k _ => hterm k
    have hsumpos : 0 < ∑ k, g k := by linarith [hdecomp, hg0, hrest]
    change 0 < ∑ k, w k * detR (toReal q) (z k) (toReal p) at hsumpos
    linarith [hsumf]
  have not_all_neg : ¬ ∀ i, f i < 0 := by
    intro hall
    obtain ⟨k0, hk0⟩ := exists_pos_weight
    obtain ⟨j0, _, hjeq⟩ := hfz k0
    set g : ι → ℝ := fun k => w k * detR (toReal q) (z k) (toReal p)
    have hterm : ∀ k, g k ≤ 0 := by
      intro k
      obtain ⟨j, _, heq⟩ := hfz k
      exact mul_nonpos_of_nonneg_of_nonpos (hw0 k)
        (le_of_lt (by simpa [heq] using hall j))
    have hg0 : g k0 < 0 :=
      mul_neg_of_pos_of_neg hk0 (by simpa [hjeq] using hall j0)
    have hdecomp : ∑ k, g k = ∑ k ∈ Finset.univ.erase k0, g k + g k0 :=
      (Finset.sum_erase_add (s := Finset.univ) g (Finset.mem_univ k0)).symm
    have hrest : ∑ k ∈ Finset.univ.erase k0, g k ≤ 0 :=
      Finset.sum_nonpos fun k _ => hterm k
    have hsumneg : ∑ k, g k < 0 := by linarith [hdecomp, hg0, hrest]
    change ∑ k, w k * detR (toReal q) (z k) (toReal p) < 0 at hsumneg
    linarith [hsumf]
  have hge : ∃ i, 0 ≤ f i := by
    by_contra hnone; push Not at hnone; exact not_all_neg hnone
  have hle : ∃ i, f i ≤ 0 := by
    by_contra hnone; push Not at hnone; exact not_all_pos hnone
  obtain ⟨i, hi_ge, hi_le⟩ := exists_cyclic_nonneg_nonpos_transition P f hge hle
  have hγ : 0 ≤ latticeDet q (P.vertex i) p := by
    have : 0 ≤ (fℤ i : ℝ) := by simpa [f, fℤ] using hi_ge
    exact_mod_cast this
  have hβ : 0 ≤ latticeDet q p (P.vertex (P.nextIdx i)) := by
    have hfn : (fℤ (P.nextIdx i) : ℝ) ≤ 0 := by simpa [f, fℤ] using hi_le
    have hfnZ : latticeDet q (P.vertex (P.nextIdx i)) p ≤ 0 := by exact_mod_cast hfn
    have hswap : latticeDet q p (P.vertex (P.nextIdx i)) =
        -latticeDet q (P.vertex (P.nextIdx i)) p := by unfold latticeDet; ring
    linarith
  have hα : 0 ≤ latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) p :=
    det_edge_nonneg_of_ConvexCCW_of_mem_hull P hsc.1 hp i
  have hD : 0 < latticeDet q (P.vertex i) (P.vertex (P.nextIdx i)) := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hpos i
  exact ⟨i, memClosedTriangle_of_area_weights_nonneg q (P.vertex i)
    (P.vertex (P.nextIdx i)) p hD hα hβ hγ⟩

theorem exists_mem_interiorFanTriangle_of_twoInterior
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) :
    ∃ i : Fin P.nVertices,
      MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r :=
  exists_mem_interiorFanTriangle_of_mem_hull P hsc
    (InteriorFanDetsPos_of_twoInterior_left P hsc hinj hedge h)
    (mem_interior_of_twoInterior_right P h).1

theorem not_InteriorFanTrianglesEmpty_of_twoInterior
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) :
    ¬ InteriorFanTrianglesEmpty P q := by
  classical
  intro hempty
  obtain ⟨i, hi⟩ := exists_mem_interiorFanTriangle_of_twoInterior P hsc hinj hedge h
  have hmem := hempty i r (by simpa [interiorFanTriangle] using hi)
  have hr_int := mem_interior_of_twoInterior_right P h
  have hr_not_bd : r ∉ P.boundaryLatticePoints := hr_int.2
  have hq_ne : q ≠ r := h.1
  have hv_bd : ∀ j : Fin P.nVertices, P.vertex j ∈ P.boundaryLatticePoints := by
    intro j
    have : P.vertex j ∈ P.vertexFinset := by
      rw [vertexFinset_eq_univ_image]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
  rcases hmem with h1 | h2 | h3
  · exact hq_ne h1.symm
  · exact hr_not_bd (by simpa [interiorFanTriangle, h2] using hv_bd i)
  · exact hr_not_bd (by simpa [interiorFanTriangle, h3] using hv_bd (P.nextIdx i))

/-! ### Remaining I > 1 checklist (honest)

Still open on this spine (classical Pick FAIL):

1. ~~Fan covering~~: **green** — `exists_mem_interiorFanTriangle_of_mem_hull` /
   `exists_mem_interiorFanTriangle_of_twoInterior`; also
   `not_InteriorFanTrianglesEmpty_of_twoInterior`.
2. Ear inheritance: an ear triangle `(q, vᵢ, vᵢ₊₁)` carrying exactly one leftover
   interior point is a `LatticePolygon` with `UniqueInterior` / `StrictlyConvexCCW`
   / primitive ear edges, so I=1 applies; empty ears are det-primitive.
3. Bookkeeping: sum of ear shoelaces = polygon shoelace (already have the det-sum
   identity); convert ear `B` counts on shared apex-spokes into global `B`.
4. Shoelace = Haar/Lebesgue; EP → planar Euler.

The Finset `I ≤ 1` theorem above is the base of that induction.
-/

end InteriorFan
end LatticeFan
end Picks
end EulersGem
