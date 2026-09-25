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
`InteriorFanDetsPos` discharges from `UniqueInterior q` + `StrictlyConvexCCW` +
injective vertices + `PrimitiveEdges`. Non-boundary points in fan ears equal the
unique apex. Full `InteriorFanTrianglesEmpty` (foreign-vertex extremality) open.

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
apex. Foreign-vertex emptiness (boundary case) still needs extremality
renormalization — see audit. -/
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

/-- **I = 1 shoelace Pick-form** with `InteriorFanDetsPos` discharged from
`UniqueInterior` + `StrictlyConvexCCW` (not classical Pick).

Still takes `InteriorFanTrianglesEmpty` (foreign-vertex extremality open). -/
theorem shoelace_eq_I_add_B_div_two_sub_one_of_uniqueInterior_of_empty
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hsc : StrictlyConvexCCW P)
    {q : ℤ × ℤ} (hU : UniqueInterior P q)
    (hempty : InteriorFanTrianglesEmpty P q) :
    P.shoelace = (1 : ℚ) + (P.B : ℚ) / 2 - 1 :=
  shoelace_eq_I_add_B_div_two_sub_one_of_interior_fan P hverts hedge
    (InteriorFanDetsPos_of_uniqueInterior P hsc hverts hedge hU) hempty

/-! ## I > 1 gap (honest)

A fan from a single interior lattice point, when `I > 1`, leaves polygonal cells
that still contain interior lattice points. Closing Pick for general `I` needs a
recursive / multi-apex triangulation existence theorem (open on this spine).
-/


end InteriorFan
end LatticeFan
end Picks
end EulersGem
