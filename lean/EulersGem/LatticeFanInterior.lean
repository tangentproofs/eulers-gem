/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.Tactic
import Mathlib.Data.Rat.Defs
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

Honesty: `InteriorFanTrianglesEmpty` / `InteriorFanDetsPos` are geometric hyps
(discharge from `UniqueInterior` + `StrictlyConvexCCW` is partial / open).
Shoelace ≠ Haar; general I > 1 triangulation existence open.
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

end InteriorFan
end LatticeFan
end Picks
end EulersGem
