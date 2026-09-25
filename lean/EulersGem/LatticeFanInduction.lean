/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.OnSpoke

/-!
# I ≤ 2 Finset unification + I ≥ 3 induction scaffold (not classical Pick)

Packages `I ∈ {0,1,2}` into one Finset shoelace Pick-form, then starts the
`I ≥ 3` induction substrate: `ThreeInterior`, ear lattice classification for a
general interior apex, empty-ear `|det|=1`, and an honest `card = 3` Pick-form
under two distinct off-boundary occupied ears (each inheriting `UniqueInterior`),
with ear-uniqueness discharged from general OffBoundary cone arguments.

**Honesty / not classical Pick:**
Shoelace ≠ Haar/Lebesgue. EP→planar open. General I induction open.
Same-ear Off occupation reuses I=2 on the ear triangle. Unified Off I=3
(two-ear ∨ same-ear) and Finset `card=3` under Off-apex hyp are green.
On-spoke I=3: classification + `edgeGcd=2` + one-on-spoke/Off-nonadjacent
Pick-form green; same-spoke `edgeGcd=3` + adjacent `det=3` + Pick-form green;
unified Finset card=3 under covered (Off ∨ onSpoke-Off ∨ sameSpoke ∨ Off-adj-left/right) hyp green.
Two-spoke / Off-free Finset card=3 still open.
Classical Pick FAIL. See `PICKS_CLAUDE_AUDIT.md`.
-/

namespace EulersGem
namespace Picks
namespace LatticeFan
namespace InteriorFan

open LatticeTriangle
open LatticePolygon
open BigOperators

variable (P : LatticePolygon)

/-! ## I ≤ 2 Finset unification -/

/-- **I ∈ {0,1,2} shoelace Pick-form** (not classical Pick).

Hyps: `↑S = interiorLatticePoints`, `S.card ≤ 2`, injective vertices, primitive
edges, `StrictlyConvexCCW`. Concludes `shoelace = #S + B/2 − 1`.

* `#S ≤ 1` ⇒ `shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_one`
* `#S = 2` ⇒ `TwoInterior` + unified Off/on-spoke I=2 Pick-form

Still shoelace ≠ Haar; classical Pick FAIL. -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_two
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hcard : S.card ≤ 2)
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hsc : StrictlyConvexCCW P) :
    P.shoelace = (S.card : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  by_cases hle1 : S.card ≤ 1
  · exact shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_one
      P S hS hle1 hverts hedge hsc
  · have h2 : S.card = 2 := by omega
    obtain ⟨q, r, hTwo, _hSeq⟩ := twoInterior_of_finset_card_two P S hS h2
    have harea :=
      shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior P hsc hverts hedge hTwo
    calc
      P.shoelace = (2 : ℚ) + (P.B : ℚ) / 2 - 1 := harea
      _ = (S.card : ℚ) + (P.B : ℚ) / 2 - 1 := by simp [h2]

/-! ## I = 3 scaffolding (not classical Pick) -/

/-- Exactly three distinct interior lattice points (set form). -/
def ThreeInterior (q r s : ℤ × ℤ) : Prop :=
  q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
    P.interiorLatticePoints = ({q, r, s} : Set (ℤ × ℤ))

theorem mem_interior_of_threeInterior_apex {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) : q ∈ P.interiorLatticePoints := by
  rw [h.2.2.2]; simp

theorem mem_interior_of_threeInterior_left {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) : r ∈ P.interiorLatticePoints := by
  rw [h.2.2.2]; simp

theorem mem_interior_of_threeInterior_right {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) : s ∈ P.interiorLatticePoints := by
  rw [h.2.2.2]; simp

/-- Fan orientation from the apex of a three-point interior. -/
theorem InteriorFanDetsPos_of_threeInterior
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) :
    InteriorFanDetsPos P q :=
  InteriorFanDetsPos_of_mem_interior P hsc hinj hedge
    (mem_interior_of_threeInterior_apex P h)

/-- Finset form of `ThreeInterior` (API for inductive general-`I`). -/
theorem threeInterior_of_finset_card_three
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hcard : S.card = 3) :
    ∃ q r s, ThreeInterior P q r s ∧ S = {q, r, s} := by
  classical
  obtain ⟨q, r, s, hqr, hqs, hrs, rfl⟩ := Finset.card_eq_three.mp hcard
  refine ⟨q, r, s, ⟨hqr, hqs, hrs, ?_⟩, rfl⟩
  simpa [Finset.coe_insert, Finset.coe_singleton] using hS.symm

/-- Covering ear for either non-apex interior point of `ThreeInterior`. -/
theorem exists_mem_interiorFanTriangle_of_threeInterior_left
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) :
    ∃ i : Fin P.nVertices,
      MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r :=
  exists_mem_interiorFanTriangle_of_mem_hull P hsc
    (InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h)
    (mem_interior_of_threeInterior_left P h).1

theorem exists_mem_interiorFanTriangle_of_threeInterior_right
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) :
    ∃ i : Fin P.nVertices,
      MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) s :=
  exists_mem_interiorFanTriangle_of_mem_hull P hsc
    (InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h)
    (mem_interior_of_threeInterior_right P h).1

/-! ### Ear lattice classification for a general interior apex -/

/-- Lattice points of an interior-fan ear from an interior apex are among the
three ear vertices and the remaining interior lattice points of `P`. -/
theorem eq_vertices_or_interior_of_mem_interiorFan
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q : ℤ × ℤ}
    (hq : q ∈ P.interiorLatticePoints) (i : Fin P.nVertices) {p : ℤ × ℤ}
    (hp : MemClosedTriangle (interiorFanTriangle P q i).a
      (interiorFanTriangle P q i).b (interiorFanTriangle P q i).c p) :
    p = q ∨ p = P.vertex i ∨ p = P.vertex (P.nextIdx i) ∨
      p ∈ P.interiorLatticePoints := by
  classical
  by_cases hbd : p ∈ P.boundaryLatticePoints
  · -- Boundary: constructive boundary = vertex set under primitivity.
    have hbound := boundaryLatticePoints_eq_vertexFinset P hedge hinj
    have hpV : p ∈ P.vertexFinset := by simpa [hbound] using hbd
    have hpV' : p ∈ (Finset.univ : Finset (Fin P.nVertices)).image P.vertex := by
      rwa [← vertexFinset_eq_univ_image P]
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hpV'
    subst hj
    by_cases hBi : P.vertex j = P.vertex i
    · exact Or.inr (Or.inl (by simpa [interiorFanTriangle] using hBi))
    · by_cases hCi : P.vertex j = P.vertex (P.nextIdx i)
      · exact Or.inr (Or.inr (Or.inl (by simpa [interiorFanTriangle] using hCi)))
      · -- Foreign vertex in △(q, vᵢ, vᵢ₊₁): supporting half-plane contradiction.
        exfalso
        obtain ⟨α, β, γ, hα, hβ, hγ, hsum, heq⟩ := hp
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
                  γ • toReal (P.vertex (P.nextIdx i)) := by
            simpa [interiorFanTriangle] using heq.symm
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
  · -- Non-boundary ⇒ interior of P (or already a vertex of the ear via hull).
    have hq_hull : toReal q ∈ P.convexHullRegion := hq.1
    have hhull :=
      mem_convexHullRegion_of_memClosedTriangle_interiorFan P hq_hull i hp
    refine Or.inr (Or.inr (Or.inr ?_))
    refine ⟨?_, hbd⟩
    simpa [LatticePolygon.convexHullRegion,
      show (toReal : ℤ × ℤ → ℝ × ℝ) = Picks.toReal from rfl] using hhull

/-- Ears containing no other interior point of `P` meet lattice points only at
the three ear vertices. -/
theorem eq_vertices_of_mem_interiorFan_of_no_other_interior
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q : ℤ × ℤ}
    (hq : q ∈ P.interiorLatticePoints) (i : Fin P.nVertices)
    (hempty : ∀ p ∈ P.interiorLatticePoints, p ≠ q →
      ¬ MemClosedTriangle (interiorFanTriangle P q i).a
        (interiorFanTriangle P q i).b (interiorFanTriangle P q i).c p)
    {p : ℤ × ℤ}
    (hp : MemClosedTriangle (interiorFanTriangle P q i).a
      (interiorFanTriangle P q i).b (interiorFanTriangle P q i).c p) :
    p = q ∨ p = P.vertex i ∨ p = P.vertex (P.nextIdx i) := by
  rcases eq_vertices_or_interior_of_mem_interiorFan P hsc hinj hedge hq i hp with
    h1 | h2 | h3 | hint
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)
  · by_cases hpq : p = q
    · exact Or.inl hpq
    · exact (hempty p hint hpq hp).elim

/-- Empty (of other interior points) interior-fan ears are det-primitive. -/
theorem IsDetPrimitive_interiorFan_of_no_other_interior
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q : ℤ × ℤ}
    (hq : q ∈ P.interiorLatticePoints) (i : Fin P.nVertices)
    (hempty : ∀ p ∈ P.interiorLatticePoints, p ≠ q →
      ¬ MemClosedTriangle (interiorFanTriangle P q i).a
        (interiorFanTriangle P q i).b (interiorFanTriangle P q i).c p) :
    (interiorFanTriangle P q i).IsDetPrimitive := by
  have hpos := InteriorFanDetsPos_of_mem_interior P hsc hinj hedge hq
  refine IsDetPrimitive_of_memClosedTriangle_eq_vertices
    (interiorFanTriangle P q i) (ne_of_gt (hpos i)) ?_
  intro p hp
  simpa [interiorFanTriangle] using
    eq_vertices_of_mem_interiorFan_of_no_other_interior
      P hsc hinj hedge hq i hempty hp

/-- Empty (of other interior points) ears have determinant exactly `1`. -/
theorem interiorFanDet_eq_one_of_no_other_interior
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q : ℤ × ℤ}
    (hq : q ∈ P.interiorLatticePoints) (i : Fin P.nVertices)
    (hempty : ∀ p ∈ P.interiorLatticePoints, p ≠ q →
      ¬ MemClosedTriangle (interiorFanTriangle P q i).a
        (interiorFanTriangle P q i).b (interiorFanTriangle P q i).c p) :
    interiorFanDet P q i = 1 := by
  have hpos := InteriorFanDetsPos_of_mem_interior P hsc hinj hedge hq
  have hprim :=
    IsDetPrimitive_interiorFan_of_no_other_interior P hsc hinj hedge hq i hempty
  have hnat : Int.natAbs (interiorFanDet P q i) = 1 := hprim
  have hnn : 0 ≤ interiorFanDet P q i := le_of_lt (hpos i)
  have hz : interiorFanDet P q i = (Int.natAbs (interiorFanDet P q i) : ℤ) :=
    (Int.natAbs_of_nonneg hnn).symm
  rw [hz, hnat]; norm_num

/-! ### ThreeInterior: occupied-ear UniqueInterior inheritance -/

/-- Under `ThreeInterior`, lattice points of a fan ear from `q` are among
`{q, vᵢ, vᵢ₊₁, r, s}`. -/
theorem eq_vertices_or_rs_of_mem_interiorFan_of_threeInterior
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (i : Fin P.nVertices) {p : ℤ × ℤ}
    (hp : MemClosedTriangle (interiorFanTriangle P q i).a
      (interiorFanTriangle P q i).b (interiorFanTriangle P q i).c p) :
    p = q ∨ p = P.vertex i ∨ p = P.vertex (P.nextIdx i) ∨ p = r ∨ p = s := by
  rcases eq_vertices_or_interior_of_mem_interiorFan P hsc hinj hedge
      (mem_interior_of_threeInterior_apex P h) i hp with
    h1 | h2 | h3 | hint
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · have hpset : p ∈ ({q, r, s} : Set (ℤ × ℤ)) := by
      rw [← h.2.2.2]; exact hint
    rcases (Set.mem_insert_iff.mp hpset) with hpq | hp'
    · exact Or.inl hpq
    · rcases (Set.mem_insert_iff.mp hp') with hpr | hps
      · exact Or.inr (Or.inr (Or.inr (Or.inl hpr)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Set.mem_singleton_iff.mp hps))))

lemma ThreeInterior_swap {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) : ThreeInterior P q s r :=
  ⟨h.2.1, h.1, h.2.2.1.symm, by
    rw [h.2.2.2]; ext p; simp [or_comm]⟩

/-- Occupied ear containing exactly one of `{r,s}` (off boundary) inherits
`UniqueInterior` as a `trianglePolygon`. -/
theorem UniqueInterior_trianglePolygon_of_threeInterior_occupied
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (i : Fin P.nVertices)
    (hr : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hoff : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hs_not : ¬ MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) s) :
    UniqueInterior (trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))) r := by
  classical
  set v := P.vertex i
  set w := P.vertex (P.nextIdx i)
  set T := trianglePolygon q v w
  have hr_not_bd : r ∉ T.boundaryLatticePoints :=
    not_mem_boundary_trianglePolygon_of_OffTriangleBoundary hoff
  have hr_hull : toReal r ∈ T.convexHullRegion := by
    rw [trianglePolygon_convexHullRegion]
    exact mem_convexHull_of_memClosedTriangle q v w r hr
  refine ⟨⟨hr_hull, hr_not_bd⟩, ?_⟩
  intro p hp
  have hp_mem : MemClosedTriangle q v w p :=
    memClosedTriangle_of_mem_convexHull q v w p (by
      simpa [T, trianglePolygon_convexHullRegion] using hp.1)
  have hp_not_bd : p ∉ T.boundaryLatticePoints := hp.2
  rcases eq_vertices_or_rs_of_mem_interiorFan_of_threeInterior P hsc hinj hedge h i
      (by simpa [interiorFanTriangle] using hp_mem) with h1 | h2 | h3 | h4 | h5
  · have hbd : q ∈ T.boundaryLatticePoints :=
      T.vertices_mem_boundary (List.mem_cons_self (a := q) (l := [v, w]))
    exact absurd (h1.symm ▸ hbd) hp_not_bd
  · have hbd : v ∈ T.boundaryLatticePoints :=
      T.vertices_mem_boundary
        (List.mem_cons_of_mem q (List.mem_cons_self (a := v) (l := [w])))
    exact absurd (h2.symm ▸ hbd) hp_not_bd
  · have hbd : w ∈ T.boundaryLatticePoints :=
      T.vertices_mem_boundary
        (List.mem_cons_of_mem q
          (List.mem_cons_of_mem v (List.mem_singleton.mpr rfl)))
    exact absurd (h3.symm ▸ hbd) hp_not_bd
  · exact h4
  · exact absurd (by simpa [v, w, h5] using hp_mem) hs_not

/-- Occupied Off ear with exactly one of `{r,s}` has `StrictlyConvexCCW`,
`PrimitiveEdges`, and injective vertices as a `trianglePolygon`. -/
theorem StrictlyConvexCCW_PrimitiveEdges_trianglePolygon_of_threeInterior_occupied
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (i : Fin P.nVertices)
    (_hr : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hoff : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hs_not : ¬ MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) s) :
    let T := trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))
    StrictlyConvexCCW T ∧ PrimitiveEdges T ∧ Function.Injective T.vertex := by
  classical
  set v := P.vertex i
  set w := P.vertex (P.nextIdx i)
  set T := trianglePolygon q v w
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hD : 0 < latticeDet q v w := by
    simpa [v, w, interiorFanDet, interiorFanTriangle, Triangle.det] using hpos i
  have hscT : StrictlyConvexCCW T := StrictlyConvexCCW_trianglePolygon q v w hD
  have hinjT : Function.Injective T.vertex :=
    injective_vertex_trianglePolygon q v w (ne_of_gt hD)
  have hsubset :
      ∀ p : ℤ × ℤ,
        MemClosedTriangle q v w p →
          p = q ∨ p = v ∨ p = w ∨ p = r := by
    intro p hp
    have hp' : MemClosedTriangle (interiorFanTriangle P q i).a
        (interiorFanTriangle P q i).b (interiorFanTriangle P q i).c p := by
      simpa [interiorFanTriangle, v, w] using hp
    rcases eq_vertices_or_rs_of_mem_interiorFan_of_threeInterior
        P hsc hinj hedge h i hp' with h1 | h2 | h3 | h4 | h5
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr h4))
    · exact (hs_not (by simpa [v, w, h5] using hp)).elim
  have hedgeT : PrimitiveEdges T :=
    PrimitiveEdges_trianglePolygon_of_subset_four_off q v w r
      (ne_of_gt hD) hsubset hoff
  exact ⟨hscT, hedgeT, hinjT⟩

/-- Occupied Off ear with exactly one of `{r,s}` has `interiorFanDet = 3`. -/
theorem interiorFanDet_eq_three_of_threeInterior_occupied
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (i : Fin P.nVertices)
    (hr : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hoff : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hs_not : ¬ MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) s) :
    interiorFanDet P q i = 3 := by
  classical
  set v := P.vertex i
  set w := P.vertex (P.nextIdx i)
  set T := trianglePolygon q v w
  obtain ⟨hscT, hedgeT, hinjT⟩ :=
    StrictlyConvexCCW_PrimitiveEdges_trianglePolygon_of_threeInterior_occupied
      P hsc hinj hedge h i hr hoff hs_not
  have hU : UniqueInterior T r :=
    UniqueInterior_trianglePolygon_of_threeInterior_occupied
      P hsc hinj hedge h i hr hoff hs_not
  have hshoelace : T.shoelace = (1 : ℚ) + (T.B : ℚ) / 2 - 1 :=
    shoelace_eq_I_add_B_div_two_sub_one_of_uniqueInterior T hinjT hedgeT hscT hU
  have hB : T.B = 3 := by
    -- PrimitiveEdges + injective Fin-3 ⇒ B = nVertices = 3.
    have := B_eq_nVertices_of_primitive_edges T hedgeT hinjT
    simpa [T, trianglePolygon_nVertices] using this
  have harea : T.shoelace = (3 : ℚ) / 2 := by
    rw [hshoelace, hB]; ring
  have hDpos : 0 < latticeDet q v w := by
    have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
    simpa [v, w, interiorFanDet, interiorFanTriangle, Triangle.det] using hpos i
  have hnn : 0 ≤ T.shoelaceSum := by
    -- shoelaceSum of triangle = latticeDet under positive orientation
    have hseq : T.shoelaceSum = latticeDet q v w := shoelaceSum_trianglePolygon q v w
    simpa [hseq] using le_of_lt hDpos
  have hnat : Int.natAbs T.shoelaceSum = 3 := by
    have : (Int.natAbs T.shoelaceSum : ℚ) / 2 = (3 : ℚ) / 2 := by
      simpa [LatticePolygon.shoelace] using harea
    have : (Int.natAbs T.shoelaceSum : ℚ) = 3 := by linarith
    exact_mod_cast this
  have hz : T.shoelaceSum = (Int.natAbs T.shoelaceSum : ℤ) :=
    (Int.natAbs_of_nonneg hnn).symm
  have : latticeDet q v w = 3 := by
    have hseq : T.shoelaceSum = latticeDet q v w := shoelaceSum_trianglePolygon q v w
    rw [← hseq, hz, hnat]; norm_num
  simpa [interiorFanDet, interiorFanTriangle, Triangle.det, v, w] using this

/-- **I = 3 shoelace Pick-form** under two distinct Off occupied ears
(not classical Pick).

Hyps: `ThreeInterior`, ears `i ≠ j` each Off-occupied by exactly one of `{r,s}`,
empty ears contain neither, and uniqueness of each occupied ear index.
Empty ⇒ `det=1`; each occupied ⇒ `det=3`; fan sum `n+4`; `B=n` ⇒
`shoelace = 3 + B/2 − 1`.

Same-ear occupation / on-spoke I=3 still open. Shoelace ≠ Haar. Classical Pick FAIL. -/
theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_two_occupied
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (i j : Fin P.nVertices)
    (hne : i ≠ j)
    (hr : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hoff_r : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hs_not_i : ¬ MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) s)
    (hs : MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) s)
    (hoff_s : OffTriangleBoundary q (P.vertex j) (P.vertex (P.nextIdx j)) s)
    (hr_not_j : ¬ MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) r)
    (huniq_r : ∀ k : Fin P.nVertices,
      MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) r → k = i)
    (huniq_s : ∀ k : Fin P.nVertices,
      MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) s → k = j) :
    P.shoelace = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  have hq := mem_interior_of_threeInterior_apex P h
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hdet3i : interiorFanDet P q i = 3 :=
    interiorFanDet_eq_three_of_threeInterior_occupied
      P hsc hinj hedge h i hr hoff_r hs_not_i
  have hdet3j : interiorFanDet P q j = 3 :=
    interiorFanDet_eq_three_of_threeInterior_occupied
      P hsc hinj hedge (ThreeInterior_swap P h) j hs hoff_s hr_not_j
  have hdet1 : ∀ k : Fin P.nVertices, k ≠ i → k ≠ j →
      interiorFanDet P q k = 1 := by
    intro k hki hkj
    have hempty : ∀ p ∈ P.interiorLatticePoints, p ≠ q →
        ¬ MemClosedTriangle (interiorFanTriangle P q k).a
          (interiorFanTriangle P q k).b (interiorFanTriangle P q k).c p := by
      intro p hp hpq hp_mem
      have hpset : p ∈ ({q, r, s} : Set (ℤ × ℤ)) := by
        rw [← h.2.2.2]; exact hp
      rcases (Set.mem_insert_iff.mp hpset) with hpq' | hp'
      · exact hpq hpq'
      · rcases (Set.mem_insert_iff.mp hp') with hpr | hps
        · have : k = i := huniq_r k (by
            simpa [interiorFanTriangle, hpr] using hp_mem)
          exact hki this
        · have hps' : p = s := Set.mem_singleton_iff.mp hps
          have : k = j := huniq_s k (by
            simpa [interiorFanTriangle, hps'] using hp_mem)
          exact hkj this
    exact interiorFanDet_eq_one_of_no_other_interior
      P hsc hinj hedge hq k hempty
  have hsum :
      (∑ k : Fin P.nVertices, interiorFanDet P q k) = (P.nVertices : ℤ) + 4 := by
    set S := (Finset.univ.erase i).erase j
    have hi_mem : i ∈ Finset.univ := Finset.mem_univ i
    have hj_mem : j ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
    have hdecomp1 :
        (∑ k : Fin P.nVertices, interiorFanDet P q k) =
          interiorFanDet P q i +
            ∑ k ∈ Finset.univ.erase i, interiorFanDet P q k := by
      rw [add_comm]
      exact (Finset.sum_erase_add (s := Finset.univ) (interiorFanDet P q) hi_mem).symm
    have hdecomp2 :
        ∑ k ∈ Finset.univ.erase i, interiorFanDet P q k =
          interiorFanDet P q j + ∑ k ∈ S, interiorFanDet P q k := by
      dsimp [S]
      rw [add_comm]
      exact (Finset.sum_erase_add (s := Finset.univ.erase i) (interiorFanDet P q)
        hj_mem).symm
    have hrest : ∑ k ∈ S, interiorFanDet P q k = ∑ k ∈ S, (1 : ℤ) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have ⟨hne_j, hk2⟩ := Finset.mem_erase.mp hk
      have ⟨hne_i, _⟩ := Finset.mem_erase.mp hk2
      exact hdet1 k hne_i hne_j
    have hcard : S.card = P.nVertices - 2 := by
      dsimp [S]
      have h1 : (Finset.univ.erase i).card = P.nVertices - 1 := by
        rw [Finset.card_erase_of_mem hi_mem, Finset.card_univ, Fintype.card_fin]
      have h2 : ((Finset.univ.erase i).erase j).card =
          (Finset.univ.erase i).card - 1 :=
        Finset.card_erase_of_mem hj_mem
      have : 2 ≤ P.nVertices := by
        have : 3 ≤ P.nVertices := P.length_ge; omega
      omega
    calc
      ∑ k : Fin P.nVertices, interiorFanDet P q k
          = interiorFanDet P q i +
              ∑ k ∈ Finset.univ.erase i, interiorFanDet P q k := hdecomp1
      _ = 3 + (interiorFanDet P q j + ∑ k ∈ S, interiorFanDet P q k) := by
            rw [hdet3i, hdecomp2]
      _ = 3 + (3 + ∑ k ∈ S, (1 : ℤ)) := by rw [hdet3j, hrest]
      _ = 6 + (S.card : ℤ) := by simp; ring
      _ = 6 + ((P.nVertices - 2 : ℕ) : ℤ) := by rw [hcard]
      _ = (P.nVertices : ℤ) + 4 := by
            have : 2 ≤ P.nVertices := by
              have : 3 ≤ P.nVertices := P.length_ge; omega
            have hcast : ((P.nVertices - 2 : ℕ) : ℤ) = (P.nVertices : ℤ) - 2 :=
              Nat.cast_sub this
            rw [hcast]; ring
  have hshoelaceSum : P.shoelaceSum = (P.nVertices : ℤ) + 4 := by
    rw [← sum_interiorFanDet_eq_shoelaceSum P q, hsum]
  have hB : P.B = P.nVertices := B_eq_nVertices_of_primitive_edges P hedge hinj
  have hnn : 0 ≤ P.shoelaceSum := by
    have : 0 ≤ (P.nVertices : ℤ) + 4 := by
      have : 3 ≤ P.nVertices := P.length_ge; omega
    simpa [hshoelaceSum] using this
  have hnat : Int.natAbs P.shoelaceSum = P.nVertices + 4 := by
    apply Int.natCast_inj.mp
    rw [Int.natAbs_of_nonneg hnn, hshoelaceSum]
    push_cast; ring
  calc
    P.shoelace = (Int.natAbs P.shoelaceSum : ℚ) / 2 := rfl
    _ = ((P.nVertices + 4 : ℕ) : ℚ) / 2 := by
          have : (Int.natAbs P.shoelaceSum : ℚ) = ((P.nVertices + 4 : ℕ) : ℚ) := by
            exact_mod_cast hnat
          rw [this]
    _ = (P.nVertices : ℚ) / 2 + 2 := by push_cast; ring
    _ = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := by rw [hB]; ring

/-- **I = 3 shoelace Pick-form** under two distinct Off occupied ears, without
uniqueness hyps (not classical Pick).

Discharges `huniq_r` / `huniq_s` via `eq_of_mem_interiorFan_of_offBoundary`
(general cone / half-plane uniqueness from any interior apex). On-spoke I=3
still open. Shoelace ≠ Haar. Classical Pick FAIL. -/
theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_two_occupied_offBoundary
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (i j : Fin P.nVertices)
    (hne : i ≠ j)
    (hr : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hoff_r : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hs_not_i : ¬ MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) s)
    (hs : MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) s)
    (hoff_s : OffTriangleBoundary q (P.vertex j) (P.vertex (P.nextIdx j)) s)
    (hr_not_j : ¬ MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) r) :
    P.shoelace = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := by
  refine shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_two_occupied
    P hsc hinj hedge h i j hne hr hoff_r hs_not_i hs hoff_s hr_not_j ?_ ?_
  · intro k hk
    exact eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge
      (mem_interior_of_threeInterior_apex P h) i k hr hoff_r hk
  · intro k hk
    exact eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge
      (mem_interior_of_threeInterior_apex P h) j k hs hoff_s hk

/-! ### Five-point PrimitiveEdges (same-ear substrate) -/

/-- Edge `a--b` is primitive when closed-triangle lattice points lie in `{a,b,c,r,s}`
and both extras are off that edge (not classical Pick). -/
theorem edgeGcd_eq_one_of_subset_five_off_ab
    (a b c r s : ℤ × ℤ) (hD : latticeDet a b c ≠ 0)
    (hsub : ∀ p, MemClosedTriangle a b c p →
      p = a ∨ p = b ∨ p = c ∨ p = r ∨ p = s)
    (hoff_r : r ∉ edgeLatticePoints a b) (hoff_s : s ∉ edgeLatticePoints a b) :
    edgeGcd a b = 1 := by
  have hab : a ≠ b := by
    intro hab; exact hD (by simp [latticeDet, hab])
  have hge0 : edgeGcd a b ≠ 0 := fun hz => hab ((edgeGcd_eq_zero_iff a b).mp hz)
  by_contra hne1
  have h2 : 2 ≤ edgeGcd a b := by omega
  obtain ⟨t, ht, htne⟩ := exists_strict_mem_edgeLatticePoints_of_edgeGcd_ge_two a b h2
  have hm := hsub t (memClosedTriangle_of_mem_edgeLatticePoints_ab a b c t ht)
  rcases hm with h1 | h2' | h3 | h4 | h5
  · exact htne.1 h1
  · exact htne.2 h2'
  · exact hD (latticeDet_eq_zero_of_mem_edge_ab a b c (h3 ▸ ht))
  · exact hoff_r (h4 ▸ ht)
  · exact hoff_s (h5 ▸ ht)

theorem edgeGcd_eq_one_of_subset_five_off_bc
    (a b c r s : ℤ × ℤ) (hD : latticeDet a b c ≠ 0)
    (hsub : ∀ p, MemClosedTriangle a b c p →
      p = a ∨ p = b ∨ p = c ∨ p = r ∨ p = s)
    (hoff_r : r ∉ edgeLatticePoints b c) (hoff_s : s ∉ edgeLatticePoints b c) :
    edgeGcd b c = 1 := by
  have hD' : latticeDet b c a ≠ 0 := by
    simpa [← latticeDet_cyclic a b c] using hD
  have hsub' : ∀ p, MemClosedTriangle b c a p →
      p = b ∨ p = c ∨ p = a ∨ p = r ∨ p = s := by
    intro p hp
    have hp' : MemClosedTriangle a b c p := memClosedTriangle_permute_bca hp
    rcases hsub p hp' with h1 | h2 | h3 | h4 | h5
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inl h2
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
  simpa using edgeGcd_eq_one_of_subset_five_off_ab b c a r s hD' hsub' hoff_r hoff_s

theorem edgeGcd_eq_one_of_subset_five_off_ca
    (a b c r s : ℤ × ℤ) (hD : latticeDet a b c ≠ 0)
    (hsub : ∀ p, MemClosedTriangle a b c p →
      p = a ∨ p = b ∨ p = c ∨ p = r ∨ p = s)
    (hoff_r : r ∉ edgeLatticePoints c a) (hoff_s : s ∉ edgeLatticePoints c a) :
    edgeGcd c a = 1 := by
  have hD' : latticeDet c a b ≠ 0 := by
    simpa [← latticeDet_cyclic₂ a b c] using hD
  have hsub' : ∀ p, MemClosedTriangle c a b p →
      p = c ∨ p = a ∨ p = b ∨ p = r ∨ p = s := by
    intro p hp
    have hp' : MemClosedTriangle a b c p := memClosedTriangle_permute_cab hp
    rcases hsub p hp' with h1 | h2 | h3 | h4 | h5
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inl h3
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
  simpa using edgeGcd_eq_one_of_subset_five_off_ab c a b r s hD' hsub' hoff_r hoff_s

/-- `PrimitiveEdges` for a triangle whose closed lattice points are among five
points with both extras off every edge (not classical Pick). -/
theorem PrimitiveEdges_trianglePolygon_of_subset_five_off
    (a b c r s : ℤ × ℤ) (hD : latticeDet a b c ≠ 0)
    (hsub : ∀ p, MemClosedTriangle a b c p →
      p = a ∨ p = b ∨ p = c ∨ p = r ∨ p = s)
    (hoff_r : OffTriangleBoundary a b c r)
    (hoff_s : OffTriangleBoundary a b c s) :
    PrimitiveEdges (trianglePolygon a b c) := by
  intro i
  fin_cases i
  · simpa [trianglePolygon, LatticePolygon.edgePair, LatticePolygon.vertex,
      LatticePolygon.nextIdx, LatticePolygon.nVertices] using
      edgeGcd_eq_one_of_subset_five_off_ab a b c r s hD hsub hoff_r.1 hoff_s.1
  · simpa [trianglePolygon, LatticePolygon.edgePair, LatticePolygon.vertex,
      LatticePolygon.nextIdx, LatticePolygon.nVertices] using
      edgeGcd_eq_one_of_subset_five_off_bc a b c r s hD hsub hoff_r.2.1 hoff_s.2.1
  · simpa [trianglePolygon, LatticePolygon.edgePair, LatticePolygon.vertex,
      LatticePolygon.nextIdx, LatticePolygon.nVertices] using
      edgeGcd_eq_one_of_subset_five_off_ca a b c r s hD hsub hoff_r.2.2 hoff_s.2.2

/-! ### Same-ear occupation (both extras in one Off ear) -/

/-- Under `ThreeInterior`, if both `r` and `s` occupy the same Off ear, that ear
as `trianglePolygon` inherits `TwoInterior`. -/
theorem TwoInterior_trianglePolygon_of_threeInterior_same_ear
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (i : Fin P.nVertices)
    (hr : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hoff_r : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hs : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) s)
    (hoff_s : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) s) :
    TwoInterior (trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))) r s := by
  classical
  set v := P.vertex i
  set w := P.vertex (P.nextIdx i)
  set T := trianglePolygon q v w
  have hr_not_bd : r ∉ T.boundaryLatticePoints :=
    not_mem_boundary_trianglePolygon_of_OffTriangleBoundary hoff_r
  have hs_not_bd : s ∉ T.boundaryLatticePoints :=
    not_mem_boundary_trianglePolygon_of_OffTriangleBoundary hoff_s
  have hr_hull : toReal r ∈ T.convexHullRegion := by
    rw [trianglePolygon_convexHullRegion]
    exact mem_convexHull_of_memClosedTriangle q v w r hr
  have hs_hull : toReal s ∈ T.convexHullRegion := by
    rw [trianglePolygon_convexHullRegion]
    exact mem_convexHull_of_memClosedTriangle q v w s hs
  refine ⟨h.2.2.1, ?_⟩
  ext p
  constructor
  · intro hp
    have hp_mem : MemClosedTriangle q v w p :=
      memClosedTriangle_of_mem_convexHull q v w p (by
        simpa [T, trianglePolygon_convexHullRegion] using hp.1)
    have hp_not_bd : p ∉ T.boundaryLatticePoints := hp.2
    rcases eq_vertices_or_rs_of_mem_interiorFan_of_threeInterior P hsc hinj hedge h i
        (by simpa [interiorFanTriangle, v, w] using hp_mem) with h1 | h2 | h3 | h4 | h5
    · have hbd : q ∈ T.boundaryLatticePoints :=
        T.vertices_mem_boundary (List.mem_cons_self (a := q) (l := [v, w]))
      exact absurd (h1.symm ▸ hbd) hp_not_bd
    · have hbd : v ∈ T.boundaryLatticePoints :=
        T.vertices_mem_boundary
          (List.mem_cons_of_mem q (List.mem_cons_self (a := v) (l := [w])))
      exact absurd (h2.symm ▸ hbd) hp_not_bd
    · have hbd : w ∈ T.boundaryLatticePoints :=
        T.vertices_mem_boundary
          (List.mem_cons_of_mem q
            (List.mem_cons_of_mem v (List.mem_singleton.mpr rfl)))
      exact absurd (h3.symm ▸ hbd) hp_not_bd
    · exact Or.inl h4
    · exact Or.inr (Set.mem_singleton_iff.mpr h5)
  · intro hp
    rcases (Set.mem_insert_iff.mp hp) with hpr | hps
    · subst hpr; exact ⟨hr_hull, hr_not_bd⟩
    · have hps' : p = s := Set.mem_singleton_iff.mp hps
      subst hps'; exact ⟨hs_hull, hs_not_bd⟩

/-- Same-ear Off occupation: ear has `StrictlyConvexCCW`, `PrimitiveEdges`, injective
vertices as a `trianglePolygon`. -/
theorem StrictlyConvexCCW_PrimitiveEdges_trianglePolygon_of_threeInterior_same_ear
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (i : Fin P.nVertices)
    (_hr : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hoff_r : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (_hs : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) s)
    (hoff_s : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) s) :
    let T := trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))
    StrictlyConvexCCW T ∧ PrimitiveEdges T ∧ Function.Injective T.vertex := by
  classical
  set v := P.vertex i
  set w := P.vertex (P.nextIdx i)
  set T := trianglePolygon q v w
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hD : 0 < latticeDet q v w := by
    simpa [v, w, interiorFanDet, interiorFanTriangle, Triangle.det] using hpos i
  have hscT : StrictlyConvexCCW T := StrictlyConvexCCW_trianglePolygon q v w hD
  have hinjT : Function.Injective T.vertex :=
    injective_vertex_trianglePolygon q v w (ne_of_gt hD)
  have hsubset :
      ∀ p : ℤ × ℤ,
        MemClosedTriangle q v w p →
          p = q ∨ p = v ∨ p = w ∨ p = r ∨ p = s := by
    intro p hp
    have hp' : MemClosedTriangle (interiorFanTriangle P q i).a
        (interiorFanTriangle P q i).b (interiorFanTriangle P q i).c p := by
      simpa [interiorFanTriangle, v, w] using hp
    rcases eq_vertices_or_rs_of_mem_interiorFan_of_threeInterior
        P hsc hinj hedge h i hp' with h1 | h2 | h3 | h4 | h5
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
  have hedgeT : PrimitiveEdges T :=
    PrimitiveEdges_trianglePolygon_of_subset_five_off q v w r s
      (ne_of_gt hD) hsubset hoff_r hoff_s
  exact ⟨hscT, hedgeT, hinjT⟩

/-- Same-ear Off occupation has `interiorFanDet = 5` (I=2 on the ear ⇒ shoelace
`5/2`). -/
theorem interiorFanDet_eq_five_of_threeInterior_same_ear
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (i : Fin P.nVertices)
    (hr : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hoff_r : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hs : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) s)
    (hoff_s : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) s) :
    interiorFanDet P q i = 5 := by
  classical
  set v := P.vertex i
  set w := P.vertex (P.nextIdx i)
  set T := trianglePolygon q v w
  obtain ⟨hscT, hedgeT, hinjT⟩ :=
    StrictlyConvexCCW_PrimitiveEdges_trianglePolygon_of_threeInterior_same_ear
      P hsc hinj hedge h i hr hoff_r hs hoff_s
  have hTwo : TwoInterior T r s :=
    TwoInterior_trianglePolygon_of_threeInterior_same_ear
      P hsc hinj hedge h i hr hoff_r hs hoff_s
  have hshoelace : T.shoelace = (2 : ℚ) + (T.B : ℚ) / 2 - 1 :=
    shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior T hscT hinjT hedgeT hTwo
  have hB : T.B = 3 := by
    have := B_eq_nVertices_of_primitive_edges T hedgeT hinjT
    simpa [T, trianglePolygon_nVertices] using this
  have harea : T.shoelace = (5 : ℚ) / 2 := by
    rw [hshoelace, hB]; ring
  have hDpos : 0 < latticeDet q v w := by
    have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
    simpa [v, w, interiorFanDet, interiorFanTriangle, Triangle.det] using hpos i
  have hnn : 0 ≤ T.shoelaceSum := by
    have hseq : T.shoelaceSum = latticeDet q v w := shoelaceSum_trianglePolygon q v w
    simpa [hseq] using le_of_lt hDpos
  have hnat : Int.natAbs T.shoelaceSum = 5 := by
    have : (Int.natAbs T.shoelaceSum : ℚ) / 2 = (5 : ℚ) / 2 := by
      simpa [LatticePolygon.shoelace] using harea
    have : (Int.natAbs T.shoelaceSum : ℚ) = 5 := by linarith
    exact_mod_cast this
  have hz : T.shoelaceSum = (Int.natAbs T.shoelaceSum : ℤ) :=
    (Int.natAbs_of_nonneg hnn).symm
  have : latticeDet q v w = 5 := by
    have hseq : T.shoelaceSum = latticeDet q v w := shoelaceSum_trianglePolygon q v w
    rw [← hseq, hz, hnat]; norm_num
  simpa [interiorFanDet, interiorFanTriangle, Triangle.det, v, w] using this

/-- **I = 3 shoelace Pick-form** under same-ear Off occupation (not classical Pick).

Both remaining interior points occupy one Off ear: that ear is `TwoInterior` as a
`trianglePolygon` ⇒ `det=5`; other ears empty ⇒ `det=1`; fan sum `n+4`; `B=n` ⇒
`shoelace = 3 + B/2 − 1`. Uniqueness of the occupied ear from general OffBoundary
cone arguments. On-spoke I=3 still open. Shoelace ≠ Haar. Classical Pick FAIL. -/
theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_same_ear_offBoundary
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (i : Fin P.nVertices)
    (hr : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hoff_r : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hs : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) s)
    (hoff_s : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) s) :
    P.shoelace = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  have hq := mem_interior_of_threeInterior_apex P h
  have hdet5 : interiorFanDet P q i = 5 :=
    interiorFanDet_eq_five_of_threeInterior_same_ear
      P hsc hinj hedge h i hr hoff_r hs hoff_s
  have huniq_r : ∀ k : Fin P.nVertices,
      MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) r → k = i := by
    intro k hk
    exact eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq i k hr hoff_r hk
  have huniq_s : ∀ k : Fin P.nVertices,
      MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) s → k = i := by
    intro k hk
    exact eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq i k hs hoff_s hk
  have hdet1 : ∀ k : Fin P.nVertices, k ≠ i →
      interiorFanDet P q k = 1 := by
    intro k hki
    have hempty : ∀ p ∈ P.interiorLatticePoints, p ≠ q →
        ¬ MemClosedTriangle (interiorFanTriangle P q k).a
          (interiorFanTriangle P q k).b (interiorFanTriangle P q k).c p := by
      intro p hp hpq hp_mem
      have hpset : p ∈ ({q, r, s} : Set (ℤ × ℤ)) := by
        rw [← h.2.2.2]; exact hp
      rcases (Set.mem_insert_iff.mp hpset) with hpq' | hp'
      · exact hpq hpq'
      · rcases (Set.mem_insert_iff.mp hp') with hpr | hps
        · have : k = i := huniq_r k (by
            simpa [interiorFanTriangle, hpr] using hp_mem)
          exact hki this
        · have hps' : p = s := Set.mem_singleton_iff.mp hps
          have : k = i := huniq_s k (by
            simpa [interiorFanTriangle, hps'] using hp_mem)
          exact hki this
    exact interiorFanDet_eq_one_of_no_other_interior
      P hsc hinj hedge hq k hempty
  have hsum :
      (∑ k : Fin P.nVertices, interiorFanDet P q k) = (P.nVertices : ℤ) + 4 := by
    have hi_mem : i ∈ Finset.univ := Finset.mem_univ i
    have hdecomp :
        (∑ k : Fin P.nVertices, interiorFanDet P q k) =
          interiorFanDet P q i +
            ∑ k ∈ Finset.univ.erase i, interiorFanDet P q k := by
      rw [add_comm]
      exact (Finset.sum_erase_add (s := Finset.univ) (interiorFanDet P q) hi_mem).symm
    have hrest :
        ∑ k ∈ Finset.univ.erase i, interiorFanDet P q k =
          ∑ k ∈ Finset.univ.erase i, (1 : ℤ) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have ⟨hne_i, _⟩ := Finset.mem_erase.mp hk
      exact hdet1 k hne_i
    have hcard : (Finset.univ.erase i).card = P.nVertices - 1 := by
      rw [Finset.card_erase_of_mem hi_mem, Finset.card_univ, Fintype.card_fin]
    calc
      ∑ k : Fin P.nVertices, interiorFanDet P q k
          = interiorFanDet P q i +
              ∑ k ∈ Finset.univ.erase i, interiorFanDet P q k := hdecomp
      _ = 5 + ∑ k ∈ Finset.univ.erase i, (1 : ℤ) := by rw [hdet5, hrest]
      _ = 5 + ((Finset.univ.erase i).card : ℤ) := by simp
      _ = 5 + ((P.nVertices - 1 : ℕ) : ℤ) := by rw [hcard]
      _ = (P.nVertices : ℤ) + 4 := by
            have : 1 ≤ P.nVertices := by
              have : 3 ≤ P.nVertices := P.length_ge; omega
            have hcast : ((P.nVertices - 1 : ℕ) : ℤ) = (P.nVertices : ℤ) - 1 :=
              Nat.cast_sub this
            rw [hcast]; ring
  have hshoelaceSum : P.shoelaceSum = (P.nVertices : ℤ) + 4 := by
    rw [← sum_interiorFanDet_eq_shoelaceSum P q, hsum]
  have hB : P.B = P.nVertices := B_eq_nVertices_of_primitive_edges P hedge hinj
  have hnn : 0 ≤ P.shoelaceSum := by
    have : 0 ≤ (P.nVertices : ℤ) + 4 := by
      have : 3 ≤ P.nVertices := P.length_ge; omega
    simpa [hshoelaceSum] using this
  have hnat : Int.natAbs P.shoelaceSum = P.nVertices + 4 := by
    apply Int.natCast_inj.mp
    rw [Int.natAbs_of_nonneg hnn, hshoelaceSum]
    push_cast; ring
  calc
    P.shoelace = (Int.natAbs P.shoelaceSum : ℚ) / 2 := rfl
    _ = ((P.nVertices + 4 : ℕ) : ℚ) / 2 := by
          have : (Int.natAbs P.shoelaceSum : ℚ) = ((P.nVertices + 4 : ℕ) : ℚ) := by
            exact_mod_cast hnat
          rw [this]
    _ = (P.nVertices : ℚ) / 2 + 2 := by push_cast; ring
    _ = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := by rw [hB]; ring


/-! ### Unified Off I = 3 (two-ear ∨ same-ear) + Finset packaging -/

/-- **I = 3 shoelace Pick-form** under Off occupation of both non-apex interiors
(not classical Pick).

Hyps: `ThreeInterior` plus Off covering ears for `r` and `s` (indices may
coincide). Case-split:
* same ear ⇒ `shoelace_eq_three_…_same_ear_offBoundary` (`det=5` + empties)
* distinct ears ⇒ exclusivity from `eq_of_mem_interiorFan_of_offBoundary`, then
  `shoelace_eq_three_…_two_occupied_offBoundary` (`det=3` each + empties)

Both paths give fan sum `n+4` and `shoelace = 3 + B/2 − 1`. On-spoke I=3 still
open. Shoelace ≠ Haar. Classical Pick FAIL. -/
theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_off
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (i j : Fin P.nVertices)
    (hr : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hoff_r : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hs : MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) s)
    (hoff_s : OffTriangleBoundary q (P.vertex j) (P.vertex (P.nextIdx j)) s) :
    P.shoelace = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  by_cases hije : i = j
  · subst hije
    exact shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_same_ear_offBoundary
      P hsc hinj hedge h i hr hoff_r hs hoff_s
  · have hq := mem_interior_of_threeInterior_apex P h
    have hs_not_i :
        ¬ MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) s := by
      intro hs_i
      have : i = j :=
        eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq j i hs hoff_s
          hs_i
      exact hije this
    have hr_not_j :
        ¬ MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) r := by
      intro hr_j
      have : j = i :=
        eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq i j hr hoff_r hr_j
      exact hije this.symm
    exact shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_two_occupied_offBoundary
      P hsc hinj hedge h i j hije hr hoff_r hs_not_i hs hoff_s hr_not_j

/-- **I = 3 shoelace Pick-form** from existential Off coverings (not classical Pick). -/
theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_off_exists
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s)
    (hr_off : ∃ i : Fin P.nVertices,
      MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r ∧
        OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r)
    (hs_off : ∃ j : Fin P.nVertices,
      MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) s ∧
        OffTriangleBoundary q (P.vertex j) (P.vertex (P.nextIdx j)) s) :
    P.shoelace = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  obtain ⟨i, hr, hoff_r⟩ := hr_off
  obtain ⟨j, hs, hoff_s⟩ := hs_off
  exact shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_off
    P hsc hinj hedge h i j hr hoff_r hs hoff_s

/-- **Finset `card = 3` shoelace Pick-form** under an Off-apex hyp
(not classical Pick).

Hyps: `↑S = interiorLatticePoints`, `S.card = 3`, injective vertices, primitive
edges, `StrictlyConvexCCW`, and an apex `q ∈ S` such that every other interior
point is `OffTriangleBoundary` in some fan ear from `q`. Covers all Off two-ear
and same-ear configurations. On-spoke I=3 still open. Shoelace ≠ Haar.
Classical Pick FAIL. -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_three
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hcard : S.card = 3)
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hsc : StrictlyConvexCCW P)
    (hoff : ∃ q ∈ S, ∀ r ∈ S, r ≠ q →
      ∃ i : Fin P.nVertices,
        MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r ∧
          OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r) :
    P.shoelace = (S.card : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  obtain ⟨q₀, hq₀S, hcover⟩ := hoff
  have herase : (S.erase q₀).card = 2 := by
    rw [Finset.card_erase_of_mem hq₀S, hcard]
  obtain ⟨a, b, hab, hEr⟩ := Finset.card_eq_two.mp herase
  have ha_ne : a ≠ q₀ := by
    have : a ∈ S.erase q₀ := by
      rw [hEr]; exact Finset.mem_insert_self a {b}
    exact (Finset.mem_erase.mp this).1
  have hb_ne : b ≠ q₀ := by
    have : b ∈ S.erase q₀ := by
      rw [hEr]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    exact (Finset.mem_erase.mp this).1
  have haS : a ∈ S := by
    have : a ∈ S.erase q₀ := by
      rw [hEr]; exact Finset.mem_insert_self a {b}
    exact (Finset.mem_erase.mp this).2
  have hbS : b ∈ S := by
    have : b ∈ S.erase q₀ := by
      rw [hEr]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    exact (Finset.mem_erase.mp this).2
  have hSeq : S = {q₀, a, b} := by
    ext x
    constructor
    · intro hx
      by_cases hxq : x = q₀
      · simp [hxq]
      · have : x ∈ S.erase q₀ := Finset.mem_erase.mpr ⟨hxq, hx⟩
        rw [hEr] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with hxa | hxb
        · simp [hxa]
        · simp [hxb]
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hxq | hxa | hxb
      · simpa [hxq] using hq₀S
      · simpa [hxa] using haS
      · simpa [hxb] using hbS
  have hThree : ThreeInterior P q₀ a b := by
    refine ⟨ha_ne.symm, hb_ne.symm, hab, ?_⟩
    rw [← hS, hSeq]
    simp [Finset.coe_insert, Finset.coe_singleton]
  have ha_off := hcover a haS ha_ne
  have hb_off := hcover b hbS hb_ne
  have harea :=
    shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_off_exists
      P hsc hverts hedge hThree ha_off hb_off
  calc
    P.shoelace = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := harea
    _ = (S.card : ℚ) + (P.B : ℚ) / 2 - 1 := by simp [hcard]

/-! ### On-spoke I = 3 (one on-spoke + Off companion; not classical Pick)

Classification: each of `{r,s}` is Off or on-spoke in a covering ear from apex
`q`. When exactly one lies strictly on a spoke and the other is Off in a
non-adjacent ear, adjacent ears contribute `det = 2` (I=2 doubling + empty
half-ears), the Off ear contributes `det = 3`, and the rest `det = 1`, so the
fan sum is `n + 4` and `shoelace = 3 + B/2 − 1`.

Same-spoke / Off-adjacent-left/right Pick-form green; two-spoke still open. Shoelace ≠ Haar.
Classical Pick FAIL.
-/

/-- Strict on-spoke endpoints under `ThreeInterior`. -/
lemma ne_endpoints_of_threeInterior_onSpoke
    {q r s : ℤ × ℤ} (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (_hs : r ∈ edgeLatticePoints q (P.vertex k)) :
    r ≠ q ∧ r ≠ P.vertex k := by
  refine ⟨h.1.symm, ?_⟩
  intro heq
  have hv_bd : P.vertex k ∈ P.boundaryLatticePoints := by
    have : P.vertex k ∈ P.vertexFinset := by
      rw [vertexFinset_eq_univ_image]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
  exact (mem_interior_of_threeInterior_left P h).2 (heq ▸ hv_bd)

/-- Under `ThreeInterior`, if `r` is strictly on spoke `q -- vertex k` and `s`
is not on that spoke, then `edgeGcd = 2`. -/
theorem edgeGcd_eq_two_of_threeInterior_onSpoke
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hs_not : s ∉ edgeLatticePoints q (P.vertex k)) :
    edgeGcd q (P.vertex k) = 2 := by
  classical
  have hne_qv : q ≠ P.vertex k := by
    intro heq
    have hq := mem_interior_of_threeInterior_apex P h
    have hv_bd : P.vertex k ∈ P.boundaryLatticePoints := by
      have : P.vertex k ∈ P.vertexFinset := by
        rw [vertexFinset_eq_univ_image]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
    exact hq.2 (by simpa [heq] using hv_bd)
  have hge2 : 2 ≤ edgeGcd q (P.vertex k) := by
    have hcard := card_edgeLatticePoints q (P.vertex k)
    have hsub : ({q, P.vertex k} : Finset (ℤ × ℤ)) ⊆
        edgeLatticePoints q (P.vertex k) := by
      intro x hx
      have hx' : x = q ∨ x = P.vertex k := by simpa using hx
      rcases hx' with hxq | hxv
      · rw [hxq]; exact self_mem_edgeLatticePoints q (P.vertex k)
      · rw [hxv]; exact other_mem_edgeLatticePoints q (P.vertex k)
    have hcard2 : ({q, P.vertex k} : Finset (ℤ × ℤ)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hne_qv]), Finset.card_singleton]
    have hlt : ({q, P.vertex k} : Finset (ℤ × ℤ)).card <
        (edgeLatticePoints q (P.vertex k)).card := by
      have hr_ne : r ∉ ({q, P.vertex k} : Finset (ℤ × ℤ)) := by
        simp [hne_q, hne_v]
      have : ({q, P.vertex k} : Finset (ℤ × ℤ)).card <
          (insert r ({q, P.vertex k} : Finset (ℤ × ℤ))).card := by
        rw [Finset.card_insert_of_notMem hr_ne]; omega
      have hsub' : insert r ({q, P.vertex k} : Finset (ℤ × ℤ)) ⊆
          edgeLatticePoints q (P.vertex k) := by
        intro x hx
        have hx' : x = r ∨ x = q ∨ x = P.vertex k := by simpa using hx
        rcases hx' with hxr | hxq | hxv
        · rw [hxr]; exact hs
        · rw [hxq]; exact self_mem_edgeLatticePoints q (P.vertex k)
        · rw [hxv]; exact other_mem_edgeLatticePoints q (P.vertex k)
      exact lt_of_lt_of_le this (Finset.card_le_card hsub')
    omega
  by_contra hne2
  have hcard4 : 4 ≤ (edgeLatticePoints q (P.vertex k)).card := by
    have := card_edgeLatticePoints q (P.vertex k); omega
  have hne_qr : q ≠ r := hne_q.symm
  have hne_vr : P.vertex k ≠ r := hne_v.symm
  have hsub3 : ({q, P.vertex k, r} : Finset (ℤ × ℤ)) ⊆
      edgeLatticePoints q (P.vertex k) := by
    intro x hx
    have hx' : x = q ∨ x = P.vertex k ∨ x = r := by simpa using hx
    rcases hx' with hxq | hxv | hxr
    · rw [hxq]; exact self_mem_edgeLatticePoints q (P.vertex k)
    · rw [hxv]; exact other_mem_edgeLatticePoints q (P.vertex k)
    · rw [hxr]; exact hs
  have hcard3 : ({q, P.vertex k, r} : Finset (ℤ × ℤ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hne_qv, hne_qr]),
        Finset.card_insert_of_notMem (by simp [hne_vr]),
        Finset.card_singleton]
  have hlt : ({q, P.vertex k, r} : Finset (ℤ × ℤ)).card <
      (edgeLatticePoints q (P.vertex k)).card := by omega
  obtain ⟨t, htE, htnotin⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have htne : t ≠ q ∧ t ≠ P.vertex k ∧ t ≠ r := by
    refine ⟨?_, ?_, ?_⟩
    · intro htq; exact htnotin (by simp [htq])
    · intro htv; exact htnotin (by simp [htv])
    · intro htr; exact htnotin (by simp [htr])
  have hmem :=
    memClosedTriangle_of_mem_edgeLatticePoints_ab q (P.vertex k)
      (P.vertex (P.nextIdx k)) t htE
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDpos : 0 < latticeDet q (P.vertex k) (P.vertex (P.nextIdx k)) := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hpos k
  rcases eq_vertices_or_rs_of_mem_interiorFan_of_threeInterior P hsc hinj hedge h k
      (by simpa [interiorFanTriangle] using hmem) with h1 | h2 | h3 | h4 | h5
  · exact htne.1 h1
  · exact htne.2.1 h2
  · have : latticeDet q (P.vertex k) (P.vertex (P.nextIdx k)) = 0 :=
      latticeDet_eq_zero_of_mem_edge_ab q (P.vertex k) (P.vertex (P.nextIdx k))
        (by simpa [h3] using htE)
    exact (ne_of_gt hDpos this).elim
  · exact htne.2.2 h4
  · exact hs_not (by simpa [h5] using htE)

/-- Covering-ear classification for a non-apex interior point under
`ThreeInterior`: Off or on-spoke. -/
theorem exists_offBoundary_or_onSpoke_covering_of_threeInterior_left
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) :
    ∃ i : Fin P.nVertices,
      MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r ∧
        (OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r ∨
          r ∈ edgeLatticePoints q (P.vertex i) ∨
            r ∈ edgeLatticePoints (P.vertex (P.nextIdx i)) q) := by
  obtain ⟨i, hr⟩ :=
    exists_mem_interiorFanTriangle_of_threeInterior_left P hsc hinj hedge h
  refine ⟨i, hr, ?_⟩
  exact offBoundary_or_onSpoke_of_mem_interiorFan P
    (mem_interior_of_threeInterior_left P h) i hr

theorem exists_offBoundary_or_onSpoke_covering_of_threeInterior_right
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) :
    ∃ i : Fin P.nVertices,
      MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) s ∧
        (OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) s ∨
          s ∈ edgeLatticePoints q (P.vertex i) ∨
            s ∈ edgeLatticePoints (P.vertex (P.nextIdx i)) q) :=
  exists_offBoundary_or_onSpoke_covering_of_threeInterior_left P hsc hinj hedge
    (ThreeInterior_swap P h)

/-- Lattice points of an ear containing on-spoke `r` but not `s` are among
`{q, vᵢ, vᵢ₊₁, r}`. -/
theorem eq_vertices_or_r_of_mem_interiorFan_of_threeInterior_exclude_s
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (i : Fin P.nVertices)
    (hs_not : ¬ MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) s)
    {p : ℤ × ℤ}
    (hp : MemClosedTriangle (interiorFanTriangle P q i).a
      (interiorFanTriangle P q i).b (interiorFanTriangle P q i).c p) :
    p = q ∨ p = P.vertex i ∨ p = P.vertex (P.nextIdx i) ∨ p = r := by
  rcases eq_vertices_or_rs_of_mem_interiorFan_of_threeInterior P hsc hinj hedge h i hp with
    h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr h4))
  · exact (hs_not (by simpa [interiorFanTriangle, h5] using hp)).elim

/-- Left half-ear △`(q,r,w)` under ThreeInterior on-spoke is empty when `s` is
absent from the left-adjacent ear. -/
theorem eq_vertices_of_memClosedTriangle_threeInterior_onSpoke_left
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hs_not_spoke : s ∉ edgeLatticePoints q (P.vertex k))
    (hs_not_ear : ¬ MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) s)
    {p : ℤ × ℤ}
    (hp : MemClosedTriangle q r (P.vertex (P.nextIdx k)) p) :
    p = q ∨ p = r ∨ p = P.vertex (P.nextIdx k) := by
  classical
  set v := P.vertex k
  set w := P.vertex (P.nextIdx k)
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hs hne_q hne_v
      hs_not_spoke
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDbig : 0 < latticeDet q v w := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, v, w] using hpos k
  have hdouble : latticeDet q v w = 2 * latticeDet q r w :=
    latticeDet_eq_two_mul_of_edgeGcd_eq_two_mem q v w r hd hs hne_q hne_v
  have hDsmall : 0 < latticeDet q r w := by
    have : 0 < 2 * latticeDet q r w := by rwa [← hdouble]
    omega
  have hp_big : MemClosedTriangle q v w p :=
    memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem q v w r p hd hs
      hne_q hne_v hp
  rcases eq_vertices_or_r_of_mem_interiorFan_of_threeInterior_exclude_s
      P hsc hinj hedge h k hs_not_ear
      (by simpa [interiorFanTriangle, v, w] using hp_big) with h1 | h2 | h3 | h4
  · exact Or.inl h1
  · subst h2
    have hγ0 : latticeDet q r v = 0 := by
      have : latticeDet q v r = 0 := latticeDet_eq_zero_of_mem_edge_ab q v r hs
      have hsw : latticeDet q r v = -latticeDet q v r := by unfold latticeDet; ring
      linarith
    have hedge_qr : v ∈ edgeLatticePoints q r :=
      mem_edgeLatticePoints_of_weight_zero_ab q r w v hp hDsmall hγ0
    have hprim : edgeGcd q r = 1 :=
      edgeGcd_eq_one_left_of_edgeGcd_eq_two_mem q v r hd hs hne_q hne_v
    have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one q r v hprim
      (mem_segment_of_mem_edgeLatticePoints q r v hedge_qr)
    refine False.elim (hend.elim ?_ ?_)
    · intro hvq
      have hq_int := mem_interior_of_threeInterior_apex P h
      have hv_bd : v ∈ P.boundaryLatticePoints := by
        have : v ∈ P.vertexFinset := by
          rw [vertexFinset_eq_univ_image]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
      exact hq_int.2 (hvq ▸ hv_bd)
    · intro hvr
      exact (hne_v hvr.symm).elim
  · exact Or.inr (Or.inr h3)
  · exact Or.inr (Or.inl h4)

/-- Right half-ear △`(q,v_prev,r)` under ThreeInterior on-spoke is empty when
`s` is absent from the right-adjacent ear. -/
theorem eq_vertices_of_memClosedTriangle_threeInterior_onSpoke_right
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hs_not_spoke : s ∉ edgeLatticePoints q (P.vertex k))
    (hs_not_ear : ¬ MemClosedTriangle q (P.vertex (P.prevIdx k)) (P.vertex k) s)
    {p : ℤ × ℤ}
    (hp : MemClosedTriangle q (P.vertex (P.prevIdx k)) r p) :
    p = q ∨ p = P.vertex (P.prevIdx k) ∨ p = r := by
  classical
  set v := P.vertex k
  set u := P.vertex (P.prevIdx k)
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hs hne_q hne_v
      hs_not_spoke
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDbig : 0 < latticeDet q u v := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, u, v,
      P.nextIdx_prevIdx] using hpos (P.prevIdx k)
  have hdouble : latticeDet q u v = 2 * latticeDet q u r :=
    latticeDet_eq_two_mul_ac_of_edgeGcd_eq_two_mem q u v r hd hs hne_q hne_v
  have hDsmall : 0 < latticeDet q u r := by
    have : 0 < 2 * latticeDet q u r := by rwa [← hdouble]
    omega
  have hp_big : MemClosedTriangle q u v p :=
    memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem_ac q u v r p hd hs
      hne_q hne_v hp
  have hs_not_ear' :
      ¬ MemClosedTriangle q (P.vertex (P.prevIdx k))
        (P.vertex (P.nextIdx (P.prevIdx k))) s := by
    simpa [P.nextIdx_prevIdx] using hs_not_ear
  rcases eq_vertices_or_r_of_mem_interiorFan_of_threeInterior_exclude_s
      P hsc hinj hedge h (P.prevIdx k) hs_not_ear'
      (by simpa [interiorFanTriangle, u, v, P.nextIdx_prevIdx] using hp_big) with
    h1 | h2 | h3 | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · have hpv : p = v := by simpa [v, P.nextIdx_prevIdx] using h3
    have hp' : MemClosedTriangle q u r v := by simpa [hpv] using hp
    have hβ0 : latticeDet q v r = 0 :=
      latticeDet_eq_zero_of_mem_edge_ab q v r hs
    have hedge_rq : v ∈ edgeLatticePoints r q :=
      mem_edgeLatticePoints_of_weight_zero_ca q u r v hp' hDsmall hβ0
    have hedge_qr : v ∈ edgeLatticePoints q r := mem_edgeLatticePoints_comm hedge_rq
    have hprim : edgeGcd q r = 1 :=
      edgeGcd_eq_one_left_of_edgeGcd_eq_two_mem q v r hd hs hne_q hne_v
    have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one q r v hprim
      (mem_segment_of_mem_edgeLatticePoints q r v hedge_qr)
    refine False.elim (hend.elim ?_ ?_)
    · intro hvq
      have hq_int := mem_interior_of_threeInterior_apex P h
      have hv_bd : v ∈ P.boundaryLatticePoints := by
        have : v ∈ P.vertexFinset := by
          rw [vertexFinset_eq_univ_image]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
      exact hq_int.2 (hvq ▸ hv_bd)
    · intro hvr
      exact (hne_v hvr.symm).elim
  · exact Or.inr (Or.inr h4)

theorem natAbs_latticeDet_eq_one_of_threeInterior_onSpoke_left
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hs_not_spoke : s ∉ edgeLatticePoints q (P.vertex k))
    (hs_not_ear : ¬ MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) s) :
    Int.natAbs (latticeDet q r (P.vertex (P.nextIdx k))) = 1 := by
  classical
  set v := P.vertex k
  set w := P.vertex (P.nextIdx k)
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hs hne_q hne_v
      hs_not_spoke
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDbig : 0 < latticeDet q v w := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, v, w] using hpos k
  have hdouble : latticeDet q v w = 2 * latticeDet q r w :=
    latticeDet_eq_two_mul_of_edgeGcd_eq_two_mem q v w r hd hs hne_q hne_v
  have hDne : latticeDet q r w ≠ 0 := by
    have : 0 < 2 * latticeDet q r w := by rwa [← hdouble]
    omega
  refine natAbs_det_eq_one_of_memClosedTriangle_eq_vertices q r w hDne ?_
  intro p hp
  exact eq_vertices_of_memClosedTriangle_threeInterior_onSpoke_left
    P hsc hinj hedge h k hs hne_q hne_v hs_not_spoke hs_not_ear hp

theorem natAbs_latticeDet_eq_one_of_threeInterior_onSpoke_right
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hs_not_spoke : s ∉ edgeLatticePoints q (P.vertex k))
    (hs_not_ear : ¬ MemClosedTriangle q (P.vertex (P.prevIdx k)) (P.vertex k) s) :
    Int.natAbs (latticeDet q (P.vertex (P.prevIdx k)) r) = 1 := by
  classical
  set v := P.vertex k
  set u := P.vertex (P.prevIdx k)
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hs hne_q hne_v
      hs_not_spoke
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDbig : 0 < latticeDet q u v := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, u, v,
      P.nextIdx_prevIdx] using hpos (P.prevIdx k)
  have hdouble : latticeDet q u v = 2 * latticeDet q u r :=
    latticeDet_eq_two_mul_ac_of_edgeGcd_eq_two_mem q u v r hd hs hne_q hne_v
  have hDne : latticeDet q u r ≠ 0 := by
    have : 0 < 2 * latticeDet q u r := by rwa [← hdouble]
    omega
  refine natAbs_det_eq_one_of_memClosedTriangle_eq_vertices q u r hDne ?_
  intro p hp
  exact eq_vertices_of_memClosedTriangle_threeInterior_onSpoke_right
    P hsc hinj hedge h k hs hne_q hne_v hs_not_spoke hs_not_ear hp

/-- Left-adjacent ear has `interiorFanDet = 2` under ThreeInterior on-spoke. -/
theorem interiorFanDet_eq_two_of_threeInterior_onSpoke_left
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hs_not_spoke : s ∉ edgeLatticePoints q (P.vertex k))
    (hs_not_ear : ¬ MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) s) :
    interiorFanDet P q k = 2 := by
  classical
  set v := P.vertex k
  set w := P.vertex (P.nextIdx k)
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hs hne_q hne_v
      hs_not_spoke
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDbig : 0 < latticeDet q v w := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, v, w] using hpos k
  have hdouble : latticeDet q v w = 2 * latticeDet q r w :=
    latticeDet_eq_two_mul_of_edgeGcd_eq_two_mem q v w r hd hs hne_q hne_v
  have hnat :=
    natAbs_latticeDet_eq_one_of_threeInterior_onSpoke_left
      P hsc hinj hedge h k hs hne_q hne_v hs_not_spoke hs_not_ear
  have hnn : 0 ≤ latticeDet q r w := by
    have : 0 < 2 * latticeDet q r w := by rwa [← hdouble]
    omega
  have hz : latticeDet q r w = (Int.natAbs (latticeDet q r w) : ℤ) :=
    (Int.natAbs_of_nonneg hnn).symm
  have h1 : latticeDet q r w = 1 := by rw [hz, hnat]; norm_num
  have : latticeDet q v w = 2 := by rw [hdouble, h1]; norm_num
  simpa [interiorFanDet, interiorFanTriangle, Triangle.det, v, w] using this

/-- Right-adjacent ear has `interiorFanDet = 2` under ThreeInterior on-spoke. -/
theorem interiorFanDet_eq_two_of_threeInterior_onSpoke_right
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hs_not_spoke : s ∉ edgeLatticePoints q (P.vertex k))
    (hs_not_ear : ¬ MemClosedTriangle q (P.vertex (P.prevIdx k)) (P.vertex k) s) :
    interiorFanDet P q (P.prevIdx k) = 2 := by
  classical
  set v := P.vertex k
  set u := P.vertex (P.prevIdx k)
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hs hne_q hne_v
      hs_not_spoke
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDbig : 0 < latticeDet q u v := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, u, v,
      P.nextIdx_prevIdx] using hpos (P.prevIdx k)
  have hdouble : latticeDet q u v = 2 * latticeDet q u r :=
    latticeDet_eq_two_mul_ac_of_edgeGcd_eq_two_mem q u v r hd hs hne_q hne_v
  have hnat :=
    natAbs_latticeDet_eq_one_of_threeInterior_onSpoke_right
      P hsc hinj hedge h k hs hne_q hne_v hs_not_spoke hs_not_ear
  have hnn : 0 ≤ latticeDet q u r := by
    have : 0 < 2 * latticeDet q u r := by rwa [← hdouble]
    omega
  have hz : latticeDet q u r = (Int.natAbs (latticeDet q u r) : ℤ) :=
    (Int.natAbs_of_nonneg hnn).symm
  have h1 : latticeDet q u r = 1 := by rw [hz, hnat]; norm_num
  have : latticeDet q u v = 2 := by rw [hdouble, h1]; norm_num
  simpa [interiorFanDet, interiorFanTriangle, Triangle.det, u, v,
    P.nextIdx_prevIdx] using this

/-- **I = 3 shoelace Pick-form** under on-spoke `r` + Off `s` in a non-adjacent
ear (not classical Pick).

Adjacent ears: `det = 2`; Off ear: `det = 3`; others: `det = 1`; fan sum `n+4`;
`B = n` ⇒ `shoelace = 3 + B/2 − 1`. Same-spoke / both-on-spoke / Off-adjacent
still open. Shoelace ≠ Haar. Classical Pick FAIL. -/
theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_onSpoke_off
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k j : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hs_ear : MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) s)
    (hoff_s : OffTriangleBoundary q (P.vertex j) (P.vertex (P.nextIdx j)) s)
    (hne_k : j ≠ k) (hne_prev : j ≠ P.prevIdx k) :
    P.shoelace = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  have hq := mem_interior_of_threeInterior_apex P h
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  -- s not on the occupied spoke (else it would occupy ear k by on-spoke left)
  have hs_not_spoke : s ∉ edgeLatticePoints q (P.vertex k) := by
    intro hs_spoke
    have hs_k : MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) s :=
      mem_interiorFan_of_onSpoke_left P k hs_spoke
    have : k = j :=
      eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq j k hs_ear hoff_s
        hs_k
    exact hne_k this.symm
  -- s not in adjacent ears (Off uniqueness)
  have hs_not_k :
      ¬ MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) s := by
    intro hs_k
    have : k = j :=
      eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq j k hs_ear hoff_s
        hs_k
    exact hne_k this.symm
  have hs_not_prev :
      ¬ MemClosedTriangle q (P.vertex (P.prevIdx k)) (P.vertex k) s := by
    intro hs_p
    have hs_p' : MemClosedTriangle q (P.vertex (P.prevIdx k))
        (P.vertex (P.nextIdx (P.prevIdx k))) s := by
      simpa [P.nextIdx_prevIdx] using hs_p
    have : P.prevIdx k = j :=
      eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq j (P.prevIdx k)
        hs_ear hoff_s hs_p'
    exact hne_prev this.symm
  -- r not in Off ear j (on-spoke occupies only adjacent ears via Off contradiction)
  have hr_not_j :
      ¬ MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) r := by
    intro hrj
    -- foreign ear containing on-spoke r is Off, then uniqueness vs left ear
    have hoff_r :
        OffTriangleBoundary q (P.vertex j) (P.vertex (P.nextIdx j)) r := by
      -- reuse TwoInterior-style argument with ThreeInterior edgeGcd=2
      classical
      set vj := P.vertex j
      set wj := P.vertex (P.nextIdx j)
      set vk := P.vertex k
      refine ⟨?_, ?_, ?_⟩
      · intro hspoke
        have hne_vj : r ≠ vj := by
          intro heq
          have hv_bd : vj ∈ P.boundaryLatticePoints := by
            have : vj ∈ P.vertexFinset := by
              rw [vertexFinset_eq_univ_image]
              exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
            exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
          exact (mem_interior_of_threeInterior_left P h).2 (heq ▸ hv_bd)
        have hdj : edgeGcd q vj = 2 :=
          edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h j hspoke
            hne_q hne_vj (by
              intro hs_j
              have hs_j_ear :
                  MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) s :=
                mem_interiorFan_of_onSpoke_left P j hs_j
              -- s Off in j and on spoke j is impossible: Off excludes spokes
              exact hoff_s.1 hs_j)
        have hdk : edgeGcd q vk = 2 :=
          edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hs
            hne_q hne_v hs_not_spoke
        have heq :=
          eq_vertex_of_mem_edgeLatticePoints_of_edgeGcd_eq_two q vj vk r hdj hdk
            hspoke hs hne_q hne_vj hne_v
        exact hne_k (hinj heq)
      · exact not_mem_polygon_edge_of_mem_interior P
          (mem_interior_of_threeInterior_left P h) j
      · intro hspoke
        have hs' : r ∈ edgeLatticePoints q wj := mem_edgeLatticePoints_comm hspoke
        have hne_wj : r ≠ wj := by
          intro heq
          have hv_bd : wj ∈ P.boundaryLatticePoints := by
            have : wj ∈ P.vertexFinset := by
              rw [vertexFinset_eq_univ_image]
              exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
            exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
          exact (mem_interior_of_threeInterior_left P h).2 (heq ▸ hv_bd)
        have hdj : edgeGcd q wj = 2 :=
          edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h (P.nextIdx j)
            hs' hne_q hne_wj (by
              intro hs_w
              exact hoff_s.2.2 (mem_edgeLatticePoints_comm hs_w))
        have hdk : edgeGcd q vk = 2 :=
          edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hs
            hne_q hne_v hs_not_spoke
        have heq :=
          eq_vertex_of_mem_edgeLatticePoints_of_edgeGcd_eq_two q wj vk r hdj hdk
            hs' hs hne_q hne_wj hne_v
        have : P.nextIdx j = k := hinj heq
        have : j = P.prevIdx k := by
          rw [← this, prevIdx_nextIdx]
        exact hne_prev this
    have hrk : MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) r :=
      mem_interiorFan_of_onSpoke_left P k hs
    have : k = j :=
      eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq j k hrj hoff_r hrk
    exact hne_k this.symm
  have hdetL : interiorFanDet P q k = 2 :=
    interiorFanDet_eq_two_of_threeInterior_onSpoke_left
      P hsc hinj hedge h k hs hne_q hne_v hs_not_spoke hs_not_k
  have hdetR : interiorFanDet P q (P.prevIdx k) = 2 :=
    interiorFanDet_eq_two_of_threeInterior_onSpoke_right
      P hsc hinj hedge h k hs hne_q hne_v hs_not_spoke hs_not_prev
  have hdet3 : interiorFanDet P q j = 3 :=
    interiorFanDet_eq_three_of_threeInterior_occupied
      P hsc hinj hedge (ThreeInterior_swap P h) j hs_ear hoff_s hr_not_j
  have hne_adj : k ≠ P.prevIdx k := by
    intro heq
    have hnext : P.nextIdx k = k := by
      have h1 : P.nextIdx k = P.nextIdx (P.prevIdx k) := congrArg P.nextIdx heq
      rw [h1, P.nextIdx_prevIdx]
    have hD : 0 < latticeDet q (P.vertex k) (P.vertex (P.nextIdx k)) := by
      simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hpos k
    rw [hnext] at hD
    have hz : latticeDet q (P.vertex k) (P.vertex k) = 0 := by
      simp only [latticeDet]; ring
    exact (ne_of_gt hD) hz
  have hdet1 : ∀ i : Fin P.nVertices,
      i ≠ k → i ≠ P.prevIdx k → i ≠ j → interiorFanDet P q i = 1 := by
    intro i hik hip hij
    have hempty : ∀ p ∈ P.interiorLatticePoints, p ≠ q →
        ¬ MemClosedTriangle (interiorFanTriangle P q i).a
          (interiorFanTriangle P q i).b (interiorFanTriangle P q i).c p := by
      intro p hp hpq hp_mem
      have hpset : p ∈ ({q, r, s} : Set (ℤ × ℤ)) := by
        rw [← h.2.2.2]; exact hp
      rcases (Set.mem_insert_iff.mp hpset) with hpq' | hp'
      · exact hpq hpq'
      · rcases (Set.mem_insert_iff.mp hp') with hpr | hps
        · -- p = r: only adjacent ears
          have hr_i : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r := by
            simpa [interiorFanTriangle, hpr] using hp_mem
          -- r on-spoke ⇒ if in ear i then i adjacent, else Off uniqueness from left
          by_cases hi_adj : i = k ∨ i = P.prevIdx k
          · rcases hi_adj with h1 | h2
            · exact hik h1
            · exact hip h2
          · push Not at hi_adj
            have hoff_r :
                OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r := by
              -- same Off construction as above with j := i
              classical
              set vj := P.vertex i
              set wj := P.vertex (P.nextIdx i)
              set vk := P.vertex k
              refine ⟨?_, ?_, ?_⟩
              · intro hspoke
                have hne_vj : r ≠ vj := by
                  intro heq
                  have hv_bd : vj ∈ P.boundaryLatticePoints := by
                    have : vj ∈ P.vertexFinset := by
                      rw [vertexFinset_eq_univ_image]
                      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
                    exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
                  exact (mem_interior_of_threeInterior_left P h).2 (heq ▸ hv_bd)
                have hdj : edgeGcd q vj = 2 :=
                  edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h i
                    hspoke hne_q hne_vj (by
                      intro hs_i
                      have : MemClosedTriangle q (P.vertex i)
                          (P.vertex (P.nextIdx i)) s :=
                        mem_interiorFan_of_onSpoke_left P i hs_i
                      have : i = j :=
                        eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq j i
                          hs_ear hoff_s this
                      exact hij this)
                have hdk : edgeGcd q vk = 2 :=
                  edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hs
                    hne_q hne_v hs_not_spoke
                have heq :=
                  eq_vertex_of_mem_edgeLatticePoints_of_edgeGcd_eq_two
                    q vj vk r hdj hdk hspoke hs hne_q hne_vj hne_v
                exact hi_adj.1 (hinj heq)
              · exact not_mem_polygon_edge_of_mem_interior P
                  (mem_interior_of_threeInterior_left P h) i
              · intro hspoke
                have hs' : r ∈ edgeLatticePoints q wj :=
                  mem_edgeLatticePoints_comm hspoke
                have hne_wj : r ≠ wj := by
                  intro heq
                  have hv_bd : wj ∈ P.boundaryLatticePoints := by
                    have : wj ∈ P.vertexFinset := by
                      rw [vertexFinset_eq_univ_image]
                      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
                    exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
                  exact (mem_interior_of_threeInterior_left P h).2 (heq ▸ hv_bd)
                have hdj : edgeGcd q wj = 2 :=
                  edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h
                    (P.nextIdx i) hs' hne_q hne_wj (by
                      intro hs_w
                      -- s on spoke nextIdx i ⇒ s on right spoke of ear i; Off unique to j
                      have hs_i :
                          MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) s := by
                        simpa [P.prevIdx_nextIdx] using
                          mem_interiorFan_of_onSpoke_right P (P.nextIdx i) hs_w
                      have : i = j :=
                        eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq j i
                          hs_ear hoff_s hs_i
                      exact hij this)
                have hdk : edgeGcd q vk = 2 :=
                  edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hs
                    hne_q hne_v hs_not_spoke
                have heq :=
                  eq_vertex_of_mem_edgeLatticePoints_of_edgeGcd_eq_two
                    q wj vk r hdj hdk hs' hs hne_q hne_wj hne_v
                have : P.nextIdx i = k := hinj heq
                have : i = P.prevIdx k := by
                  rw [← this, prevIdx_nextIdx]
                exact hi_adj.2 this
            have hrk : MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) r :=
              mem_interiorFan_of_onSpoke_left P k hs
            have : k = i :=
              eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq i k hr_i
                hoff_r hrk
            exact hik this.symm
        · -- p = s: only ear j
          have hps' : p = s := Set.mem_singleton_iff.mp hps
          have hs_i : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) s := by
            simpa [interiorFanTriangle, hps'] using hp_mem
          have : i = j :=
            eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq j i hs_ear
              hoff_s hs_i
          exact hij this
    exact interiorFanDet_eq_one_of_no_other_interior
      P hsc hinj hedge hq i hempty
  -- Fan sum: erase k, prevIdx k, j (need them pairwise distinct)
  have hne_kj : k ≠ j := hne_k.symm
  have hne_pj : P.prevIdx k ≠ j := hne_prev.symm
  have hsum :
      (∑ i : Fin P.nVertices, interiorFanDet P q i) = (P.nVertices : ℤ) + 4 := by
    set S1 := Finset.univ.erase k
    set S2 := S1.erase (P.prevIdx k)
    set S3 := S2.erase j
    have hk_mem : k ∈ Finset.univ := Finset.mem_univ k
    have hp_mem : P.prevIdx k ∈ S1 :=
      Finset.mem_erase.mpr ⟨hne_adj.symm, Finset.mem_univ _⟩
    have hj_mem : j ∈ S2 := by
      refine Finset.mem_erase.mpr ⟨hne_pj.symm, ?_⟩
      exact Finset.mem_erase.mpr ⟨hne_kj.symm, Finset.mem_univ _⟩
    have hdecomp1 :
        (∑ i : Fin P.nVertices, interiorFanDet P q i) =
          interiorFanDet P q k + ∑ i ∈ S1, interiorFanDet P q i := by
      dsimp [S1]; rw [add_comm]
      exact (Finset.sum_erase_add (s := Finset.univ) (interiorFanDet P q)
        hk_mem).symm
    have hdecomp2 :
        ∑ i ∈ S1, interiorFanDet P q i =
          interiorFanDet P q (P.prevIdx k) + ∑ i ∈ S2, interiorFanDet P q i := by
      dsimp [S2]; rw [add_comm]
      exact (Finset.sum_erase_add (s := S1) (interiorFanDet P q) hp_mem).symm
    have hdecomp3 :
        ∑ i ∈ S2, interiorFanDet P q i =
          interiorFanDet P q j + ∑ i ∈ S3, interiorFanDet P q i := by
      dsimp [S3]; rw [add_comm]
      exact (Finset.sum_erase_add (s := S2) (interiorFanDet P q) hj_mem).symm
    have hrest : ∑ i ∈ S3, interiorFanDet P q i = ∑ i ∈ S3, (1 : ℤ) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have ⟨hij', hi2⟩ := Finset.mem_erase.mp hi
      have ⟨hip', hi3⟩ := Finset.mem_erase.mp hi2
      have ⟨hik', _⟩ := Finset.mem_erase.mp hi3
      exact hdet1 i hik' hip' hij'
    have hcard : S3.card = P.nVertices - 3 := by
      dsimp [S3, S2, S1]
      have h1 : (Finset.univ.erase k).card = P.nVertices - 1 := by
        rw [Finset.card_erase_of_mem hk_mem, Finset.card_univ, Fintype.card_fin]
      have h2 : ((Finset.univ.erase k).erase (P.prevIdx k)).card =
          (Finset.univ.erase k).card - 1 :=
        Finset.card_erase_of_mem hp_mem
      have h3 :
          (((Finset.univ.erase k).erase (P.prevIdx k)).erase j).card =
            ((Finset.univ.erase k).erase (P.prevIdx k)).card - 1 :=
        Finset.card_erase_of_mem hj_mem
      have : 3 ≤ P.nVertices := P.length_ge
      omega
    calc
      ∑ i : Fin P.nVertices, interiorFanDet P q i
          = interiorFanDet P q k + ∑ i ∈ S1, interiorFanDet P q i := hdecomp1
      _ = 2 + (interiorFanDet P q (P.prevIdx k) +
              ∑ i ∈ S2, interiorFanDet P q i) := by rw [hdetL, hdecomp2]
      _ = 2 + (2 + (interiorFanDet P q j + ∑ i ∈ S3, interiorFanDet P q i)) := by
            rw [hdetR, hdecomp3]
      _ = 2 + (2 + (3 + ∑ i ∈ S3, (1 : ℤ))) := by rw [hdet3, hrest]
      _ = 7 + (S3.card : ℤ) := by simp; ring
      _ = 7 + ((P.nVertices - 3 : ℕ) : ℤ) := by rw [hcard]
      _ = (P.nVertices : ℤ) + 4 := by
            have : 3 ≤ P.nVertices := P.length_ge
            have hcast : ((P.nVertices - 3 : ℕ) : ℤ) = (P.nVertices : ℤ) - 3 :=
              Nat.cast_sub this
            rw [hcast]; ring
  have hshoelaceSum : P.shoelaceSum = (P.nVertices : ℤ) + 4 := by
    rw [← sum_interiorFanDet_eq_shoelaceSum P q, hsum]
  have hB : P.B = P.nVertices := B_eq_nVertices_of_primitive_edges P hedge hinj
  have hnn : 0 ≤ P.shoelaceSum := by
    have : 0 ≤ (P.nVertices : ℤ) + 4 := by
      have : 3 ≤ P.nVertices := P.length_ge; omega
    simpa [hshoelaceSum] using this
  have hnat : Int.natAbs P.shoelaceSum = P.nVertices + 4 := by
    apply Int.natCast_inj.mp
    rw [Int.natAbs_of_nonneg hnn, hshoelaceSum]
    push_cast; ring
  calc
    P.shoelace = (Int.natAbs P.shoelaceSum : ℚ) / 2 := rfl
    _ = ((P.nVertices + 4 : ℕ) : ℚ) / 2 := by
          have : (Int.natAbs P.shoelaceSum : ℚ) = ((P.nVertices + 4 : ℕ) : ℚ) := by
            exact_mod_cast hnat
          rw [this]
    _ = (P.nVertices : ℚ) / 2 + 2 := by push_cast; ring
    _ = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := by rw [hB]; ring


/-! ### Off-adjacent companion (on-spoke + Off in adjacent ear; not classical Pick)

When `r` lies on spoke `k` and `s` is Off in ear `k`, `s` is the midpoint of
the diagonal from `r` to `v_{k+1}`. Double-doubling yields `interiorFanDet = 4`;
the other adjacent ear keeps `det = 2`; foreign ears `det = 1`; fan sum `n+4`.
Shoelace ≠ Haar. Classical Pick FAIL.
-/

/-- Under Off-adjacent left, `s` lies on the diagonal `r — v_{k+1}`. -/
theorem mem_diagonal_of_threeInterior_onSpoke_off_adjacent_left
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hr : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hs_ear : MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) s)
    (hoff_s : OffTriangleBoundary q (P.vertex k) (P.vertex (P.nextIdx k)) s) :
    s ∈ edgeLatticePoints r (P.vertex (P.nextIdx k)) := by
  classical
  set v := P.vertex k
  set w := P.vertex (P.nextIdx k)
  have hs_not_spoke : s ∉ edgeLatticePoints q v := fun hs_sp => hoff_s.1 hs_sp
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hr hne_q hne_v
      hs_not_spoke
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDbig : 0 < latticeDet q v w := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, v, w] using hpos k
  have hdouble : latticeDet q v w = 2 * latticeDet q r w :=
    latticeDet_eq_two_mul_of_edgeGcd_eq_two_mem q v w r hd hr hne_q hne_v
  have hadd : latticeDet q v w = latticeDet q r w + latticeDet r v w :=
    latticeDet_add_of_mem_edgeLatticePoints q v w r hr
  have heq_halves : latticeDet q r w = latticeDet r v w := by linarith
  have hDsmall : 0 < latticeDet q r w := by
    have : 0 < 2 * latticeDet q r w := by rwa [← hdouble]
    omega
  have hDRpos : 0 < latticeDet r v w := by linarith [heq_halves]
  have hsplit :=
    memClosedTriangle_split_of_edgeGcd_eq_two_mem q v w r s hd hr hne_q hne_v hs_ear
  have hsub_big : ∀ p, MemClosedTriangle q v w p →
      p = q ∨ p = v ∨ p = w ∨ p = r ∨ p = s := by
    intro p hp
    simpa [interiorFanTriangle, v, w] using
      eq_vertices_or_rs_of_mem_interiorFan_of_threeInterior P hsc hinj hedge h k
        (by simpa [interiorFanTriangle] using hp)
  -- Helper: v ∉ △(q,r,w) and q ∉ △(r,v,w)
  have v_not_left : ¬ MemClosedTriangle q r w v := by
    intro hp
    have hγ0 : latticeDet q r v = 0 := by
      have : latticeDet q v r = 0 := latticeDet_eq_zero_of_mem_edge_ab q v r hr
      have hsw : latticeDet q r v = -latticeDet q v r := by unfold latticeDet; ring
      linarith
    have hedge_qr : v ∈ edgeLatticePoints q r :=
      mem_edgeLatticePoints_of_weight_zero_ab q r w v hp hDsmall hγ0
    have hprim : edgeGcd q r = 1 :=
      edgeGcd_eq_one_left_of_edgeGcd_eq_two_mem q v r hd hr hne_q hne_v
    have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one q r v hprim
      (mem_segment_of_mem_edgeLatticePoints q r v hedge_qr)
    exact hend.elim
      (fun hvq => by
        have hq_int := mem_interior_of_threeInterior_apex P h
        have hv_bd : v ∈ P.boundaryLatticePoints := by
          have : v ∈ P.vertexFinset := by
            rw [vertexFinset_eq_univ_image]
            exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
          exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
        exact hq_int.2 (hvq ▸ hv_bd))
      (fun hvr => hne_v hvr.symm)
  have q_not_right : ¬ MemClosedTriangle r v w q := by
    intro hp
    have hγ0 : latticeDet r v q = 0 := by
      have : latticeDet q v r = 0 := latticeDet_eq_zero_of_mem_edge_ab q v r hr
      have h1 : latticeDet q r v = -latticeDet q v r := by unfold latticeDet; ring
      have h2 : latticeDet r v q = latticeDet q r v :=
        (latticeDet_cyclic q r v).symm
      linarith
    have hedge_rv : q ∈ edgeLatticePoints r v :=
      mem_edgeLatticePoints_of_weight_zero_ab r v w q hp hDRpos hγ0
    have hprim : edgeGcd r v = 1 :=
      edgeGcd_eq_one_right_of_edgeGcd_eq_two_mem q v r hd hr hne_q hne_v
    have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one r v q hprim
      (mem_segment_of_mem_edgeLatticePoints r v q hedge_rv)
    exact hend.elim (fun hqr => hne_q hqr.symm) (fun hqv => by
      have hq_int := mem_interior_of_threeInterior_apex P h
      have hv_bd : v ∈ P.boundaryLatticePoints := by
        have : v ∈ P.vertexFinset := by
          rw [vertexFinset_eq_univ_image]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
      exact hq_int.2 (hqv ▸ hv_bd))
  rcases hsplit with hsL | hsR
  · by_cases hdiag : s ∈ edgeLatticePoints r w
    · exact hdiag
    · -- s Off left half; right empty ⇒ det contradiction
      have hoffL : OffTriangleBoundary q r w s := by
        refine ⟨?_, hdiag, ?_⟩
        · intro hqr
          have hprim : edgeGcd q r = 1 :=
            edgeGcd_eq_one_left_of_edgeGcd_eq_two_mem q v r hd hr hne_q hne_v
          have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one q r s hprim
            (mem_segment_of_mem_edgeLatticePoints q r s hqr)
          rcases hend with hsq | hsr
          · exact h.2.1 hsq.symm
          · exact h.2.2.1 hsr.symm
        · exact hoff_s.2.2
      have hsubL : ∀ p, MemClosedTriangle q r w p →
          p = q ∨ p = r ∨ p = w ∨ p = s := by
        intro p hp
        have hp_big : MemClosedTriangle q v w p :=
          memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem q v w r p
            hd hr hne_q hne_v hp
        rcases hsub_big p hp_big with h1 | h2 | h3 | h4 | h5
        · exact Or.inl h1
        · exact absurd (h2 ▸ hp) v_not_left
        · exact Or.inr (Or.inr (Or.inl h3))
        · exact Or.inr (Or.inl h4)
        · exact Or.inr (Or.inr (Or.inr h5))
      have hdetL3 : latticeDet q r w = 3 :=
        latticeDet_eq_three_of_subset_four_off q r w s hDsmall hsubL hoffL hsL
      have hsubR : ∀ p, MemClosedTriangle r v w p → p = r ∨ p = v ∨ p = w := by
        intro p hp
        have hp_big : MemClosedTriangle q v w p :=
          memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem_right
            q v w r p hd hr hne_q hne_v hp
        rcases hsub_big p hp_big with h1 | h2 | h3 | h4 | h5
        · exact absurd (h1 ▸ hp) q_not_right
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr h3)
        · exact Or.inl h4
        · -- p = s in right half too ⇒ on diagonal, contradict hdiag
          exact absurd
            (mem_edgeLatticePoints_of_memClosedTriangle_both_halves
              q v w r s hd hr hne_q hne_v hDsmall hDRpos hsL (h5 ▸ hp))
            hdiag
      have hnat1 : Int.natAbs (latticeDet r v w) = 1 :=
        natAbs_det_eq_one_of_memClosedTriangle_eq_vertices r v w
          (ne_of_gt hDRpos) hsubR
      have hdetR1 : latticeDet r v w = 1 := by
        have hnn : 0 ≤ latticeDet r v w := le_of_lt hDRpos
        have : latticeDet r v w = (Int.natAbs (latticeDet r v w) : ℤ) :=
          (Int.natAbs_of_nonneg hnn).symm
        rw [this, hnat1]; norm_num
      linarith [hdetL3, heq_halves, hdetR1]
  · by_cases hdiag : s ∈ edgeLatticePoints r w
    · exact hdiag
    · have hoffR : OffTriangleBoundary r v w s := by
        refine ⟨?_, hoff_s.2.1, fun hwr => hdiag (mem_edgeLatticePoints_comm hwr)⟩
        · intro hrv
          have hprim : edgeGcd r v = 1 :=
            edgeGcd_eq_one_right_of_edgeGcd_eq_two_mem q v r hd hr hne_q hne_v
          have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one r v s hprim
            (mem_segment_of_mem_edgeLatticePoints r v s hrv)
          rcases hend with hsr | hsv
          · exact h.2.2.1 hsr.symm
          · have hv_bd : v ∈ P.boundaryLatticePoints := by
              have : v ∈ P.vertexFinset := by
                rw [vertexFinset_eq_univ_image]
                exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
              exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
            exact (mem_interior_of_threeInterior_right P h).2 (hsv ▸ hv_bd)
      have hsubR : ∀ p, MemClosedTriangle r v w p →
          p = r ∨ p = v ∨ p = w ∨ p = s := by
        intro p hp
        have hp_big : MemClosedTriangle q v w p :=
          memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem_right
            q v w r p hd hr hne_q hne_v hp
        rcases hsub_big p hp_big with h1 | h2 | h3 | h4 | h5
        · exact absurd (h1 ▸ hp) q_not_right
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (Or.inl h3))
        · exact Or.inl h4
        · exact Or.inr (Or.inr (Or.inr h5))
      have hdetR3 : latticeDet r v w = 3 :=
        latticeDet_eq_three_of_subset_four_off r v w s hDRpos hsubR hoffR hsR
      have hsubL : ∀ p, MemClosedTriangle q r w p → p = q ∨ p = r ∨ p = w := by
        intro p hp
        have hp_big : MemClosedTriangle q v w p :=
          memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem q v w r p
            hd hr hne_q hne_v hp
        rcases hsub_big p hp_big with h1 | h2 | h3 | h4 | h5
        · exact Or.inl h1
        · exact absurd (h2 ▸ hp) v_not_left
        · exact Or.inr (Or.inr h3)
        · exact Or.inr (Or.inl h4)
        · exact absurd
            (mem_edgeLatticePoints_of_memClosedTriangle_both_halves
              q v w r s hd hr hne_q hne_v hDsmall hDRpos (h5 ▸ hp) hsR)
            hdiag
      have hnat1 : Int.natAbs (latticeDet q r w) = 1 :=
        natAbs_det_eq_one_of_memClosedTriangle_eq_vertices q r w
          (ne_of_gt hDsmall) hsubL
      have hdetL1 : latticeDet q r w = 1 := by
        have hnn : 0 ≤ latticeDet q r w := le_of_lt hDsmall
        have : latticeDet q r w = (Int.natAbs (latticeDet q r w) : ℤ) :=
          (Int.natAbs_of_nonneg hnn).symm
        rw [this, hnat1]; norm_num
      linarith [hdetR3, heq_halves, hdetL1]



/-- Diagonal of Off-adjacent left ear has `edgeGcd = 2` (unique midpoint `s`). -/
theorem edgeGcd_eq_two_of_diagonal_threeInterior_onSpoke_off_adjacent_left
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hr : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hs_ear : MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) s)
    (hoff_s : OffTriangleBoundary q (P.vertex k) (P.vertex (P.nextIdx k)) s) :
    edgeGcd r (P.vertex (P.nextIdx k)) = 2 := by
  classical
  set v := P.vertex k
  set w := P.vertex (P.nextIdx k)
  have hs_diag : s ∈ edgeLatticePoints r w :=
    mem_diagonal_of_threeInterior_onSpoke_off_adjacent_left
      P hsc hinj hedge h k hr hne_q hne_v hs_ear hoff_s
  have hne_sr : s ≠ r := h.2.2.1.symm
  have hne_sw : s ≠ w := by
    intro heq
    have hv_bd : w ∈ P.boundaryLatticePoints := by
      have : w ∈ P.vertexFinset := by
        rw [vertexFinset_eq_univ_image]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
    exact (mem_interior_of_threeInterior_right P h).2 (heq ▸ hv_bd)
  have hne_rw : r ≠ w := by
    intro heq
    have hz : edgeGcd r w = 0 := (edgeGcd_eq_zero_iff r w).mpr heq
    have hE : edgeLatticePoints r w = {r} := by
      unfold edgeLatticePoints; simp [hz]
    have hs' : s ∈ ({r} : Finset (ℤ × ℤ)) := by rwa [hE] at hs_diag
    exact hne_sr (Finset.mem_singleton.mp hs')
  have hge2 : 2 ≤ edgeGcd r w := by
    have hsub : ({r, w, s} : Finset (ℤ × ℤ)) ⊆ edgeLatticePoints r w := by
      intro x hx
      have hx' : x = r ∨ x = w ∨ x = s := by simpa using hx
      rcases hx' with hxr | hxw | hxs
      · rw [hxr]; exact self_mem_edgeLatticePoints r w
      · rw [hxw]; exact other_mem_edgeLatticePoints r w
      · rw [hxs]; exact hs_diag
    have hcard3 : ({r, w, s} : Finset (ℤ × ℤ)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hne_rw, hne_sr.symm]),
          Finset.card_insert_of_notMem (by simp [hne_sw.symm]),
          Finset.card_singleton]
    have : 3 ≤ (edgeLatticePoints r w).card :=
      hcard3 ▸ Finset.card_le_card hsub
    have := card_edgeLatticePoints r w
    omega
  by_contra hne2
  have hge3 : 3 ≤ edgeGcd r w := by omega
  have hcard4 : 4 ≤ (edgeLatticePoints r w).card := by
    have := card_edgeLatticePoints r w; omega
  have hsub3 : ({r, w, s} : Finset (ℤ × ℤ)) ⊆ edgeLatticePoints r w := by
    intro x hx
    have hx' : x = r ∨ x = w ∨ x = s := by simpa using hx
    rcases hx' with hxr | hxw | hxs
    · rw [hxr]; exact self_mem_edgeLatticePoints r w
    · rw [hxw]; exact other_mem_edgeLatticePoints r w
    · rw [hxs]; exact hs_diag
  have hcard3 : ({r, w, s} : Finset (ℤ × ℤ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hne_rw, hne_sr.symm]),
        Finset.card_insert_of_notMem (by simp [hne_sw.symm]),
        Finset.card_singleton]
  have hltc : ({r, w, s} : Finset (ℤ × ℤ)).card <
      (edgeLatticePoints r w).card := by omega
  obtain ⟨t, htE, htnotin⟩ := Finset.exists_mem_notMem_of_card_lt_card hltc
  have htne : t ≠ r ∧ t ≠ w ∧ t ≠ s :=
    ⟨fun htr => htnotin (by simp [htr]),
     fun htw => htnotin (by simp [htw]),
     fun hts => htnotin (by simp [hts])⟩
  have hs_not_spoke : s ∉ edgeLatticePoints q v := fun hs_sp => hoff_s.1 hs_sp
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hr hne_q hne_v
      hs_not_spoke
  have ht_small : MemClosedTriangle q r w t :=
    memClosedTriangle_of_mem_edgeLatticePoints_bc q r w t htE
  have ht_ear : MemClosedTriangle q v w t :=
    memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem
      q v w r t hd hr hne_q hne_v ht_small
  have hdouble : latticeDet q v w = 2 * latticeDet q r w :=
    latticeDet_eq_two_mul_of_edgeGcd_eq_two_mem q v w r hd hr hne_q hne_v
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDbig : 0 < latticeDet q v w := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, v, w] using hpos k
  have hDsmall : 0 < latticeDet q r w := by
    have : 0 < 2 * latticeDet q r w := by rwa [← hdouble]
    omega
  have hadd : latticeDet q v w = latticeDet q r w + latticeDet r v w :=
    latticeDet_add_of_mem_edgeLatticePoints q v w r hr
  have heq_halves : latticeDet q r w = latticeDet r v w := by linarith
  have hDRpos : 0 < latticeDet r v w := by linarith
  rcases eq_vertices_or_rs_of_mem_interiorFan_of_threeInterior
      P hsc hinj hedge h k (by simpa [interiorFanTriangle, v, w] using ht_ear) with
    h1 | h2 | h3 | h4 | h5
  · -- t = q
    have htq : t = q := h1
    have hγ0 : latticeDet r w q = 0 := by
      simpa [htq] using latticeDet_eq_zero_of_mem_edge_ab r w t htE
    have : latticeDet q r w = 0 := by
      have hc : latticeDet r w q = latticeDet q r w :=
        (latticeDet_cyclic q r w).symm
      linarith
    exact (ne_of_gt hDsmall) this
  · -- t = v
    have htv : t = v := h2
    have hz : latticeDet r w v = 0 := by
      simpa [htv] using latticeDet_eq_zero_of_mem_edge_ab r w t htE
    have : latticeDet r v w = 0 := by
      have hsw : latticeDet r w v = -latticeDet r v w := by unfold latticeDet; ring
      linarith
    exact (ne_of_gt hDRpos) this
  · exact htne.2.1 h3
  · exact htne.1 h4
  · exact htne.2.2 h5


/-- Left Off-adjacent ear has `interiorFanDet = 4` via diagonal midpoint double-doubling. -/
theorem interiorFanDet_eq_four_of_threeInterior_onSpoke_off_adjacent_left
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hr : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hs_ear : MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) s)
    (hoff_s : OffTriangleBoundary q (P.vertex k) (P.vertex (P.nextIdx k)) s) :
    interiorFanDet P q k = 4 := by
  classical
  set v := P.vertex k
  set w := P.vertex (P.nextIdx k)
  have hs_not_spoke : s ∉ edgeLatticePoints q v := fun hs_sp => hoff_s.1 hs_sp
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hr hne_q hne_v
      hs_not_spoke
  have hs_diag : s ∈ edgeLatticePoints r w :=
    mem_diagonal_of_threeInterior_onSpoke_off_adjacent_left
      P hsc hinj hedge h k hr hne_q hne_v hs_ear hoff_s
  have hd_diag : edgeGcd r w = 2 :=
    edgeGcd_eq_two_of_diagonal_threeInterior_onSpoke_off_adjacent_left
      P hsc hinj hedge h k hr hne_q hne_v hs_ear hoff_s
  have hne_sr : s ≠ r := h.2.2.1.symm
  have hne_sw : s ≠ w := by
    intro heq
    have hv_bd : w ∈ P.boundaryLatticePoints := by
      have : w ∈ P.vertexFinset := by
        rw [vertexFinset_eq_univ_image]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
    exact (mem_interior_of_threeInterior_right P h).2 (heq ▸ hv_bd)
  have hdouble1 : latticeDet q v w = 2 * latticeDet q r w :=
    latticeDet_eq_two_mul_of_edgeGcd_eq_two_mem q v w r hd hr hne_q hne_v
  have hdouble2 : latticeDet q r w = 2 * latticeDet q r s :=
    latticeDet_eq_two_mul_of_edgeGcd_eq_two_mem_bc q r w s hd_diag hs_diag hne_sr
      hne_sw
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDbig : 0 < latticeDet q v w := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, v, w] using hpos k
  have hDmid : 0 < latticeDet q r w := by
    have : 0 < 2 * latticeDet q r w := by rwa [← hdouble1]
    omega
  have hDtiny : 0 < latticeDet q r s := by
    have : 0 < 2 * latticeDet q r s := by rwa [← hdouble2]
    omega
  have hsub : ∀ p, MemClosedTriangle q r s p → p = q ∨ p = r ∨ p = s := by
    intro p hp
    have hp_mid : MemClosedTriangle q r w p :=
      memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem_bc
        q r w s p hd_diag hs_diag hne_sr hne_sw hp
    have hp_big : MemClosedTriangle q v w p :=
      memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem
        q v w r p hd hr hne_q hne_v hp_mid
    rcases eq_vertices_or_rs_of_mem_interiorFan_of_threeInterior
        P hsc hinj hedge h k (by simpa [interiorFanTriangle, v, w] using hp_big) with
      h1 | h2 | h3 | h4 | h5
    · exact Or.inl h1
    · -- p = v: collinear on q—r
      subst h2
      have hγ0 : latticeDet q r v = 0 := by
        have : latticeDet q v r = 0 := latticeDet_eq_zero_of_mem_edge_ab q v r hr
        have hsw : latticeDet q r v = -latticeDet q v r := by unfold latticeDet; ring
        linarith
      have hedge_qr : v ∈ edgeLatticePoints q r :=
        mem_edgeLatticePoints_of_weight_zero_ab q r s v hp hDtiny hγ0
      have hprim : edgeGcd q r = 1 :=
        edgeGcd_eq_one_left_of_edgeGcd_eq_two_mem q v r hd hr hne_q hne_v
      have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one q r v hprim
        (mem_segment_of_mem_edgeLatticePoints q r v hedge_qr)
      exact False.elim (hend.elim
        (fun hvq => by
          have hq_int := mem_interior_of_threeInterior_apex P h
          have hv_bd : v ∈ P.boundaryLatticePoints := by
            have : v ∈ P.vertexFinset := by
              rw [vertexFinset_eq_univ_image]
              exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
            exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
          exact hq_int.2 (hvq ▸ hv_bd))
        (fun hvr => hne_v hvr.symm))
    · -- p = w: collinear on r—s (half of rw)
      subst h3
      have hγ0 : latticeDet q r w = 0 ∨ True := Or.inr trivial
      -- w on △(q,r,s): weight on edge rs
      have hprim : edgeGcd r s = 1 :=
        edgeGcd_eq_one_left_of_edgeGcd_eq_two_mem r w s hd_diag hs_diag hne_sr hne_sw
      -- latticeDet r s w = 0 since s mid of rw ⇒ w,s,r collinear
      have hz : latticeDet r s w = 0 := by
        obtain ⟨hx, hy⟩ :=
          two_mul_sub_of_mem_edgeLatticePoints_of_edgeGcd_eq_two r w s hd_diag
            hs_diag hne_sr hne_sw
        -- w - r = 2(s - r) ⇒ w,s,r collinear
        simp only [latticeDet]
        have hx' : w.1 - r.1 = 2 * (s.1 - r.1) := by linarith
        have hy' : w.2 - r.2 = 2 * (s.2 - r.2) := by linarith
        -- latticeDet r s w = (s-r)×(w-r) = (s-r)×2(s-r) = 0
        have : (s.1 - r.1) * (w.2 - r.2) - (s.2 - r.2) * (w.1 - r.1) = 0 := by
          rw [hx', hy']; ring
        exact this
      have hedge_rs : w ∈ edgeLatticePoints r s :=
        mem_edgeLatticePoints_of_weight_zero_bc q r s w hp hDtiny (by
          -- latticeDet r s w = 0 is weight for q? 
          -- weight_zero_bc: latticeDet v w p = 0 with (q,v,w)=(q,r,s) means
          -- latticeDet r s w = 0 ⇒ w on edge r s. Yes!
          exact hz)
      have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one r s w hprim
        (mem_segment_of_mem_edgeLatticePoints r s w hedge_rs)
      exact False.elim (hend.elim
        (fun hwr => by
          have : edgeGcd r w = 0 := (edgeGcd_eq_zero_iff r w).mpr hwr.symm
          omega)
        (fun hws => hne_sw hws.symm))
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr h5)
  have hnat1 : Int.natAbs (latticeDet q r s) = 1 :=
    natAbs_det_eq_one_of_memClosedTriangle_eq_vertices q r s (ne_of_gt hDtiny) hsub
  have hdet1 : latticeDet q r s = 1 := by
    have hnn : 0 ≤ latticeDet q r s := le_of_lt hDtiny
    have : latticeDet q r s = (Int.natAbs (latticeDet q r s) : ℤ) :=
      (Int.natAbs_of_nonneg hnn).symm
    rw [this, hnat1]; norm_num
  have : latticeDet q v w = 4 := by
    rw [hdouble1, hdouble2, hdet1]; norm_num
  simpa [interiorFanDet, interiorFanTriangle, Triangle.det, v, w] using this


/-- **I = 3 shoelace Pick-form** under on-spoke + Off-adjacent-left (not classical Pick).

`r` on spoke `k`, `s` Off in ear `k`: ear `k` has `det = 4`, right-adjacent
`det = 2`, foreign `det = 1`; fan sum `n+4`; `B = n` ⇒ `shoelace = 3 + B/2 − 1`.
Right-adjacent (`s` in ear `prevIdx k`) follows by mirror. Shoelace ≠ Haar. Classical Pick FAIL. -/
theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_onSpoke_off_adjacent_left
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hr : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hs_ear : MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) s)
    (hoff_s : OffTriangleBoundary q (P.vertex k) (P.vertex (P.nextIdx k)) s) :
    P.shoelace = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  have hq := mem_interior_of_threeInterior_apex P h
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hs_not_spoke : s ∉ edgeLatticePoints q (P.vertex k) := fun hs_sp => hoff_s.1 hs_sp
  have hs_not_prev :
      ¬ MemClosedTriangle q (P.vertex (P.prevIdx k)) (P.vertex k) s := by
    intro hs_p
    have hs_p' : MemClosedTriangle q (P.vertex (P.prevIdx k))
        (P.vertex (P.nextIdx (P.prevIdx k))) s := by
      simpa [P.nextIdx_prevIdx] using hs_p
    have : P.prevIdx k = k :=
      eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq k (P.prevIdx k)
        hs_ear hoff_s hs_p'
    have hne_adj : P.prevIdx k ≠ k := by
      intro heq
      have hnext : P.nextIdx k = k := by
        have h1 : P.nextIdx k = P.nextIdx (P.prevIdx k) := congrArg P.nextIdx heq.symm
        rw [h1, P.nextIdx_prevIdx]
      have hD : 0 < latticeDet q (P.vertex k) (P.vertex (P.nextIdx k)) := by
        simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hpos k
      rw [hnext] at hD
      have hz : latticeDet q (P.vertex k) (P.vertex k) = 0 := by
        simp only [latticeDet]; ring
      exact (ne_of_gt hD) hz
    exact hne_adj this
  have hdet4 : interiorFanDet P q k = 4 :=
    interiorFanDet_eq_four_of_threeInterior_onSpoke_off_adjacent_left
      P hsc hinj hedge h k hr hne_q hne_v hs_ear hoff_s
  have hdetR : interiorFanDet P q (P.prevIdx k) = 2 :=
    interiorFanDet_eq_two_of_threeInterior_onSpoke_right
      P hsc hinj hedge h k hr hne_q hne_v hs_not_spoke hs_not_prev
  have hne_adj : k ≠ P.prevIdx k := by
    intro heq
    have hnext : P.nextIdx k = k := by
      have h1 : P.nextIdx k = P.nextIdx (P.prevIdx k) := congrArg P.nextIdx heq
      rw [h1, P.nextIdx_prevIdx]
    have hD : 0 < latticeDet q (P.vertex k) (P.vertex (P.nextIdx k)) := by
      simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hpos k
    rw [hnext] at hD
    have hz : latticeDet q (P.vertex k) (P.vertex k) = 0 := by
      simp only [latticeDet]; ring
    exact (ne_of_gt hD) hz
  have hdet1 : ∀ i : Fin P.nVertices,
      i ≠ k → i ≠ P.prevIdx k → interiorFanDet P q i = 1 := by
    intro i hik hip
    have hempty : ∀ p ∈ P.interiorLatticePoints, p ≠ q →
        ¬ MemClosedTriangle (interiorFanTriangle P q i).a
          (interiorFanTriangle P q i).b (interiorFanTriangle P q i).c p := by
      intro p hp hpq hp_mem
      have hpset : p ∈ ({q, r, s} : Set (ℤ × ℤ)) := by
        rw [← h.2.2.2]; exact hp
      rcases (Set.mem_insert_iff.mp hpset) with hpq' | hp'
      · exact hpq hpq'
      · rcases (Set.mem_insert_iff.mp hp') with hpr | hps
        · -- p = r: only adjacent ears
          have hr_i : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r := by
            simpa [interiorFanTriangle, hpr] using hp_mem
          by_cases hi_adj : i = k ∨ i = P.prevIdx k
          · rcases hi_adj with h1 | h2
            · exact hik h1
            · exact hip h2
          · push Not at hi_adj
            have hoff_r :
                OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r := by
              classical
              set vj := P.vertex i
              set wj := P.vertex (P.nextIdx i)
              set vk := P.vertex k
              refine ⟨?_, ?_, ?_⟩
              · intro hspoke
                have hne_vj : r ≠ vj := by
                  intro heq
                  have hv_bd : vj ∈ P.boundaryLatticePoints := by
                    have : vj ∈ P.vertexFinset := by
                      rw [vertexFinset_eq_univ_image]
                      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
                    exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
                  exact (mem_interior_of_threeInterior_left P h).2 (heq ▸ hv_bd)
                have hdj : edgeGcd q vj = 2 :=
                  edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h i
                    hspoke hne_q hne_vj (by
                      intro hs_i
                      have : MemClosedTriangle q (P.vertex i)
                          (P.vertex (P.nextIdx i)) s :=
                        mem_interiorFan_of_onSpoke_left P i hs_i
                      have : i = k :=
                        eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq k i
                          hs_ear hoff_s this
                      exact hik this)
                have hdk : edgeGcd q vk = 2 :=
                  edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hr
                    hne_q hne_v hs_not_spoke
                have heq :=
                  eq_vertex_of_mem_edgeLatticePoints_of_edgeGcd_eq_two
                    q vj vk r hdj hdk hspoke hr hne_q hne_vj hne_v
                exact hi_adj.1 (hinj heq)
              · exact not_mem_polygon_edge_of_mem_interior P
                  (mem_interior_of_threeInterior_left P h) i
              · intro hspoke
                have hs' : r ∈ edgeLatticePoints q wj :=
                  mem_edgeLatticePoints_comm hspoke
                have hne_wj : r ≠ wj := by
                  intro heq
                  have hv_bd : wj ∈ P.boundaryLatticePoints := by
                    have : wj ∈ P.vertexFinset := by
                      rw [vertexFinset_eq_univ_image]
                      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
                    exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
                  exact (mem_interior_of_threeInterior_left P h).2 (heq ▸ hv_bd)
                have hdj : edgeGcd q wj = 2 :=
                  edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h
                    (P.nextIdx i) hs' hne_q hne_wj (by
                      intro hs_w
                      have hs_i :
                          MemClosedTriangle q (P.vertex i)
                            (P.vertex (P.nextIdx i)) s := by
                        simpa [P.prevIdx_nextIdx] using
                          mem_interiorFan_of_onSpoke_right P (P.nextIdx i) hs_w
                      have : i = k :=
                        eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq k i
                          hs_ear hoff_s hs_i
                      exact hik this)
                have hdk : edgeGcd q vk = 2 :=
                  edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hr
                    hne_q hne_v hs_not_spoke
                have heq :=
                  eq_vertex_of_mem_edgeLatticePoints_of_edgeGcd_eq_two
                    q wj vk r hdj hdk hs' hr hne_q hne_wj hne_v
                have : P.nextIdx i = k := hinj heq
                have : i = P.prevIdx k := by
                  rw [← this, prevIdx_nextIdx]
                exact hi_adj.2 this
            have hrk : MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) r :=
              mem_interiorFan_of_onSpoke_left P k hr
            have : k = i :=
              eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq i k hr_i
                hoff_r hrk
            exact hik this.symm
        · -- p = s: only ear k
          have hps' : p = s := Set.mem_singleton_iff.mp hps
          have hs_i : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) s := by
            simpa [interiorFanTriangle, hps'] using hp_mem
          have : i = k :=
            eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq k i hs_ear
              hoff_s hs_i
          exact hik this
    exact interiorFanDet_eq_one_of_no_other_interior
      P hsc hinj hedge hq i hempty
  have hsum :
      (∑ i : Fin P.nVertices, interiorFanDet P q i) = (P.nVertices : ℤ) + 4 := by
    set S1 := Finset.univ.erase k
    set S2 := S1.erase (P.prevIdx k)
    have hk_mem : k ∈ Finset.univ := Finset.mem_univ k
    have hp_mem : P.prevIdx k ∈ S1 :=
      Finset.mem_erase.mpr ⟨hne_adj.symm, Finset.mem_univ _⟩
    have hdecomp1 :
        (∑ i : Fin P.nVertices, interiorFanDet P q i) =
          interiorFanDet P q k + ∑ i ∈ S1, interiorFanDet P q i := by
      dsimp [S1]; rw [add_comm]
      exact (Finset.sum_erase_add (s := Finset.univ) (interiorFanDet P q)
        hk_mem).symm
    have hdecomp2 :
        ∑ i ∈ S1, interiorFanDet P q i =
          interiorFanDet P q (P.prevIdx k) + ∑ i ∈ S2, interiorFanDet P q i := by
      dsimp [S2]; rw [add_comm]
      exact (Finset.sum_erase_add (s := S1) (interiorFanDet P q) hp_mem).symm
    have hrest : ∑ i ∈ S2, interiorFanDet P q i = ∑ i ∈ S2, (1 : ℤ) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have ⟨hip', hi2⟩ := Finset.mem_erase.mp hi
      have ⟨hik', _⟩ := Finset.mem_erase.mp hi2
      exact hdet1 i hik' hip'
    have hcard : S2.card = P.nVertices - 2 := by
      dsimp [S2, S1]
      have h1 : (Finset.univ.erase k).card = P.nVertices - 1 := by
        rw [Finset.card_erase_of_mem hk_mem, Finset.card_univ, Fintype.card_fin]
      have h2 : ((Finset.univ.erase k).erase (P.prevIdx k)).card =
          (Finset.univ.erase k).card - 1 :=
        Finset.card_erase_of_mem hp_mem
      have : 2 ≤ P.nVertices := by have := P.length_ge; omega
      omega
    calc
      ∑ i : Fin P.nVertices, interiorFanDet P q i
          = interiorFanDet P q k + ∑ i ∈ S1, interiorFanDet P q i := hdecomp1
      _ = 4 + (interiorFanDet P q (P.prevIdx k) +
              ∑ i ∈ S2, interiorFanDet P q i) := by rw [hdet4, hdecomp2]
      _ = 4 + (2 + ∑ i ∈ S2, (1 : ℤ)) := by rw [hdetR, hrest]
      _ = 6 + (S2.card : ℤ) := by simp; ring
      _ = 6 + ((P.nVertices - 2 : ℕ) : ℤ) := by rw [hcard]
      _ = (P.nVertices : ℤ) + 4 := by
            have : 2 ≤ P.nVertices := by have := P.length_ge; omega
            have hcast : ((P.nVertices - 2 : ℕ) : ℤ) = (P.nVertices : ℤ) - 2 :=
              Nat.cast_sub this
            rw [hcast]; ring
  have hshoelaceSum : P.shoelaceSum = (P.nVertices : ℤ) + 4 := by
    rw [← sum_interiorFanDet_eq_shoelaceSum P q, hsum]
  have hB : P.B = P.nVertices := B_eq_nVertices_of_primitive_edges P hedge hinj
  have hnn : 0 ≤ P.shoelaceSum := by
    have : 0 ≤ (P.nVertices : ℤ) + 4 := by
      have : 3 ≤ P.nVertices := P.length_ge; omega
    simpa [hshoelaceSum] using this
  have hnat : Int.natAbs P.shoelaceSum = P.nVertices + 4 := by
    apply Int.natCast_inj.mp
    rw [Int.natAbs_of_nonneg hnn, hshoelaceSum]
    push_cast; ring
  calc
    P.shoelace = (Int.natAbs P.shoelaceSum : ℚ) / 2 := rfl
    _ = ((P.nVertices + 4 : ℕ) : ℚ) / 2 := by
          have : (Int.natAbs P.shoelaceSum : ℚ) = ((P.nVertices + 4 : ℕ) : ℚ) := by
            exact_mod_cast hnat
          rw [this]
    _ = (P.nVertices : ℚ) / 2 + 2 := by push_cast; ring
    _ = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := by rw [hB]; ring

/-! ### Off-adjacent-right I = 3 (not classical Pick)

Mirror of Off-adjacent-left: `r` on spoke `k`, `s` Off in ear `prevIdx k`
(△`(q,vₖ₋₁,vₖ)`). Then `s` lies on the diagonal `vₖ₋₁—r`, that diagonal has
`edgeGcd = 2`, and the right-adjacent ear has `interiorFanDet = 4`. Shoelace ≠ Haar.
Classical Pick FAIL.
-/

/-- Off point in the right-adjacent ear of an on-spoke `r` lies on the diagonal
`vₖ₋₁—r`. -/
theorem mem_diagonal_of_threeInterior_onSpoke_off_adjacent_right
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hr : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hs_ear : MemClosedTriangle q (P.vertex (P.prevIdx k)) (P.vertex k) s)
    (hoff_s : OffTriangleBoundary q (P.vertex (P.prevIdx k)) (P.vertex k) s) :
    s ∈ edgeLatticePoints (P.vertex (P.prevIdx k)) r := by
  classical
  set v := P.vertex k
  set u := P.vertex (P.prevIdx k)
  have hs_not_spoke : s ∉ edgeLatticePoints q v := fun hs_sp =>
    hoff_s.2.2 (mem_edgeLatticePoints_comm hs_sp)
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hr hne_q hne_v
      hs_not_spoke
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDbig : 0 < latticeDet q u v := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, u, v,
      P.nextIdx_prevIdx] using hpos (P.prevIdx k)
  have hdouble : latticeDet q u v = 2 * latticeDet q u r :=
    latticeDet_eq_two_mul_ac_of_edgeGcd_eq_two_mem q u v r hd hr hne_q hne_v
  have hadd : latticeDet q u v = latticeDet q u r + latticeDet r u v :=
    latticeDet_add_of_mem_edgeLatticePoints_ac q u v r hr
  have heq_halves : latticeDet q u r = latticeDet r u v := by linarith
  have hDsmall : 0 < latticeDet q u r := by
    have : 0 < 2 * latticeDet q u r := by rwa [← hdouble]
    omega
  have hDRpos : 0 < latticeDet r u v := by linarith [heq_halves]
  have hsplit :=
    memClosedTriangle_split_of_edgeGcd_eq_two_mem_ac q u v r s hd hr hne_q hne_v hs_ear
  have hsub_big : ∀ p, MemClosedTriangle q u v p →
      p = q ∨ p = u ∨ p = v ∨ p = r ∨ p = s := by
    intro p hp
    have hp' : MemClosedTriangle q (P.vertex (P.prevIdx k))
        (P.vertex (P.nextIdx (P.prevIdx k))) p := by
      simpa [u, v, P.nextIdx_prevIdx] using hp
    simpa [interiorFanTriangle, u, v, P.nextIdx_prevIdx] using
      eq_vertices_or_rs_of_mem_interiorFan_of_threeInterior P hsc hinj hedge h
        (P.prevIdx k) (by simpa [interiorFanTriangle] using hp')
  have v_not_left : ¬ MemClosedTriangle q u r v := by
    intro hp
    have hβ0 : latticeDet q v r = 0 :=
      latticeDet_eq_zero_of_mem_edge_ab q v r hr
    have hedge_qr : v ∈ edgeLatticePoints q r :=
      mem_edgeLatticePoints_comm
        (mem_edgeLatticePoints_of_weight_zero_ca q u r v hp hDsmall hβ0)
    have hprim : edgeGcd q r = 1 :=
      edgeGcd_eq_one_left_of_edgeGcd_eq_two_mem q v r hd hr hne_q hne_v
    have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one q r v hprim
      (mem_segment_of_mem_edgeLatticePoints q r v hedge_qr)
    exact hend.elim
      (fun hvq => by
        have hq_int := mem_interior_of_threeInterior_apex P h
        have hv_bd : v ∈ P.boundaryLatticePoints := by
          have : v ∈ P.vertexFinset := by
            rw [vertexFinset_eq_univ_image]
            exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
          exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
        exact hq_int.2 (hvq ▸ hv_bd))
      (fun hvr => hne_v hvr.symm)
  have q_not_right : ¬ MemClosedTriangle r u v q := by
    intro hp
    have hγ0 : latticeDet r q v = 0 := by
      have : latticeDet q v r = 0 := latticeDet_eq_zero_of_mem_edge_ab q v r hr
      have h1 : latticeDet q r v = -latticeDet q v r := by unfold latticeDet; ring
      have h2 : latticeDet r q v = -latticeDet q r v := by unfold latticeDet; ring
      linarith
    have hedge_rv : q ∈ edgeLatticePoints r v :=
      mem_edgeLatticePoints_comm
        (mem_edgeLatticePoints_of_weight_zero_ca r u v q hp hDRpos hγ0)
    have hprim : edgeGcd r v = 1 :=
      edgeGcd_eq_one_right_of_edgeGcd_eq_two_mem q v r hd hr hne_q hne_v
    have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one r v q hprim
      (mem_segment_of_mem_edgeLatticePoints r v q hedge_rv)
    exact hend.elim (fun hqr => hne_q hqr.symm) (fun hqv => by
      have hq_int := mem_interior_of_threeInterior_apex P h
      have hv_bd : v ∈ P.boundaryLatticePoints := by
        have : v ∈ P.vertexFinset := by
          rw [vertexFinset_eq_univ_image]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
      exact hq_int.2 (hqv ▸ hv_bd))
  rcases hsplit with hsL | hsR
  · by_cases hdiag : s ∈ edgeLatticePoints u r
    · exact hdiag
    · have hoffL : OffTriangleBoundary q u r s := by
        refine ⟨hoff_s.1, hdiag, ?_⟩
        · intro hrq
          have hprim : edgeGcd q r = 1 :=
            edgeGcd_eq_one_left_of_edgeGcd_eq_two_mem q v r hd hr hne_q hne_v
          have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one q r s hprim
            (mem_segment_of_mem_edgeLatticePoints q r s
              (mem_edgeLatticePoints_comm hrq))
          rcases hend with hsq | hsr
          · exact h.2.1 hsq.symm
          · exact h.2.2.1 hsr.symm
      have hsubL : ∀ p, MemClosedTriangle q u r p →
          p = q ∨ p = u ∨ p = r ∨ p = s := by
        intro p hp
        have hp_big : MemClosedTriangle q u v p :=
          memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem_ac q u v r p
            hd hr hne_q hne_v hp
        rcases hsub_big p hp_big with h1 | h2 | h3 | h4 | h5
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact absurd (h3 ▸ hp) v_not_left
        · exact Or.inr (Or.inr (Or.inl h4))
        · exact Or.inr (Or.inr (Or.inr h5))
      have hdetL3 : latticeDet q u r = 3 :=
        latticeDet_eq_three_of_subset_four_off q u r s hDsmall hsubL hoffL hsL
      have hsubR : ∀ p, MemClosedTriangle r u v p → p = r ∨ p = u ∨ p = v := by
        intro p hp
        have hp_big : MemClosedTriangle q u v p :=
          memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem_ac_right
            q u v r p hd hr hne_q hne_v hp
        rcases hsub_big p hp_big with h1 | h2 | h3 | h4 | h5
        · exact absurd (h1 ▸ hp) q_not_right
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr h3)
        · exact Or.inl h4
        · exact absurd
            (mem_edgeLatticePoints_of_memClosedTriangle_both_halves_ac
              q u v r s hd hr hne_q hne_v hDsmall hDRpos hsL (h5 ▸ hp))
            hdiag
      have hnat1 : Int.natAbs (latticeDet r u v) = 1 :=
        natAbs_det_eq_one_of_memClosedTriangle_eq_vertices r u v
          (ne_of_gt hDRpos) hsubR
      have hdetR1 : latticeDet r u v = 1 := by
        have hnn : 0 ≤ latticeDet r u v := le_of_lt hDRpos
        have : latticeDet r u v = (Int.natAbs (latticeDet r u v) : ℤ) :=
          (Int.natAbs_of_nonneg hnn).symm
        rw [this, hnat1]; norm_num
      linarith [hdetL3, heq_halves, hdetR1]
  · by_cases hdiag : s ∈ edgeLatticePoints u r
    · exact hdiag
    · have hoffR : OffTriangleBoundary r u v s := by
        refine ⟨fun hru => hdiag (mem_edgeLatticePoints_comm hru), hoff_s.2.1, ?_⟩
        · intro hvr
          have hprim : edgeGcd r v = 1 :=
            edgeGcd_eq_one_right_of_edgeGcd_eq_two_mem q v r hd hr hne_q hne_v
          have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one r v s hprim
            (mem_segment_of_mem_edgeLatticePoints r v s
              (mem_edgeLatticePoints_comm hvr))
          rcases hend with hsr | hsv
          · exact h.2.2.1 hsr.symm
          · have hv_bd : v ∈ P.boundaryLatticePoints := by
              have : v ∈ P.vertexFinset := by
                rw [vertexFinset_eq_univ_image]
                exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
              exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
            exact (mem_interior_of_threeInterior_right P h).2 (hsv ▸ hv_bd)
      have hsubR : ∀ p, MemClosedTriangle r u v p →
          p = r ∨ p = u ∨ p = v ∨ p = s := by
        intro p hp
        have hp_big : MemClosedTriangle q u v p :=
          memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem_ac_right
            q u v r p hd hr hne_q hne_v hp
        rcases hsub_big p hp_big with h1 | h2 | h3 | h4 | h5
        · exact absurd (h1 ▸ hp) q_not_right
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (Or.inl h3))
        · exact Or.inl h4
        · exact Or.inr (Or.inr (Or.inr h5))
      have hdetR3 : latticeDet r u v = 3 :=
        latticeDet_eq_three_of_subset_four_off r u v s hDRpos hsubR hoffR hsR
      have hsubL : ∀ p, MemClosedTriangle q u r p → p = q ∨ p = u ∨ p = r := by
        intro p hp
        have hp_big : MemClosedTriangle q u v p :=
          memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem_ac q u v r p
            hd hr hne_q hne_v hp
        rcases hsub_big p hp_big with h1 | h2 | h3 | h4 | h5
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact absurd (h3 ▸ hp) v_not_left
        · exact Or.inr (Or.inr h4)
        · exact absurd
            (mem_edgeLatticePoints_of_memClosedTriangle_both_halves_ac
              q u v r s hd hr hne_q hne_v hDsmall hDRpos (h5 ▸ hp) hsR)
            hdiag
      have hnat1 : Int.natAbs (latticeDet q u r) = 1 :=
        natAbs_det_eq_one_of_memClosedTriangle_eq_vertices q u r
          (ne_of_gt hDsmall) hsubL
      have hdetL1 : latticeDet q u r = 1 := by
        have hnn : 0 ≤ latticeDet q u r := le_of_lt hDsmall
        have : latticeDet q u r = (Int.natAbs (latticeDet q u r) : ℤ) :=
          (Int.natAbs_of_nonneg hnn).symm
        rw [this, hnat1]; norm_num
      linarith [hdetR3, heq_halves, hdetL1]


/-- Diagonal of Off-adjacent right ear has `edgeGcd = 2` (unique midpoint `s`). -/
theorem edgeGcd_eq_two_of_diagonal_threeInterior_onSpoke_off_adjacent_right
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hr : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hs_ear : MemClosedTriangle q (P.vertex (P.prevIdx k)) (P.vertex k) s)
    (hoff_s : OffTriangleBoundary q (P.vertex (P.prevIdx k)) (P.vertex k) s) :
    edgeGcd (P.vertex (P.prevIdx k)) r = 2 := by
  classical
  set v := P.vertex k
  set u := P.vertex (P.prevIdx k)
  have hs_diag : s ∈ edgeLatticePoints u r :=
    mem_diagonal_of_threeInterior_onSpoke_off_adjacent_right
      P hsc hinj hedge h k hr hne_q hne_v hs_ear hoff_s
  have hne_su : s ≠ u := by
    intro heq
    have hv_bd : u ∈ P.boundaryLatticePoints := by
      have : u ∈ P.vertexFinset := by
        rw [vertexFinset_eq_univ_image]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
    exact (mem_interior_of_threeInterior_right P h).2 (heq ▸ hv_bd)
  have hne_sr : s ≠ r := h.2.2.1.symm
  have hne_ur : u ≠ r := by
    intro heq
    have hz : edgeGcd u r = 0 := (edgeGcd_eq_zero_iff u r).mpr heq
    have hE : edgeLatticePoints u r = {u} := by
      unfold edgeLatticePoints; simp [hz]
    have hs' : s ∈ ({u} : Finset (ℤ × ℤ)) := by rwa [hE] at hs_diag
    exact hne_su (Finset.mem_singleton.mp hs')
  have hge2 : 2 ≤ edgeGcd u r := by
    have hsub : ({u, r, s} : Finset (ℤ × ℤ)) ⊆ edgeLatticePoints u r := by
      intro x hx
      have hx' : x = u ∨ x = r ∨ x = s := by simpa using hx
      rcases hx' with hxu | hxr | hxs
      · rw [hxu]; exact self_mem_edgeLatticePoints u r
      · rw [hxr]; exact other_mem_edgeLatticePoints u r
      · rw [hxs]; exact hs_diag
    have hcard3 : ({u, r, s} : Finset (ℤ × ℤ)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hne_ur, hne_su.symm]),
          Finset.card_insert_of_notMem (by simp [hne_sr.symm]),
          Finset.card_singleton]
    have : 3 ≤ (edgeLatticePoints u r).card :=
      hcard3 ▸ Finset.card_le_card hsub
    have := card_edgeLatticePoints u r
    omega
  by_contra hne2
  have hge3 : 3 ≤ edgeGcd u r := by omega
  have hcard4 : 4 ≤ (edgeLatticePoints u r).card := by
    have := card_edgeLatticePoints u r; omega
  have hsub3 : ({u, r, s} : Finset (ℤ × ℤ)) ⊆ edgeLatticePoints u r := by
    intro x hx
    have hx' : x = u ∨ x = r ∨ x = s := by simpa using hx
    rcases hx' with hxu | hxr | hxs
    · rw [hxu]; exact self_mem_edgeLatticePoints u r
    · rw [hxr]; exact other_mem_edgeLatticePoints u r
    · rw [hxs]; exact hs_diag
  have hcard3 : ({u, r, s} : Finset (ℤ × ℤ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hne_ur, hne_su.symm]),
        Finset.card_insert_of_notMem (by simp [hne_sr.symm]),
        Finset.card_singleton]
  have hltc : ({u, r, s} : Finset (ℤ × ℤ)).card <
      (edgeLatticePoints u r).card := by omega
  obtain ⟨t, htE, htnotin⟩ := Finset.exists_mem_notMem_of_card_lt_card hltc
  have htne : t ≠ u ∧ t ≠ r ∧ t ≠ s :=
    ⟨fun htu => htnotin (by simp [htu]),
     fun htr => htnotin (by simp [htr]),
     fun hts => htnotin (by simp [hts])⟩
  have hs_not_spoke : s ∉ edgeLatticePoints q v := fun hs_sp =>
    hoff_s.2.2 (mem_edgeLatticePoints_comm hs_sp)
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hr hne_q hne_v
      hs_not_spoke
  have ht_small : MemClosedTriangle q u r t :=
    memClosedTriangle_of_mem_edgeLatticePoints_bc q u r t htE
  have ht_ear : MemClosedTriangle q u v t :=
    memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem_ac
      q u v r t hd hr hne_q hne_v ht_small
  have hdouble : latticeDet q u v = 2 * latticeDet q u r :=
    latticeDet_eq_two_mul_ac_of_edgeGcd_eq_two_mem q u v r hd hr hne_q hne_v
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDbig : 0 < latticeDet q u v := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, u, v,
      P.nextIdx_prevIdx] using hpos (P.prevIdx k)
  have hDsmall : 0 < latticeDet q u r := by
    have : 0 < 2 * latticeDet q u r := by rwa [← hdouble]
    omega
  have hadd : latticeDet q u v = latticeDet q u r + latticeDet r u v :=
    latticeDet_add_of_mem_edgeLatticePoints_ac q u v r hr
  have heq_halves : latticeDet q u r = latticeDet r u v := by linarith
  have hDRpos : 0 < latticeDet r u v := by linarith
  have ht_ear' : MemClosedTriangle q (P.vertex (P.prevIdx k))
      (P.vertex (P.nextIdx (P.prevIdx k))) t := by
    simpa [u, v, P.nextIdx_prevIdx] using ht_ear
  rcases eq_vertices_or_rs_of_mem_interiorFan_of_threeInterior
      P hsc hinj hedge h (P.prevIdx k)
      (by simpa [interiorFanTriangle] using ht_ear') with
    h1 | h2 | h3 | h4 | h5
  · -- t = q
    have htq : t = q := h1
    have hγ0 : latticeDet u r q = 0 := by
      simpa [htq] using latticeDet_eq_zero_of_mem_edge_ab u r t htE
    have : latticeDet q u r = 0 := by
      have hc : latticeDet u r q = latticeDet q u r :=
        (latticeDet_cyclic q u r).symm
      linarith
    exact (ne_of_gt hDsmall) this
  · -- t = u
    exact htne.1 h2
  · -- t = v (= nextIdx prevIdx)
    have htv : t = v := by simpa [v, P.nextIdx_prevIdx] using h3
    have hz : latticeDet u r v = 0 := by
      simpa [htv] using latticeDet_eq_zero_of_mem_edge_ab u r t htE
    have : latticeDet r u v = 0 := by
      have hsw : latticeDet u r v = -latticeDet r u v := by unfold latticeDet; ring
      linarith
    exact (ne_of_gt hDRpos) this
  · exact htne.2.1 h4
  · exact htne.2.2 h5


/-- Right Off-adjacent ear has `interiorFanDet = 4` via diagonal midpoint double-doubling. -/
theorem interiorFanDet_eq_four_of_threeInterior_onSpoke_off_adjacent_right
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hr : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hs_ear : MemClosedTriangle q (P.vertex (P.prevIdx k)) (P.vertex k) s)
    (hoff_s : OffTriangleBoundary q (P.vertex (P.prevIdx k)) (P.vertex k) s) :
    interiorFanDet P q (P.prevIdx k) = 4 := by
  classical
  set v := P.vertex k
  set u := P.vertex (P.prevIdx k)
  have hs_not_spoke : s ∉ edgeLatticePoints q v := fun hs_sp =>
    hoff_s.2.2 (mem_edgeLatticePoints_comm hs_sp)
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hr hne_q hne_v
      hs_not_spoke
  have hs_diag : s ∈ edgeLatticePoints u r :=
    mem_diagonal_of_threeInterior_onSpoke_off_adjacent_right
      P hsc hinj hedge h k hr hne_q hne_v hs_ear hoff_s
  have hd_diag : edgeGcd u r = 2 :=
    edgeGcd_eq_two_of_diagonal_threeInterior_onSpoke_off_adjacent_right
      P hsc hinj hedge h k hr hne_q hne_v hs_ear hoff_s
  have hne_su : s ≠ u := by
    intro heq
    have hv_bd : u ∈ P.boundaryLatticePoints := by
      have : u ∈ P.vertexFinset := by
        rw [vertexFinset_eq_univ_image]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
    exact (mem_interior_of_threeInterior_right P h).2 (heq ▸ hv_bd)
  have hne_sr : s ≠ r := h.2.2.1.symm
  have hdouble1 : latticeDet q u v = 2 * latticeDet q u r :=
    latticeDet_eq_two_mul_ac_of_edgeGcd_eq_two_mem q u v r hd hr hne_q hne_v
  have hdouble2 : latticeDet q u r = 2 * latticeDet q u s :=
    latticeDet_eq_two_mul_of_edgeGcd_eq_two_mem_bc q u r s hd_diag hs_diag hne_su
      hne_sr
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDbig : 0 < latticeDet q u v := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, u, v,
      P.nextIdx_prevIdx] using hpos (P.prevIdx k)
  have hDmid : 0 < latticeDet q u r := by
    have : 0 < 2 * latticeDet q u r := by rwa [← hdouble1]
    omega
  have hDtiny : 0 < latticeDet q u s := by
    have : 0 < 2 * latticeDet q u s := by rwa [← hdouble2]
    omega
  have hsub : ∀ p, MemClosedTriangle q u s p → p = q ∨ p = u ∨ p = s := by
    intro p hp
    have hp_mid : MemClosedTriangle q u r p :=
      memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem_bc
        q u r s p hd_diag hs_diag hne_su hne_sr hp
    have hp_big : MemClosedTriangle q u v p :=
      memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem_ac
        q u v r p hd hr hne_q hne_v hp_mid
    have hp_ear : MemClosedTriangle q (P.vertex (P.prevIdx k))
        (P.vertex (P.nextIdx (P.prevIdx k))) p := by
      simpa [u, v, P.nextIdx_prevIdx] using hp_big
    rcases eq_vertices_or_rs_of_mem_interiorFan_of_threeInterior
        P hsc hinj hedge h (P.prevIdx k)
        (by simpa [interiorFanTriangle] using hp_ear) with
      h1 | h2 | h3 | h4 | h5
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · -- p = v: then v ∈ △(q,u,r) via mid inclusion, contradict spoke primitivity
      have hpv : p = v := by simpa [v, P.nextIdx_prevIdx] using h3
      have hv_mid : MemClosedTriangle q u r v := by simpa [hpv] using hp_mid
      have hβ0 : latticeDet q v r = 0 :=
        latticeDet_eq_zero_of_mem_edge_ab q v r hr
      have hedge_qr : v ∈ edgeLatticePoints q r :=
        mem_edgeLatticePoints_comm
          (mem_edgeLatticePoints_of_weight_zero_ca q u r v hv_mid hDmid hβ0)
      have hprim : edgeGcd q r = 1 :=
        edgeGcd_eq_one_left_of_edgeGcd_eq_two_mem q v r hd hr hne_q hne_v
      have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one q r v hprim
        (mem_segment_of_mem_edgeLatticePoints q r v hedge_qr)
      exact False.elim (hend.elim
        (fun hvq => by
          have hq_int := mem_interior_of_threeInterior_apex P h
          have hv_bd : v ∈ P.boundaryLatticePoints := by
            have : v ∈ P.vertexFinset := by
              rw [vertexFinset_eq_univ_image]
              exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
            exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
          exact hq_int.2 (hvq ▸ hv_bd))
        (fun hvr => hne_v hvr.symm))
    · -- p = r: on edge u—s (s mid of u—r)
      have hpr : p = r := h4
      have hprim : edgeGcd u s = 1 :=
        edgeGcd_eq_one_left_of_edgeGcd_eq_two_mem u r s hd_diag hs_diag hne_su
          hne_sr
      have hz : latticeDet u s r = 0 := by
        obtain ⟨hx, hy⟩ :=
          two_mul_sub_of_mem_edgeLatticePoints_of_edgeGcd_eq_two u r s hd_diag
            hs_diag hne_su hne_sr
        simp only [latticeDet]
        have hx' : r.1 - u.1 = 2 * (s.1 - u.1) := by linarith
        have hy' : r.2 - u.2 = 2 * (s.2 - u.2) := by linarith
        have : (s.1 - u.1) * (r.2 - u.2) - (s.2 - u.2) * (r.1 - u.1) = 0 := by
          rw [hx', hy']; ring
        exact this
      have hp' : MemClosedTriangle q u s r := by simpa [hpr] using hp
      have hedge_us : r ∈ edgeLatticePoints u s :=
        mem_edgeLatticePoints_of_weight_zero_bc q u s r hp' hDtiny hz
      have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one u s r hprim
        (mem_segment_of_mem_edgeLatticePoints u s r hedge_us)
      exact False.elim (hend.elim
        (fun hru => by
          have : edgeGcd u r = 0 := (edgeGcd_eq_zero_iff u r).mpr hru.symm
          omega)
        (fun hrs => hne_sr hrs.symm))
    · exact Or.inr (Or.inr h5)
  have hnat1 : Int.natAbs (latticeDet q u s) = 1 :=
    natAbs_det_eq_one_of_memClosedTriangle_eq_vertices q u s (ne_of_gt hDtiny) hsub
  have hdet1 : latticeDet q u s = 1 := by
    have hnn : 0 ≤ latticeDet q u s := le_of_lt hDtiny
    have : latticeDet q u s = (Int.natAbs (latticeDet q u s) : ℤ) :=
      (Int.natAbs_of_nonneg hnn).symm
    rw [this, hnat1]; norm_num
  have : latticeDet q u v = 4 := by
    rw [hdouble1, hdouble2, hdet1]; norm_num
  simpa [interiorFanDet, interiorFanTriangle, Triangle.det, u, v,
    P.nextIdx_prevIdx] using this




/-- **I = 3 shoelace Pick-form** under on-spoke + Off-adjacent-right (not classical Pick).

`r` on spoke `k`, `s` Off in ear `prevIdx k`: that ear has `det = 4`, left-adjacent
`det = 2`, foreign `det = 1`; fan sum `n+4`; `B = n` ⇒ `shoelace = 3 + B/2 − 1`.
Shoelace ≠ Haar. Classical Pick FAIL. -/
theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_onSpoke_off_adjacent_right
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hr : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hs_ear : MemClosedTriangle q (P.vertex (P.prevIdx k)) (P.vertex k) s)
    (hoff_s : OffTriangleBoundary q (P.vertex (P.prevIdx k)) (P.vertex k) s) :
    P.shoelace = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  have hq := mem_interior_of_threeInterior_apex P h
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hs_not_spoke : s ∉ edgeLatticePoints q (P.vertex k) := fun hs_sp =>
    hoff_s.2.2 (mem_edgeLatticePoints_comm hs_sp)
  have hs_ear' : MemClosedTriangle q (P.vertex (P.prevIdx k))
      (P.vertex (P.nextIdx (P.prevIdx k))) s := by
    simpa [P.nextIdx_prevIdx] using hs_ear
  have hoff_s' : OffTriangleBoundary q (P.vertex (P.prevIdx k))
      (P.vertex (P.nextIdx (P.prevIdx k))) s := by
    simpa [P.nextIdx_prevIdx] using hoff_s
  have hs_not_left :
      ¬ MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) s := by
    intro hs_l
    have : k = P.prevIdx k :=
      eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq (P.prevIdx k) k
        hs_ear' hoff_s' hs_l
    have hne_adj : k ≠ P.prevIdx k := by
      intro heq
      have hnext : P.nextIdx k = k := by
        have h1 : P.nextIdx k = P.nextIdx (P.prevIdx k) := congrArg P.nextIdx heq
        rw [h1, P.nextIdx_prevIdx]
      have hD : 0 < latticeDet q (P.vertex k) (P.vertex (P.nextIdx k)) := by
        simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hpos k
      rw [hnext] at hD
      have hz : latticeDet q (P.vertex k) (P.vertex k) = 0 := by
        simp only [latticeDet]; ring
      exact (ne_of_gt hD) hz
    exact hne_adj this
  have hdet4 : interiorFanDet P q (P.prevIdx k) = 4 :=
    interiorFanDet_eq_four_of_threeInterior_onSpoke_off_adjacent_right
      P hsc hinj hedge h k hr hne_q hne_v hs_ear hoff_s
  have hdetL : interiorFanDet P q k = 2 :=
    interiorFanDet_eq_two_of_threeInterior_onSpoke_left
      P hsc hinj hedge h k hr hne_q hne_v hs_not_spoke hs_not_left
  have hne_adj : k ≠ P.prevIdx k := by
    intro heq
    have hnext : P.nextIdx k = k := by
      have h1 : P.nextIdx k = P.nextIdx (P.prevIdx k) := congrArg P.nextIdx heq
      rw [h1, P.nextIdx_prevIdx]
    have hD : 0 < latticeDet q (P.vertex k) (P.vertex (P.nextIdx k)) := by
      simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hpos k
    rw [hnext] at hD
    have hz : latticeDet q (P.vertex k) (P.vertex k) = 0 := by
      simp only [latticeDet]; ring
    exact (ne_of_gt hD) hz
  have hdet1 : ∀ i : Fin P.nVertices,
      i ≠ k → i ≠ P.prevIdx k → interiorFanDet P q i = 1 := by
    intro i hik hip
    have hempty : ∀ p ∈ P.interiorLatticePoints, p ≠ q →
        ¬ MemClosedTriangle (interiorFanTriangle P q i).a
          (interiorFanTriangle P q i).b (interiorFanTriangle P q i).c p := by
      intro p hp hpq hp_mem
      have hpset : p ∈ ({q, r, s} : Set (ℤ × ℤ)) := by
        rw [← h.2.2.2]; exact hp
      rcases (Set.mem_insert_iff.mp hpset) with hpq' | hp'
      · exact hpq hpq'
      · rcases (Set.mem_insert_iff.mp hp') with hpr | hps
        · -- p = r: only adjacent ears
          have hr_i : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r := by
            simpa [interiorFanTriangle, hpr] using hp_mem
          by_cases hi_adj : i = k ∨ i = P.prevIdx k
          · rcases hi_adj with h1 | h2
            · exact hik h1
            · exact hip h2
          · push Not at hi_adj
            have hoff_r :
                OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r := by
              classical
              set vj := P.vertex i
              set wj := P.vertex (P.nextIdx i)
              set vk := P.vertex k
              refine ⟨?_, ?_, ?_⟩
              · intro hspoke
                have hne_vj : r ≠ vj := by
                  intro heq
                  have hv_bd : vj ∈ P.boundaryLatticePoints := by
                    have : vj ∈ P.vertexFinset := by
                      rw [vertexFinset_eq_univ_image]
                      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
                    exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
                  exact (mem_interior_of_threeInterior_left P h).2 (heq ▸ hv_bd)
                have hdj : edgeGcd q vj = 2 :=
                  edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h i
                    hspoke hne_q hne_vj (by
                      intro hs_i
                      have : MemClosedTriangle q (P.vertex i)
                          (P.vertex (P.nextIdx i)) s :=
                        mem_interiorFan_of_onSpoke_left P i hs_i
                      have : i = P.prevIdx k :=
                        eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq
                          (P.prevIdx k) i hs_ear' hoff_s' this
                      exact hip this)
                have hdk : edgeGcd q vk = 2 :=
                  edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hr
                    hne_q hne_v hs_not_spoke
                have heq :=
                  eq_vertex_of_mem_edgeLatticePoints_of_edgeGcd_eq_two
                    q vj vk r hdj hdk hspoke hr hne_q hne_vj hne_v
                exact hi_adj.1 (hinj heq)
              · exact not_mem_polygon_edge_of_mem_interior P
                  (mem_interior_of_threeInterior_left P h) i
              · intro hspoke
                have hs' : r ∈ edgeLatticePoints q wj :=
                  mem_edgeLatticePoints_comm hspoke
                have hne_wj : r ≠ wj := by
                  intro heq
                  have hv_bd : wj ∈ P.boundaryLatticePoints := by
                    have : wj ∈ P.vertexFinset := by
                      rw [vertexFinset_eq_univ_image]
                      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
                    exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
                  exact (mem_interior_of_threeInterior_left P h).2 (heq ▸ hv_bd)
                have hdj : edgeGcd q wj = 2 :=
                  edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h
                    (P.nextIdx i) hs' hne_q hne_wj (by
                      intro hs_w
                      have hs_i :
                          MemClosedTriangle q (P.vertex i)
                            (P.vertex (P.nextIdx i)) s := by
                        simpa [P.prevIdx_nextIdx] using
                          mem_interiorFan_of_onSpoke_right P (P.nextIdx i) hs_w
                      have : i = P.prevIdx k :=
                        eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq
                          (P.prevIdx k) i hs_ear' hoff_s' hs_i
                      exact hip this)
                have hdk : edgeGcd q vk = 2 :=
                  edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h k hr
                    hne_q hne_v hs_not_spoke
                have heq :=
                  eq_vertex_of_mem_edgeLatticePoints_of_edgeGcd_eq_two
                    q wj vk r hdj hdk hs' hr hne_q hne_wj hne_v
                have : P.nextIdx i = k := hinj heq
                have : i = P.prevIdx k := by
                  rw [← this, prevIdx_nextIdx]
                exact hi_adj.2 this
            have hrk : MemClosedTriangle q (P.vertex (P.prevIdx k))
                (P.vertex (P.nextIdx (P.prevIdx k))) r := by
              simpa [P.nextIdx_prevIdx] using
                mem_interiorFan_of_onSpoke_right P k hr
            have : P.prevIdx k = i :=
              eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq i (P.prevIdx k)
                hr_i hoff_r hrk
            exact hip this.symm
        · -- p = s: only ear prevIdx k
          have hps' : p = s := Set.mem_singleton_iff.mp hps
          have hs_i : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) s := by
            simpa [interiorFanTriangle, hps'] using hp_mem
          have : i = P.prevIdx k :=
            eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq (P.prevIdx k) i
              hs_ear' hoff_s' hs_i
          exact hip this
    exact interiorFanDet_eq_one_of_no_other_interior
      P hsc hinj hedge hq i hempty
  have hsum :
      (∑ i : Fin P.nVertices, interiorFanDet P q i) = (P.nVertices : ℤ) + 4 := by
    set S1 := Finset.univ.erase (P.prevIdx k)
    set S2 := S1.erase k
    have hp_mem : P.prevIdx k ∈ Finset.univ := Finset.mem_univ _
    have hk_mem : k ∈ S1 :=
      Finset.mem_erase.mpr ⟨hne_adj, Finset.mem_univ _⟩
    have hdecomp1 :
        (∑ i : Fin P.nVertices, interiorFanDet P q i) =
          interiorFanDet P q (P.prevIdx k) + ∑ i ∈ S1, interiorFanDet P q i := by
      dsimp [S1]; rw [add_comm]
      exact (Finset.sum_erase_add (s := Finset.univ) (interiorFanDet P q)
        hp_mem).symm
    have hdecomp2 :
        ∑ i ∈ S1, interiorFanDet P q i =
          interiorFanDet P q k + ∑ i ∈ S2, interiorFanDet P q i := by
      dsimp [S2]; rw [add_comm]
      exact (Finset.sum_erase_add (s := S1) (interiorFanDet P q) hk_mem).symm
    have hrest : ∑ i ∈ S2, interiorFanDet P q i = ∑ i ∈ S2, (1 : ℤ) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have ⟨hik', hi2⟩ := Finset.mem_erase.mp hi
      have ⟨hip', _⟩ := Finset.mem_erase.mp hi2
      exact hdet1 i hik' hip'
    have hcard : S2.card = P.nVertices - 2 := by
      dsimp [S2, S1]
      have h1 : (Finset.univ.erase (P.prevIdx k)).card = P.nVertices - 1 := by
        rw [Finset.card_erase_of_mem hp_mem, Finset.card_univ, Fintype.card_fin]
      have h2 : ((Finset.univ.erase (P.prevIdx k)).erase k).card =
          (Finset.univ.erase (P.prevIdx k)).card - 1 :=
        Finset.card_erase_of_mem hk_mem
      have : 2 ≤ P.nVertices := by have := P.length_ge; omega
      omega
    calc
      ∑ i : Fin P.nVertices, interiorFanDet P q i
          = interiorFanDet P q (P.prevIdx k) + ∑ i ∈ S1, interiorFanDet P q i :=
            hdecomp1
      _ = 4 + (interiorFanDet P q k + ∑ i ∈ S2, interiorFanDet P q i) := by
            rw [hdet4, hdecomp2]
      _ = 4 + (2 + ∑ i ∈ S2, (1 : ℤ)) := by rw [hdetL, hrest]
      _ = 6 + (S2.card : ℤ) := by simp; ring
      _ = 6 + ((P.nVertices - 2 : ℕ) : ℤ) := by rw [hcard]
      _ = (P.nVertices : ℤ) + 4 := by
            have : 2 ≤ P.nVertices := by have := P.length_ge; omega
            have hcast : ((P.nVertices - 2 : ℕ) : ℤ) = (P.nVertices : ℤ) - 2 :=
              Nat.cast_sub this
            rw [hcast]; ring
  have hshoelaceSum : P.shoelaceSum = (P.nVertices : ℤ) + 4 := by
    rw [← sum_interiorFanDet_eq_shoelaceSum P q, hsum]
  have hB : P.B = P.nVertices := B_eq_nVertices_of_primitive_edges P hedge hinj
  have hnn : 0 ≤ P.shoelaceSum := by
    have : 0 ≤ (P.nVertices : ℤ) + 4 := by
      have : 3 ≤ P.nVertices := P.length_ge; omega
    simpa [hshoelaceSum] using this
  have hnat : Int.natAbs P.shoelaceSum = P.nVertices + 4 := by
    apply Int.natCast_inj.mp
    rw [Int.natAbs_of_nonneg hnn, hshoelaceSum]
    push_cast; ring
  calc
    P.shoelace = (Int.natAbs P.shoelaceSum : ℚ) / 2 := rfl
    _ = ((P.nVertices + 4 : ℕ) : ℚ) / 2 := by
          have : (Int.natAbs P.shoelaceSum : ℚ) = ((P.nVertices + 4 : ℕ) : ℚ) := by
            exact_mod_cast hnat
          rw [this]
    _ = (P.nVertices : ℚ) / 2 + 2 := by push_cast; ring
    _ = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := by rw [hB]; ring

/-! ### Same-spoke I = 3 substrate (not classical Pick)

When both `r` and `s` lie strictly on the same spoke `q -- vₖ`, that spoke has
`edgeGcd = 3`. Adjacent ears have `interiorFanDet = 3` (trisect + empty
third-ear). Full same-spoke Pick-form (fan sum `n+4`) remains: need foreign-ear
exclusion for `{r,s}` on the occupied spoke. Shoelace ≠ Haar. Classical Pick FAIL.
-/

/-- Under `ThreeInterior`, if both `r` and `s` lie strictly on spoke `q -- vertex k`,
then `edgeGcd = 3`. -/
theorem edgeGcd_eq_three_of_threeInterior_sameSpoke
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hr : r ∈ edgeLatticePoints q (P.vertex k))
    (hs : s ∈ edgeLatticePoints q (P.vertex k))
    (hne_rq : r ≠ q) (hne_rv : r ≠ P.vertex k)
    (hne_sq : s ≠ q) (hne_sv : s ≠ P.vertex k)
    (hne_rs : r ≠ s) :
    edgeGcd q (P.vertex k) = 3 := by
  classical
  have hne_qv : q ≠ P.vertex k := by
    intro heq
    have hq := mem_interior_of_threeInterior_apex P h
    have hv_bd : P.vertex k ∈ P.boundaryLatticePoints := by
      have : P.vertex k ∈ P.vertexFinset := by
        rw [vertexFinset_eq_univ_image]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
    exact hq.2 (by simpa [heq] using hv_bd)
  have hge3 : 3 ≤ edgeGcd q (P.vertex k) := by
    have hcard := card_edgeLatticePoints q (P.vertex k)
    have hsub : ({q, P.vertex k, r, s} : Finset (ℤ × ℤ)) ⊆
        edgeLatticePoints q (P.vertex k) := by
      intro x hx
      have hx' : x = q ∨ x = P.vertex k ∨ x = r ∨ x = s := by simpa using hx
      rcases hx' with hxq | hxv | hxr | hxs
      · rw [hxq]; exact self_mem_edgeLatticePoints q (P.vertex k)
      · rw [hxv]; exact other_mem_edgeLatticePoints q (P.vertex k)
      · rw [hxr]; exact hr
      · rw [hxs]; exact hs
    have hcard4 : ({q, P.vertex k, r, s} : Finset (ℤ × ℤ)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hne_qv, hne_rq.symm, hne_sq.symm]),
          Finset.card_insert_of_notMem (by simp [hne_rv.symm, hne_sv.symm]),
          Finset.card_insert_of_notMem (by simp [hne_rs]),
          Finset.card_singleton]
    have : 4 ≤ (edgeLatticePoints q (P.vertex k)).card :=
      hcard4 ▸ Finset.card_le_card hsub
    omega
  by_contra hne3
  have hcard5 : 5 ≤ (edgeLatticePoints q (P.vertex k)).card := by
    have := card_edgeLatticePoints q (P.vertex k); omega
  have hsub4 : ({q, P.vertex k, r, s} : Finset (ℤ × ℤ)) ⊆
      edgeLatticePoints q (P.vertex k) := by
    intro x hx
    have hx' : x = q ∨ x = P.vertex k ∨ x = r ∨ x = s := by simpa using hx
    rcases hx' with hxq | hxv | hxr | hxs
    · rw [hxq]; exact self_mem_edgeLatticePoints q (P.vertex k)
    · rw [hxv]; exact other_mem_edgeLatticePoints q (P.vertex k)
    · rw [hxr]; exact hr
    · rw [hxs]; exact hs
  have hcard4 : ({q, P.vertex k, r, s} : Finset (ℤ × ℤ)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hne_qv, hne_rq.symm, hne_sq.symm]),
        Finset.card_insert_of_notMem (by simp [hne_rv.symm, hne_sv.symm]),
        Finset.card_insert_of_notMem (by simp [hne_rs]),
        Finset.card_singleton]
  have hlt : ({q, P.vertex k, r, s} : Finset (ℤ × ℤ)).card <
      (edgeLatticePoints q (P.vertex k)).card := by omega
  obtain ⟨t, htE, htnotin⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have htne : t ≠ q ∧ t ≠ P.vertex k ∧ t ≠ r ∧ t ≠ s := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro htq; exact htnotin (by simp [htq])
    · intro htv; exact htnotin (by simp [htv])
    · intro htr; exact htnotin (by simp [htr])
    · intro hts; exact htnotin (by simp [hts])
  have hmem :=
    memClosedTriangle_of_mem_edgeLatticePoints_ab q (P.vertex k)
      (P.vertex (P.nextIdx k)) t htE
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDpos : 0 < latticeDet q (P.vertex k) (P.vertex (P.nextIdx k)) := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hpos k
  rcases eq_vertices_or_rs_of_mem_interiorFan_of_threeInterior P hsc hinj hedge h k
      (by simpa [interiorFanTriangle] using hmem) with h1 | h2 | h3 | h4 | h5
  · exact htne.1 h1
  · exact htne.2.1 h2
  · have : latticeDet q (P.vertex k) (P.vertex (P.nextIdx k)) = 0 :=
      latticeDet_eq_zero_of_mem_edge_ab q (P.vertex k) (P.vertex (P.nextIdx k))
        (by simpa [h3] using htE)
    exact (ne_of_gt hDpos this).elim
  · exact htne.2.2.1 h4
  · exact htne.2.2.2 h5


/-- Left third-ear △`(q,p1,w)` under same-spoke is empty of extra lattice points. -/
theorem eq_vertices_of_memClosedTriangle_threeInterior_sameSpoke_left
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hr : r ∈ edgeLatticePoints q (P.vertex k))
    (hs : s ∈ edgeLatticePoints q (P.vertex k))
    (hne_rq : r ≠ q) (hne_rv : r ≠ P.vertex k)
    (hne_sq : s ≠ q) (hne_sv : s ≠ P.vertex k)
    (hne_rs : r ≠ s)
    {p : ℤ × ℤ}
    (hp : MemClosedTriangle q
      (q.1 + ((P.vertex k).1 - q.1) / 3, q.2 + ((P.vertex k).2 - q.2) / 3)
      (P.vertex (P.nextIdx k)) p) :
    p = q ∨
      p = (q.1 + ((P.vertex k).1 - q.1) / 3, q.2 + ((P.vertex k).2 - q.2) / 3) ∨
        p = P.vertex (P.nextIdx k) := by
  classical
  set v := P.vertex k
  set w := P.vertex (P.nextIdx k)
  set p1 : ℤ × ℤ := (q.1 + (v.1 - q.1) / 3, q.2 + (v.2 - q.2) / 3)
  set p2 : ℤ × ℤ := (q.1 + 2 * ((v.1 - q.1) / 3), q.2 + 2 * ((v.2 - q.2) / 3))
  change MemClosedTriangle q p1 w p at hp
  have hd : edgeGcd q v = 3 :=
    edgeGcd_eq_three_of_threeInterior_sameSpoke P hsc hinj hedge h k hr hs
      hne_rq hne_rv hne_sq hne_sv hne_rs
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDbig : 0 < latticeDet q v w := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, v, w] using hpos k
  have htriple : latticeDet q v w = 3 * latticeDet q p1 w := by
    simpa [p1, v] using latticeDet_eq_three_mul_of_edgeGcd_eq_three_step_one q v w hd
  have hDsmall : 0 < latticeDet q p1 w := by
    have : 0 < 3 * latticeDet q p1 w := by rwa [← htriple]
    omega
  have hp_big : MemClosedTriangle q v w p :=
    memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_three_step_one q v w p hd
      (by simpa [p1, v] using hp)
  have hprim : edgeGcd q p1 = 1 := by
    simpa [p1, v] using edgeGcd_eq_one_of_edgeGcd_eq_three_step_one q v hd
  have hsteps :=
    eq_steps_of_mem_edgeLatticePoints_of_edgeGcd_eq_three q v r s hd hr hs
      hne_rq hne_rv hne_sq hne_sv hne_rs
  have hnot_p2 : ¬ MemClosedTriangle q p1 w p2 := by
    intro hp2
    have hdet0 : latticeDet q p1 p2 = 0 := by
      simpa [p1, p2, v] using
        latticeDet_eq_zero_step_one_step_two_of_edgeGcd_eq_three q v hd
    have hedge' : p2 ∈ edgeLatticePoints q p1 :=
      mem_edgeLatticePoints_of_weight_zero_ab q p1 w p2 hp2 hDsmall hdet0
    have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one q p1 p2 hprim
      (mem_segment_of_mem_edgeLatticePoints q p1 p2 hedge')
    have hab : q ≠ v := fun hh => by
      have : edgeGcd q v = 0 := (edgeGcd_eq_zero_iff q v).mpr hh; omega
    have hdvd1 : (edgeGcd q v : ℤ) ∣ (v.1 - q.1) := by
      simpa [edgeGcd] using Int.gcd_dvd_left (v.1 - q.1) (v.2 - q.2)
    have hdvd2 : (edgeGcd q v : ℤ) ∣ (v.2 - q.2) := by
      simpa [edgeGcd] using Int.gcd_dvd_right (v.1 - q.1) (v.2 - q.2)
    have hdx : (3 : ℤ) ∣ (v.1 - q.1) := by simpa [hd] using hdvd1
    have hdy : (3 : ℤ) ∣ (v.2 - q.2) := by simpa [hd] using hdvd2
    have hsx : (3 : ℤ) * ((v.1 - q.1) / 3) = v.1 - q.1 := by
      rw [mul_comm]; exact Int.ediv_mul_cancel hdx
    have hsy : (3 : ℤ) * ((v.2 - q.2) / 3) = v.2 - q.2 := by
      rw [mul_comm]; exact Int.ediv_mul_cancel hdy
    refine hend.elim ?_ ?_
    · intro h2q
      have hx := congrArg Prod.fst h2q; simp [p2] at hx
      exact hab (Prod.ext (by linarith [hx, hsx]) (by
        have hy := congrArg Prod.snd h2q; simp [p2] at hy
        linarith [hy, hsy]))
    · intro h2p1
      have hx := congrArg Prod.fst h2p1; simp [p2, p1] at hx
      exact hab (Prod.ext (by linarith [hx, hsx]) (by
        have hy := congrArg Prod.snd h2p1; simp [p2, p1] at hy
        linarith [hy, hsy]))
  rcases eq_vertices_or_rs_of_mem_interiorFan_of_threeInterior P hsc hinj hedge h k
      (by simpa [interiorFanTriangle, v, w] using hp_big) with h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1
  · -- p = v
    subst h2
    have hγ0 : latticeDet q p1 v = 0 := by
      simpa [p1, v] using latticeDet_eq_zero_of_edgeGcd_eq_three_step_one q v hd
    have hedge_qp1 : v ∈ edgeLatticePoints q p1 :=
      mem_edgeLatticePoints_of_weight_zero_ab q p1 w v hp hDsmall hγ0
    have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one q p1 v hprim
      (mem_segment_of_mem_edgeLatticePoints q p1 v hedge_qp1)
    refine False.elim (hend.elim ?_ ?_)
    · intro hvq
      have hq_int := mem_interior_of_threeInterior_apex P h
      have hv_bd : v ∈ P.boundaryLatticePoints := by
        have : v ∈ P.vertexFinset := by
          rw [vertexFinset_eq_univ_image]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
      exact hq_int.2 (hvq ▸ hv_bd)
    · intro hvp1
      have hab : q ≠ v := fun hh => by
        have : edgeGcd q v = 0 := (edgeGcd_eq_zero_iff q v).mpr hh; omega
      obtain ⟨hx, hy⟩ := three_mul_sub_step_one_of_edgeGcd_eq_three q v hd
      have hx' : v.1 - q.1 = 3 * (p1.1 - q.1) := by simpa [p1] using hx.symm
      have hy' : v.2 - q.2 = 3 * (p1.2 - q.2) := by simpa [p1] using hy.symm
      exact hab (Prod.ext (by linarith [congrArg Prod.fst hvp1, hx'])
        (by linarith [congrArg Prod.snd hvp1, hy']))
  · exact Or.inr (Or.inr h3)
  · -- p = r
    rcases hsteps with ⟨hr1, _⟩ | ⟨hr2, _⟩
    · exact Or.inr (Or.inl (h4.trans hr1))
    · have : MemClosedTriangle q p1 w p2 := by
        simpa [h4, hr2] using hp
      exact (hnot_p2 this).elim
  · -- p = s
    rcases hsteps with ⟨_, hs2⟩ | ⟨_, hs1⟩
    · have : MemClosedTriangle q p1 w p2 := by
        simpa [h5, hs2] using hp
      exact (hnot_p2 this).elim
    · exact Or.inr (Or.inl (h5.trans hs1))

/-- Left-adjacent ear has `interiorFanDet = 3` under same-spoke ThreeInterior. -/
theorem interiorFanDet_eq_three_of_threeInterior_sameSpoke_left
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hr : r ∈ edgeLatticePoints q (P.vertex k))
    (hs : s ∈ edgeLatticePoints q (P.vertex k))
    (hne_rq : r ≠ q) (hne_rv : r ≠ P.vertex k)
    (hne_sq : s ≠ q) (hne_sv : s ≠ P.vertex k)
    (hne_rs : r ≠ s) :
    interiorFanDet P q k = 3 := by
  classical
  set v := P.vertex k
  set w := P.vertex (P.nextIdx k)
  set p1 : ℤ × ℤ := (q.1 + (v.1 - q.1) / 3, q.2 + (v.2 - q.2) / 3)
  have hd : edgeGcd q v = 3 :=
    edgeGcd_eq_three_of_threeInterior_sameSpoke P hsc hinj hedge h k hr hs
      hne_rq hne_rv hne_sq hne_sv hne_rs
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDbig : 0 < latticeDet q v w := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, v, w] using hpos k
  have htriple : latticeDet q v w = 3 * latticeDet q p1 w := by
    simpa [p1, v] using latticeDet_eq_three_mul_of_edgeGcd_eq_three_step_one q v w hd
  have hDsmall : 0 < latticeDet q p1 w := by
    have : 0 < 3 * latticeDet q p1 w := by rwa [← htriple]
    omega
  have hnat :
      Int.natAbs (latticeDet q p1 w) = 1 := by
    refine natAbs_det_eq_one_of_memClosedTriangle_eq_vertices q p1 w (ne_of_gt hDsmall) ?_
    intro p hp
    have := eq_vertices_of_memClosedTriangle_threeInterior_sameSpoke_left
      P hsc hinj hedge h k hr hs hne_rq hne_rv hne_sq hne_sv hne_rs
      (by simpa [p1, v] using hp)
    simpa [p1, v, w] using this
  have hnn : 0 ≤ latticeDet q p1 w := le_of_lt hDsmall
  have hz : latticeDet q p1 w = (Int.natAbs (latticeDet q p1 w) : ℤ) :=
    (Int.natAbs_of_nonneg hnn).symm
  have h1 : latticeDet q p1 w = 1 := by rw [hz, hnat]; norm_num
  have : latticeDet q v w = 3 := by rw [htriple, h1]; norm_num
  simpa [interiorFanDet, interiorFanTriangle, Triangle.det, v, w] using this


/-- Right third-ear △`(q,u,p1)` under same-spoke is empty of extra lattice points. -/
theorem eq_vertices_of_memClosedTriangle_threeInterior_sameSpoke_right
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hr : r ∈ edgeLatticePoints q (P.vertex k))
    (hs : s ∈ edgeLatticePoints q (P.vertex k))
    (hne_rq : r ≠ q) (hne_rv : r ≠ P.vertex k)
    (hne_sq : s ≠ q) (hne_sv : s ≠ P.vertex k)
    (hne_rs : r ≠ s)
    {p : ℤ × ℤ}
    (hp : MemClosedTriangle q (P.vertex (P.prevIdx k))
      (q.1 + ((P.vertex k).1 - q.1) / 3, q.2 + ((P.vertex k).2 - q.2) / 3) p) :
    p = q ∨ p = P.vertex (P.prevIdx k) ∨
      p = (q.1 + ((P.vertex k).1 - q.1) / 3, q.2 + ((P.vertex k).2 - q.2) / 3) := by
  classical
  set v := P.vertex k
  set u := P.vertex (P.prevIdx k)
  set p1 : ℤ × ℤ := (q.1 + (v.1 - q.1) / 3, q.2 + (v.2 - q.2) / 3)
  set p2 : ℤ × ℤ := (q.1 + 2 * ((v.1 - q.1) / 3), q.2 + 2 * ((v.2 - q.2) / 3))
  change MemClosedTriangle q u p1 p at hp
  have hd : edgeGcd q v = 3 :=
    edgeGcd_eq_three_of_threeInterior_sameSpoke P hsc hinj hedge h k hr hs
      hne_rq hne_rv hne_sq hne_sv hne_rs
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDbig : 0 < latticeDet q u v := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, u, v,
      P.nextIdx_prevIdx] using hpos (P.prevIdx k)
  have htriple : latticeDet q u v = 3 * latticeDet q u p1 := by
    simpa [p1, v] using
      latticeDet_eq_three_mul_ac_of_edgeGcd_eq_three_step_one q u v hd
  have hDsmall : 0 < latticeDet q u p1 := by
    have : 0 < 3 * latticeDet q u p1 := by rwa [← htriple]
    omega
  have hp_big : MemClosedTriangle q u v p :=
    memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_three_step_one_ac q u v p hd
      (by simpa [p1, v] using hp)
  have hprim : edgeGcd q p1 = 1 := by
    simpa [p1, v] using edgeGcd_eq_one_of_edgeGcd_eq_three_step_one q v hd
  have hsteps :=
    eq_steps_of_mem_edgeLatticePoints_of_edgeGcd_eq_three q v r s hd hr hs
      hne_rq hne_rv hne_sq hne_sv hne_rs
  have hne_qv : q ≠ v := fun hh => by
    have : edgeGcd q v = 0 := (edgeGcd_eq_zero_iff q v).mpr hh; omega
  have hdvd1 : (edgeGcd q v : ℤ) ∣ (v.1 - q.1) := by
    simpa [edgeGcd] using Int.gcd_dvd_left (v.1 - q.1) (v.2 - q.2)
  have hdvd2 : (edgeGcd q v : ℤ) ∣ (v.2 - q.2) := by
    simpa [edgeGcd] using Int.gcd_dvd_right (v.1 - q.1) (v.2 - q.2)
  have hdx : (3 : ℤ) ∣ (v.1 - q.1) := by simpa [hd] using hdvd1
  have hdy : (3 : ℤ) ∣ (v.2 - q.2) := by simpa [hd] using hdvd2
  have hsx : (3 : ℤ) * ((v.1 - q.1) / 3) = v.1 - q.1 := by
    rw [mul_comm]; exact Int.ediv_mul_cancel hdx
  have hsy : (3 : ℤ) * ((v.2 - q.2) / 3) = v.2 - q.2 := by
    rw [mul_comm]; exact Int.ediv_mul_cancel hdy
  have hnot_p2 : ¬ MemClosedTriangle q u p1 p2 := by
    intro hp2
    have hβ0 : latticeDet q p2 p1 = 0 := by
      have h0 : latticeDet q p1 p2 = 0 := by
        simpa [p1, p2, v] using
          latticeDet_eq_zero_step_one_step_two_of_edgeGcd_eq_three q v hd
      have hsw : latticeDet q p2 p1 = -latticeDet q p1 p2 := by unfold latticeDet; ring
      linarith
    have hedge_rq : p2 ∈ edgeLatticePoints p1 q :=
      mem_edgeLatticePoints_of_weight_zero_ca q u p1 p2 hp2 hDsmall hβ0
    have hedge_qr : p2 ∈ edgeLatticePoints q p1 := mem_edgeLatticePoints_comm hedge_rq
    have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one q p1 p2 hprim
      (mem_segment_of_mem_edgeLatticePoints q p1 p2 hedge_qr)
    refine hend.elim ?_ ?_
    · intro h2q
      have hx := congrArg Prod.fst h2q; simp [p2] at hx
      exact hne_qv (Prod.ext (by linarith [hx, hsx]) (by
        have hy := congrArg Prod.snd h2q; simp [p2] at hy
        linarith [hy, hsy]))
    · intro h2p1
      have hx := congrArg Prod.fst h2p1; simp [p2, p1] at hx
      exact hne_qv (Prod.ext (by linarith [hx, hsx]) (by
        have hy := congrArg Prod.snd h2p1; simp [p2, p1] at hy
        linarith [hy, hsy]))
  rcases eq_vertices_or_rs_of_mem_interiorFan_of_threeInterior P hsc hinj hedge h
      (P.prevIdx k) (by simpa [interiorFanTriangle, u, v, P.nextIdx_prevIdx]
        using hp_big) with h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · have hpv : p = v := by simpa [v, P.nextIdx_prevIdx] using h3
    have hp' : MemClosedTriangle q u p1 v := by simpa [hpv] using hp
    have hβ0 : latticeDet q v p1 = 0 := by
      have : latticeDet q p1 v = 0 := by
        simpa [p1, v] using latticeDet_eq_zero_of_edgeGcd_eq_three_step_one q v hd
      have hsw : latticeDet q v p1 = -latticeDet q p1 v := by unfold latticeDet; ring
      linarith
    have hedge_rq : v ∈ edgeLatticePoints p1 q :=
      mem_edgeLatticePoints_of_weight_zero_ca q u p1 v hp' hDsmall hβ0
    have hedge_qr : v ∈ edgeLatticePoints q p1 := mem_edgeLatticePoints_comm hedge_rq
    have hend := eq_endpoints_of_mem_segment_of_edgeGcd_eq_one q p1 v hprim
      (mem_segment_of_mem_edgeLatticePoints q p1 v hedge_qr)
    refine False.elim (hend.elim ?_ ?_)
    · intro hvq
      have hq_int := mem_interior_of_threeInterior_apex P h
      have hv_bd : v ∈ P.boundaryLatticePoints := by
        have : v ∈ P.vertexFinset := by
          rw [vertexFinset_eq_univ_image]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
      exact hq_int.2 (hvq ▸ hv_bd)
    · intro hvp1
      obtain ⟨hx, hy⟩ := three_mul_sub_step_one_of_edgeGcd_eq_three q v hd
      have hx' : v.1 - q.1 = 3 * (p1.1 - q.1) := by simpa [p1] using hx.symm
      have hy' : v.2 - q.2 = 3 * (p1.2 - q.2) := by simpa [p1] using hy.symm
      exact hne_qv (Prod.ext (by linarith [congrArg Prod.fst hvp1, hx'])
        (by linarith [congrArg Prod.snd hvp1, hy']))
  · rcases hsteps with ⟨hr1, _⟩ | ⟨hr2, _⟩
    · exact Or.inr (Or.inr (h4.trans hr1))
    · have : MemClosedTriangle q u p1 p2 := by simpa [h4, hr2] using hp
      exact (hnot_p2 this).elim
  · rcases hsteps with ⟨_, hs2⟩ | ⟨_, hs1⟩
    · have : MemClosedTriangle q u p1 p2 := by simpa [h5, hs2] using hp
      exact (hnot_p2 this).elim
    · exact Or.inr (Or.inr (h5.trans hs1))

/-- Right-adjacent ear has `interiorFanDet = 3` under same-spoke ThreeInterior. -/
theorem interiorFanDet_eq_three_of_threeInterior_sameSpoke_right
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hr : r ∈ edgeLatticePoints q (P.vertex k))
    (hs : s ∈ edgeLatticePoints q (P.vertex k))
    (hne_rq : r ≠ q) (hne_rv : r ≠ P.vertex k)
    (hne_sq : s ≠ q) (hne_sv : s ≠ P.vertex k)
    (hne_rs : r ≠ s) :
    interiorFanDet P q (P.prevIdx k) = 3 := by
  classical
  set v := P.vertex k
  set u := P.vertex (P.prevIdx k)
  set p1 : ℤ × ℤ := (q.1 + (v.1 - q.1) / 3, q.2 + (v.2 - q.2) / 3)
  have hd : edgeGcd q v = 3 :=
    edgeGcd_eq_three_of_threeInterior_sameSpoke P hsc hinj hedge h k hr hs
      hne_rq hne_rv hne_sq hne_sv hne_rs
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hDbig : 0 < latticeDet q u v := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, u, v,
      P.nextIdx_prevIdx] using hpos (P.prevIdx k)
  have htriple : latticeDet q u v = 3 * latticeDet q u p1 := by
    simpa [p1, v] using
      latticeDet_eq_three_mul_ac_of_edgeGcd_eq_three_step_one q u v hd
  have hDsmall : 0 < latticeDet q u p1 := by
    have : 0 < 3 * latticeDet q u p1 := by rwa [← htriple]
    omega
  have hnat : Int.natAbs (latticeDet q u p1) = 1 := by
    refine natAbs_det_eq_one_of_memClosedTriangle_eq_vertices q u p1 (ne_of_gt hDsmall) ?_
    intro p hp
    have := eq_vertices_of_memClosedTriangle_threeInterior_sameSpoke_right
      P hsc hinj hedge h k hr hs hne_rq hne_rv hne_sq hne_sv hne_rs
      (by simpa [p1, v] using hp)
    simpa [p1, v, u] using this
  have hnn : 0 ≤ latticeDet q u p1 := le_of_lt hDsmall
  have hz : latticeDet q u p1 = (Int.natAbs (latticeDet q u p1) : ℤ) :=
    (Int.natAbs_of_nonneg hnn).symm
  have h1 : latticeDet q u p1 = 1 := by rw [hz, hnat]; norm_num
  have : latticeDet q u v = 3 := by rw [htriple, h1]; norm_num
  simpa [interiorFanDet, interiorFanTriangle, Triangle.det, u, v,
    P.nextIdx_prevIdx] using this



/-! ### Same-spoke foreign-ear exclusion + Pick-form (not classical Pick)

Foreign ears (neither `k` nor `prevIdx k`) contain neither `r` nor `s` when both lie
on spoke `q—vₖ` with `edgeGcd = 3`. Empty ⇒ `interiorFanDet = 1`. Combined with
adjacent `det = 3`, fan sum is `n + 4`, so `shoelace = 3 + B/2 − 1`.
Shoelace ≠ Haar. Classical Pick FAIL.
-/

/-- Foreign ear containing same-spoke `r` is `OffTriangleBoundary`. -/
lemma OffTriangleBoundary_of_mem_interiorFan_of_threeInterior_sameSpoke_ne_adjacent
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k j : Fin P.nVertices)
    (hr : r ∈ edgeLatticePoints q (P.vertex k))
    (hs : s ∈ edgeLatticePoints q (P.vertex k))
    (hne_rq : r ≠ q) (hne_rv : r ≠ P.vertex k)
    (hne_sq : s ≠ q) (hne_sv : s ≠ P.vertex k)
    (hne_rs : r ≠ s)
    (_hrj : MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) r)
    (hne_k : j ≠ k) (hne_prev : j ≠ P.prevIdx k) :
    OffTriangleBoundary q (P.vertex j) (P.vertex (P.nextIdx j)) r := by
  classical
  set vj := P.vertex j
  set wj := P.vertex (P.nextIdx j)
  set vk := P.vertex k
  have hdk : edgeGcd q vk = 3 :=
    edgeGcd_eq_three_of_threeInterior_sameSpoke P hsc hinj hedge h k hr hs
      hne_rq hne_rv hne_sq hne_sv hne_rs
  refine ⟨?_, ?_, ?_⟩
  · -- not on spoke q—vj
    intro hspoke
    have hne_vj : r ≠ vj := by
      intro heq
      have hv_bd : vj ∈ P.boundaryLatticePoints := by
        have : vj ∈ P.vertexFinset := by
          rw [vertexFinset_eq_univ_image]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
      exact (mem_interior_of_threeInterior_left P h).2 (heq ▸ hv_bd)
    by_cases hs_j : s ∈ edgeLatticePoints q vj
    · -- both on spoke j ⇒ edgeGcd = 3, endpoints coincide
      have hne_vj_s : s ≠ vj := by
        intro heq
        have hv_bd : vj ∈ P.boundaryLatticePoints := by
          have : vj ∈ P.vertexFinset := by
            rw [vertexFinset_eq_univ_image]
            exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
          exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
        exact (mem_interior_of_threeInterior_right P h).2 (heq ▸ hv_bd)
      have hdj : edgeGcd q vj = 3 :=
        edgeGcd_eq_three_of_threeInterior_sameSpoke P hsc hinj hedge h j hspoke hs_j
          hne_rq hne_vj hne_sq hne_vj_s hne_rs
      have heq :=
        eq_vertex_of_mem_edgeLatticePoints_of_edgeGcd_eq_three q vj vk r s hdj hdk
          hspoke hs_j hr hs hne_rq hne_vj hne_sq hne_vj_s hne_rv hne_sv hne_rs
      exact hne_k (hinj heq)
    · -- only r on spoke j ⇒ edgeGcd = 2; midpoint recovers p2 of gcd=3 spoke
      have hdj : edgeGcd q vj = 2 :=
        edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h j hspoke
          hne_rq hne_vj hs_j
      obtain ⟨hxx, hyy⟩ :=
        two_mul_sub_of_mem_edgeLatticePoints_of_edgeGcd_eq_two q vj r hdj hspoke
          hne_rq hne_vj
      set p1 : ℤ × ℤ := (q.1 + (vk.1 - q.1) / 3, q.2 + (vk.2 - q.2) / 3)
      set p2 : ℤ × ℤ := (q.1 + 2 * ((vk.1 - q.1) / 3), q.2 + 2 * ((vk.2 - q.2) / 3))
      have hsteps :=
        eq_steps_of_mem_edgeLatticePoints_of_edgeGcd_eq_three q vk r s hdk hr hs
          hne_rq hne_rv hne_sq hne_sv hne_rs
      have hsteps' : (r = p1 ∧ s = p2) ∨ (r = p2 ∧ s = p1) := by
        simpa [p1, p2] using hsteps
      rcases hsteps' with ⟨hr1, hs2⟩ | ⟨hr2, hs1⟩
      · -- r = p1 ⇒ vj = p2 = s, but s interior
        have hvj_eq : vj = p2 := by
          apply Prod.ext
          · have : vj.1 - q.1 = 2 * (r.1 - q.1) := hxx.symm
            have : r.1 - q.1 = p1.1 - q.1 := by simp [hr1, p1]
            have hp2 : p2.1 - q.1 = 2 * (p1.1 - q.1) := by simp [p1, p2]
            linarith
          · have : vj.2 - q.2 = 2 * (r.2 - q.2) := hyy.symm
            have : r.2 - q.2 = p1.2 - q.2 := by simp [hr1, p1]
            have hp2 : p2.2 - q.2 = 2 * (p1.2 - q.2) := by simp [p1, p2]
            linarith
        have : vj = s := hvj_eq.trans hs2.symm
        have hv_bd : vj ∈ P.boundaryLatticePoints := by
          have : vj ∈ P.vertexFinset := by
            rw [vertexFinset_eq_univ_image]
            exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
          exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
        exact (mem_interior_of_threeInterior_right P h).2 (this ▸ hv_bd)
      · -- r = p2 ⇒ edgeGcd q vj = 4, contradicts = 2
        obtain ⟨hx3, hy3⟩ := three_mul_sub_step_one_of_edgeGcd_eq_three q vk hdk
        have hsx : vk.1 - q.1 = 3 * (p1.1 - q.1) := by simpa [p1] using hx3.symm
        have hsy : vk.2 - q.2 = 3 * (p1.2 - q.2) := by simpa [p1] using hy3.symm
        have hrx : r.1 - q.1 = 2 * (p1.1 - q.1) := by simp [hr2, p1, p2]
        have hry : r.2 - q.2 = 2 * (p1.2 - q.2) := by simp [hr2, p1, p2]
        have hvjx : vj.1 - q.1 = 4 * (p1.1 - q.1) := by linarith [hxx, hrx]
        have hvjy : vj.2 - q.2 = 4 * (p1.2 - q.2) := by linarith [hyy, hry]
        have hprim : Int.gcd (p1.1 - q.1) (p1.2 - q.2) = 1 := by
          have hgcd : Int.gcd (vk.1 - q.1) (vk.2 - q.2) = 3 := by
            simpa [edgeGcd] using hdk
          have hmul := Int.gcd_mul_left (3 : ℤ) (p1.1 - q.1) (p1.2 - q.2)
          have : 3 = 3 * Int.gcd (p1.1 - q.1) (p1.2 - q.2) := by
            calc
              3 = Int.gcd (vk.1 - q.1) (vk.2 - q.2) := hgcd.symm
              _ = Int.gcd (3 * (p1.1 - q.1)) (3 * (p1.2 - q.2)) := by rw [hsx, hsy]
              _ = Int.natAbs (3 : ℤ) * Int.gcd (p1.1 - q.1) (p1.2 - q.2) := hmul
              _ = 3 * Int.gcd (p1.1 - q.1) (p1.2 - q.2) := by simp
          omega
        have : edgeGcd q vj = 4 := by
          have hmul := Int.gcd_mul_left (4 : ℤ) (p1.1 - q.1) (p1.2 - q.2)
          have : Int.gcd (vj.1 - q.1) (vj.2 - q.2) =
              Int.natAbs (4 : ℤ) * Int.gcd (p1.1 - q.1) (p1.2 - q.2) := by
            rw [hvjx, hvjy, hmul]
          simpa [edgeGcd, hprim] using this
        omega
  · exact not_mem_polygon_edge_of_mem_interior P
      (mem_interior_of_threeInterior_left P h) j
  · -- not on spoke wj—q
    intro hspoke
    have hs' : r ∈ edgeLatticePoints q wj := mem_edgeLatticePoints_comm hspoke
    have hne_wj : r ≠ wj := by
      intro heq
      have hv_bd : wj ∈ P.boundaryLatticePoints := by
        have : wj ∈ P.vertexFinset := by
          rw [vertexFinset_eq_univ_image]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
      exact (mem_interior_of_threeInterior_left P h).2 (heq ▸ hv_bd)
    by_cases hs_w : s ∈ edgeLatticePoints q wj
    · have hne_wj_s : s ≠ wj := by
        intro heq
        have hv_bd : wj ∈ P.boundaryLatticePoints := by
          have : wj ∈ P.vertexFinset := by
            rw [vertexFinset_eq_univ_image]
            exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
          exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
        exact (mem_interior_of_threeInterior_right P h).2 (heq ▸ hv_bd)
      have hdj : edgeGcd q wj = 3 :=
        edgeGcd_eq_three_of_threeInterior_sameSpoke P hsc hinj hedge h (P.nextIdx j)
          hs' hs_w hne_rq hne_wj hne_sq hne_wj_s hne_rs
      have heq :=
        eq_vertex_of_mem_edgeLatticePoints_of_edgeGcd_eq_three q wj vk r s hdj hdk
          hs' hs_w hr hs hne_rq hne_wj hne_sq hne_wj_s hne_rv hne_sv hne_rs
      have : P.nextIdx j = k := hinj heq
      have : j = P.prevIdx k := by rw [← this, prevIdx_nextIdx]
      exact hne_prev this
    · have hdj : edgeGcd q wj = 2 :=
        edgeGcd_eq_two_of_threeInterior_onSpoke P hsc hinj hedge h (P.nextIdx j) hs'
          hne_rq hne_wj hs_w
      obtain ⟨hxx, hyy⟩ :=
        two_mul_sub_of_mem_edgeLatticePoints_of_edgeGcd_eq_two q wj r hdj hs'
          hne_rq hne_wj
      set p1 : ℤ × ℤ := (q.1 + (vk.1 - q.1) / 3, q.2 + (vk.2 - q.2) / 3)
      set p2 : ℤ × ℤ := (q.1 + 2 * ((vk.1 - q.1) / 3), q.2 + 2 * ((vk.2 - q.2) / 3))
      have hsteps' : (r = p1 ∧ s = p2) ∨ (r = p2 ∧ s = p1) := by
        simpa [p1, p2] using
          eq_steps_of_mem_edgeLatticePoints_of_edgeGcd_eq_three q vk r s hdk hr hs
            hne_rq hne_rv hne_sq hne_sv hne_rs
      rcases hsteps' with ⟨hr1, hs2⟩ | ⟨hr2, hs1⟩
      · have hwj_eq : wj = p2 := by
          apply Prod.ext
          · have : wj.1 - q.1 = 2 * (r.1 - q.1) := hxx.symm
            have : r.1 - q.1 = p1.1 - q.1 := by simp [hr1, p1]
            have hp2 : p2.1 - q.1 = 2 * (p1.1 - q.1) := by simp [p1, p2]
            linarith
          · have : wj.2 - q.2 = 2 * (r.2 - q.2) := hyy.symm
            have : r.2 - q.2 = p1.2 - q.2 := by simp [hr1, p1]
            have hp2 : p2.2 - q.2 = 2 * (p1.2 - q.2) := by simp [p1, p2]
            linarith
        have : wj = s := hwj_eq.trans hs2.symm
        have hv_bd : wj ∈ P.boundaryLatticePoints := by
          have : wj ∈ P.vertexFinset := by
            rw [vertexFinset_eq_univ_image]
            exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
          exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
        exact (mem_interior_of_threeInterior_right P h).2 (this ▸ hv_bd)
      · obtain ⟨hx3, hy3⟩ := three_mul_sub_step_one_of_edgeGcd_eq_three q vk hdk
        have hsx : vk.1 - q.1 = 3 * (p1.1 - q.1) := by simpa [p1] using hx3.symm
        have hsy : vk.2 - q.2 = 3 * (p1.2 - q.2) := by simpa [p1] using hy3.symm
        have hrx : r.1 - q.1 = 2 * (p1.1 - q.1) := by simp [hr2, p1, p2]
        have hry : r.2 - q.2 = 2 * (p1.2 - q.2) := by simp [hr2, p1, p2]
        have hwjx : wj.1 - q.1 = 4 * (p1.1 - q.1) := by linarith [hxx, hrx]
        have hwjy : wj.2 - q.2 = 4 * (p1.2 - q.2) := by linarith [hyy, hry]
        have hprim : Int.gcd (p1.1 - q.1) (p1.2 - q.2) = 1 := by
          have hgcd : Int.gcd (vk.1 - q.1) (vk.2 - q.2) = 3 := by
            simpa [edgeGcd] using hdk
          have hmul := Int.gcd_mul_left (3 : ℤ) (p1.1 - q.1) (p1.2 - q.2)
          have : 3 = 3 * Int.gcd (p1.1 - q.1) (p1.2 - q.2) := by
            calc
              3 = Int.gcd (vk.1 - q.1) (vk.2 - q.2) := hgcd.symm
              _ = Int.gcd (3 * (p1.1 - q.1)) (3 * (p1.2 - q.2)) := by rw [hsx, hsy]
              _ = Int.natAbs (3 : ℤ) * Int.gcd (p1.1 - q.1) (p1.2 - q.2) := hmul
              _ = 3 * Int.gcd (p1.1 - q.1) (p1.2 - q.2) := by simp
          omega
        have : edgeGcd q wj = 4 := by
          have hmul := Int.gcd_mul_left (4 : ℤ) (p1.1 - q.1) (p1.2 - q.2)
          have : Int.gcd (wj.1 - q.1) (wj.2 - q.2) =
              Int.natAbs (4 : ℤ) * Int.gcd (p1.1 - q.1) (p1.2 - q.2) := by
            rw [hwjx, hwjy, hmul]
          simpa [edgeGcd, hprim] using this
        omega

/-- Same-spoke `r` occupies only the two adjacent fan ears. -/
theorem eq_of_mem_interiorFan_of_threeInterior_sameSpoke
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k j : Fin P.nVertices)
    (hr : r ∈ edgeLatticePoints q (P.vertex k))
    (hs : s ∈ edgeLatticePoints q (P.vertex k))
    (hne_rq : r ≠ q) (hne_rv : r ≠ P.vertex k)
    (hne_sq : s ≠ q) (hne_sv : s ≠ P.vertex k)
    (hne_rs : r ≠ s)
    (hrj : MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) r) :
    j = k ∨ j = P.prevIdx k := by
  classical
  by_cases hjk : j = k
  · exact Or.inl hjk
  · by_cases hjp : j = P.prevIdx k
    · exact Or.inr hjp
    · have hoff :=
        OffTriangleBoundary_of_mem_interiorFan_of_threeInterior_sameSpoke_ne_adjacent
          P hsc hinj hedge h k j hr hs hne_rq hne_rv hne_sq hne_sv hne_rs hrj hjk hjp
      have hrk : MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) r :=
        mem_interiorFan_of_onSpoke_left P k hr
      have hq := mem_interior_of_threeInterior_apex P h
      have : k = j :=
        eq_of_mem_interiorFan_of_offBoundary P hsc hinj hedge hq j k hrj hoff hrk
      exact (hjk this.symm).elim

/-- Foreign same-spoke ears have `interiorFanDet = 1`. -/
theorem interiorFanDet_eq_one_of_threeInterior_sameSpoke_not_adjacent
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k j : Fin P.nVertices)
    (hr : r ∈ edgeLatticePoints q (P.vertex k))
    (hs : s ∈ edgeLatticePoints q (P.vertex k))
    (hne_rq : r ≠ q) (hne_rv : r ≠ P.vertex k)
    (hne_sq : s ≠ q) (hne_sv : s ≠ P.vertex k)
    (hne_rs : r ≠ s)
    (hne_k : j ≠ k) (hne_prev : j ≠ P.prevIdx k) :
    interiorFanDet P q j = 1 := by
  classical
  have hq := mem_interior_of_threeInterior_apex P h
  have hempty : ∀ p ∈ P.interiorLatticePoints, p ≠ q →
      ¬ MemClosedTriangle (interiorFanTriangle P q j).a
        (interiorFanTriangle P q j).b (interiorFanTriangle P q j).c p := by
    intro p hp hpq hp_mem
    have hpset : p ∈ ({q, r, s} : Set (ℤ × ℤ)) := by
      rw [← h.2.2.2]; exact hp
    rcases (Set.mem_insert_iff.mp hpset) with hpq' | hp'
    · exact hpq hpq'
    · rcases (Set.mem_insert_iff.mp hp') with hpr | hps
      · have hrj : MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) r := by
          simpa [interiorFanTriangle, hpr] using hp_mem
        rcases eq_of_mem_interiorFan_of_threeInterior_sameSpoke
            P hsc hinj hedge h k j hr hs hne_rq hne_rv hne_sq hne_sv hne_rs hrj with
          h1 | h2
        · exact hne_k h1
        · exact hne_prev h2
      · have hsj : MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) s := by
          simpa [interiorFanTriangle, Set.mem_singleton_iff.mp hps] using hp_mem
        -- swap r/s
        rcases eq_of_mem_interiorFan_of_threeInterior_sameSpoke
            P hsc hinj hedge (ThreeInterior_swap P h) k j hs hr
            hne_sq hne_sv hne_rq hne_rv hne_rs.symm hsj with
          h1 | h2
        · exact hne_k h1
        · exact hne_prev h2
  exact interiorFanDet_eq_one_of_no_other_interior P hsc hinj hedge hq j hempty

/-- **I = 3 shoelace Pick-form** under same-spoke occupation (not classical Pick).

Adjacent ears contribute `det = 3`; all foreign ears `det = 1`; fan sum `n + 4`;
`B = n` ⇒ `shoelace = 3 + B/2 − 1`. -/
theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_sameSpoke
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r s : ℤ × ℤ}
    (h : ThreeInterior P q r s) (k : Fin P.nVertices)
    (hr : r ∈ edgeLatticePoints q (P.vertex k))
    (hs : s ∈ edgeLatticePoints q (P.vertex k))
    (hne_rq : r ≠ q) (hne_rv : r ≠ P.vertex k)
    (hne_sq : s ≠ q) (hne_sv : s ≠ P.vertex k)
    (hne_rs : r ≠ s) :
    P.shoelace = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  have hpos := InteriorFanDetsPos_of_threeInterior P hsc hinj hedge h
  have hdetL : interiorFanDet P q k = 3 :=
    interiorFanDet_eq_three_of_threeInterior_sameSpoke_left
      P hsc hinj hedge h k hr hs hne_rq hne_rv hne_sq hne_sv hne_rs
  have hdetR : interiorFanDet P q (P.prevIdx k) = 3 :=
    interiorFanDet_eq_three_of_threeInterior_sameSpoke_right
      P hsc hinj hedge h k hr hs hne_rq hne_rv hne_sq hne_sv hne_rs
  have hne_adj : k ≠ P.prevIdx k := by
    intro heq
    have hnext : P.nextIdx k = k := by
      have h1 : P.nextIdx k = P.nextIdx (P.prevIdx k) := congrArg P.nextIdx heq
      rw [h1, P.nextIdx_prevIdx]
    have hD : 0 < latticeDet q (P.vertex k) (P.vertex (P.nextIdx k)) := by
      simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hpos k
    rw [hnext] at hD
    have hz : latticeDet q (P.vertex k) (P.vertex k) = 0 := by
      simp only [latticeDet]; ring
    exact (ne_of_gt hD) hz
  have hdet1 : ∀ j : Fin P.nVertices, j ≠ k → j ≠ P.prevIdx k →
      interiorFanDet P q j = 1 :=
    fun j h1 h2 =>
      interiorFanDet_eq_one_of_threeInterior_sameSpoke_not_adjacent
        P hsc hinj hedge h k j hr hs hne_rq hne_rv hne_sq hne_sv hne_rs h1 h2
  have hsum :
      (∑ j : Fin P.nVertices, interiorFanDet P q j) = (P.nVertices : ℤ) + 4 := by
    set S := (Finset.univ.erase k).erase (P.prevIdx k)
    have hk_mem : k ∈ Finset.univ := Finset.mem_univ k
    have hprev_mem : P.prevIdx k ∈ Finset.univ.erase k :=
      Finset.mem_erase.mpr ⟨hne_adj.symm, Finset.mem_univ _⟩
    have hdecomp1 :
        (∑ j : Fin P.nVertices, interiorFanDet P q j) =
          interiorFanDet P q k +
            ∑ j ∈ Finset.univ.erase k, interiorFanDet P q j := by
      rw [add_comm]
      exact (Finset.sum_erase_add (s := Finset.univ) (interiorFanDet P q) hk_mem).symm
    have hdecomp2 :
        ∑ j ∈ Finset.univ.erase k, interiorFanDet P q j =
          interiorFanDet P q (P.prevIdx k) +
            ∑ j ∈ S, interiorFanDet P q j := by
      dsimp [S]
      rw [add_comm]
      exact (Finset.sum_erase_add (s := Finset.univ.erase k) (interiorFanDet P q)
        hprev_mem).symm
    have hrest : ∑ j ∈ S, interiorFanDet P q j = ∑ j ∈ S, (1 : ℤ) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have ⟨hne_p, hj2⟩ := Finset.mem_erase.mp hj
      have ⟨hne_kk, _⟩ := Finset.mem_erase.mp hj2
      exact hdet1 j hne_kk hne_p
    have hcard : S.card = P.nVertices - 2 := by
      dsimp [S]
      have h1 : (Finset.univ.erase k).card = P.nVertices - 1 := by
        rw [Finset.card_erase_of_mem hk_mem, Finset.card_univ, Fintype.card_fin]
      have h2 : ((Finset.univ.erase k).erase (P.prevIdx k)).card =
          (Finset.univ.erase k).card - 1 :=
        Finset.card_erase_of_mem hprev_mem
      have : 2 ≤ P.nVertices := by
        have : 3 ≤ P.nVertices := P.length_ge; omega
      omega
    calc
      ∑ j : Fin P.nVertices, interiorFanDet P q j
          = interiorFanDet P q k +
              ∑ j ∈ Finset.univ.erase k, interiorFanDet P q j := hdecomp1
      _ = 3 + (interiorFanDet P q (P.prevIdx k) + ∑ j ∈ S, interiorFanDet P q j) := by
            rw [hdetL, hdecomp2]
      _ = 3 + (3 + ∑ j ∈ S, (1 : ℤ)) := by rw [hdetR, hrest]
      _ = 6 + (S.card : ℤ) := by simp; ring
      _ = 6 + ((P.nVertices - 2 : ℕ) : ℤ) := by rw [hcard]
      _ = (P.nVertices : ℤ) + 4 := by
            have : 2 ≤ P.nVertices := by
              have : 3 ≤ P.nVertices := P.length_ge; omega
            have hcast : ((P.nVertices - 2 : ℕ) : ℤ) = (P.nVertices : ℤ) - 2 :=
              Nat.cast_sub this
            rw [hcast]; ring
  have hshoelaceSum : P.shoelaceSum = (P.nVertices : ℤ) + 4 := by
    rw [← sum_interiorFanDet_eq_shoelaceSum P q, hsum]
  have hB : P.B = P.nVertices := B_eq_nVertices_of_primitive_edges P hedge hinj
  have hnn : 0 ≤ P.shoelaceSum := by
    have : 0 ≤ (P.nVertices : ℤ) + 4 := by
      have : 3 ≤ P.nVertices := P.length_ge; omega
    simpa [hshoelaceSum] using this
  have hnat : Int.natAbs P.shoelaceSum = P.nVertices + 4 := by
    apply Int.natCast_inj.mp
    rw [Int.natAbs_of_nonneg hnn, hshoelaceSum]
    push_cast; ring
  calc
    P.shoelace = (Int.natAbs P.shoelaceSum : ℚ) / 2 := rfl
    _ = ((P.nVertices + 4 : ℕ) : ℚ) / 2 := by
          have : (Int.natAbs P.shoelaceSum : ℚ) = ((P.nVertices + 4 : ℕ) : ℚ) := by
            exact_mod_cast hnat
          rw [this]
    _ = (P.nVertices : ℚ) / 2 + 2 := by push_cast; ring
    _ = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := by rw [hB]; ring


/-! ### Finset card=3 under covered I=3 cases (not classical Pick)

Unifies Off (same-ear ∨ two-ear), on-spoke+Off-nonadjacent, Off-adjacent-left,
Off-adjacent-right, and same-spoke into one Finset `card = 3` statement. Two
distinct spokes still open — remaining gap before an Off-free Finset card=3.
Shoelace ≠ Haar. Classical Pick FAIL.
-/

/-- Covered I=3 configurations from apex `q` that already have Pick-form. -/
def ThreeInteriorCovered (q r s : ℤ × ℤ) : Prop :=
  ThreeInterior P q r s ∧ (
    (∃ i j : Fin P.nVertices,
      MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r ∧
        OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r ∧
          MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) s ∧
            OffTriangleBoundary q (P.vertex j) (P.vertex (P.nextIdx j)) s) ∨
    (∃ k j : Fin P.nVertices,
      r ∈ edgeLatticePoints q (P.vertex k) ∧ r ≠ q ∧ r ≠ P.vertex k ∧
        MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) s ∧
          OffTriangleBoundary q (P.vertex j) (P.vertex (P.nextIdx j)) s ∧
            j ≠ k ∧ j ≠ P.prevIdx k) ∨
    (∃ k : Fin P.nVertices,
      r ∈ edgeLatticePoints q (P.vertex k) ∧ r ≠ q ∧ r ≠ P.vertex k ∧
        MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) s ∧
          OffTriangleBoundary q (P.vertex k) (P.vertex (P.nextIdx k)) s) ∨
    (∃ k : Fin P.nVertices,
      r ∈ edgeLatticePoints q (P.vertex k) ∧ r ≠ q ∧ r ≠ P.vertex k ∧
        MemClosedTriangle q (P.vertex (P.prevIdx k)) (P.vertex k) s ∧
          OffTriangleBoundary q (P.vertex (P.prevIdx k)) (P.vertex k) s) ∨
    (∃ k : Fin P.nVertices,
      r ∈ edgeLatticePoints q (P.vertex k) ∧ s ∈ edgeLatticePoints q (P.vertex k) ∧
        r ≠ q ∧ r ≠ P.vertex k ∧ s ≠ q ∧ s ≠ P.vertex k ∧ r ≠ s))

/-- **I = 3 shoelace Pick-form** under covered configurations (not classical Pick).

Finset `card = 3` when the three interior points form a `ThreeInteriorCovered`
configuration (Off / on-spoke+Off-nonadjacent / Off-adjacent-left/right / same-spoke).
Two-spoke still open. Shoelace ≠ Haar. Classical Pick FAIL. -/
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_three_covered
    (S : Finset (ℤ × ℤ))
    (_hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hcard : S.card = 3)
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hsc : StrictlyConvexCCW P)
    (hcov : ∃ q r s : ℤ × ℤ, S = {q, r, s} ∧ ThreeInteriorCovered P q r s) :
    P.shoelace = (S.card : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  obtain ⟨q, r, s, _hSeq, ⟨hThree, hcases⟩⟩ := hcov
  have harea : P.shoelace = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := by
    rcases hcases with
      ⟨i, j, hr, hoff_r, hs, hoff_s⟩ |
      ⟨k, j, hr, hne_q, hne_v, hs, hoff_s, hne_k, hne_prev⟩ |
      ⟨k, hr, hne_q, hne_v, hs, hoff_s⟩ |
      ⟨k, hr, hne_q, hne_v, hs, hoff_s⟩ |
      ⟨k, hr, hs, hne_rq, hne_rv, hne_sq, hne_sv, hne_rs⟩
    · exact shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_off
        P hsc hverts hedge hThree i j hr hoff_r hs hoff_s
    · exact shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_onSpoke_off
        P hsc hverts hedge hThree k j hr hne_q hne_v hs hoff_s hne_k hne_prev
    · exact shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_onSpoke_off_adjacent_left
        P hsc hverts hedge hThree k hr hne_q hne_v hs hoff_s
    · exact shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_onSpoke_off_adjacent_right
        P hsc hverts hedge hThree k hr hne_q hne_v hs hoff_s
    · exact shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_sameSpoke
        P hsc hverts hedge hThree k hr hs hne_rq hne_rv hne_sq hne_sv hne_rs
  calc
    P.shoelace = (3 : ℚ) + (P.B : ℚ) / 2 - 1 := harea
    _ = (S.card : ℚ) + (P.B : ℚ) / 2 - 1 := by simp [hcard]


end InteriorFan
end LatticeFan
end Picks
end EulersGem
