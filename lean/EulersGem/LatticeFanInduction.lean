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
under two distinct off-boundary occupied ears (each inheriting `UniqueInterior`).

**Honesty / not classical Pick:**
Shoelace ≠ Haar/Lebesgue. EP→planar open. General I induction open.
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

end InteriorFan
end LatticeFan
end Picks
end EulersGem
