/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.EarUniqueness

/-!
# On-spoke I = 2 substrate (not classical Pick)

Case-split: a covering ear for the second interior point is either
`OffTriangleBoundary` or on-spoke (base ruled out by interior).
Under `TwoInterior`, an occupied spoke has `edgeGcd = 2`.

The right-spoke disjunct keeps the `OffTriangleBoundary` edge orientation
`edgeLatticePoints (vᵢ₊₁) q` (no symmetry lemma required).

On-spoke det bookkeeping (`det = 2` on the two adjacent ears) and the
unified `TwoInterior => shoelace = 2 + B/2 - 1` remain open.
Classical Pick FAIL.
-/

namespace EulersGem
namespace Picks
namespace LatticeFan
namespace InteriorFan

open LatticeTriangle
open LatticePolygon

variable (P : LatticePolygon)

/-! ### Base edge impossible; covering ear Off or on-spoke -/

lemma not_mem_polygon_edge_of_mem_interior {p : ℤ × ℤ}
    (hp : p ∈ P.interiorLatticePoints) (i : Fin P.nVertices) :
    p ∉ edgeLatticePoints (P.edgePair i).1 (P.edgePair i).2 := by
  intro hedge
  have hbd : p ∈ P.boundaryLatticePoints :=
    (P.mem_boundaryLatticePoints_iff p).mpr ⟨i, hedge⟩
  exact hp.2 hbd

/-- Covering ear for `r` is `OffTriangleBoundary` or on-spoke.
Right-spoke uses edge orientation `(vᵢ₊₁, q)` matching `OffTriangleBoundary`. -/
theorem offBoundary_or_onSpoke_of_mem_interiorFan_of_twoInterior
    {q r : ℤ × ℤ}
    (h : TwoInterior P q r) (i : Fin P.nVertices)
    (_hr : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r) :
    OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r ∨
      r ∈ edgeLatticePoints q (P.vertex i) ∨
        r ∈ edgeLatticePoints (P.vertex (P.nextIdx i)) q := by
  classical
  by_cases hoff : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r
  · exact Or.inl hoff
  · have hr_int := mem_interior_of_twoInterior_right P h
    have hbase :
        r ∉ edgeLatticePoints (P.vertex i) (P.vertex (P.nextIdx i)) := by
      simpa [LatticePolygon.edgePair] using
        not_mem_polygon_edge_of_mem_interior P hr_int i
    simp only [OffTriangleBoundary, not_and_or] at hoff
    rcases hoff with h1 | h2 | h3
    · exact Or.inr (Or.inl (not_not.mp h1))
    · exact absurd (not_not.mp h2) hbase
    · exact Or.inr (Or.inr (not_not.mp h3))

/-! ### Occupied spoke has edgeGcd = 2 under TwoInterior -/

/-- Under `TwoInterior`, if `r` lies strictly on spoke `q -- vertex k`
(either orientation) then `edgeGcd q (vertex k) = 2`. -/
theorem edgeGcd_eq_two_of_twoInterior_onSpoke
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) (k : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k) :
    edgeGcd q (P.vertex k) = 2 := by
  classical
  have hne_qv : q ≠ P.vertex k := by
    intro heq
    have hq := mem_interior_of_twoInterior_left P h
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
  obtain ⟨s, hsE, hsnotin⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hsne_qvr : s ≠ q ∧ s ≠ P.vertex k ∧ s ≠ r := by
    refine ⟨?_, ?_, ?_⟩
    · intro hsq; exact hsnotin (by simp [hsq])
    · intro hsv; exact hsnotin (by simp [hsv])
    · intro hsr; exact hsnotin (by simp [hsr])
  have hmem :=
    memClosedTriangle_of_mem_edgeLatticePoints_ab q (P.vertex k)
      (P.vertex (P.nextIdx k)) s hsE
  have hpos := InteriorFanDetsPos_of_twoInterior_left P hsc hinj hedge h
  have hDpos : 0 < latticeDet q (P.vertex k) (P.vertex (P.nextIdx k)) := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hpos k
  rcases eq_vertices_or_r_of_mem_interiorFan_of_twoInterior P hsc hinj hedge h k
      (by simpa [interiorFanTriangle] using hmem) with h1 | h2 | h3 | h4
  · exact hsne_qvr.1 h1
  · exact hsne_qvr.2.1 h2
  · have : latticeDet q (P.vertex k) (P.vertex (P.nextIdx k)) = 0 :=
      latticeDet_eq_zero_of_mem_edge_ab q (P.vertex k) (P.vertex (P.nextIdx k))
        (by simpa [h3] using hsE)
    exact (ne_of_gt hDpos this).elim
  · exact hsne_qvr.2.2 h4


end InteriorFan
end LatticeFan
end Picks
end EulersGem
