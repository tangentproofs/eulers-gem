/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.DiskEuler
import EulersGem.LatticeArea

/-!
# Pick's area from a primitive triangulation

A strictly convex lattice polygon is cut into det-primitive triangles:

* an edge of lattice length at least `2` is split at its first interior
  lattice point;
* a triangle with primitive edges and an interior lattice point is fanned
  from that point;
* an empty polygon is the corner fan, and each fan triangle is triangulated
  as above.

The resulting list has length `T = 2I + B − 2`, and the polygon shoelace is
the sum of the triangle shoelaces, hence `T/2`. Turning `T/2` into
`I + B/2 − 1` is `pick_count_of_disk_from_characteristic`: the same counts
have disk Euler number `2` because they are reached from the triangle's
characteristic by the fan, boundary insertions, diagonals, and stellar
subdivisions.
-/

namespace EulersGem
namespace Picks
namespace LatticeFan

open InteriorFan
open LatticeTriangle
open LatticeArea
open BigOperators

variable {α : Type}

/-- Concatenate a `Fin n`-indexed family of lists, `0` first. -/
def concatFin {n : ℕ} (f : Fin n → List α) : List α :=
  match n with
  | 0 => []
  | _ + 1 => f 0 ++ concatFin (fun i => f i.succ)

lemma concatFin_zero (f : Fin 0 → List α) : concatFin f = [] := rfl

lemma concatFin_succ {n : ℕ} (f : Fin (n + 1) → List α) :
    concatFin f = f 0 ++ concatFin (fun i => f i.succ) := rfl

lemma concatFin_length {n : ℕ} (f : Fin n → List α) :
    (concatFin f).length = ∑ i, (f i).length := by
  induction n with
  | zero => simp [concatFin_zero]
  | succ n ih =>
    rw [concatFin_succ, List.length_append, ih, Fin.sum_univ_succ]

lemma concatFin_sum_map {β : Type} [AddCommMonoid β] (g : α → β) {n : ℕ}
    (f : Fin n → List α) :
    ((concatFin f).map g).sum = ∑ i, ((f i).map g).sum := by
  induction n with
  | zero => simp [concatFin_zero]
  | succ n ih =>
    rw [concatFin_succ, List.map_append, List.sum_append, ih, Fin.sum_univ_succ]

lemma forall_mem_concatFin {p : α → Prop} {n : ℕ} {f : Fin n → List α}
    (h : ∀ i, ∀ a ∈ f i, p a) : ∀ a ∈ concatFin f, p a := by
  induction n with
  | zero => simp [concatFin_zero]
  | succ n ih =>
    intro a ha
    rw [concatFin_succ] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h 0 a ha
    · exact ih (fun i => h i.succ) a ha

lemma list_shoelace_eq_length_div_two (ts : List Triangle)
    (h : ∀ t ∈ ts, t.IsDetPrimitive) :
    (ts.map Triangle.shoelace).sum = (ts.length : ℚ) / 2 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have ht := Triangle.shoelace_eq_half_of_isDetPrimitive t
      (h t (List.mem_cons_self (a := t) (l := ts)))
    have hts : ∀ u ∈ ts, u.IsDetPrimitive := fun u hu => h u (List.mem_cons_of_mem t hu)
    rw [List.map_cons, List.sum_cons, List.length_cons, ht, ih hts]
    push_cast
    ring

/-- Listed vertices are boundary lattice points, so `n ≤ B`. -/
theorem nVertices_le_B (P : LatticePolygon) (hverts : Function.Injective P.vertex) :
    P.nVertices ≤ P.B := by
  classical
  have hnodup : P.vertices.Nodup := (List.nodup_iff_injective_get).mpr hverts
  have hcard : P.vertexFinset.card = P.nVertices := by
    simpa [LatticePolygon.vertexFinset, LatticePolygon.nVertices] using
      (List.toFinset_card_of_nodup hnodup)
  have hsub : P.vertexFinset ⊆ P.boundaryLatticePoints := by
    intro v hv
    exact P.vertices_mem_boundary (List.mem_toFinset.mp hv)
  simpa [hcard, LatticePolygon.B] using Finset.card_le_card hsub

lemma sum_sub_const {n : ℕ} (f : Fin n → ℕ) (c : ℕ) (hf : ∀ i, c ≤ f i) :
    ∑ i, (f i - c) = (∑ i, f i) - c * n := by
  have h : ∑ i, (f i - c + c) = ∑ i, f i := by
    refine Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hf i)
  rw [Finset.sum_add_distrib] at h
  have hc : ∑ _i : Fin n, c = c * n := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.mul_comm]
  rw [hc] at h
  omega

/-- Triangle count across an interior fan: each ear contributes
`2 Iₑ + Bₑ − 2`, spokes contribute `gcd − 1` interior points of the parent,
and `∑ Bₑ = 2 ∑ gcd + B`. -/
lemma length_of_interior_fan {n : ℕ} (I B : ℕ) (Iear Bear gcdS : Fin n → ℕ)
    (hI : I = 1 + (∑ i, Iear i) + (∑ i, (gcdS i - 1)))
    (hg : ∀ i, 1 ≤ gcdS i)
    (hBearSum : ∑ i, Bear i = 2 * (∑ i, gcdS i) + B)
    (hB2 : ∀ i, 2 ≤ Bear i)
    (hBB : 2 ≤ 2 * I + B) :
    ∑ i, (2 * Iear i + Bear i - 2) = 2 * I + B - 2 := by
  have hlen : ∑ i, (2 * Iear i + Bear i - 2) =
      (∑ i, (2 * Iear i + Bear i)) - 2 * n := by
    refine sum_sub_const (fun i => 2 * Iear i + Bear i) 2 ?_
    intro i
    exact le_trans (hB2 i) (Nat.le_add_left _ _)
  have hsplit : ∑ i, (2 * Iear i + Bear i) =
      2 * (∑ i, Iear i) + ∑ i, Bear i := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hgcd : ∑ i, gcdS i = (∑ i, (gcdS i - 1)) + n := by
    have hrew : ∑ i, gcdS i = ∑ i, ((gcdS i - 1) + 1) := by
      refine Finset.sum_congr rfl fun i _ => (Nat.sub_add_cancel (hg i)).symm
    rw [hrew, Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hrest : (∑ i, Iear i) + (∑ i, (gcdS i - 1)) = I - 1 := by
    have : 1 + ((∑ i, Iear i) + (∑ i, (gcdS i - 1))) = I := by
      simpa [add_assoc, add_left_comm, add_comm] using hI.symm
    omega
  have hS1 : ∑ i, (2 * Iear i + Bear i) = 2 * (I - 1) + 2 * n + B := by
    rw [hsplit, hBearSum, hgcd]
    have h2 : 2 * ((∑ i, Iear i) + (∑ i, (gcdS i - 1))) =
        2 * (∑ i, Iear i) + 2 * (∑ i, (gcdS i - 1)) := by ring
    calc
      2 * (∑ i, Iear i) + (2 * ((∑ i, (gcdS i - 1)) + n) + B)
          = 2 * (∑ i, Iear i) + 2 * (∑ i, (gcdS i - 1)) + 2 * n + B := by ring
      _ = 2 * ((∑ i, Iear i) + (∑ i, (gcdS i - 1))) + 2 * n + B := by rw [← h2]
      _ = 2 * (I - 1) + 2 * n + B := by rw [hrest]
  have hS1' : ∑ i, (2 * Iear i + Bear i) = 2 * I + B + 2 * n - 2 := by
    have hsub : 2 * (I - 1) = 2 * I - 2 := by omega
    rw [hS1, hsub]
    omega
  have hL : (∑ i, (2 * Iear i + Bear i - 2)) + 2 * n =
      ∑ i, (2 * Iear i + Bear i) := by
    have hle : 2 * n ≤ ∑ i, (2 * Iear i + Bear i) := by
      rw [hS1']; omega
    omega
  rw [hlen, hS1']
  omega

lemma edgeStep_length (I IL IR g BL BR B : ℕ)
    (hg : 1 ≤ g) (hI : I = IL + IR + (g - 1))
    (hB : BL + BR = B + 2 * g)
    (hBL : 2 ≤ BL) (hBR : 2 ≤ BR) (hBB : 2 ≤ 2 * I + B) :
    (2 * IL + BL - 2) + (2 * IR + BR - 2) = 2 * I + B - 2 := by
  have hL : 2 ≤ 2 * IL + BL := by omega
  have hR : 2 ≤ 2 * IR + BR := by omega
  zify [hL, hR, hBB, hg] at *
  omega

lemma B_triangle_ge_three (a b c : ℤ × ℤ) (hD : latticeDet a b c ≠ 0) :
    3 ≤ (trianglePolygon a b c).B := by
  have hB := B_trianglePolygon_eq_sum_edgeGcd a b c hD
  have hab : 1 ≤ edgeGcd a b := Nat.pos_of_ne_zero fun h0 =>
    hD (by
      have : a = b := (edgeGcd_eq_zero_iff a b).mp h0
      subst this
      unfold latticeDet
      ring)
  have hbc : 1 ≤ edgeGcd b c := Nat.pos_of_ne_zero fun h0 =>
    hD (by
      have : b = c := (edgeGcd_eq_zero_iff b c).mp h0
      subst this
      unfold latticeDet
      ring)
  have hca : 1 ≤ edgeGcd c a := Nat.pos_of_ne_zero fun h0 =>
    hD (by
      have : c = a := (edgeGcd_eq_zero_iff c a).mp h0
      subst this
      unfold latticeDet
      ring)
  rw [hB]
  omega

lemma sum_fanTriangle_shoelace (P : LatticePolygon)
    (hnn : FanDetsNonneg P) (hverts : Function.Injective P.vertex) :
    P.shoelace =
      ∑ i : Fin (P.nVertices - 2), (fanTriangle P i.val i.isLt).shoelace := by
  classical
  have hsum := shoelace_eq_sum_fan_shoelace P hnn hverts
  have hinj : Function.Injective
      (fun i : { x // x ∈ Finset.range (P.nVertices - 2) } =>
        fanTriangle P i.1 (Finset.mem_range.mp i.2)) := fun a b h =>
    Subtype.ext (fanTriangle_eq_of_eq P (Finset.mem_range.mp a.2)
      (Finset.mem_range.mp b.2) hverts h)
  dsimp [fanTriangles] at hsum
  rw [Finset.sum_image (fun _ _ _ _ h => hinj h)] at hsum
  let e : Fin (P.nVertices - 2) ≃ { x // x ∈ Finset.range (P.nVertices - 2) } :=
    { toFun := fun i => ⟨i.val, Finset.mem_range.mpr i.isLt⟩
      invFun := fun ⟨i, hi⟩ => ⟨i, Finset.mem_range.mp hi⟩
      left_inv := fun _ => Fin.ext rfl
      right_inv := fun _ => rfl }
  exact hsum.trans (Fintype.sum_equiv e
    (fun i => (fanTriangle P i.val i.isLt).shoelace)
    (fun i => (fanTriangle P i.1 (Finset.mem_range.mp i.2)).shoelace)
    (fun _ => rfl)).symm

lemma trianglePolygon_shoelace_eq_triangle (a b c : ℤ × ℤ) :
    (trianglePolygon a b c).shoelace = (⟨a, b, c⟩ : Triangle).shoelace := by
  simp [Triangle.shoelace, triangleShoelace,
    shoelace_trianglePolygon_eq_half_natAbs_det]

lemma mem_parent_interior_edgeStep_left (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b) {r : ℤ × ℤ}
    (hr : r ∈ (trianglePolygon a (edgeStep a b) c).interiorLatticePoints) :
    r ∈ (trianglePolygon a b c).interiorLatticePoints := by
  set p := edgeStep a b
  have hr' := (mem_interiorLatticePoints_trianglePolygon_iff a p c r).mp hr
  have hp := edgeStep_mem_edgeLatticePoints a b (by omega)
  exact (mem_interiorLatticePoints_trianglePolygon_iff a b c r).mpr
    ⟨memClosedTriangle_of_memClosedTriangle_edgeStep_left a b c p r hp hr'.1,
      OffTriangleBoundary_of_mem_interior_edgeStep_left a b c hD hd r hr'.1 hr'.2⟩

lemma mem_parent_interior_edgeStep_right (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b) {r : ℤ × ℤ}
    (hr : r ∈ (trianglePolygon (edgeStep a b) b c).interiorLatticePoints) :
    r ∈ (trianglePolygon a b c).interiorLatticePoints := by
  set p := edgeStep a b
  have hr' := (mem_interiorLatticePoints_trianglePolygon_iff p b c r).mp hr
  have hp := edgeStep_mem_edgeLatticePoints a b (by omega)
  exact (mem_interiorLatticePoints_trianglePolygon_iff a b c r).mpr
    ⟨memClosedTriangle_of_memClosedTriangle_edgeStep_right a b c p r hp hr'.1,
      OffTriangleBoundary_of_mem_interior_edgeStep_right a b c hD hd r hr'.1 hr'.2⟩

set_option maxHeartbeats 1000000 in
/-- Split one non-primitive edge. Both halves have smaller `|det|`, so the
induction hypothesis supplies their primitive triangulations. -/
lemma exists_primitive_triangle_list_of_edgeStep (n : ℕ)
    (ih : ∀ m, m < n → ∀ a' b' c' (S' : Finset (ℤ × ℤ)),
      0 < latticeDet a' b' c' →
      (S' : Set (ℤ × ℤ)) = (trianglePolygon a' b' c').interiorLatticePoints →
      Int.natAbs (latticeDet a' b' c') = m →
      ∃ ts : List Triangle,
        (∀ t ∈ ts, t.IsDetPrimitive) ∧
        ts.length = 2 * S'.card + (trianglePolygon a' b' c').B - 2 ∧
        (trianglePolygon a' b' c').shoelace = (ts.map Triangle.shoelace).sum)
    (a b c : ℤ × ℤ) (hD : 0 < latticeDet a b c) (hd : 2 ≤ edgeGcd a b)
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = (trianglePolygon a b c).interiorLatticePoints)
    (hn : Int.natAbs (latticeDet a b c) = n) :
    ∃ ts : List Triangle,
      (∀ t ∈ ts, t.IsDetPrimitive) ∧
      ts.length = 2 * S.card + (trianglePolygon a b c).B - 2 ∧
      (trianglePolygon a b c).shoelace = (ts.map Triangle.shoelace).sum := by
  classical
  set p := edgeStep a b
  set g := edgeGcd p c
  let SL := S.filter fun r => r ∈ (trianglePolygon a p c).interiorLatticePoints
  let SR := S.filter fun r => r ∈ (trianglePolygon p b c).interiorLatticePoints
  let SC := S.filter fun r => r ∈ edgeLatticePoints p c ∧ r ≠ p ∧ r ≠ c
  have hD1 : 0 < latticeDet a p c := latticeDet_edgeStep_pos a b c hD (by omega)
  have hD2 : 0 < latticeDet p b c := latticeDet_edgeStep_right_pos a b c hD hd
  have hlt := natAbs_latticeDet_edgeStep_lt a b c hD hd
  have hSL : (SL : Set (ℤ × ℤ)) = (trianglePolygon a p c).interiorLatticePoints := by
    ext r
    constructor
    · intro hr
      exact (Finset.mem_filter.mp (Finset.mem_coe.mp hr)).2
    · intro hr
      have hrP := mem_parent_interior_edgeStep_left a b c hD hd hr
      have hrS : r ∈ S := by
        have hrSet : r ∈ (trianglePolygon a b c).interiorLatticePoints := hrP
        rw [← hS] at hrSet
        exact hrSet
      exact Finset.mem_filter.mpr ⟨hrS, hr⟩
  have hSR : (SR : Set (ℤ × ℤ)) = (trianglePolygon p b c).interiorLatticePoints := by
    ext r
    constructor
    · intro hr
      exact (Finset.mem_filter.mp (Finset.mem_coe.mp hr)).2
    · intro hr
      have hrP := mem_parent_interior_edgeStep_right a b c hD hd hr
      have hrS : r ∈ S := by
        have hrSet : r ∈ (trianglePolygon a b c).interiorLatticePoints := hrP
        rw [← hS] at hrSet
        exact hrSet
      exact Finset.mem_filter.mpr ⟨hrS, hr⟩
  have hpc : p ≠ c := by
    intro h
    have hp := edgeStep_mem_edgeLatticePoints a b (by omega)
    exact (ne_of_gt hD) (by
      simpa [h] using latticeDet_eq_zero_of_mem_edge_ab a b p hp)
  have hg : 1 ≤ g := Nat.pos_of_ne_zero fun h0 =>
    hpc ((edgeGcd_eq_zero_iff p c).mp h0)
  have hSC : SC = ((edgeLatticePoints p c).erase p).erase c := by
    ext r
    simp only [SC, Finset.mem_filter, Finset.mem_erase]
    constructor
    · intro ⟨_, hrE, hrne_p, hrne_c⟩
      exact ⟨hrne_c, hrne_p, hrE⟩
    · intro ⟨hrne_c, hrne_p, hrE⟩
      have hrI := mem_interiorLatticePoints_of_strict_mem_edgeStep_chord a b c hD hd hrE hrne_p hrne_c
      have hrS : r ∈ S := by
        rw [← hS] at hrI
        exact hrI
      exact ⟨hrS, hrE, hrne_p, hrne_c⟩
  have hSCcard : SC.card = g - 1 := by
    rw [hSC]
    have hcard := card_edgeLatticePoints p c
    have hp := self_mem_edgeLatticePoints p c
    have hc := other_mem_edgeLatticePoints p c
    have hc' : c ∈ (edgeLatticePoints p c).erase p :=
      Finset.mem_erase.mpr ⟨fun h => hpc h.symm, hc⟩
    have h1 : ((edgeLatticePoints p c).erase p).card = g := by
      rw [Finset.card_erase_of_mem hp, hcard]; omega
    rw [Finset.card_erase_of_mem hc', h1]
  have hdLR : Disjoint SL SR := by
    rw [Finset.disjoint_left]
    intro r hrL hrR
    have hL := (Finset.mem_filter.mp hrL).2
    have hR := (Finset.mem_filter.mp hrR).2
    have hLp := (mem_interiorLatticePoints_trianglePolygon_iff a p c r).mp hL
    have hRp := (mem_interiorLatticePoints_trianglePolygon_iff p b c r).mp hR
    have hposL := latticeDet_pos_of_memClosedTriangle_offBoundary a p c r hLp.1 hD1 hLp.2
    have hposR := latticeDet_pos_of_memClosedTriangle_offBoundary p b c r hRp.1 hD2 hRp.2
    have hneg : latticeDet p c r = -latticeDet p r c := latticeDet_swap_middle p c r
    linarith
  have hdLC : Disjoint SL SC := by
    rw [Finset.disjoint_left]
    intro r hrL hrC
    have hL := (Finset.mem_filter.mp hrL).2
    have hC := (Finset.mem_filter.mp hrC).2
    have hLp := (mem_interiorLatticePoints_trianglePolygon_iff a p c r).mp hL
    exact hLp.2.2.1 hC.1
  have hdRC : Disjoint SR SC := by
    rw [Finset.disjoint_left]
    intro r hrR hrC
    have hR := (Finset.mem_filter.mp hrR).2
    have hC := (Finset.mem_filter.mp hrC).2
    have hRp := (mem_interiorLatticePoints_trianglePolygon_iff p b c r).mp hR
    exact hRp.2.2.2 (mem_edgeLatticePoints_comm hC.1)
  have hU : SL ∪ SR ∪ SC = S := by
    ext r
    constructor
    · intro hr
      rcases Finset.mem_union.mp hr with hr | hr
      · rcases Finset.mem_union.mp hr with hr | hr
        · exact (Finset.mem_filter.mp hr).1
        · exact (Finset.mem_filter.mp hr).1
      · exact (Finset.mem_filter.mp hr).1
    · intro hr
      have hrI : r ∈ (trianglePolygon a b c).interiorLatticePoints := by
        have hrSet : r ∈ (S : Set (ℤ × ℤ)) := hr
        rwa [hS] at hrSet
      have htri := mem_interior_left_or_right_or_chord_of_mem_interior_edgeStep a b c hD hd hrI
      rcases htri with hL | hR | hC
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr ⟨hr, hL⟩))))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨hr, hR⟩))))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hr, hC⟩))
  have hI : S.card = SL.card + SR.card + SC.card := by
    have hdU : Disjoint (SL ∪ SR) SC := by
      rw [Finset.disjoint_union_left]
      exact ⟨hdLC, hdRC⟩
    rw [← hU, Finset.card_union_of_disjoint hdU, Finset.card_union_of_disjoint hdLR]
  have hlt1 : Int.natAbs (latticeDet a p c) < n := by simpa [hn, p] using hlt.1
  have hlt2 : Int.natAbs (latticeDet p b c) < n := by simpa [hn, p] using hlt.2
  obtain ⟨tsL, hprimL, hlenL, hshoeL⟩ :=
    ih _ hlt1 a p c SL hD1 hSL rfl
  obtain ⟨tsR, hprimR, hlenR, hshoeR⟩ :=
    ih _ hlt2 p b c SR hD2 hSR rfl
  refine ⟨tsL ++ tsR, ?_, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hprimL t ht
    · exact hprimR t ht
  · rw [List.length_append, hlenL, hlenR]
    have hBa := B_add_of_edgeStep_of_gcd a b c hD hd
    have hBL := B_triangle_ge_three a p c (ne_of_gt hD1)
    have hBR := B_triangle_ge_three p b c (ne_of_gt hD2)
    have hBB : 2 ≤ 2 * S.card + (trianglePolygon a b c).B := by
      have hB3 := B_triangle_ge_three a b c (ne_of_gt hD)
      omega
    exact edgeStep_length S.card SL.card SR.card g
      (trianglePolygon a p c).B (trianglePolygon p b c).B (trianglePolygon a b c).B
      hg (by simpa [hSCcard, add_assoc, add_left_comm, add_comm] using hI)
      (by simpa [p, g] using hBa) (by omega) (by omega) hBB
  · rw [List.map_append, List.sum_append, ← hshoeL, ← hshoeR,
      shoelace_add_of_edgeStep a b c hD hd]

set_option maxHeartbeats 1000000 in
/-- Every positively oriented lattice triangle has a det-primitive triangulation
of length `2I + B − 2` whose shoelaces sum to the triangle shoelace.
Induction is on `|det|`. -/
theorem exists_primitive_triangle_list (a b c : ℤ × ℤ)
    (hD : 0 < latticeDet a b c) (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = (trianglePolygon a b c).interiorLatticePoints) :
    ∃ ts : List Triangle,
      (∀ t ∈ ts, t.IsDetPrimitive) ∧
      ts.length = 2 * S.card + (trianglePolygon a b c).B - 2 ∧
      (trianglePolygon a b c).shoelace = (ts.map Triangle.shoelace).sum := by
  classical
  have hmain : ∀ n a b c (S : Finset (ℤ × ℤ)),
      0 < latticeDet a b c →
      (S : Set (ℤ × ℤ)) = (trianglePolygon a b c).interiorLatticePoints →
      Int.natAbs (latticeDet a b c) = n →
      ∃ ts : List Triangle,
        (∀ t ∈ ts, t.IsDetPrimitive) ∧
        ts.length = 2 * S.card + (trianglePolygon a b c).B - 2 ∧
        (trianglePolygon a b c).shoelace = (ts.map Triangle.shoelace).sum := by
    intro n
    refine Nat.strong_induction_on n fun n ih a b c S hD hS hn => ?_
    have hposG := edgeGcd_pos_of_latticeDet_pos a b c hD
    by_cases hprim : edgeGcd a b = 1 ∧ edgeGcd b c = 1 ∧ edgeGcd c a = 1
    · by_cases hempty : S.card = 0
      · have hSe : S = ∅ := Finset.card_eq_zero.mp hempty
        let T := trianglePolygon a b c
        have hsc := StrictlyConvexCCW_trianglePolygon a b c hD
        have hinj := injective_vertex_trianglePolygon a b c (ne_of_gt hD)
        have hedge := PrimitiveEdges_trianglePolygon_of_edgeGcds a b c hprim.1 hprim.2.1 hprim.2.2
        have hI : EmptyInterior T := by
          simpa [EmptyInterior, hSe] using hS.symm
        have hpos := FanDetsPos_of_strictlyConvexCCW T hsc hinj
        have hext := VerticesExtreme_of_strictlyConvexCCW T hsc hinj
        have hemptyFan := FanTrianglesEmpty_of_empty_interior T hinj hedge hI hext
        have hfan := FanDetPrimitive_of_empty_fan_triangles T hpos hemptyFan
        have hi0 : (0 : ℕ) < T.nVertices - 2 := by
          simp [T, trianglePolygon_nVertices]
        have hdet : (fanTriangle T 0 hi0).IsDetPrimitive := hfan 0 hi0
        have hB : T.B = 3 := by
          simpa [T, trianglePolygon_nVertices] using
            B_eq_nVertices_of_primitive_edges T hedge hinj
        refine ⟨[fanTriangle T 0 hi0], ?_, ?_, ?_⟩
        · intro t ht
          simp only [List.mem_singleton] at ht
          simpa [ht] using hdet
        · simp [hempty, hB, T]
        · have harea :=
            shoelace_eq_B_div_two_sub_one_of_empty_interior_convex T hinj hedge hI hsc
          have hhalf : T.shoelace = 1 / 2 := by
            rw [harea, hB]
            norm_num
          change T.shoelace = (List.map Triangle.shoelace [fanTriangle T 0 hi0]).sum
          rw [hhalf]
          simp [Triangle.shoelace_eq_half_of_isDetPrimitive _ hdet]
      · let T := trianglePolygon a b c
        have hsc := StrictlyConvexCCW_trianglePolygon a b c hD
        have hinj := injective_vertex_trianglePolygon a b c (ne_of_gt hD)
        have hedge := PrimitiveEdges_trianglePolygon_of_edgeGcds a b c hprim.1 hprim.2.1 hprim.2.2
        have hneS : S.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨q, hq⟩ := hneS
        have hqI : q ∈ T.interiorLatticePoints := by
          have hqS : q ∈ (S : Set (ℤ × ℤ)) := hq
          simpa [hS, T] using hqS
        have hposFan := InteriorFanDetsPos_of_mem_interior T hsc hinj hedge hqI
        have hEar : ∀ i : Fin T.nVertices, ∃ ts : List Triangle,
            (∀ t ∈ ts, t.IsDetPrimitive) ∧
            ts.length = 2 * (earOffInterior T q i S).card +
              (trianglePolygon q (T.vertex i) (T.vertex (T.nextIdx i))).B - 2 ∧
            (trianglePolygon q (T.vertex i) (T.vertex (T.nextIdx i))).shoelace =
              (ts.map Triangle.shoelace).sum := by
          intro i
          have hDear : 0 < latticeDet q (T.vertex i) (T.vertex (T.nextIdx i)) := by
            simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hposFan i
          have hlt : Int.natAbs (latticeDet q (T.vertex i) (T.vertex (T.nextIdx i))) < n := by
            have hsum := sum_interiorFanDet_eq_shoelaceSum T q
            have hsho : T.shoelaceSum = latticeDet a b c := by
              simpa [T] using shoelaceSum_trianglePolygon a b c
            have hone : ∀ j : Fin T.nVertices, (1 : ℤ) ≤ interiorFanDet T q j := fun j =>
              by have := hposFan j; omega
            have hrest : interiorFanDet T q i + 2 ≤ ∑ j, interiorFanDet T q j := by
              have herase := Finset.sum_erase_add Finset.univ (interiorFanDet T q)
                (Finset.mem_univ i)
              rw [← herase]
              have hcard : (Finset.univ.erase i).card = 2 := by
                rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
                  Fintype.card_fin]
                simp [T, trianglePolygon_nVertices]
              have hge : ∑ j ∈ Finset.univ.erase i, (1 : ℤ) ≤
                  ∑ j ∈ Finset.univ.erase i, interiorFanDet T q j :=
                Finset.sum_le_sum fun j _ => hone j
              have hones : ∑ j ∈ Finset.univ.erase i, (1 : ℤ) = 2 := by
                simp [Finset.sum_const, hcard]
              linarith
            have hltZ : interiorFanDet T q i < latticeDet a b c := by
              have hsum' : ∑ j, interiorFanDet T q j = latticeDet a b c := by
                rw [hsum, hsho]
              linarith
            have hnn1 : 0 ≤ interiorFanDet T q i := le_of_lt (hposFan i)
            have hnn2 : 0 ≤ latticeDet a b c := le_of_lt hD
            have hltInt : interiorFanDet T q i < (n : ℤ) := by
              have hparent : (Int.natAbs (latticeDet a b c) : ℤ) = latticeDet a b c :=
                Int.natAbs_of_nonneg hnn2
              calc
                interiorFanDet T q i < latticeDet a b c := hltZ
                _ = (Int.natAbs (latticeDet a b c) : ℤ) := hparent.symm
                _ = (n : ℤ) := by rw [hn]
            have hnatEq : (Int.natAbs (interiorFanDet T q i) : ℤ) = interiorFanDet T q i :=
              Int.natAbs_of_nonneg hnn1
            have hcast : (Int.natAbs (interiorFanDet T q i) : ℤ) < (n : ℤ) := by
              rwa [hnatEq]
            simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using
              (show Int.natAbs (interiorFanDet T q i) < n from by exact_mod_cast hcast)
          have hSear :=
            coe_earOffInterior_eq_interiorLatticePoints_trianglePolygon
              T S (by simpa [T] using hS) hsc hinj hedge hq i
          exact ih _ hlt q (T.vertex i) (T.vertex (T.nextIdx i))
            (earOffInterior T q i S) hDear hSear rfl
        choose ts hpack using hEar
        have hprim_i : ∀ i, ∀ t ∈ ts i, t.IsDetPrimitive := fun i => (hpack i).1
        have hlen_i : ∀ i, (ts i).length =
            2 * (earOffInterior T q i S).card +
              (trianglePolygon q (T.vertex i) (T.vertex (T.nextIdx i))).B - 2 :=
          fun i => (hpack i).2.1
        have hshoe_i : ∀ i,
            (trianglePolygon q (T.vertex i) (T.vertex (T.nextIdx i))).shoelace =
              ((ts i).map Triangle.shoelace).sum := fun i => (hpack i).2.2
        refine ⟨concatFin ts, forall_mem_concatFin hprim_i, ?_, ?_⟩
        · rw [concatFin_length]
          have hIcard := card_eq_one_add_earOff_add_spoke T S (by simpa [T] using hS)
            hsc hinj hedge hq
          have hspoke := fun k =>
            card_spokeInterior_eq_edgeGcd_sub_one T S (by simpa [T] using hS)
              hsc hinj hedge hq k
          have hgcd : ∀ k : Fin T.nVertices, 1 ≤ edgeGcd q (T.vertex k) := by
            intro k
            have hne := ne_vertex_of_mem_interior T hinj hedge hqI k
            exact Nat.pos_of_ne_zero fun h0 =>
              hne ((edgeGcd_eq_zero_iff q (T.vertex k)).mp h0)
          have hBear : ∀ i : Fin T.nVertices,
              (trianglePolygon q (T.vertex i) (T.vertex (T.nextIdx i))).B =
                edgeGcd q (T.vertex i) +
                  edgeGcd (T.vertex i) (T.vertex (T.nextIdx i)) +
                    edgeGcd (T.vertex (T.nextIdx i)) q := by
            intro i
            have hDi := hposFan i
            exact B_trianglePolygon_eq_sum_edgeGcd _ _ _
              (by simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using (ne_of_gt hDi))
          have hBsum : (∑ i : Fin T.nVertices,
              (trianglePolygon q (T.vertex i) (T.vertex (T.nextIdx i))).B) =
              2 * (∑ k : Fin T.nVertices, edgeGcd q (T.vertex k)) + T.B := by
            have hcongr : (∑ i, (trianglePolygon q (T.vertex i) (T.vertex (T.nextIdx i))).B) =
                ∑ i, (edgeGcd q (T.vertex i) +
                  edgeGcd (T.vertex i) (T.vertex (T.nextIdx i)) +
                    edgeGcd q (T.vertex (T.nextIdx i))) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hBear i, edgeGcd_comm (T.vertex (T.nextIdx i)) q]
            rw [hcongr, Finset.sum_add_distrib, Finset.sum_add_distrib]
            have hre : (∑ i, edgeGcd q (T.vertex (T.nextIdx i))) =
                ∑ i, edgeGcd q (T.vertex i) := by
              refine Finset.sum_bij (fun i _ => T.nextIdx i) (fun _ _ => Finset.mem_univ _)
                (fun i _ j _ hij => by
                  simpa [T.prevIdx_nextIdx] using congrArg T.prevIdx hij)
                (fun j _ => ⟨T.prevIdx j, Finset.mem_univ _, T.nextIdx_prevIdx j⟩)
                (fun _ _ => rfl)
            have hbound := B_eq_sum_edgeGcd T hsc hinj
            rw [hre, hbound]
            ring
          have hIform : S.card = 1 + (∑ i, (earOffInterior T q i S).card) +
              (∑ i, (edgeGcd q (T.vertex i) - 1)) := by
            rw [hIcard]
            congr 1
            refine Finset.sum_congr rfl fun k _ => hspoke k
          have hB2 : ∀ i : Fin T.nVertices,
              2 ≤ (trianglePolygon q (T.vertex i) (T.vertex (T.nextIdx i))).B := by
            intro i
            exact le_trans (by omega : 2 ≤ 3)
              (B_triangle_ge_three _ _ _
                (ne_of_gt (by
                  simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hposFan i)))
          have hBB : 2 ≤ 2 * S.card + T.B := by
            have hB3 := B_triangle_ge_three a b c (ne_of_gt hD)
            simpa [T] using (by omega : 2 ≤ 2 * S.card + (trianglePolygon a b c).B)
          have hlen := length_of_interior_fan S.card T.B
            (fun i => (earOffInterior T q i S).card)
            (fun i => (trianglePolygon q (T.vertex i) (T.vertex (T.nextIdx i))).B)
            (fun i => edgeGcd q (T.vertex i))
            hIform hgcd hBsum hB2 hBB
          have hlens : ∑ i, (ts i).length =
              ∑ i, (2 * (earOffInterior T q i S).card +
                (trianglePolygon q (T.vertex i) (T.vertex (T.nextIdx i))).B - 2) := by
            refine Finset.sum_congr rfl fun i _ => hlen_i i
          rw [hlens]
          exact hlen
        · rw [concatFin_sum_map]
          have hshoe : (∑ i, ((ts i).map Triangle.shoelace).sum) =
              ∑ i, (trianglePolygon q (T.vertex i) (T.vertex (T.nextIdx i))).shoelace := by
            refine Finset.sum_congr rfl fun i _ => (hshoe_i i).symm
          rw [hshoe, sum_ear_shoelace_eq_shoelace (P := T) hposFan]
    · have hge : 2 ≤ edgeGcd a b ∨ 2 ≤ edgeGcd b c ∨ 2 ≤ edgeGcd c a := by
        omega
      rcases hge with hab | hbc | hca
      · exact exists_primitive_triangle_list_of_edgeStep n ih a b c hD hab S hS hn
      · have hDc : 0 < latticeDet b c a := by simpa [← latticeDet_cyclic a b c] using hD
        have hSc : (S : Set (ℤ × ℤ)) = (trianglePolygon b c a).interiorLatticePoints := by
          rw [hS, interiorLatticePoints_trianglePolygon_cyclic]
        have hnc : Int.natAbs (latticeDet b c a) = n := by
          rw [← latticeDet_cyclic a b c, hn]
        obtain ⟨ts, hprim, hlen, hshoe⟩ :=
          exists_primitive_triangle_list_of_edgeStep n ih b c a hDc hbc S hSc hnc
        have hB := B_trianglePolygon_cyclic a b c (ne_of_gt hD)
        have hs := shoelace_trianglePolygon_cyclic a b c
        refine ⟨ts, hprim, ?_, ?_⟩
        · rw [← hB] at hlen; exact hlen
        · rw [hs]; exact hshoe
      · have hDc : 0 < latticeDet c a b := by simpa [← latticeDet_cyclic₂ a b c] using hD
        have hSc : (S : Set (ℤ × ℤ)) = (trianglePolygon c a b).interiorLatticePoints := by
          rw [hS, interiorLatticePoints_trianglePolygon_cyclic,
            interiorLatticePoints_trianglePolygon_cyclic]
        have hnc : Int.natAbs (latticeDet c a b) = n := by
          rw [← latticeDet_cyclic₂ a b c, hn]
        obtain ⟨ts, hprim, hlen, hshoe⟩ :=
          exists_primitive_triangle_list_of_edgeStep n ih c a b hDc hca S hSc hnc
        have hB1 := B_trianglePolygon_cyclic a b c (ne_of_gt hD)
        have hB2 := B_trianglePolygon_cyclic b c a
          (by simpa [← latticeDet_cyclic a b c] using ne_of_gt hD)
        have hs1 := shoelace_trianglePolygon_cyclic a b c
        have hs2 := shoelace_trianglePolygon_cyclic b c a
        refine ⟨ts, hprim, ?_, ?_⟩
        · rw [← hB2, ← hB1] at hlen; exact hlen
        · rw [hs1, hs2]; exact hshoe
  exact hmain _ a b c S hD hS rfl

set_option maxHeartbeats 1000000 in
/-- A strictly convex lattice polygon has a det-primitive triangulation of
length `2I + B − 2`. Empty polygons use the corner fan; a polygon with an
interior point is fanned from that point, and each ear is a triangle. -/
theorem exists_primitive_polygon_list (P : LatticePolygon) (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hverts : Function.Injective P.vertex) (hsc : StrictlyConvexCCW P) :
    ∃ ts : List Triangle,
      (∀ t ∈ ts, t.IsDetPrimitive) ∧
      ts.length = 2 * S.card + P.B - 2 ∧
      P.shoelace = (ts.map Triangle.shoelace).sum := by
  classical
  by_cases hempty : S.card = 0
  · have hSe : S = ∅ := Finset.card_eq_zero.mp hempty
    have hI : EmptyInterior P := by simpa [EmptyInterior, hSe] using hS.symm
    have hpos := FanDetsPos_of_strictlyConvexCCW P hsc hverts
    have hnn := FanDetsNonneg_of_pos P hpos
    have hEar : ∀ i : Fin (P.nVertices - 2), ∃ ts : List Triangle,
        (∀ t ∈ ts, t.IsDetPrimitive) ∧
        ts.length =
          (trianglePolygon (fanTriangle P i.val i.isLt).a (fanTriangle P i.val i.isLt).b
            (fanTriangle P i.val i.isLt).c).B - 2 ∧
        (trianglePolygon (fanTriangle P i.val i.isLt).a (fanTriangle P i.val i.isLt).b
            (fanTriangle P i.val i.isLt).c).shoelace =
          (ts.map Triangle.shoelace).sum := by
      intro i
      have hemptyEar := EmptyInterior_trianglePolygon_fanTriangle P hsc hverts hI i.val i.isLt
      have hD : 0 < latticeDet (fanTriangle P i.val i.isLt).a
          (fanTriangle P i.val i.isLt).b (fanTriangle P i.val i.isLt).c := by
        simpa [fanDet, Triangle.det] using hpos i.val i.isLt
      have hSempty : ((∅ : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) =
          (trianglePolygon (fanTriangle P i.val i.isLt).a (fanTriangle P i.val i.isLt).b
            (fanTriangle P i.val i.isLt).c).interiorLatticePoints := by
        simpa [EmptyInterior] using hemptyEar.symm
      obtain ⟨ts, hprim, hlen, hshoe⟩ := exists_primitive_triangle_list
        (fanTriangle P i.val i.isLt).a (fanTriangle P i.val i.isLt).b
        (fanTriangle P i.val i.isLt).c hD ∅ hSempty
      refine ⟨ts, hprim, ?_, hshoe⟩
      simpa using hlen
    choose ts hpack using hEar
    refine ⟨concatFin ts, forall_mem_concatFin (fun i => (hpack i).1), ?_, ?_⟩
    · rw [concatFin_length]
      have hlen_i : ∀ i : Fin (P.nVertices - 2), (ts i).length =
          (trianglePolygon (fanTriangle P i.val i.isLt).a (fanTriangle P i.val i.isLt).b
            (fanTriangle P i.val i.isLt).c).B - 2 := fun i => by
        simpa using (hpack i).2.1
      have hsumB := sum_B_fan_ears_eq_B_add_two_mul_n_sub_three P hsc hverts hI
      have hB2 : ∀ i : Fin (P.nVertices - 2),
          2 ≤ (trianglePolygon (fanTriangle P i.val i.isLt).a
            (fanTriangle P i.val i.isLt).b (fanTriangle P i.val i.isLt).c).B := by
        intro i
        have hD := hpos i.val i.isLt
        exact le_trans (by omega : 2 ≤ 3) (B_triangle_ge_three _ _ _
          (ne_of_gt (by simpa [fanDet, Triangle.det] using hD)))
      have hsub := sum_sub_const
        (fun i : Fin (P.nVertices - 2) =>
          (trianglePolygon (fanTriangle P i.val i.isLt).a (fanTriangle P i.val i.isLt).b
            (fanTriangle P i.val i.isLt).c).B) 2 hB2
      have hn : 3 ≤ P.nVertices := P.length_ge
      have hlens : ∑ i : Fin (P.nVertices - 2), (ts i).length =
          ∑ i : Fin (P.nVertices - 2), ((trianglePolygon (fanTriangle P i.val i.isLt).a
            (fanTriangle P i.val i.isLt).b (fanTriangle P i.val i.isLt).c).B - 2) := by
        refine Finset.sum_congr rfl fun i _ => hlen_i i
      have : ∑ i, (ts i).length = P.B - 2 := by
        rw [hlens, hsub, hsumB]
        omega
      simpa [hempty] using this
    · rw [concatFin_sum_map]
      have hshoe : (∑ i, ((ts i).map Triangle.shoelace).sum) =
          ∑ i : Fin (P.nVertices - 2), (fanTriangle P i.val i.isLt).shoelace := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← (hpack i).2.2, trianglePolygon_shoelace_eq_triangle]
      rw [hshoe, ← sum_fanTriangle_shoelace P hnn hverts]
  · have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨q, hq⟩ := hne
    have hqI : q ∈ P.interiorLatticePoints := by
      have hqS : q ∈ (S : Set (ℤ × ℤ)) := hq
      simpa [hS] using hqS
    have hposFan := InteriorFanDetsPos_of_mem_interior_no_pe P hsc hverts hqI
    have hEar : ∀ i : Fin P.nVertices, ∃ ts : List Triangle,
        (∀ t ∈ ts, t.IsDetPrimitive) ∧
        ts.length = 2 * (earOffInterior P q i S).card +
          (trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))).B - 2 ∧
        (trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))).shoelace =
          (ts.map Triangle.shoelace).sum := by
      intro i
      have hDear : 0 < latticeDet q (P.vertex i) (P.vertex (P.nextIdx i)) := by
        simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hposFan i
      have hSear := coe_earOffInterior_eq_interiorLatticePoints_trianglePolygon_no_pe
        P S hS hsc hverts hq i
      exact exists_primitive_triangle_list q (P.vertex i) (P.vertex (P.nextIdx i))
        hDear (earOffInterior P q i S) hSear
    choose ts hpack using hEar
    refine ⟨concatFin ts, forall_mem_concatFin (fun i => (hpack i).1), ?_, ?_⟩
    · rw [concatFin_length]
      have hIcard := card_eq_one_add_earOff_add_spoke_no_pe P S hS hsc hverts hq
      have hspoke := fun k =>
        card_spokeInterior_eq_edgeGcd_sub_one_no_pe P S hS hsc hverts hq k
      have hgcd : ∀ k, 1 ≤ edgeGcd q (P.vertex k) := by
        intro k
        have hne_v := ne_vertex_of_mem_interior_no_pe P hqI k
        exact Nat.pos_of_ne_zero fun h0 =>
          hne_v ((edgeGcd_eq_zero_iff q (P.vertex k)).mp h0)
      have hBear : ∀ i,
          (trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))).B =
            edgeGcd q (P.vertex i) + edgeGcd (P.vertex i) (P.vertex (P.nextIdx i)) +
              edgeGcd (P.vertex (P.nextIdx i)) q := by
        intro i
        exact B_trianglePolygon_eq_sum_edgeGcd _ _ _
          (ne_of_gt (by simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hposFan i))
      have hBsum : (∑ i, (trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))).B) =
          2 * (∑ k, edgeGcd q (P.vertex k)) + P.B := by
        have hcongr : (∑ i, (trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))).B) =
            ∑ i, (edgeGcd q (P.vertex i) +
              edgeGcd (P.vertex i) (P.vertex (P.nextIdx i)) +
                edgeGcd q (P.vertex (P.nextIdx i))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hBear i, edgeGcd_comm (P.vertex (P.nextIdx i)) q]
        rw [hcongr, Finset.sum_add_distrib, Finset.sum_add_distrib]
        have hre : (∑ i, edgeGcd q (P.vertex (P.nextIdx i))) =
            ∑ i, edgeGcd q (P.vertex i) := by
          refine Finset.sum_bij (fun i _ => P.nextIdx i) (fun _ _ => Finset.mem_univ _)
            (fun i _ j _ hij => by
              simpa [P.prevIdx_nextIdx] using congrArg P.prevIdx hij)
            (fun j _ => ⟨P.prevIdx j, Finset.mem_univ _, P.nextIdx_prevIdx j⟩)
            (fun _ _ => rfl)
        rw [hre, B_eq_sum_edgeGcd P hsc hverts]
        ring
      have hIform : S.card = 1 + (∑ i, (earOffInterior P q i S).card) +
          (∑ i, (edgeGcd q (P.vertex i) - 1)) := by
        rw [hIcard]
        congr 1
        refine Finset.sum_congr rfl fun k _ => hspoke k
      have hB2 : ∀ i, 2 ≤ (trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))).B := by
        intro i
        exact le_trans (by omega : 2 ≤ 3) (B_triangle_ge_three _ _ _
          (ne_of_gt (by
            simpa [interiorFanDet, interiorFanTriangle, Triangle.det] using hposFan i)))
      have hBB : 2 ≤ 2 * S.card + P.B := by
        have hnB := nVertices_le_B P hverts
        have hn : 3 ≤ P.nVertices := P.length_ge
        omega
      have hlen := length_of_interior_fan S.card P.B
        (fun i => (earOffInterior P q i S).card)
        (fun i => (trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))).B)
        (fun i => edgeGcd q (P.vertex i))
        hIform hgcd hBsum hB2 hBB
      have hlens : ∑ i : Fin P.nVertices, (ts i).length =
          ∑ i : Fin P.nVertices, (2 * (earOffInterior P q i S).card +
            (trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))).B - 2) := by
        refine Finset.sum_congr rfl fun i _ => (hpack i).2.1
      rw [hlens]
      exact hlen
    · rw [concatFin_sum_map]
      have hshoe : (∑ i, ((ts i).map Triangle.shoelace).sum) =
          ∑ i, (trianglePolygon q (P.vertex i) (P.vertex (P.nextIdx i))).shoelace := by
        refine Finset.sum_congr rfl fun i _ => ((hpack i).2.2).symm
      rw [hshoe, sum_ear_shoelace_eq_shoelace (P := P) hposFan]

/-- **Shoelace is half the primitive-triangle count.** The count `2I + B − 2`
is the length of the triangulation above, not the ear-induction Pick formula. -/
theorem shoelace_eq_two_cardI_add_B_sub_two_div_two (P : LatticePolygon)
    (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hverts : Function.Injective P.vertex) (hsc : StrictlyConvexCCW P) :
    P.shoelace = ((2 * S.card + P.B - 2 : ℕ) : ℚ) / 2 := by
  obtain ⟨ts, hprim, hlen, hadd⟩ := exists_primitive_polygon_list P S hS hverts hsc
  have hsum := list_shoelace_eq_length_div_two ts hprim
  calc
    P.shoelace = (ts.map Triangle.shoelace).sum := hadd
    _ = (ts.length : ℚ) / 2 := hsum
    _ = ((2 * S.card + P.B - 2 : ℕ) : ℚ) / 2 := by rw [hlen]

/-- **Pick for an empty primitive polygon, from the characteristic.**
`I = 0`, so the triangulation has length `B − 2` and shoelace `(B − 2)/2`.
`pick_count_of_disk_from_characteristic` turns that into `B/2 − 1`. -/
theorem volume_pick_of_empty_primitive_from_characteristic
    (P : LatticePolygon)
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hsc : StrictlyConvexCCW P)
    (hI : EmptyInterior P) :
    MeasureTheory.volume P.convexHullRegion =
      ENNReal.ofReal ((P.B : ℚ) / 2 - 1) := by
  have hS : ((∅ : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = P.interiorLatticePoints := by
    simpa [EmptyInterior] using hI.symm
  have _hB := B_eq_nVertices_of_primitive_edges P hedge hverts
  have harea := shoelace_eq_two_cardI_add_B_sub_two_div_two P ∅ hS hverts hsc
  have hn : 3 ≤ P.nVertices := P.length_ge
  have hnB : P.nVertices ≤ P.B := nVertices_le_B P hverts
  have hpick :=
    pick_count_of_disk_from_characteristic P.nVertices P.B 0 P.shoelace hn hnB
      (by simpa using harea)
  have hvol := volume_convexHullRegion_eq_ofReal_shoelace P hsc hverts
  have hsh : P.shoelace = (P.B : ℚ) / 2 - 1 := by simpa using hpick
  rw [hvol]
  refine congrArg ENNReal.ofReal ?_
  calc
    (P.shoelace : ℝ) = (((P.B : ℚ) / 2 - 1 : ℚ) : ℝ) := congrArg Rat.cast hsh
    _ = (P.B : ℝ) / 2 - 1 := by push_cast; ring

end LatticeFan
end Picks
end EulersGem
