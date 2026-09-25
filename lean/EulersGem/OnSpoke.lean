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

Edge helpers green: `edgeGcd`/`edgeLatticePoints` symmetry, unique midpoint when
`edgeGcd=2`, det-doubling along an occupied spoke, and `edgeGcd(q,r)=1`.
On-spoke half-ear emptiness ⇒ `|det|=1`; adjacent ears `interiorFanDet = 2`;
non-adjacent exclusion; unified `TwoInterior ⇒ shoelace = 2+B/2-1` **green**.
Still **not** classical Pick (no Haar; EP→planar open). Classical Pick FAIL.
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

/-- Covering ear for an interior lattice point `r` is `OffTriangleBoundary` or
on-spoke. Base edge is impossible for interior points. Right-spoke uses edge
orientation `(vᵢ₊₁, q)` matching `OffTriangleBoundary`. -/
theorem offBoundary_or_onSpoke_of_mem_interiorFan
    {q r : ℤ × ℤ}
    (hr_int : r ∈ P.interiorLatticePoints) (i : Fin P.nVertices)
    (_hr : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r) :
    OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r ∨
      r ∈ edgeLatticePoints q (P.vertex i) ∨
        r ∈ edgeLatticePoints (P.vertex (P.nextIdx i)) q := by
  classical
  by_cases hoff : OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r
  · exact Or.inl hoff
  · have hbase :
        r ∉ edgeLatticePoints (P.vertex i) (P.vertex (P.nextIdx i)) := by
      simpa [LatticePolygon.edgePair] using
        not_mem_polygon_edge_of_mem_interior P hr_int i
    simp only [OffTriangleBoundary, not_and_or] at hoff
    rcases hoff with h1 | h2 | h3
    · exact Or.inr (Or.inl (not_not.mp h1))
    · exact absurd (not_not.mp h2) hbase
    · exact Or.inr (Or.inr (not_not.mp h3))

/-- Specialization of `offBoundary_or_onSpoke_of_mem_interiorFan` under `TwoInterior`. -/
theorem offBoundary_or_onSpoke_of_mem_interiorFan_of_twoInterior
    {q r : ℤ × ℤ}
    (h : TwoInterior P q r) (i : Fin P.nVertices)
    (hr : MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r) :
    OffTriangleBoundary q (P.vertex i) (P.vertex (P.nextIdx i)) r ∨
      r ∈ edgeLatticePoints q (P.vertex i) ∨
        r ∈ edgeLatticePoints (P.vertex (P.nextIdx i)) q :=
  offBoundary_or_onSpoke_of_mem_interiorFan P
    (mem_interior_of_twoInterior_right P h) i hr

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



/-! ### Edge helpers: symmetry, midpoint, det doubling -/

lemma edgeGcd_comm (a b : ℤ × ℤ) : edgeGcd a b = edgeGcd b a := by
  unfold edgeGcd
  have h1 : Int.natAbs (b.1 - a.1) = Int.natAbs (a.1 - b.1) := by
    rw [← Int.natAbs_neg (a.1 - b.1)]; congr 1; ring
  have h2 : Int.natAbs (b.2 - a.2) = Int.natAbs (a.2 - b.2) := by
    rw [← Int.natAbs_neg (a.2 - b.2)]; congr 1; ring
  change Nat.gcd (Int.natAbs (b.1 - a.1)) (Int.natAbs (b.2 - a.2)) =
      Nat.gcd (Int.natAbs (a.1 - b.1)) (Int.natAbs (a.2 - b.2))
  rw [h1, h2]

lemma mem_segment_of_mem_edgeLatticePoints (a b p : ℤ × ℤ)
    (hp : p ∈ edgeLatticePoints a b) :
    toReal p ∈ segment ℝ (toReal a) (toReal b) := by
  classical
  simp only [edgeLatticePoints] at hp
  split_ifs at hp with hd
  · simp only [Finset.mem_singleton] at hp
    subst hp
    exact left_mem_segment _ _ _
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
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
    rw [segment_eq_image]
    refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
    apply Prod.ext
    · have hb1 : (b.1 : ℝ) = (a.1 : ℝ) + (d : ℝ) * (sx : ℝ) := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hsx
        push_cast at this ⊢; linarith
      have hkdiv : (k : ℝ) * (sx : ℝ) = t * ((d : ℝ) * (sx : ℝ)) := by
        dsimp [t]; field_simp
      have hx : ((a.1 + (k : ℤ) * sx : ℤ) : ℝ) = (1 - t) * a.1 + t * b.1 := by
        calc
          (↑(a.1 + (k : ℤ) * sx) : ℝ)
              = (a.1 : ℝ) + (k : ℝ) * sx := by push_cast; rfl
          _ = (a.1 : ℝ) + t * ((d : ℝ) * sx) := by rw [hkdiv]
          _ = (1 - t) * a.1 + t * b.1 := by rw [hb1]; ring
      simp only [toReal, Prod.smul_def, smul_eq_mul]
      exact hx.symm
    · have hb2 : (b.2 : ℝ) = (a.2 : ℝ) + (d : ℝ) * (sy : ℝ) := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hsy
        push_cast at this ⊢; linarith
      have hkdiv : (k : ℝ) * (sy : ℝ) = t * ((d : ℝ) * (sy : ℝ)) := by
        dsimp [t]; field_simp
      have hy : ((a.2 + (k : ℤ) * sy : ℤ) : ℝ) = (1 - t) * a.2 + t * b.2 := by
        calc
          (↑(a.2 + (k : ℤ) * sy) : ℝ)
              = (a.2 : ℝ) + (k : ℝ) * sy := by push_cast; rfl
          _ = (a.2 : ℝ) + t * ((d : ℝ) * sy) := by rw [hkdiv]
          _ = (1 - t) * a.2 + t * b.2 := by rw [hb2]; ring
      simp only [toReal, Prod.smul_def, smul_eq_mul]
      exact hy.symm

lemma mem_edgeLatticePoints_comm {a b r : ℤ × ℤ}
    (h : r ∈ edgeLatticePoints a b) : r ∈ edgeLatticePoints b a := by
  have hseg := mem_segment_of_mem_edgeLatticePoints a b r h
  have hseg' : toReal r ∈ segment ℝ (toReal b) (toReal a) := by
    simpa [segment_symm] using hseg
  exact mem_edgeLatticePoints_of_mem_segment b a r hseg'

lemma eq_step_one_of_mem_edgeLatticePoints_of_edgeGcd_eq_two
    (a b r : ℤ × ℤ) (hd : edgeGcd a b = 2)
    (hr : r ∈ edgeLatticePoints a b) (hne_a : r ≠ a) (hne_b : r ≠ b) :
    r = (a.1 + (b.1 - a.1) / 2, a.2 + (b.2 - a.2) / 2) := by
  classical
  set mid : ℤ × ℤ := (a.1 + (b.1 - a.1) / 2, a.2 + (b.2 - a.2) / 2)
  have hmid_mem : mid ∈ edgeLatticePoints a b := by
    have himg : mid ∈ (Finset.range (2 + 1)).image fun k : ℕ =>
        (a.1 + (k : ℤ) * ((b.1 - a.1) / 2),
         a.2 + (k : ℤ) * ((b.2 - a.2) / 2)) := by
      refine Finset.mem_image.mpr ⟨1, by simp, ?_⟩
      simp [mid]
    simpa [edgeLatticePoints, show edgeGcd a b = 2 from hd] using himg
  have hab : a ≠ b := fun h => by
    have : edgeGcd a b = 0 := (edgeGcd_eq_zero_iff a b).mpr h
    omega
  have hdvd1 : (edgeGcd a b : ℤ) ∣ (b.1 - a.1) := by
    simpa [edgeGcd] using Int.gcd_dvd_left (b.1 - a.1) (b.2 - a.2)
  have hdvd2 : (edgeGcd a b : ℤ) ∣ (b.2 - a.2) := by
    simpa [edgeGcd] using Int.gcd_dvd_right (b.1 - a.1) (b.2 - a.2)
  have hdx : (2 : ℤ) ∣ (b.1 - a.1) := by simpa [hd] using hdvd1
  have hdy : (2 : ℤ) ∣ (b.2 - a.2) := by simpa [hd] using hdvd2
  have hsx : (2 : ℤ) * ((b.1 - a.1) / 2) = b.1 - a.1 := by
    rw [mul_comm]; exact Int.ediv_mul_cancel hdx
  have hsy : (2 : ℤ) * ((b.2 - a.2) / 2) = b.2 - a.2 := by
    rw [mul_comm]; exact Int.ediv_mul_cancel hdy
  have hmid_ne_a : mid ≠ a := by
    intro h
    have hx := congrArg Prod.fst h; simp only [mid] at hx
    have hy := congrArg Prod.snd h; simp only [mid] at hy
    exact hab (Prod.ext (by linarith [hx, hsx]) (by linarith [hy, hsy]))
  have hmid_ne_b : mid ≠ b := by
    intro h
    have hx := congrArg Prod.fst h; simp only [mid] at hx
    have hy := congrArg Prod.snd h; simp only [mid] at hy
    exact hab (Prod.ext (by linarith [hx, hsx]) (by linarith [hy, hsy]))
  have hsub_m : ({a, b, mid} : Finset (ℤ × ℤ)) ⊆ edgeLatticePoints a b := by
    intro x hx
    have hx' : x = a ∨ x = b ∨ x = mid := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hx
    rcases hx' with hxa | hxb | hxm
    · rw [hxa]; exact self_mem_edgeLatticePoints a b
    · rw [hxb]; exact other_mem_edgeLatticePoints a b
    · rw [hxm]; exact hmid_mem
  have heq_m : ({a, b, mid} : Finset (ℤ × ℤ)) = edgeLatticePoints a b :=
    Finset.eq_of_subset_of_card_le hsub_m (by
      rw [card_edgeLatticePoints, hd]
      have : ({a, b, mid} : Finset (ℤ × ℤ)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hmid_ne_a.symm]),
            Finset.card_insert_of_notMem (by simp [hmid_ne_b.symm]),
            Finset.card_singleton]
      omega)
  have hr_in : r ∈ ({a, b, mid} : Finset (ℤ × ℤ)) := by rwa [heq_m]
  have this' : r = a ∨ r = b ∨ r = mid := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hr_in
  rcases this' with h1 | h2 | h3
  · exact (hne_a h1).elim
  · exact (hne_b h2).elim
  · exact h3

lemma two_mul_sub_of_mem_edgeLatticePoints_of_edgeGcd_eq_two
    (a b r : ℤ × ℤ) (hd : edgeGcd a b = 2)
    (hr : r ∈ edgeLatticePoints a b) (hne_a : r ≠ a) (hne_b : r ≠ b) :
    (2 : ℤ) * (r.1 - a.1) = b.1 - a.1 ∧
      (2 : ℤ) * (r.2 - a.2) = b.2 - a.2 := by
  have hr' := eq_step_one_of_mem_edgeLatticePoints_of_edgeGcd_eq_two a b r hd hr hne_a hne_b
  have hdvd1 : (edgeGcd a b : ℤ) ∣ (b.1 - a.1) := by
    simpa [edgeGcd] using Int.gcd_dvd_left (b.1 - a.1) (b.2 - a.2)
  have hdvd2 : (edgeGcd a b : ℤ) ∣ (b.2 - a.2) := by
    simpa [edgeGcd] using Int.gcd_dvd_right (b.1 - a.1) (b.2 - a.2)
  have hdx : (2 : ℤ) ∣ (b.1 - a.1) := by simpa [hd] using hdvd1
  have hdy : (2 : ℤ) ∣ (b.2 - a.2) := by simpa [hd] using hdvd2
  have hsx : (2 : ℤ) * ((b.1 - a.1) / 2) = b.1 - a.1 := by
    rw [mul_comm]; exact Int.ediv_mul_cancel hdx
  have hsy : (2 : ℤ) * ((b.2 - a.2) / 2) = b.2 - a.2 := by
    rw [mul_comm]; exact Int.ediv_mul_cancel hdy
  constructor
  · have hx := congrArg Prod.fst hr'; simp only at hx; linarith [hx, hsx]
  · have hy := congrArg Prod.snd hr'; simp only at hy; linarith [hy, hsy]

lemma latticeDet_eq_two_mul_of_edgeGcd_eq_two_mem
    (a b c r : ℤ × ℤ) (hd : edgeGcd a b = 2)
    (hr : r ∈ edgeLatticePoints a b) (hne_a : r ≠ a) (hne_b : r ≠ b) :
    latticeDet a b c = 2 * latticeDet a r c := by
  obtain ⟨hx, hy⟩ :=
    two_mul_sub_of_mem_edgeLatticePoints_of_edgeGcd_eq_two a b r hd hr hne_a hne_b
  simp only [latticeDet]
  have hx' : b.1 - a.1 = 2 * (r.1 - a.1) := by linarith
  have hy' : b.2 - a.2 = 2 * (r.2 - a.2) := by linarith
  rw [hx', hy']; ring

lemma edgeGcd_eq_one_left_of_edgeGcd_eq_two_mem
    (a b r : ℤ × ℤ) (hd : edgeGcd a b = 2)
    (hr : r ∈ edgeLatticePoints a b) (hne_a : r ≠ a) (hne_b : r ≠ b) :
    edgeGcd a r = 1 := by
  obtain ⟨hx, hy⟩ :=
    two_mul_sub_of_mem_edgeLatticePoints_of_edgeGcd_eq_two a b r hd hr hne_a hne_b
  have hgcd_ab : Int.gcd (b.1 - a.1) (b.2 - a.2) = 2 := by
    simpa [edgeGcd] using hd
  have hx' : b.1 - a.1 = 2 * (r.1 - a.1) := by linarith
  have hy' : b.2 - a.2 = 2 * (r.2 - a.2) := by linarith
  have hmul := Int.gcd_mul_left (2 : ℤ) (r.1 - a.1) (r.2 - a.2)
  have : 2 = 2 * Int.gcd (r.1 - a.1) (r.2 - a.2) := by
    calc
      2 = Int.gcd (b.1 - a.1) (b.2 - a.2) := hgcd_ab.symm
      _ = Int.gcd (2 * (r.1 - a.1)) (2 * (r.2 - a.2)) := by rw [hx', hy']
      _ = Int.natAbs (2 : ℤ) * Int.gcd (r.1 - a.1) (r.2 - a.2) := hmul
      _ = 2 * Int.gcd (r.1 - a.1) (r.2 - a.2) := by simp
  have : Int.gcd (r.1 - a.1) (r.2 - a.2) = 1 := by omega
  simpa [edgeGcd] using this

lemma mem_interiorFan_of_onSpoke_left {q r : ℤ × ℤ} (k : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k)) :
    MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) r :=
  memClosedTriangle_of_mem_edgeLatticePoints_ab q (P.vertex k)
    (P.vertex (P.nextIdx k)) r hs

lemma mem_interiorFan_of_onSpoke_right {q r : ℤ × ℤ} (k : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k)) :
    MemClosedTriangle q (P.vertex (P.prevIdx k)) (P.vertex k) r := by
  have hs' : r ∈ edgeLatticePoints (P.vertex k) q := mem_edgeLatticePoints_comm hs
  simpa [P.nextIdx_prevIdx] using
    memClosedTriangle_of_mem_edgeLatticePoints_ca q (P.vertex (P.prevIdx k))
      (P.vertex k) r hs'


/-! ### Small-triangle emptiness + adjacent det=2 (not classical Pick)

When `r` is the unique midpoint of spoke `q—vₖ`, the half-ears `△(q,r,vₖ₊₁)` and
`△(q,vₖ₋₁,r)` are empty of extra lattice points, so `|det|=1`. Doubling along the
spoke then gives adjacent fan ears `interiorFanDet = 2`. Non-adjacent ears exclude
`r`, hence `det = 1`. Fan sum `n+2` ⇒ `shoelace = 2 + B/2 − 1`.
-/

/-- Determinant doubles when the third vertex is scaled along the `a—c` spoke. -/
lemma latticeDet_eq_two_mul_ac_of_edgeGcd_eq_two_mem
    (a b c r : ℤ × ℤ) (hd : edgeGcd a c = 2)
    (hr : r ∈ edgeLatticePoints a c) (hne_a : r ≠ a) (hne_c : r ≠ c) :
    latticeDet a b c = 2 * latticeDet a b r := by
  obtain ⟨hx, hy⟩ :=
    two_mul_sub_of_mem_edgeLatticePoints_of_edgeGcd_eq_two a c r hd hr hne_a hne_c
  simp only [latticeDet]
  have hx' : c.1 - a.1 = 2 * (r.1 - a.1) := by linarith
  have hy' : c.2 - a.2 = 2 * (r.2 - a.2) := by linarith
  rw [hx', hy']; ring

/-- Midpoint of `a—b` (edgeGcd=2): closed △`(a,r,c)` sits inside △`(a,b,c)`. -/
lemma memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem
    (a b c r p : ℤ × ℤ) (hd : edgeGcd a b = 2)
    (hr : r ∈ edgeLatticePoints a b) (hne_a : r ≠ a) (hne_b : r ≠ b)
    (hp : MemClosedTriangle a r c p) :
    MemClosedTriangle a b c p := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, heq⟩ := hp
  obtain ⟨hx, hy⟩ :=
    two_mul_sub_of_mem_edgeLatticePoints_of_edgeGcd_eq_two a b r hd hr hne_a hne_b
  have hr1 : (r.1 : ℝ) = (a.1 : ℝ) + (1 / 2) * ((b.1 : ℝ) - a.1) := by
    have : (2 : ℤ) * (r.1 - a.1) = b.1 - a.1 := hx
    have := congrArg (fun z : ℤ => (z : ℝ)) this
    push_cast at this ⊢; linarith
  have hr2 : (r.2 : ℝ) = (a.2 : ℝ) + (1 / 2) * ((b.2 : ℝ) - a.2) := by
    have : (2 : ℤ) * (r.2 - a.2) = b.2 - a.2 := hy
    have := congrArg (fun z : ℤ => (z : ℝ)) this
    push_cast at this ⊢; linarith
  refine ⟨α + β / 2, β / 2, γ, by linarith, by linarith, hγ, by linarith, ?_⟩
  apply Prod.ext
  · have h1 := congrArg Prod.fst heq
    simp only [Prod.smul_def, smul_eq_mul] at h1 ⊢
    calc
      (α + β / 2) * (a.1 : ℝ) + (β / 2) * b.1 + γ * c.1
          = α * a.1 + β * ((a.1 : ℝ) + (1 / 2) * (b.1 - a.1)) + γ * c.1 := by ring
      _ = α * a.1 + β * r.1 + γ * c.1 := by rw [← hr1]
      _ = p.1 := h1
  · have h2 := congrArg Prod.snd heq
    simp only [Prod.smul_def, smul_eq_mul] at h2 ⊢
    calc
      (α + β / 2) * (a.2 : ℝ) + (β / 2) * b.2 + γ * c.2
          = α * a.2 + β * ((a.2 : ℝ) + (1 / 2) * (b.2 - a.2)) + γ * c.2 := by ring
      _ = α * a.2 + β * r.2 + γ * c.2 := by rw [← hr2]
      _ = p.2 := h2

/-- Same inclusion with midpoint on the `a—c` spoke (right-adjacent half-ear). -/
lemma memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem_ac
    (a b c r p : ℤ × ℤ) (hd : edgeGcd a c = 2)
    (hr : r ∈ edgeLatticePoints a c) (hne_a : r ≠ a) (hne_c : r ≠ c)
    (hp : MemClosedTriangle a b r p) :
    MemClosedTriangle a b c p := by
  -- Rewrite via swap: MemClosed a b r ↔ MemClosed a r b after permute, then use ab form.
  -- Direct barycentric with midpoint on a—c.
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, heq⟩ := hp
  obtain ⟨hx, hy⟩ :=
    two_mul_sub_of_mem_edgeLatticePoints_of_edgeGcd_eq_two a c r hd hr hne_a hne_c
  have hr1 : (r.1 : ℝ) = (a.1 : ℝ) + (1 / 2) * ((c.1 : ℝ) - a.1) := by
    have : (2 : ℤ) * (r.1 - a.1) = c.1 - a.1 := hx
    have := congrArg (fun z : ℤ => (z : ℝ)) this
    push_cast at this ⊢; linarith
  have hr2 : (r.2 : ℝ) = (a.2 : ℝ) + (1 / 2) * ((c.2 : ℝ) - a.2) := by
    have : (2 : ℤ) * (r.2 - a.2) = c.2 - a.2 := hy
    have := congrArg (fun z : ℤ => (z : ℝ)) this
    push_cast at this ⊢; linarith
  refine ⟨α + γ / 2, β, γ / 2, by linarith, hβ, by linarith, by linarith, ?_⟩
  apply Prod.ext
  · have h1 := congrArg Prod.fst heq
    simp only [Prod.smul_def, smul_eq_mul] at h1 ⊢
    calc
      (α + γ / 2) * (a.1 : ℝ) + β * b.1 + (γ / 2) * c.1
          = α * a.1 + β * b.1 + γ * ((a.1 : ℝ) + (1 / 2) * (c.1 - a.1)) := by ring
      _ = α * a.1 + β * b.1 + γ * r.1 := by rw [← hr1]
      _ = p.1 := h1
  · have h2 := congrArg Prod.snd heq
    simp only [Prod.smul_def, smul_eq_mul] at h2 ⊢
    calc
      (α + γ / 2) * (a.2 : ℝ) + β * b.2 + (γ / 2) * c.2
          = α * a.2 + β * b.2 + γ * ((a.2 : ℝ) + (1 / 2) * (c.2 - a.2)) := by ring
      _ = α * a.2 + β * b.2 + γ * r.2 := by rw [← hr2]
      _ = p.2 := h2

/-- Spoke endpoints agree when they share the same strict intermediate lattice point
with `edgeGcd = 2`. -/
lemma eq_vertex_of_mem_edgeLatticePoints_of_edgeGcd_eq_two
    (a b c r : ℤ × ℤ) (hdb : edgeGcd a b = 2) (hdc : edgeGcd a c = 2)
    (hrb : r ∈ edgeLatticePoints a b) (hrc : r ∈ edgeLatticePoints a c)
    (hne_a : r ≠ a) (hne_b : r ≠ b) (hne_c : r ≠ c) :
    b = c := by
  obtain ⟨hx1, hy1⟩ :=
    two_mul_sub_of_mem_edgeLatticePoints_of_edgeGcd_eq_two a b r hdb hrb hne_a hne_b
  obtain ⟨hx2, hy2⟩ :=
    two_mul_sub_of_mem_edgeLatticePoints_of_edgeGcd_eq_two a c r hdc hrc hne_a hne_c
  apply Prod.ext <;> linarith

/-- Left half-ear △`(q,r,w)` under on-spoke is empty of extra lattice points. -/
theorem eq_vertices_of_memClosedTriangle_onSpoke_left
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) (k : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    {p : ℤ × ℤ}
    (hp : MemClosedTriangle q r (P.vertex (P.nextIdx k)) p) :
    p = q ∨ p = r ∨ p = P.vertex (P.nextIdx k) := by
  classical
  set v := P.vertex k
  set w := P.vertex (P.nextIdx k)
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_twoInterior_onSpoke P hsc hinj hedge h k hs hne_q hne_v
  have hpos := InteriorFanDetsPos_of_twoInterior_left P hsc hinj hedge h
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
  rcases eq_vertices_or_r_of_mem_interiorFan_of_twoInterior P hsc hinj hedge h k
      (by simpa [interiorFanTriangle, v, w] using hp_big) with h1 | h2 | h3 | h4
  · exact Or.inl h1
  · -- p = v: weight-zero on edge q—r of the small triangle
    subst h2
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
      have hq_int := mem_interior_of_twoInterior_left P h
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

/-- Right half-ear △`(q,v_prev,r)` under on-spoke is empty of extra lattice points. -/
theorem eq_vertices_of_memClosedTriangle_onSpoke_right
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) (k : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    {p : ℤ × ℤ}
    (hp : MemClosedTriangle q (P.vertex (P.prevIdx k)) r p) :
    p = q ∨ p = P.vertex (P.prevIdx k) ∨ p = r := by
  classical
  set v := P.vertex k
  set u := P.vertex (P.prevIdx k)
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_twoInterior_onSpoke P hsc hinj hedge h k hs hne_q hne_v
  have hpos := InteriorFanDetsPos_of_twoInterior_left P hsc hinj hedge h
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
  rcases eq_vertices_or_r_of_mem_interiorFan_of_twoInterior P hsc hinj hedge h
      (P.prevIdx k) (by simpa [interiorFanTriangle, u, v, P.nextIdx_prevIdx]
        using hp_big) with h1 | h2 | h3 | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · -- p = v: β-weight vanishes ⇒ on edge q—r
    have hpv : p = v := by simpa [v, P.nextIdx_prevIdx] using h3
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
      have hq_int := mem_interior_of_twoInterior_left P h
      have hv_bd : v ∈ P.boundaryLatticePoints := by
        have : v ∈ P.vertexFinset := by
          rw [vertexFinset_eq_univ_image]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
      exact hq_int.2 (hvq ▸ hv_bd)
    · intro hvr
      exact (hne_v hvr.symm).elim
  · exact Or.inr (Or.inr h4)

/-- Left half-ear is det-primitive: `|det(q,r,w)| = 1`. -/
theorem natAbs_latticeDet_eq_one_of_onSpoke_left
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) (k : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k) :
    Int.natAbs (latticeDet q r (P.vertex (P.nextIdx k))) = 1 := by
  classical
  set v := P.vertex k
  set w := P.vertex (P.nextIdx k)
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_twoInterior_onSpoke P hsc hinj hedge h k hs hne_q hne_v
  have hpos := InteriorFanDetsPos_of_twoInterior_left P hsc hinj hedge h
  have hDbig : 0 < latticeDet q v w := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, v, w] using hpos k
  have hdouble : latticeDet q v w = 2 * latticeDet q r w :=
    latticeDet_eq_two_mul_of_edgeGcd_eq_two_mem q v w r hd hs hne_q hne_v
  have hDne : latticeDet q r w ≠ 0 := by
    have : 0 < 2 * latticeDet q r w := by rwa [← hdouble]
    omega
  refine natAbs_det_eq_one_of_memClosedTriangle_eq_vertices q r w hDne ?_
  intro p hp
  exact eq_vertices_of_memClosedTriangle_onSpoke_left P hsc hinj hedge h k hs
    hne_q hne_v hp

/-- Right half-ear is det-primitive: `|det(q,u,r)| = 1`. -/
theorem natAbs_latticeDet_eq_one_of_onSpoke_right
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) (k : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k) :
    Int.natAbs (latticeDet q (P.vertex (P.prevIdx k)) r) = 1 := by
  classical
  set v := P.vertex k
  set u := P.vertex (P.prevIdx k)
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_twoInterior_onSpoke P hsc hinj hedge h k hs hne_q hne_v
  have hpos := InteriorFanDetsPos_of_twoInterior_left P hsc hinj hedge h
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
  exact eq_vertices_of_memClosedTriangle_onSpoke_right P hsc hinj hedge h k hs
    hne_q hne_v hp

/-- Left-adjacent on-spoke ear has `interiorFanDet = 2`. -/
theorem interiorFanDet_eq_two_of_onSpoke_left
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) (k : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k) :
    interiorFanDet P q k = 2 := by
  classical
  set v := P.vertex k
  set w := P.vertex (P.nextIdx k)
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_twoInterior_onSpoke P hsc hinj hedge h k hs hne_q hne_v
  have hpos := InteriorFanDetsPos_of_twoInterior_left P hsc hinj hedge h
  have hDbig : 0 < latticeDet q v w := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, v, w] using hpos k
  have hdouble : latticeDet q v w = 2 * latticeDet q r w :=
    latticeDet_eq_two_mul_of_edgeGcd_eq_two_mem q v w r hd hs hne_q hne_v
  have hnat :=
    natAbs_latticeDet_eq_one_of_onSpoke_left P hsc hinj hedge h k hs hne_q hne_v
  have hnn : 0 ≤ latticeDet q r w := by
    have : 0 < 2 * latticeDet q r w := by rwa [← hdouble]
    omega
  have hz : latticeDet q r w = (Int.natAbs (latticeDet q r w) : ℤ) :=
    (Int.natAbs_of_nonneg hnn).symm
  have h1 : latticeDet q r w = 1 := by rw [hz, hnat]; norm_num
  have : latticeDet q v w = 2 := by rw [hdouble, h1]; norm_num
  simpa [interiorFanDet, interiorFanTriangle, Triangle.det, v, w] using this

/-- Right-adjacent on-spoke ear has `interiorFanDet = 2`. -/
theorem interiorFanDet_eq_two_of_onSpoke_right
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) (k : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k) :
    interiorFanDet P q (P.prevIdx k) = 2 := by
  classical
  set v := P.vertex k
  set u := P.vertex (P.prevIdx k)
  have hd : edgeGcd q v = 2 :=
    edgeGcd_eq_two_of_twoInterior_onSpoke P hsc hinj hedge h k hs hne_q hne_v
  have hpos := InteriorFanDetsPos_of_twoInterior_left P hsc hinj hedge h
  have hDbig : 0 < latticeDet q u v := by
    simpa [interiorFanDet, interiorFanTriangle, Triangle.det, u, v,
      P.nextIdx_prevIdx] using hpos (P.prevIdx k)
  have hdouble : latticeDet q u v = 2 * latticeDet q u r :=
    latticeDet_eq_two_mul_ac_of_edgeGcd_eq_two_mem q u v r hd hs hne_q hne_v
  have hnat :=
    natAbs_latticeDet_eq_one_of_onSpoke_right P hsc hinj hedge h k hs hne_q hne_v
  have hnn : 0 ≤ latticeDet q u r := by
    have : 0 < 2 * latticeDet q u r := by rwa [← hdouble]
    omega
  have hz : latticeDet q u r = (Int.natAbs (latticeDet q u r) : ℤ) :=
    (Int.natAbs_of_nonneg hnn).symm
  have h1 : latticeDet q u r = 1 := by rw [hz, hnat]; norm_num
  have : latticeDet q u v = 2 := by rw [hdouble, h1]; norm_num
  simpa [interiorFanDet, interiorFanTriangle, Triangle.det, u, v,
    P.nextIdx_prevIdx] using this

/-- Foreign ear containing on-spoke `r` is `OffTriangleBoundary` (spokes force
adjacency). -/
lemma OffTriangleBoundary_of_mem_interiorFan_of_onSpoke_ne_adjacent
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) (k j : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (_hrj : MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) r)
    (hne_k : j ≠ k) (hne_prev : j ≠ P.prevIdx k) :
    OffTriangleBoundary q (P.vertex j) (P.vertex (P.nextIdx j)) r := by
  classical
  set vj := P.vertex j
  set wj := P.vertex (P.nextIdx j)
  set vk := P.vertex k
  refine ⟨?_, ?_, ?_⟩
  · -- not on spoke edge q—vj
    intro hspoke
    have hne_vj : r ≠ vj := by
      intro heq
      have hv_bd : vj ∈ P.boundaryLatticePoints := by
        have : vj ∈ P.vertexFinset := by
          rw [vertexFinset_eq_univ_image]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
      exact (mem_interior_of_twoInterior_right P h).2 (heq ▸ hv_bd)
    have hdj : edgeGcd q vj = 2 :=
      edgeGcd_eq_two_of_twoInterior_onSpoke P hsc hinj hedge h j hspoke hne_q hne_vj
    have hdk : edgeGcd q vk = 2 :=
      edgeGcd_eq_two_of_twoInterior_onSpoke P hsc hinj hedge h k hs hne_q hne_v
    have heq :=
      eq_vertex_of_mem_edgeLatticePoints_of_edgeGcd_eq_two q vj vk r hdj hdk
        hspoke hs hne_q hne_vj hne_v
    exact hne_k (hinj heq)
  · -- not on polygon base
    exact not_mem_polygon_edge_of_mem_interior P
      (mem_interior_of_twoInterior_right P h) j
  · -- not on spoke edge wj—q
    intro hspoke
    have hs' : r ∈ edgeLatticePoints q wj := mem_edgeLatticePoints_comm hspoke
    have hne_wj : r ≠ wj := by
      intro heq
      have hv_bd : wj ∈ P.boundaryLatticePoints := by
        have : wj ∈ P.vertexFinset := by
          rw [vertexFinset_eq_univ_image]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
      exact (mem_interior_of_twoInterior_right P h).2 (heq ▸ hv_bd)
    have hdj : edgeGcd q wj = 2 :=
      edgeGcd_eq_two_of_twoInterior_onSpoke P hsc hinj hedge h (P.nextIdx j) hs'
        hne_q hne_wj
    have hdk : edgeGcd q vk = 2 :=
      edgeGcd_eq_two_of_twoInterior_onSpoke P hsc hinj hedge h k hs hne_q hne_v
    have heq :=
      eq_vertex_of_mem_edgeLatticePoints_of_edgeGcd_eq_two q wj vk r hdj hdk
        hs' hs hne_q hne_wj hne_v
    -- wj = vk ⇒ nextIdx j = k ⇒ j = prevIdx k
    have : P.nextIdx j = k := hinj heq
    have : j = P.prevIdx k := by
      rw [← this, prevIdx_nextIdx]
    exact hne_prev this

/-- On-spoke `r` occupies exactly the two adjacent fan ears. -/
theorem eq_of_mem_interiorFan_of_twoInterior_onSpoke
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) (k j : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hrj : MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) r) :
    j = k ∨ j = P.prevIdx k := by
  classical
  by_cases hjk : j = k
  · exact Or.inl hjk
  · by_cases hjp : j = P.prevIdx k
    · exact Or.inr hjp
    · have hoff :=
        OffTriangleBoundary_of_mem_interiorFan_of_onSpoke_ne_adjacent
          P hsc hinj hedge h k j hs hne_q hne_v hrj hjk hjp
      have hrk : MemClosedTriangle q (P.vertex k) (P.vertex (P.nextIdx k)) r :=
        mem_interiorFan_of_onSpoke_left P k hs
      have : k = j :=
        eq_of_mem_interiorFan_of_twoInterior_offBoundary
          P hsc hinj hedge h j k hrj hoff hrk
      exact (hjk this.symm).elim

/-- Non-adjacent on-spoke ears have `interiorFanDet = 1`. -/
theorem interiorFanDet_eq_one_of_onSpoke_not_adjacent
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) (k j : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k)
    (hne_k : j ≠ k) (hne_prev : j ≠ P.prevIdx k) :
    interiorFanDet P q j = 1 := by
  have hrj :
      ¬ MemClosedTriangle (interiorFanTriangle P q j).a
        (interiorFanTriangle P q j).b (interiorFanTriangle P q j).c r := by
    intro hj
    have hj' : MemClosedTriangle q (P.vertex j) (P.vertex (P.nextIdx j)) r := by
      simpa [interiorFanTriangle] using hj
    rcases eq_of_mem_interiorFan_of_twoInterior_onSpoke P hsc hinj hedge h k j
        hs hne_q hne_v hj' with h1 | h2
    · exact hne_k h1
    · exact hne_prev h2
  exact interiorFanDet_eq_one_of_twoInterior_of_not_mem_r P hsc hinj hedge h j hrj

/-- **I = 2 shoelace Pick-form** under on-spoke occupation (not classical Pick).

Adjacent ears contribute `det = 2`; all others `det = 1`; fan sum `n + 2`;
`B = n` ⇒ `shoelace = 2 + B/2 − 1`. -/
theorem shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior_onSpoke
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) (k : Fin P.nVertices)
    (hs : r ∈ edgeLatticePoints q (P.vertex k))
    (hne_q : r ≠ q) (hne_v : r ≠ P.vertex k) :
    P.shoelace = (2 : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  have hpos := InteriorFanDetsPos_of_twoInterior_left P hsc hinj hedge h
  have hdetL : interiorFanDet P q k = 2 :=
    interiorFanDet_eq_two_of_onSpoke_left P hsc hinj hedge h k hs hne_q hne_v
  have hdetR : interiorFanDet P q (P.prevIdx k) = 2 :=
    interiorFanDet_eq_two_of_onSpoke_right P hsc hinj hedge h k hs hne_q hne_v
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
      interiorFanDet_eq_one_of_onSpoke_not_adjacent P hsc hinj hedge h k j
        hs hne_q hne_v h1 h2
  have hsum :
      (∑ j : Fin P.nVertices, interiorFanDet P q j) = (P.nVertices : ℤ) + 2 := by
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
      have hj' : j ∈ (Finset.univ.erase k).erase (P.prevIdx k) := hj
      have ⟨hne_p, hj2⟩ := Finset.mem_erase.mp hj'
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
      _ = 2 + (interiorFanDet P q (P.prevIdx k) + ∑ j ∈ S, interiorFanDet P q j) := by
            rw [hdetL, hdecomp2]
      _ = 2 + (2 + ∑ j ∈ S, (1 : ℤ)) := by rw [hdetR, hrest]
      _ = 4 + (S.card : ℤ) := by simp; ring
      _ = 4 + ((P.nVertices - 2 : ℕ) : ℤ) := by rw [hcard]
      _ = (P.nVertices : ℤ) + 2 := by
            have : 2 ≤ P.nVertices := by
              have : 3 ≤ P.nVertices := P.length_ge; omega
            have hcast : ((P.nVertices - 2 : ℕ) : ℤ) = (P.nVertices : ℤ) - 2 :=
              Nat.cast_sub this
            rw [hcast]; ring
  have hshoelaceSum : P.shoelaceSum = (P.nVertices : ℤ) + 2 := by
    rw [← sum_interiorFanDet_eq_shoelaceSum P q, hsum]
  have hB : P.B = P.nVertices := B_eq_nVertices_of_primitive_edges P hedge hinj
  have hnn : 0 ≤ P.shoelaceSum := by
    have : 0 ≤ (P.nVertices : ℤ) + 2 := by
      have : 3 ≤ P.nVertices := P.length_ge; omega
    simpa [hshoelaceSum] using this
  have hnat : Int.natAbs P.shoelaceSum = P.nVertices + 2 := by
    apply Int.natCast_inj.mp
    rw [Int.natAbs_of_nonneg hnn, hshoelaceSum]
    push_cast; ring
  calc
    P.shoelace = (Int.natAbs P.shoelaceSum : ℚ) / 2 := rfl
    _ = ((P.nVertices + 2 : ℕ) : ℚ) / 2 := by
          have : (Int.natAbs P.shoelaceSum : ℚ) = ((P.nVertices + 2 : ℕ) : ℚ) := by
            exact_mod_cast hnat
          rw [this]
    _ = (P.nVertices : ℚ) / 2 + 1 := by push_cast; ring
    _ = (2 : ℚ) + (P.B : ℚ) / 2 - 1 := by rw [hB]; ring

/-- Strict on-spoke endpoints: interior point ≠ apex / vertex. -/
lemma ne_endpoints_of_twoInterior_onSpoke
    {q r : ℤ × ℤ} (h : TwoInterior P q r) (k : Fin P.nVertices)
    (_hs : r ∈ edgeLatticePoints q (P.vertex k)) :
    r ≠ q ∧ r ≠ P.vertex k := by
  refine ⟨?_, ?_⟩
  · exact h.1.symm
  · intro heq
    have hv_bd : P.vertex k ∈ P.boundaryLatticePoints := by
      have : P.vertex k ∈ P.vertexFinset := by
        rw [vertexFinset_eq_univ_image]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      exact P.vertices_mem_boundary (List.mem_toFinset.mp this)
    exact (mem_interior_of_twoInterior_right P h).2 (heq ▸ hv_bd)

/-- **Unified I = 2 shoelace Pick-form** (Off or on-spoke; not classical Pick).

Covering ear is OffTriangleBoundary or on-spoke; both paths give
`shoelace = 2 + B/2 − 1`. Still **not** classical Pick (no Haar; EP→planar open). -/
theorem shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior
    (hsc : StrictlyConvexCCW P) (hinj : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P) {q r : ℤ × ℤ}
    (h : TwoInterior P q r) :
    P.shoelace = (2 : ℚ) + (P.B : ℚ) / 2 - 1 := by
  classical
  obtain ⟨i, hi⟩ :=
    exists_mem_interiorFanTriangle_of_twoInterior P hsc hinj hedge h
  rcases offBoundary_or_onSpoke_of_mem_interiorFan_of_twoInterior P h i hi with
    hoff | hsL | hsR
  · exact shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior_occupied_offBoundary
      P hsc hinj hedge h i hi hoff
  · obtain ⟨hne_q, hne_v⟩ := ne_endpoints_of_twoInterior_onSpoke P h i hsL
    exact shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior_onSpoke
      P hsc hinj hedge h i hsL hne_q hne_v
  · -- right-spoke orientation (vᵢ₊₁, q): rewrite as on-spoke to nextIdx i
    have hs : r ∈ edgeLatticePoints q (P.vertex (P.nextIdx i)) :=
      mem_edgeLatticePoints_comm hsR
    obtain ⟨hne_q, hne_v⟩ :=
      ne_endpoints_of_twoInterior_onSpoke P h (P.nextIdx i) hs
    exact shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior_onSpoke
      P hsc hinj hedge h (P.nextIdx i) hs hne_q hne_v

end InteriorFan
end LatticeFan
end Picks
end EulersGem
