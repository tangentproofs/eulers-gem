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

/-! ### Det additivity / diagonal doubling helpers (Off-adjacent substrate) -/

/-- Collinear `r` on line `a—b` ⇒ oriented area splits across `r`. -/
lemma latticeDet_add_of_collinear_ab
    (a b c r : ℤ × ℤ) (h : latticeDet a b r = 0) :
    latticeDet a b c = latticeDet a r c + latticeDet r b c := by
  have H : latticeDet a b c - (latticeDet a r c + latticeDet r b c) =
      latticeDet a b r := by
    unfold latticeDet; ring
  linarith

/-- Lattice point on edge `a—b` ⇒ oriented area splits across it. -/
lemma latticeDet_add_of_mem_edgeLatticePoints
    (a b c r : ℤ × ℤ) (hr : r ∈ edgeLatticePoints a b) :
    latticeDet a b c = latticeDet a r c + latticeDet r b c :=
  latticeDet_add_of_collinear_ab a b c r (latticeDet_eq_zero_of_mem_edge_ab a b r hr)

/-- Right half of an `edgeGcd = 2` edge is primitive. -/
lemma edgeGcd_eq_one_right_of_edgeGcd_eq_two_mem
    (a b r : ℤ × ℤ) (hd : edgeGcd a b = 2)
    (hr : r ∈ edgeLatticePoints a b) (hne_a : r ≠ a) (hne_b : r ≠ b) :
    edgeGcd r b = 1 := by
  obtain ⟨hx, hy⟩ :=
    two_mul_sub_of_mem_edgeLatticePoints_of_edgeGcd_eq_two a b r hd hr hne_a hne_b
  have hx' : b.1 - a.1 = 2 * (r.1 - a.1) := by linarith
  have hy' : b.2 - a.2 = 2 * (r.2 - a.2) := by linarith
  have hx2 : b.1 - r.1 = r.1 - a.1 := by linarith
  have hy2 : b.2 - r.2 = r.2 - a.2 := by linarith
  have hleft : edgeGcd a r = 1 :=
    edgeGcd_eq_one_left_of_edgeGcd_eq_two_mem a b r hd hr hne_a hne_b
  simpa [edgeGcd, hx2, hy2] using hleft

/-- Determinant doubles when the third vertex is the far endpoint of a midpoint
on the `b—c` edge (`s` midpoint of `b—c`). -/
lemma latticeDet_eq_two_mul_of_edgeGcd_eq_two_mem_bc
    (a b c s : ℤ × ℤ) (hd : edgeGcd b c = 2)
    (hs : s ∈ edgeLatticePoints b c) (hne_b : s ≠ b) (hne_c : s ≠ c) :
    latticeDet a b c = 2 * latticeDet a b s := by
  obtain ⟨hx, hy⟩ :=
    two_mul_sub_of_mem_edgeLatticePoints_of_edgeGcd_eq_two b c s hd hs hne_b hne_c
  simp only [latticeDet]
  have hx' : c.1 - b.1 = 2 * (s.1 - b.1) := by linarith
  have hy' : c.2 - b.2 = 2 * (s.2 - b.2) := by linarith
  have hx2 : c.1 - a.1 = 2 * (s.1 - a.1) - (b.1 - a.1) := by linarith
  have hy2 : c.2 - a.2 = 2 * (s.2 - a.2) - (b.2 - a.2) := by linarith
  rw [hx2, hy2]; ring

/-- Midpoint of `a—b`: closed △`(r,b,c)` sits inside △`(a,b,c)`. -/
lemma memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem_right
    (a b c r p : ℤ × ℤ) (hd : edgeGcd a b = 2)
    (hr : r ∈ edgeLatticePoints a b) (hne_a : r ≠ a) (hne_b : r ≠ b)
    (hp : MemClosedTriangle r b c p) :
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
  refine ⟨α / 2, α / 2 + β, γ, by linarith, by linarith, hγ, by linarith, ?_⟩
  apply Prod.ext
  · have h1 := congrArg Prod.fst heq
    simp only [Prod.smul_def, smul_eq_mul] at h1 ⊢
    calc
      (α / 2) * (a.1 : ℝ) + (α / 2 + β) * b.1 + γ * c.1
          = α * ((a.1 : ℝ) + (1 / 2) * (b.1 - a.1)) + β * b.1 + γ * c.1 := by ring
      _ = α * r.1 + β * b.1 + γ * c.1 := by rw [← hr1]
      _ = p.1 := h1
  · have h2 := congrArg Prod.snd heq
    simp only [Prod.smul_def, smul_eq_mul] at h2 ⊢
    calc
      (α / 2) * (a.2 : ℝ) + (α / 2 + β) * b.2 + γ * c.2
          = α * ((a.2 : ℝ) + (1 / 2) * (b.2 - a.2)) + β * b.2 + γ * c.2 := by ring
      _ = α * r.2 + β * b.2 + γ * c.2 := by rw [← hr2]
      _ = p.2 := h2

/-- Midpoint split: closed △`(a,b,c)` is the union of △`(a,r,c)` and △`(r,b,c)`. -/
lemma memClosedTriangle_split_of_edgeGcd_eq_two_mem
    (a b c r p : ℤ × ℤ) (hd : edgeGcd a b = 2)
    (hr : r ∈ edgeLatticePoints a b) (hne_a : r ≠ a) (hne_b : r ≠ b)
    (hp : MemClosedTriangle a b c p) :
    MemClosedTriangle a r c p ∨ MemClosedTriangle r b c p := by
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
  by_cases hle : β ≤ α
  · refine Or.inl ⟨α - β, 2 * β, γ, by linarith, by linarith, hγ, by linarith, ?_⟩
    apply Prod.ext
    · have h1 := congrArg Prod.fst heq
      simp only [Prod.smul_def, smul_eq_mul] at h1 ⊢
      calc
        (α - β) * (a.1 : ℝ) + (2 * β) * r.1 + γ * c.1
            = α * a.1 + β * (2 * r.1 - a.1) + γ * c.1 := by ring
        _ = α * a.1 + β * b.1 + γ * c.1 := by
              have : (2 : ℝ) * r.1 - a.1 = b.1 := by linarith [hr1]
              rw [this]
        _ = p.1 := h1
    · have h2 := congrArg Prod.snd heq
      simp only [Prod.smul_def, smul_eq_mul] at h2 ⊢
      calc
        (α - β) * (a.2 : ℝ) + (2 * β) * r.2 + γ * c.2
            = α * a.2 + β * (2 * r.2 - a.2) + γ * c.2 := by ring
        _ = α * a.2 + β * b.2 + γ * c.2 := by
              have : (2 : ℝ) * r.2 - a.2 = b.2 := by linarith [hr2]
              rw [this]
        _ = p.2 := h2
  · push Not at hle
    refine Or.inr ⟨2 * α, β - α, γ, by linarith, by linarith, hγ, by linarith, ?_⟩
    apply Prod.ext
    · have h1 := congrArg Prod.fst heq
      simp only [Prod.smul_def, smul_eq_mul] at h1 ⊢
      calc
        (2 * α) * (r.1 : ℝ) + (β - α) * b.1 + γ * c.1
            = α * (2 * r.1 - b.1) + β * b.1 + γ * c.1 := by ring
        _ = α * a.1 + β * b.1 + γ * c.1 := by
              have : (2 : ℝ) * r.1 - b.1 = a.1 := by linarith [hr1]
              rw [this]
        _ = p.1 := h1
    · have h2 := congrArg Prod.snd heq
      simp only [Prod.smul_def, smul_eq_mul] at h2 ⊢
      calc
        (2 * α) * (r.2 : ℝ) + (β - α) * b.2 + γ * c.2
            = α * (2 * r.2 - b.2) + β * b.2 + γ * c.2 := by ring
        _ = α * a.2 + β * b.2 + γ * c.2 := by
              have : (2 : ℝ) * r.2 - b.2 = a.2 := by linarith [hr2]
              rw [this]
        _ = p.2 := h2

/-- Midpoint of `b—c`: closed △`(a,b,s)` sits inside △`(a,b,c)`. -/
lemma memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem_bc
    (a b c s p : ℤ × ℤ) (hd : edgeGcd b c = 2)
    (hs : s ∈ edgeLatticePoints b c) (hne_b : s ≠ b) (hne_c : s ≠ c)
    (hp : MemClosedTriangle a b s p) :
    MemClosedTriangle a b c p := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, heq⟩ := hp
  obtain ⟨hx, hy⟩ :=
    two_mul_sub_of_mem_edgeLatticePoints_of_edgeGcd_eq_two b c s hd hs hne_b hne_c
  have hs1 : (s.1 : ℝ) = (b.1 : ℝ) + (1 / 2) * ((c.1 : ℝ) - b.1) := by
    have : (2 : ℤ) * (s.1 - b.1) = c.1 - b.1 := hx
    have := congrArg (fun z : ℤ => (z : ℝ)) this
    push_cast at this ⊢; linarith
  have hs2 : (s.2 : ℝ) = (b.2 : ℝ) + (1 / 2) * ((c.2 : ℝ) - b.2) := by
    have : (2 : ℤ) * (s.2 - b.2) = c.2 - b.2 := hy
    have := congrArg (fun z : ℤ => (z : ℝ)) this
    push_cast at this ⊢; linarith
  refine ⟨α, β + γ / 2, γ / 2, hα, by linarith, by linarith, by linarith, ?_⟩
  apply Prod.ext
  · have h1 := congrArg Prod.fst heq
    simp only [Prod.smul_def, smul_eq_mul] at h1 ⊢
    calc
      α * (a.1 : ℝ) + (β + γ / 2) * b.1 + (γ / 2) * c.1
          = α * a.1 + β * b.1 + γ * ((b.1 : ℝ) + (1 / 2) * (c.1 - b.1)) := by ring
      _ = α * a.1 + β * b.1 + γ * s.1 := by rw [← hs1]
      _ = p.1 := h1
  · have h2 := congrArg Prod.snd heq
    simp only [Prod.smul_def, smul_eq_mul] at h2 ⊢
    calc
      α * (a.2 : ℝ) + (β + γ / 2) * b.2 + (γ / 2) * c.2
          = α * a.2 + β * b.2 + γ * ((b.2 : ℝ) + (1 / 2) * (c.2 - b.2)) := by ring
      _ = α * a.2 + β * b.2 + γ * s.2 := by rw [← hs2]
      _ = p.2 := h2

/-- A point in both midpoint half-triangles lies on the shared diagonal. -/
lemma mem_edgeLatticePoints_of_memClosedTriangle_both_halves
    (a b c r p : ℤ × ℤ) (_hd : edgeGcd a b = 2)
    (_hr : r ∈ edgeLatticePoints a b) (_hne_a : r ≠ a) (_hne_b : r ≠ b)
    (hDL : 0 < latticeDet a r c) (hDR : 0 < latticeDet r b c)
    (hpL : MemClosedTriangle a r c p) (hpR : MemClosedTriangle r b c p) :
    p ∈ edgeLatticePoints r c := by
  have ⟨hle, _, _⟩ := latticeDet_nonneg_of_memClosedTriangle a r c p hpL hDL
  have ⟨_, hmid, _⟩ := latticeDet_nonneg_of_memClosedTriangle r b c p hpR hDR
  -- hle: 0 ≤ latticeDet r c p; hmid: 0 ≤ latticeDet r p c = -latticeDet r c p
  have hswap : latticeDet r p c = -latticeDet r c p := by
    unfold latticeDet; ring
  have hge : latticeDet r c p ≤ 0 := by linarith [hmid, hswap]
  have hz : latticeDet r c p = 0 := le_antisymm hge hle
  exact mem_edgeLatticePoints_of_weight_zero_bc a r c p hpL hDL hz

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

/-! ### Edge helpers for edgeGcd = 3 (same-spoke I = 3 substrate) -/

/-- The two strict lattice points on an `edgeGcd = 3` segment are the step-1 and
step-2 points (order unspecified). -/
lemma eq_steps_of_mem_edgeLatticePoints_of_edgeGcd_eq_three
    (a b r s : ℤ × ℤ) (hd : edgeGcd a b = 3)
    (hr : r ∈ edgeLatticePoints a b) (hs : s ∈ edgeLatticePoints a b)
    (hne_ra : r ≠ a) (hne_rb : r ≠ b) (hne_sa : s ≠ a) (hne_sb : s ≠ b)
    (hne_rs : r ≠ s) :
    let p1 : ℤ × ℤ := (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3)
    let p2 : ℤ × ℤ := (a.1 + 2 * ((b.1 - a.1) / 3), a.2 + 2 * ((b.2 - a.2) / 3))
    (r = p1 ∧ s = p2) ∨ (r = p2 ∧ s = p1) := by
  classical
  set p1 : ℤ × ℤ := (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3)
  set p2 : ℤ × ℤ := (a.1 + 2 * ((b.1 - a.1) / 3), a.2 + 2 * ((b.2 - a.2) / 3))
  have hab : a ≠ b := fun h => by
    have : edgeGcd a b = 0 := (edgeGcd_eq_zero_iff a b).mpr h
    omega
  have hdvd1 : (edgeGcd a b : ℤ) ∣ (b.1 - a.1) := by
    simpa [edgeGcd] using Int.gcd_dvd_left (b.1 - a.1) (b.2 - a.2)
  have hdvd2 : (edgeGcd a b : ℤ) ∣ (b.2 - a.2) := by
    simpa [edgeGcd] using Int.gcd_dvd_right (b.1 - a.1) (b.2 - a.2)
  have hdx : (3 : ℤ) ∣ (b.1 - a.1) := by simpa [hd] using hdvd1
  have hdy : (3 : ℤ) ∣ (b.2 - a.2) := by simpa [hd] using hdvd2
  have hsx : (3 : ℤ) * ((b.1 - a.1) / 3) = b.1 - a.1 := by
    rw [mul_comm]; exact Int.ediv_mul_cancel hdx
  have hsy : (3 : ℤ) * ((b.2 - a.2) / 3) = b.2 - a.2 := by
    rw [mul_comm]; exact Int.ediv_mul_cancel hdy
  have hp1_mem : p1 ∈ edgeLatticePoints a b := by
    have himg : p1 ∈ (Finset.range (3 + 1)).image fun k : ℕ =>
        (a.1 + (k : ℤ) * ((b.1 - a.1) / 3),
         a.2 + (k : ℤ) * ((b.2 - a.2) / 3)) := by
      refine Finset.mem_image.mpr ⟨1, by simp, ?_⟩
      simp [p1]
    simpa [edgeLatticePoints, show edgeGcd a b = 3 from hd] using himg
  have hp2_mem : p2 ∈ edgeLatticePoints a b := by
    have himg : p2 ∈ (Finset.range (3 + 1)).image fun k : ℕ =>
        (a.1 + (k : ℤ) * ((b.1 - a.1) / 3),
         a.2 + (k : ℤ) * ((b.2 - a.2) / 3)) := by
      refine Finset.mem_image.mpr ⟨2, by simp, rfl⟩
    simpa [edgeLatticePoints, show edgeGcd a b = 3 from hd, p2] using himg
  have hp1_ne_a : p1 ≠ a := by
    intro h
    have hx := congrArg Prod.fst h; simp only [p1] at hx
    have hy := congrArg Prod.snd h; simp only [p1] at hy
    exact hab (Prod.ext (by linarith [hx, hsx]) (by linarith [hy, hsy]))
  have hp1_ne_b : p1 ≠ b := by
    intro h
    have hx := congrArg Prod.fst h; simp only [p1] at hx
    have hy := congrArg Prod.snd h; simp only [p1] at hy
    exact hab (Prod.ext (by linarith [hx, hsx]) (by linarith [hy, hsy]))
  have hp2_ne_a : p2 ≠ a := by
    intro h
    have hx := congrArg Prod.fst h; simp only [p2] at hx
    have hy := congrArg Prod.snd h; simp only [p2] at hy
    exact hab (Prod.ext (by linarith [hx, hsx]) (by linarith [hy, hsy]))
  have hp2_ne_b : p2 ≠ b := by
    intro h
    have hx := congrArg Prod.fst h; simp only [p2] at hx
    have hy := congrArg Prod.snd h; simp only [p2] at hy
    exact hab (Prod.ext (by linarith [hx, hsx]) (by linarith [hy, hsy]))
  have hp1_ne_p2 : p1 ≠ p2 := by
    intro h
    have hx := congrArg Prod.fst h; simp only [p1, p2] at hx
    have hy := congrArg Prod.snd h; simp only [p1, p2] at hy
    exact hab (Prod.ext (by linarith [hx, hsx]) (by linarith [hy, hsy]))
  have hsub : ({a, b, p1, p2} : Finset (ℤ × ℤ)) ⊆ edgeLatticePoints a b := by
    intro x hx
    have hx' : x = a ∨ x = b ∨ x = p1 ∨ x = p2 := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hx
    rcases hx' with hxa | hxb | hx1 | hx2
    · rw [hxa]; exact self_mem_edgeLatticePoints a b
    · rw [hxb]; exact other_mem_edgeLatticePoints a b
    · rw [hx1]; exact hp1_mem
    · rw [hx2]; exact hp2_mem
  have heq : ({a, b, p1, p2} : Finset (ℤ × ℤ)) = edgeLatticePoints a b :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [card_edgeLatticePoints, hd]
      have hcard4 : ({a, b, p1, p2} : Finset (ℤ × ℤ)).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hp1_ne_a.symm, hp2_ne_a.symm]),
            Finset.card_insert_of_notMem (by simp [hp1_ne_b.symm, hp2_ne_b.symm]),
            Finset.card_insert_of_notMem (by simp [hp1_ne_p2]),
            Finset.card_singleton]
      omega)
  have hr_in : r ∈ ({a, b, p1, p2} : Finset (ℤ × ℤ)) := by rwa [heq]
  have hs_in : s ∈ ({a, b, p1, p2} : Finset (ℤ × ℤ)) := by rwa [heq]
  have hr' : r = a ∨ r = b ∨ r = p1 ∨ r = p2 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hr_in
  have hs' : s = a ∨ s = b ∨ s = p1 ∨ s = p2 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hs_in
  rcases hr' with hr1 | hr2 | hr3 | hr4
  · exact (hne_ra hr1).elim
  · exact (hne_rb hr2).elim
  · rcases hs' with hs1 | hs2 | hs3 | hs4
    · exact (hne_sa hs1).elim
    · exact (hne_sb hs2).elim
    · exact (hne_rs (hr3.trans hs3.symm)).elim
    · exact Or.inl ⟨hr3, hs4⟩
  · rcases hs' with hs1 | hs2 | hs3 | hs4
    · exact (hne_sa hs1).elim
    · exact (hne_sb hs2).elim
    · exact Or.inr ⟨hr4, hs3⟩
    · exact (hne_rs (hr4.trans hs4.symm)).elim

/-- Step-1 point on an `edgeGcd = 3` segment: `3 · (p1 - a) = b - a`. -/
lemma three_mul_sub_step_one_of_edgeGcd_eq_three
    (a b : ℤ × ℤ) (hd : edgeGcd a b = 3) :
    let p1 : ℤ × ℤ := (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3)
    (3 : ℤ) * (p1.1 - a.1) = b.1 - a.1 ∧
      (3 : ℤ) * (p1.2 - a.2) = b.2 - a.2 := by
  classical
  set p1 : ℤ × ℤ := (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3)
  have hdvd1 : (edgeGcd a b : ℤ) ∣ (b.1 - a.1) := by
    simpa [edgeGcd] using Int.gcd_dvd_left (b.1 - a.1) (b.2 - a.2)
  have hdvd2 : (edgeGcd a b : ℤ) ∣ (b.2 - a.2) := by
    simpa [edgeGcd] using Int.gcd_dvd_right (b.1 - a.1) (b.2 - a.2)
  have hdx : (3 : ℤ) ∣ (b.1 - a.1) := by simpa [hd] using hdvd1
  have hdy : (3 : ℤ) ∣ (b.2 - a.2) := by simpa [hd] using hdvd2
  have hsx : (3 : ℤ) * ((b.1 - a.1) / 3) = b.1 - a.1 := by
    rw [mul_comm]; exact Int.ediv_mul_cancel hdx
  have hsy : (3 : ℤ) * ((b.2 - a.2) / 3) = b.2 - a.2 := by
    rw [mul_comm]; exact Int.ediv_mul_cancel hdy
  constructor
  · simp [p1]; linarith [hsx]
  · simp [p1]; linarith [hsy]

/-- Determinant triples along an `edgeGcd = 3` spoke at a point `r` with
`3 · (r - a) = b - a`. -/
lemma latticeDet_eq_three_mul_of_three_mul_sub
    (a b c r : ℤ × ℤ)
    (hx : (3 : ℤ) * (r.1 - a.1) = b.1 - a.1)
    (hy : (3 : ℤ) * (r.2 - a.2) = b.2 - a.2) :
    latticeDet a b c = 3 * latticeDet a r c := by
  simp only [latticeDet]
  have hx' : b.1 - a.1 = 3 * (r.1 - a.1) := by linarith
  have hy' : b.2 - a.2 = 3 * (r.2 - a.2) := by linarith
  rw [hx', hy']; ring

lemma latticeDet_eq_three_mul_of_edgeGcd_eq_three_step_one
    (a b c : ℤ × ℤ) (hd : edgeGcd a b = 3) :
    latticeDet a b c =
      3 * latticeDet a (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3) c := by
  obtain ⟨hx, hy⟩ := three_mul_sub_step_one_of_edgeGcd_eq_three a b hd
  exact latticeDet_eq_three_mul_of_three_mul_sub a b c _ hx hy

lemma latticeDet_eq_three_mul_ac_of_three_mul_sub
    (a b c r : ℤ × ℤ)
    (hx : (3 : ℤ) * (r.1 - a.1) = c.1 - a.1)
    (hy : (3 : ℤ) * (r.2 - a.2) = c.2 - a.2) :
    latticeDet a b c = 3 * latticeDet a b r := by
  have h := latticeDet_eq_three_mul_of_three_mul_sub a c b r hx hy
  have hsw1 : latticeDet a c b = -latticeDet a b c := by unfold latticeDet; ring
  have hsw2 : latticeDet a r b = -latticeDet a b r := by unfold latticeDet; ring
  linarith

lemma latticeDet_eq_three_mul_ac_of_edgeGcd_eq_three_step_one
    (a b c : ℤ × ℤ) (hd : edgeGcd a c = 3) :
    latticeDet a b c =
      3 * latticeDet a b (a.1 + (c.1 - a.1) / 3, a.2 + (c.2 - a.2) / 3) := by
  obtain ⟨hx, hy⟩ := three_mul_sub_step_one_of_edgeGcd_eq_three a c hd
  exact latticeDet_eq_three_mul_ac_of_three_mul_sub a b c _ hx hy

/-- Step-1 point is in `edgeLatticePoints`. -/
lemma step_one_mem_edgeLatticePoints_of_edgeGcd_eq_three
    (a b : ℤ × ℤ) (hd : edgeGcd a b = 3) :
    (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3) ∈ edgeLatticePoints a b := by
  have himg :
      (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3) ∈
        (Finset.range (3 + 1)).image fun k : ℕ =>
          (a.1 + (k : ℤ) * ((b.1 - a.1) / 3),
           a.2 + (k : ℤ) * ((b.2 - a.2) / 3)) := by
    refine Finset.mem_image.mpr ⟨1, by simp, ?_⟩
    simp
  simpa [edgeLatticePoints, show edgeGcd a b = 3 from hd] using himg

/-- Closed △`(a, p1, c)` sits inside △`(a, b, c)` when `p1` is step-1 on `a—b`. -/
lemma memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_three_step_one
    (a b c p : ℤ × ℤ) (hd : edgeGcd a b = 3)
    (hp : MemClosedTriangle a
      (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3) c p) :
    MemClosedTriangle a b c p := by
  set p1 : ℤ × ℤ := (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3)
  change MemClosedTriangle a p1 c p at hp
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, heq⟩ := hp
  obtain ⟨hx, hy⟩ := three_mul_sub_step_one_of_edgeGcd_eq_three a b hd
  have hr1 : (p1.1 : ℝ) = (a.1 : ℝ) + (1 / 3) * ((b.1 : ℝ) - a.1) := by
    have : (3 : ℤ) * (p1.1 - a.1) = b.1 - a.1 := by simpa [p1] using hx
    have := congrArg (fun z : ℤ => (z : ℝ)) this
    push_cast at this ⊢; linarith
  have hr2 : (p1.2 : ℝ) = (a.2 : ℝ) + (1 / 3) * ((b.2 : ℝ) - a.2) := by
    have : (3 : ℤ) * (p1.2 - a.2) = b.2 - a.2 := by simpa [p1] using hy
    have := congrArg (fun z : ℤ => (z : ℝ)) this
    push_cast at this ⊢; linarith
  refine ⟨α + (2 : ℝ) / 3 * β, (1 : ℝ) / 3 * β, γ, by linarith, by linarith, hγ, by linarith, ?_⟩
  apply Prod.ext
  · have h1 := congrArg Prod.fst heq
    simp only [Prod.smul_def, smul_eq_mul] at h1 ⊢
    calc
      (α + (2 : ℝ) / 3 * β) * (a.1 : ℝ) + ((1 : ℝ) / 3 * β) * b.1 + γ * c.1
          = α * a.1 + β * ((a.1 : ℝ) + (1 / 3) * (b.1 - a.1)) + γ * c.1 := by ring
      _ = α * a.1 + β * p1.1 + γ * c.1 := by rw [← hr1]
      _ = p.1 := h1
  · have h2 := congrArg Prod.snd heq
    simp only [Prod.smul_def, smul_eq_mul] at h2 ⊢
    calc
      (α + (2 : ℝ) / 3 * β) * (a.2 : ℝ) + ((1 : ℝ) / 3 * β) * b.2 + γ * c.2
          = α * a.2 + β * ((a.2 : ℝ) + (1 / 3) * (b.2 - a.2)) + γ * c.2 := by ring
      _ = α * a.2 + β * p1.2 + γ * c.2 := by rw [← hr2]
      _ = p.2 := h2

/-- Closed △`(a, b, p1)` sits inside △`(a, b, c)` when `p1` is step-1 on `a—c`. -/
lemma memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_three_step_one_ac
    (a b c p : ℤ × ℤ) (hd : edgeGcd a c = 3)
    (hp : MemClosedTriangle a b
      (a.1 + (c.1 - a.1) / 3, a.2 + (c.2 - a.2) / 3) p) :
    MemClosedTriangle a b c p := by
  set p1 : ℤ × ℤ := (a.1 + (c.1 - a.1) / 3, a.2 + (c.2 - a.2) / 3)
  change MemClosedTriangle a b p1 p at hp
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, heq⟩ := hp
  obtain ⟨hx, hy⟩ := three_mul_sub_step_one_of_edgeGcd_eq_three a c hd
  have hr1 : (p1.1 : ℝ) = (a.1 : ℝ) + (1 / 3) * ((c.1 : ℝ) - a.1) := by
    have : (3 : ℤ) * (p1.1 - a.1) = c.1 - a.1 := by simpa [p1] using hx
    have := congrArg (fun z : ℤ => (z : ℝ)) this
    push_cast at this ⊢; linarith
  have hr2 : (p1.2 : ℝ) = (a.2 : ℝ) + (1 / 3) * ((c.2 : ℝ) - a.2) := by
    have : (3 : ℤ) * (p1.2 - a.2) = c.2 - a.2 := by simpa [p1] using hy
    have := congrArg (fun z : ℤ => (z : ℝ)) this
    push_cast at this ⊢; linarith
  refine ⟨α + (2 : ℝ) / 3 * γ, β, (1 : ℝ) / 3 * γ, by linarith, hβ, by linarith, by linarith, ?_⟩
  apply Prod.ext
  · have h1 := congrArg Prod.fst heq
    simp only [Prod.smul_def, smul_eq_mul] at h1 ⊢
    calc
      (α + (2 : ℝ) / 3 * γ) * (a.1 : ℝ) + β * b.1 + ((1 : ℝ) / 3 * γ) * c.1
          = α * a.1 + β * b.1 + γ * ((a.1 : ℝ) + (1 / 3) * (c.1 - a.1)) := by ring
      _ = α * a.1 + β * b.1 + γ * p1.1 := by rw [← hr1]
      _ = p.1 := h1
  · have h2 := congrArg Prod.snd heq
    simp only [Prod.smul_def, smul_eq_mul] at h2 ⊢
    calc
      (α + (2 : ℝ) / 3 * γ) * (a.2 : ℝ) + β * b.2 + ((1 : ℝ) / 3 * γ) * c.2
          = α * a.2 + β * b.2 + γ * ((a.2 : ℝ) + (1 / 3) * (c.2 - a.2)) := by ring
      _ = α * a.2 + β * b.2 + γ * p1.2 := by rw [← hr2]
      _ = p.2 := h2

/-- Step-1 point of an `edgeGcd = 3` segment has `edgeGcd = 1` with the start. -/
lemma edgeGcd_eq_one_of_edgeGcd_eq_three_step_one
    (a b : ℤ × ℤ) (hd : edgeGcd a b = 3) :
    edgeGcd a (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3) = 1 := by
  set p1 : ℤ × ℤ := (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3)
  obtain ⟨hx, hy⟩ := three_mul_sub_step_one_of_edgeGcd_eq_three a b hd
  have hgcd_ab : Int.gcd (b.1 - a.1) (b.2 - a.2) = 3 := by simpa [edgeGcd] using hd
  have hx' : b.1 - a.1 = 3 * (p1.1 - a.1) := by simpa [p1] using hx.symm
  have hy' : b.2 - a.2 = 3 * (p1.2 - a.2) := by simpa [p1] using hy.symm
  have hmul := Int.gcd_mul_left (3 : ℤ) (p1.1 - a.1) (p1.2 - a.2)
  have : 3 = 3 * Int.gcd (p1.1 - a.1) (p1.2 - a.2) := by
    calc
      3 = Int.gcd (b.1 - a.1) (b.2 - a.2) := hgcd_ab.symm
      _ = Int.gcd (3 * (p1.1 - a.1)) (3 * (p1.2 - a.2)) := by rw [hx', hy']
      _ = Int.natAbs (3 : ℤ) * Int.gcd (p1.1 - a.1) (p1.2 - a.2) := hmul
      _ = 3 * Int.gcd (p1.1 - a.1) (p1.2 - a.2) := by simp
  have : Int.gcd (p1.1 - a.1) (p1.2 - a.2) = 1 := by omega
  simpa [edgeGcd, p1] using this

/-- Collinearity: `latticeDet a p1 b = 0` for step-1 `p1` on `a—b`. -/
lemma latticeDet_eq_zero_of_edgeGcd_eq_three_step_one
    (a b : ℤ × ℤ) (hd : edgeGcd a b = 3) :
    latticeDet a (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3) b = 0 := by
  set p1 : ℤ × ℤ := (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3)
  obtain ⟨hx, hy⟩ := three_mul_sub_step_one_of_edgeGcd_eq_three a b hd
  have hx' : b.1 - a.1 = 3 * (p1.1 - a.1) := by simpa [p1] using hx.symm
  have hy' : b.2 - a.2 = 3 * (p1.2 - a.2) := by simpa [p1] using hy.symm
  simp only [latticeDet]
  change (p1.1 - a.1) * (b.2 - a.2) - (p1.2 - a.2) * (b.1 - a.1) = 0
  rw [hx', hy']; ring

/-- Step-2 vs step-1: `latticeDet a p1 p2 = 0`. -/
lemma latticeDet_eq_zero_step_one_step_two_of_edgeGcd_eq_three
    (a b : ℤ × ℤ) (_hd : edgeGcd a b = 3) :
    let p1 : ℤ × ℤ := (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3)
    let p2 : ℤ × ℤ := (a.1 + 2 * ((b.1 - a.1) / 3), a.2 + 2 * ((b.2 - a.2) / 3))
    latticeDet a p1 p2 = 0 := by
  set p1 : ℤ × ℤ := (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3)
  set p2 : ℤ × ℤ := (a.1 + 2 * ((b.1 - a.1) / 3), a.2 + 2 * ((b.2 - a.2) / 3))
  have hx2 : p2.1 - a.1 = 2 * (p1.1 - a.1) := by simp [p2, p1]
  have hy2 : p2.2 - a.2 = 2 * (p1.2 - a.2) := by simp [p2, p1]
  simp only [latticeDet]
  change (p1.1 - a.1) * (p2.2 - a.2) - (p1.2 - a.2) * (p2.1 - a.1) = 0
  rw [hx2, hy2]; ring


/-- Spoke endpoints agree when they share the same two strict intermediate lattice
points with `edgeGcd = 3`. -/
lemma eq_vertex_of_mem_edgeLatticePoints_of_edgeGcd_eq_three
    (a b c r s : ℤ × ℤ) (hdb : edgeGcd a b = 3) (hdc : edgeGcd a c = 3)
    (hrb : r ∈ edgeLatticePoints a b) (hsb : s ∈ edgeLatticePoints a b)
    (hrc : r ∈ edgeLatticePoints a c) (hsc : s ∈ edgeLatticePoints a c)
    (hne_ra : r ≠ a) (hne_rb : r ≠ b) (hne_sa : s ≠ a) (hne_sb : s ≠ b)
    (hne_rc : r ≠ c) (hne_sc : s ≠ c) (hne_rs : r ≠ s) :
    b = c := by
  classical
  set p1b : ℤ × ℤ := (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3)
  set p2b : ℤ × ℤ := (a.1 + 2 * ((b.1 - a.1) / 3), a.2 + 2 * ((b.2 - a.2) / 3))
  set p1c : ℤ × ℤ := (a.1 + (c.1 - a.1) / 3, a.2 + (c.2 - a.2) / 3)
  set p2c : ℤ × ℤ := (a.1 + 2 * ((c.1 - a.1) / 3), a.2 + 2 * ((c.2 - a.2) / 3))
  have hb : (r = p1b ∧ s = p2b) ∨ (r = p2b ∧ s = p1b) := by
    simpa [p1b, p2b] using
      eq_steps_of_mem_edgeLatticePoints_of_edgeGcd_eq_three a b r s hdb hrb hsb
        hne_ra hne_rb hne_sa hne_sb hne_rs
  have hc : (r = p1c ∧ s = p2c) ∨ (r = p2c ∧ s = p1c) := by
    simpa [p1c, p2c] using
      eq_steps_of_mem_edgeLatticePoints_of_edgeGcd_eq_three a c r s hdc hrc hsc
        hne_ra hne_rc hne_sa hne_sc hne_rs
  obtain ⟨hxb, hyb⟩ := three_mul_sub_step_one_of_edgeGcd_eq_three a b hdb
  obtain ⟨hxc, hyc⟩ := three_mul_sub_step_one_of_edgeGcd_eq_three a c hdc
  have hxb' : b.1 - a.1 = 3 * (p1b.1 - a.1) := by simpa [p1b] using hxb.symm
  have hyb' : b.2 - a.2 = 3 * (p1b.2 - a.2) := by simpa [p1b] using hyb.symm
  have hxc' : c.1 - a.1 = 3 * (p1c.1 - a.1) := by simpa [p1c] using hxc.symm
  have hyc' : c.2 - a.2 = 3 * (p1c.2 - a.2) := by simpa [p1c] using hyc.symm
  have hp2b_x : p2b.1 - a.1 = 2 * (p1b.1 - a.1) := by simp [p1b, p2b]
  have hp2b_y : p2b.2 - a.2 = 2 * (p1b.2 - a.2) := by simp [p1b, p2b]
  have hp2c_x : p2c.1 - a.1 = 2 * (p1c.1 - a.1) := by simp [p1c, p2c]
  have hp2c_y : p2c.2 - a.2 = 2 * (p1c.2 - a.2) := by simp [p1c, p2c]
  rcases hb with ⟨hr1b, hs2b⟩ | ⟨hr2b, hs1b⟩
  · rcases hc with ⟨hr1c, hs2c⟩ | ⟨hr2c, hs1c⟩
    · -- matching: r = p1b = p1c
      have hp : p1b = p1c := hr1b.symm.trans hr1c
      apply Prod.ext
      · have := congrArg Prod.fst hp; linarith
      · have := congrArg Prod.snd hp; linarith
    · -- crossed: r = p1b = p2c, s = p2b = p1c
      have hrp : p1b = p2c := hr1b.symm.trans hr2c
      have hsp : p2b = p1c := hs2b.symm.trans hs1c
      -- p2c - a = 2*(p1c - a) = 2*(p2b - a) = 4*(p1b - a), but p2c = p1b
      have hx : p1b.1 - a.1 = 4 * (p1b.1 - a.1) := by
        have h1 := congrArg Prod.fst hrp
        have h2 := congrArg Prod.fst hsp
        linarith [hp2c_x, hp2b_x, h1, h2]
      have hy : p1b.2 - a.2 = 4 * (p1b.2 - a.2) := by
        have h1 := congrArg Prod.snd hrp
        have h2 := congrArg Prod.snd hsp
        linarith [hp2c_y, hp2b_y, h1, h2]
      have hx0 : p1b.1 - a.1 = 0 := by omega
      have hy0 : p1b.2 - a.2 = 0 := by omega
      have : r = a := by
        apply Prod.ext
        · simp [hr1b]; linarith [hx0]
        · simp [hr1b]; linarith [hy0]
      exact (hne_ra this).elim
  · rcases hc with ⟨hr1c, hs2c⟩ | ⟨hr2c, hs1c⟩
    · -- crossed: r = p2b = p1c, s = p1b = p2c
      have hrp : p2b = p1c := hr2b.symm.trans hr1c
      have hsp : p1b = p2c := hs1b.symm.trans hs2c
      have hx : p1b.1 - a.1 = 4 * (p1b.1 - a.1) := by
        have h1 := congrArg Prod.fst hsp
        have h2 := congrArg Prod.fst hrp
        linarith [hp2c_x, hp2b_x, h1, h2]
      have hy : p1b.2 - a.2 = 4 * (p1b.2 - a.2) := by
        have h1 := congrArg Prod.snd hsp
        have h2 := congrArg Prod.snd hrp
        linarith [hp2c_y, hp2b_y, h1, h2]
      have hx0 : p1b.1 - a.1 = 0 := by omega
      have hy0 : p1b.2 - a.2 = 0 := by omega
      have : s = a := by
        apply Prod.ext
        · simp [hs1b]; linarith [hx0]
        · simp [hs1b]; linarith [hy0]
      exact (hne_sa this).elim
    · -- matching: s = p1b = p1c
      have hp : p1b = p1c := hs1b.symm.trans hs1c
      apply Prod.ext
      · have := congrArg Prod.fst hp; linarith
      · have := congrArg Prod.snd hp; linarith

end InteriorFan
end LatticeFan
end Picks
end EulersGem
