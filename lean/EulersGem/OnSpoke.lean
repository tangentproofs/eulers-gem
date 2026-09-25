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
On-spoke det bookkeeping (`det = 2` on the two adjacent ears), non-adjacent
ear exclusion, and unified Off/on-spoke Pick-form remain open.
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

end InteriorFan
end LatticeFan
end Picks
end EulersGem
