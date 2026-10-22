/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.R3Geometry
import EulersGem.ExposedFaces
import EulersGem.PlatonicOfEuler

/-!
# Face lattices of explicit polytopes in `ℝ³`, checked by the kernel

`Data` lists points in `ℤ[φ]³` together with a claimed list of edges and facets (as index
lists) and, for every pair of points that is *not* an edge, a certificate that the segment
between them meets the hull of the other points. `Data.checkAll` is a `Bool` the kernel
evaluates (`decide +kernel`); from `checkAll = true` we prove that the faces of
`convexHull ℝ (points)` are *exactly* the empty set, the body, the points, the listed edges
and the listed facets.

How the classification works (`face_cases`): a nonempty face is the hull of the vertices
maximising some functional `⟪a, ·⟫` (`face_eq_convexHull_argmax`, which rests on the
V-to-H theorem). If at least three vertices `pᵢ, pⱼ, pₖ` attain the maximum then `a` is
parallel to `n = (pⱼ - pᵢ) × (pₖ - pᵢ)` (`R3.inner_mul_crs`), so either `a ⟂ n`-everything
(the face is the body), or the vertices split by the sign of `⟪n, · - pᵢ⟫`; the checker has
verified for **every** triple that either both signs occur (impossible for a maximiser) or
the zero set is a listed facet. Two maximisers: either a listed edge, or the certificate
`d (pᵢ + pⱼ) = Σ νᵤ pᵤ` (νᵤ ≥ 0, Σ νᵤ = 2d, u ∉ {i, j}) contradicts strict maximality.
-/

open Set
open scoped RealInnerProductSpace

namespace EulersGem

namespace Explicit

open ZPhi

/-- Explicit polytope data. -/
structure Data where
  pts : List V
  facets : List (List ℕ)
  edges : List (List ℕ)
  certs : List ((ℕ × ℕ) × (Int × List (ℕ × ZPhi)))

/-- Sum of the weights of a certificate. -/
def sumZ : List (ℕ × ZPhi) → ZPhi
  | [] => 0
  | uc :: l => uc.2 + sumZ l

namespace Data

variable (D : Data)

/-! ## The computation -/

/-- Number of points. -/
def n : ℕ := D.pts.length
/-- The `i`-th point. -/
def pt (i : ℕ) : V := D.pts.getD i 0
/-- Normal of the plane through points `i, j, k`. -/
def nrm (i j k : ℕ) : V := V.cross (D.pt j - D.pt i) (D.pt k - D.pt i)
/-- Side of point `u` relative to the plane through `i` with normal `w`. -/
def side (w : V) (i u : ℕ) : Int := sgn (V.dot w (D.pt u - D.pt i))
/-- Points on the plane. -/
def zeroSet (w : V) (i : ℕ) : List ℕ := (List.range D.n).filter fun u => D.side w i u == 0
/-- Some point strictly on the positive side. -/
def hasPos (w : V) (i : ℕ) : Bool := (List.range D.n).any fun u => D.side w i u == 1
/-- Some point strictly on the negative side. -/
def hasNeg (w : V) (i : ℕ) : Bool := (List.range D.n).any fun u => D.side w i u == -1
/-- No sign computation hit the impossible case. -/
def noTwo (w : V) (i : ℕ) : Bool := (List.range D.n).all fun u => D.side w i u != 2

/-- The triple `i < j < k` spans a plane that either separates points or is a listed facet. -/
def tripleOk (i j k : ℕ) : Bool :=
  sgn (V.dot (D.nrm i j k) (D.nrm i j k)) == 1 && D.noTwo (D.nrm i j k) i &&
    ((D.hasPos (D.nrm i j k) i && D.hasNeg (D.nrm i j k) i) ||
      D.facets.contains (D.zeroSet (D.nrm i j k) i))

/-- Every triple is fine. -/
def checkTriples : Bool :=
  (List.range D.n).all fun i => (List.range D.n).all fun j => (List.range D.n).all fun k =>
    !(decide (i < j) && decide (j < k)) || D.tripleOk i j k

/-- Point `i` is the unique maximiser of `⟪pᵢ, ·⟫`. -/
def vertexOk (i : ℕ) : Bool :=
  (List.range D.n).all fun u =>
    u == i || sgn (V.dot (D.pt i) (D.pt i) - V.dot (D.pt i) (D.pt u)) == 1

/-- Every point is a vertex. -/
def checkVertices : Bool := (List.range D.n).all D.vertexOk

/-- A listed edge `[i, j]` is exposed by `⟪pᵢ + pⱼ, ·⟫`. -/
def edgeOk : List ℕ → Bool
  | [i, j] => decide (i < j) && decide (j < D.n) &&
      (V.dot (D.pt i + D.pt j) (D.pt i) == V.dot (D.pt i + D.pt j) (D.pt j) &&
        (List.range D.n).all fun u => u == i || u == j ||
          sgn (V.dot (D.pt i + D.pt j) (D.pt i) - V.dot (D.pt i + D.pt j) (D.pt u)) == 1)
  | _ => false

/-- A listed facet is the zero set of the plane through its first three points, and all
points lie on one side of that plane. -/
def facetOk : List ℕ → Bool
  | i :: j :: k :: rest =>
      sgn (V.dot (D.nrm i j k) (D.nrm i j k)) == 1 && D.noTwo (D.nrm i j k) i &&
        !(D.hasPos (D.nrm i j k) i && D.hasNeg (D.nrm i j k) i) &&
        D.zeroSet (D.nrm i j k) i == i :: j :: k :: rest
  | _ => false

/-- Weighted sum of points. -/
def sumV : List (ℕ × ZPhi) → V
  | [] => 0
  | uc :: l => V.smul uc.2 (D.pt uc.1) + sumV l

/-- A certificate that `[i, j]` is not an edge. -/
def certOk (i j : ℕ) : Bool :=
  match D.certs.lookup (i, j) with
  | some (d, ν) => decide (0 < d) &&
      ν.all (fun uc => decide (uc.1 < D.n) && uc.1 != i && uc.1 != j && sgn uc.2 != -1 &&
        sgn uc.2 != 2) &&
      sumZ ν == ofInt (2 * d) && V.smul (ofInt d) (D.pt i + D.pt j) == D.sumV ν
  | none => false

/-- Every pair is a listed edge or certified not to be one. -/
def checkPairs : Bool :=
  (List.range D.n).all fun i => (List.range D.n).all fun j =>
    !decide (i < j) || D.edges.contains [i, j] || D.certOk i j

/-- Some point lies off the plane of the first facet: the body is solid. -/
def solid : Bool :=
  match D.facets with
  | (i :: j :: k :: _) :: _ => (List.range D.n).any fun u => D.side (D.nrm i j k) i u != 0
  | _ => false

/-- Everything at once. -/
def checkAll : Bool :=
  D.checkVertices && D.checkTriples && D.checkPairs && D.edges.all D.edgeOk &&
    D.facets.all D.facetOk && D.solid

/-! ## The geometry -/

/-- The `i`-th point in `ℝ³`. -/
noncomputable def P (i : ℕ) : R3 := (D.pt i).toR3
/-- The vertex set. -/
noncomputable def verts : Set R3 := D.P '' {i | i < D.n}
/-- The polytope. -/
noncomputable def body : Set R3 := convexHull ℝ D.verts
/-- The hull of a list of points. -/
noncomputable def hull (s : List ℕ) : Set R3 := convexHull ℝ (D.P '' {i | i ∈ s})

lemma verts_finite : D.verts.Finite := (Set.finite_lt_nat D.n).image _

lemma isPolytope_body : IsPolytope D.body := ⟨D.verts, D.verts_finite, rfl⟩

lemma inner_P_sub (w : V) (i u : ℕ) :
    ⟪w.toR3, D.P u - D.P i⟫ = toReal (V.dot w (D.pt u - D.pt i)) := by
  rw [P, P, ← V.toR3_sub, V.inner_toR3]

/-- A list of indices is *exposed* if it is exactly the set of maximisers of a functional. -/
def Exposed (S : List ℕ) : Prop :=
  ∃ a : R3, ∃ c : ℝ, (∀ u < D.n, ⟪a, D.P u⟫ ≤ c) ∧ ∀ u, u ∈ S ↔ u < D.n ∧ ⟪a, D.P u⟫ = c

lemma argmax_eq {a : R3} {c : ℝ} {S : List ℕ} (hS : ∀ u, u ∈ S ↔ u < D.n ∧ ⟪a, D.P u⟫ = c) :
    {v ∈ D.verts | ⟪a, v⟫ = c} = D.P '' {i | i ∈ S} := by
  ext x
  simp only [verts, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, hc⟩; exact ⟨u, (hS u).2 ⟨hu, hc⟩, rfl⟩
  · rintro ⟨u, hu, rfl⟩; exact ⟨⟨u, ((hS u).1 hu).1, rfl⟩, ((hS u).1 hu).2⟩

lemma le_of_verts {a : R3} {c : ℝ} (hle : ∀ u < D.n, ⟪a, D.P u⟫ ≤ c) :
    ∀ v ∈ D.verts, ⟪a, v⟫ ≤ c := by
  rintro _ ⟨u, hu, rfl⟩; exact hle u hu

/-- An exposed list spans a face, cut out by its functional. -/
theorem Exposed.isFaceOf {S : List ℕ} (h : D.Exposed S) : IsFaceOf D.body (D.hull S) := by
  obtain ⟨a, c, hle, hS⟩ := h
  have := isFaceOf_convexHull_argmax (D.le_of_verts hle)
  rwa [D.argmax_eq hS] at this

theorem Exposed.hull_eq {S : List ℕ} {a : R3} {c : ℝ} (hle : ∀ u < D.n, ⟪a, D.P u⟫ ≤ c)
    (hS : ∀ u, u ∈ S ↔ u < D.n ∧ ⟪a, D.P u⟫ = c) :
    D.hull S = {x ∈ D.body | ⟪a, x⟫ = c} := by
  rw [body, inter_hyperplane_eq_convexHull_argmax (D.le_of_verts hle), D.argmax_eq hS]; rfl

/-- The vertices in the hull of an exposed list are exactly its points. -/
theorem Exposed.P_mem_hull {S : List ℕ} (h : D.Exposed S) {u : ℕ} (hu : u < D.n) :
    D.P u ∈ D.hull S ↔ u ∈ S := by
  obtain ⟨a, c, hle, hS⟩ := h
  constructor
  · intro hx
    rw [Exposed.hull_eq D hle hS] at hx
    exact (hS u).2 ⟨hu, hx.2⟩
  · intro hx
    exact subset_convexHull ℝ _ ⟨u, hx, rfl⟩

lemma Exposed.lt {S : List ℕ} (h : D.Exposed S) {u : ℕ} (hu : u ∈ S) : u < D.n := by
  obtain ⟨a, c, -, hS⟩ := h; exact ((hS u).1 hu).1

/-- Inclusion of exposed hulls is inclusion of index lists. -/
theorem Exposed.hull_subset_iff {S T : List ℕ} (hS : D.Exposed S) (hT : D.Exposed T) :
    D.hull S ⊆ D.hull T ↔ ∀ u ∈ S, u ∈ T := by
  constructor
  · intro h u hu
    exact (hT.P_mem_hull D (hS.lt D hu)).1 (h ((hS.P_mem_hull D (hS.lt D hu)).2 hu))
  · intro h
    exact convexHull_mono (by rintro _ ⟨u, hu, rfl⟩; exact ⟨u, h u hu, rfl⟩)

theorem Exposed.hull_inj {S T : List ℕ} (hS : D.Exposed S) (hT : D.Exposed T) :
    D.hull S = D.hull T ↔ ∀ u, u ∈ S ↔ u ∈ T := by
  constructor
  · intro h u
    exact ⟨fun hu => (hS.hull_subset_iff D hT).1 h.le u hu,
      fun hu => (hT.hull_subset_iff D hS).1 h.ge u hu⟩
  · intro h
    exact subset_antisymm ((hS.hull_subset_iff D hT).2 fun u hu => (h u).1 hu)
      ((hT.hull_subset_iff D hS).2 fun u hu => (h u).2 hu)

/-! ## Soundness of the checks -/

variable {D}

lemma checkAll_parts (h : D.checkAll = true) :
    D.checkVertices = true ∧ D.checkTriples = true ∧ D.checkPairs = true ∧
      D.edges.all D.edgeOk = true ∧ D.facets.all D.facetOk = true ∧ D.solid = true := by
  simp only [checkAll, Bool.and_eq_true] at h
  tauto

lemma inner_P_P (i u : ℕ) : ⟪D.P i, D.P u⟫ = toReal (V.dot (D.pt i) (D.pt u)) :=
  V.inner_toR3 _ _

lemma vertex_lt (h : D.checkVertices = true) {i u : ℕ} (hi : i < D.n) (hu : u < D.n)
    (hne : u ≠ i) : ⟪D.P i, D.P u⟫ < ⟪D.P i, D.P i⟫ := by
  simp only [checkVertices, vertexOk, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq] at h
  have h1 := sgn_eq_one ((h i hi u hu).resolve_left hne)
  rw [toReal_sub] at h1
  rw [inner_P_P, inner_P_P]
  linarith

lemma P_inj (h : D.checkVertices = true) {i u : ℕ} (hi : i < D.n) (hu : u < D.n)
    (he : D.P u = D.P i) : u = i := by
  by_contra hne
  have := vertex_lt h hi hu hne
  rw [he] at this
  exact lt_irrefl _ this

theorem exposed_vertex (h : D.checkVertices = true) {i : ℕ} (hi : i < D.n) :
    D.Exposed [i] := by
  refine ⟨D.P i, ⟪D.P i, D.P i⟫, fun u hu => ?_, fun u => ?_⟩
  · rcases eq_or_ne u i with rfl | hne
    · exact le_rfl
    · exact (vertex_lt h hi hu hne).le
  · simp only [List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨hi, rfl⟩
    · rintro ⟨hu, hc⟩
      by_contra hne
      exact (vertex_lt h hi hu hne).ne hc

lemma hull_singleton (i : ℕ) : D.hull [i] = {D.P i} := by
  simp [hull]

lemma side_pos {w : V} {i u : ℕ} (h : D.side w i u = 1) : 0 < ⟪w.toR3, D.P u - D.P i⟫ := by
  rw [inner_P_sub]; exact sgn_eq_one h

lemma side_neg {w : V} {i u : ℕ} (h : D.side w i u = -1) : ⟪w.toR3, D.P u - D.P i⟫ < 0 := by
  rw [inner_P_sub]; exact sgn_eq_neg_one h

lemma side_zero_iff {w : V} {i u : ℕ} (h : D.side w i u ≠ 2) :
    ⟪w.toR3, D.P u - D.P i⟫ = 0 ↔ D.side w i u = 0 := by
  rw [inner_P_sub]; exact toReal_eq_zero_iff_sgn h

lemma noTwo_spec {w : V} {i : ℕ} (h : D.noTwo w i = true) {u : ℕ} (hu : u < D.n) :
    D.side w i u ≠ 2 := by
  simp only [noTwo, List.all_eq_true, List.mem_range, bne_iff_ne] at h
  exact h u hu

lemma mem_zeroSet {w : V} {i u : ℕ} : u ∈ D.zeroSet w i ↔ u < D.n ∧ D.side w i u = 0 := by
  simp [zeroSet]

lemma hasPos_spec {w : V} {i : ℕ} (h : D.hasPos w i = true) :
    ∃ u < D.n, D.side w i u = 1 := by
  simpa [hasPos] using h

lemma hasNeg_spec {w : V} {i : ℕ} (h : D.hasNeg w i = true) :
    ∃ u < D.n, D.side w i u = -1 := by
  simpa [hasNeg] using h

lemma nrm_toR3 (i j k : ℕ) :
    (D.nrm i j k).toR3 = R3.crs (D.P j - D.P i) (D.P k - D.P i) := by
  rw [nrm, R3.toR3_cross, V.toR3_sub, V.toR3_sub]; rfl

lemma nrm_ne_zero {i j k : ℕ} (h : sgn (V.dot (D.nrm i j k) (D.nrm i j k)) = 1) :
    R3.crs (D.P j - D.P i) (D.P k - D.P i) ≠ 0 := by
  rw [← nrm_toR3]
  intro h0
  have := sgn_eq_one h
  rw [← V.inner_toR3, h0, inner_zero_left] at this
  exact lt_irrefl _ this

theorem edgeOk_spec {e : List ℕ} (h : D.edgeOk e = true) :
    ∃ i j, e = [i, j] ∧ i < j ∧ j < D.n ∧ D.Exposed [i, j] := by
  unfold edgeOk at h
  split at h
  swap
  · simp at h
  · rename_i i j
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
      List.mem_range, Bool.or_eq_true] at h
    obtain ⟨⟨hij, hjn⟩, heq, hrest⟩ := h
    refine ⟨i, j, rfl, hij, hjn, (D.pt i + D.pt j).toR3,
      toReal (V.dot (D.pt i + D.pt j) (D.pt i)), fun u hu => ?_, fun u => ?_⟩
    · rw [P, V.inner_toR3]
      rcases hrest u hu with (rfl | rfl) | hlt
      · exact le_rfl
      · rw [heq]
      · have := sgn_eq_one hlt; rw [toReal_sub] at this; linarith
    · rw [P, V.inner_toR3]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨by omega, rfl⟩
        · exact ⟨hjn, by rw [heq]⟩
      · rintro ⟨hu, hc⟩
        rcases hrest u hu with (rfl | rfl) | hlt
        · exact Or.inl rfl
        · exact Or.inr rfl
        · have := sgn_eq_one hlt; rw [toReal_sub] at this; linarith

theorem facetOk_spec {f : List ℕ} (h : D.facetOk f = true) :
    ∃ i j k rest, f = i :: j :: k :: rest ∧ D.zeroSet (D.nrm i j k) i = f ∧
      sgn (V.dot (D.nrm i j k) (D.nrm i j k)) = 1 ∧ D.noTwo (D.nrm i j k) i = true ∧
      ¬ (D.hasPos (D.nrm i j k) i = true ∧ D.hasNeg (D.nrm i j k) i = true) := by
  unfold facetOk at h
  split at h
  swap
  · simp at h
  · rename_i i j k rest
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨i, j, k, rest, rfl, h4, h1, h2, fun ⟨hp, hn⟩ => ?_⟩
    rw [hp, hn] at h3; exact absurd h3 (by decide)

/-- The points of a listed facet are exactly the maximisers of `±⟪n, ·⟫`. -/
theorem exposed_facet {f : List ℕ} (h : D.facetOk f = true) : D.Exposed f := by
  obtain ⟨i, j, k, rest, rfl, hz, hw, h2, hmix⟩ := facetOk_spec h
  set w := D.nrm i j k
  have hin : i < D.n := by
    have : i ∈ D.zeroSet w i := by rw [hz]; exact List.mem_cons_self
    exact (mem_zeroSet.1 this).1
  have hmem : ∀ u, u ∈ i :: j :: k :: rest ↔ u < D.n ∧ ⟪w.toR3, D.P u - D.P i⟫ = 0 := by
    intro u
    rw [← hz, mem_zeroSet]
    constructor
    · rintro ⟨hu, h0⟩; exact ⟨hu, (side_zero_iff (noTwo_spec h2 hu)).2 h0⟩
    · rintro ⟨hu, h0⟩; exact ⟨hu, (side_zero_iff (noTwo_spec h2 hu)).1 h0⟩
  by_cases hp : D.hasPos w i = true
  · have hn : ¬ D.hasNeg w i = true := fun hn => hmix ⟨hp, hn⟩
    -- every point is on the nonnegative side: use `-w`
    have hle : ∀ u < D.n, 0 ≤ ⟪w.toR3, D.P u - D.P i⟫ := by
      intro u hu
      rcases sgn_cases (V.dot w (D.pt u - D.pt i)) with h0 | h0 | h0 | h0
      · exact ((side_zero_iff (noTwo_spec h2 hu)).2 h0).ge
      · exact (side_pos h0).le
      · exact absurd (show D.hasNeg w i = true by
          simp only [hasNeg, List.any_eq_true, List.mem_range, beq_iff_eq]; exact ⟨u, hu, h0⟩) hn
      · exact absurd h0 (noTwo_spec h2 hu)
    refine ⟨-w.toR3, ⟪-w.toR3, D.P i⟫, fun u hu => ?_, fun u => ?_⟩
    · have := hle u hu
      rw [inner_sub_right] at this
      simp only [inner_neg_left]; linarith
    · rw [hmem u, inner_sub_right]
      simp only [inner_neg_left, neg_inj, sub_eq_zero]
  · have hle : ∀ u < D.n, ⟪w.toR3, D.P u - D.P i⟫ ≤ 0 := by
      intro u hu
      rcases sgn_cases (V.dot w (D.pt u - D.pt i)) with h0 | h0 | h0 | h0
      · exact ((side_zero_iff (noTwo_spec h2 hu)).2 h0).le
      · exact absurd (show D.hasPos w i = true by
          simp only [hasPos, List.any_eq_true, List.mem_range, beq_iff_eq]; exact ⟨u, hu, h0⟩) hp
      · exact (side_neg h0).le
      · exact absurd h0 (noTwo_spec h2 hu)
    refine ⟨w.toR3, ⟪w.toR3, D.P i⟫, fun u hu => ?_, fun u => ?_⟩
    · have := hle u hu
      rw [inner_sub_right] at this; linarith
    · rw [hmem u, inner_sub_right, sub_eq_zero]

/-- A listed facet has affine dimension `2`. -/
theorem affDim_facet {f : List ℕ} (h : D.facetOk f = true) : affDim (D.hull f) = 2 := by
  obtain ⟨i, j, k, rest, rfl, hz, hw, h2, -⟩ := facetOk_spec h
  have hmem : ∀ u, u ∈ i :: j :: k :: rest → u < D.n ∧ D.side (D.nrm i j k) i u = 0 := by
    intro u hu; rw [← hz] at hu; exact mem_zeroSet.1 hu
  rw [hull, R3.affDim_convexHull]
  refine R3.affDim_eq_two (p := D.P i) (q := D.P j) (r := D.P k) ⟨i, by simp, rfl⟩
    ⟨j, by simp, rfl⟩ ⟨k, by simp, rfl⟩ (nrm_ne_zero hw) ?_
  rintro _ ⟨u, hu, rfl⟩
  rw [← nrm_toR3]
  exact (side_zero_iff (noTwo_spec h2 (hmem u hu).1)).2 (hmem u hu).2

/-- A listed edge has affine dimension `1`. -/
theorem affDim_edge (hv : D.checkVertices = true) {e : List ℕ} (h : D.edgeOk e = true) :
    affDim (D.hull e) = 1 := by
  obtain ⟨i, j, rfl, hij, hjn, -⟩ := edgeOk_spec h
  rw [hull, R3.affDim_convexHull]
  have : D.P '' {u | u ∈ [i, j]} = {D.P i, D.P j} := by
    ext x; simp [eq_comm]
  rw [this]
  refine R3.affDim_pair fun he => ?_
  have := P_inj hv hjn (show i < D.n by omega) he
  omega

lemma solid_spec (h : D.solid = true) : ∃ i j k rest restF,
    D.facets = (i :: j :: k :: rest) :: restF ∧ ∃ t < D.n, D.side (D.nrm i j k) i t ≠ 0 := by
  unfold solid at h
  split at h
  · rename_i i j k rest restF hF
    simp only [List.any_eq_true, List.mem_range, bne_iff_ne] at h
    exact ⟨i, j, k, rest, restF, hF, h⟩
  · simp at h

/-- The body is three-dimensional. -/
theorem affDim_body (h : D.checkAll = true) : affDim D.body = 3 := by
  obtain ⟨-, -, -, -, hf, hs⟩ := checkAll_parts h
  obtain ⟨i, j, k, rest, restF, hF, t, ht, hside⟩ := solid_spec hs
  have hfOk : D.facetOk (i :: j :: k :: rest) = true := by
    simp only [List.all_eq_true] at hf; exact hf _ (by rw [hF]; exact List.mem_cons_self)
  obtain ⟨i', j', k', rest', heq, hz, hw, h2, -⟩ := facetOk_spec hfOk
  simp only [List.cons.injEq] at heq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
  have hmem : ∀ u, u ∈ i :: j :: k :: rest → u < D.n := by
    intro u hu; rw [← hz] at hu; exact (mem_zeroSet.1 hu).1
  rw [body, R3.affDim_convexHull]
  refine R3.affDim_eq_three (p := D.P i) (q := D.P j) (r := D.P k) (t := D.P t)
    ⟨i, hmem _ (by simp), rfl⟩ ⟨j, hmem _ (by simp), rfl⟩ ⟨k, hmem _ (by simp), rfl⟩
    ⟨t, ht, rfl⟩ ?_
  rw [← nrm_toR3]
  exact fun h0 => hside ((side_zero_iff (noTwo_spec h2 ht)).1 h0)

/-! ## Certificates against non-edges -/

lemma toReal_sumZ (ν : List (ℕ × ZPhi)) : toReal (sumZ ν) = (ν.map fun uc => toReal uc.2).sum := by
  induction ν with
  | nil => simp [sumZ]
  | cons uc l ih => simp [sumZ, ih]

lemma inner_sumV (a : R3) (ν : List (ℕ × ZPhi)) :
    ⟪a, (D.sumV ν).toR3⟫ = (ν.map fun uc => toReal uc.2 * ⟪a, D.P uc.1⟫).sum := by
  induction ν with
  | nil => simp [sumV]
  | cons uc l ih => simp [sumV, ih, inner_add_right, inner_smul_right, P]

lemma sum_le_of_forall {c : ℝ} (ν : List (ℕ × ZPhi)) (f : ℕ → ℝ)
    (h : ∀ uc ∈ ν, 0 ≤ toReal uc.2 ∧ f uc.1 ≤ c) :
    (ν.map fun uc => toReal uc.2 * f uc.1).sum ≤ (ν.map fun uc => toReal uc.2).sum * c := by
  induction ν with
  | nil => simp
  | cons uc l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h0 := h uc List.mem_cons_self
    have := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have := mul_le_mul_of_nonneg_left h0.2 h0.1
    linarith

lemma sum_lt_of_forall {c : ℝ} (ν : List (ℕ × ZPhi)) (f : ℕ → ℝ)
    (h : ∀ uc ∈ ν, 0 ≤ toReal uc.2 ∧ f uc.1 < c) (hpos : 0 < (ν.map fun uc => toReal uc.2).sum) :
    (ν.map fun uc => toReal uc.2 * f uc.1).sum < (ν.map fun uc => toReal uc.2).sum * c := by
  induction ν with
  | nil => simp at hpos
  | cons uc l ih =>
    simp only [List.map_cons, List.sum_cons] at hpos ⊢
    have h0 := h uc List.mem_cons_self
    have hl : ∀ uc ∈ l, 0 ≤ toReal uc.2 ∧ f uc.1 < c := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hle : (l.map fun uc => toReal uc.2 * f uc.1).sum ≤ (l.map fun uc => toReal uc.2).sum * c := by
      exact sum_le_of_forall l f fun x hx => ⟨(hl x hx).1, (hl x hx).2.le⟩
    rcases h0.1.lt_or_eq with hp | hp
    · have : toReal uc.2 * f uc.1 < toReal uc.2 * c := mul_lt_mul_of_pos_left h0.2 hp
      linarith
    · have hl0 : 0 < (l.map fun uc => toReal uc.2).sum := by rw [← hp] at hpos; linarith
      have := ih hl hl0
      rw [← hp]; simp only [zero_mul, zero_add]; linarith

/-- A pair with a valid certificate is not the set of maximisers of any functional. -/
theorem not_argmax_of_certOk {i j : ℕ} (hc : D.certOk i j = true) {a : R3} {c : ℝ}
    (hle : ∀ u < D.n, ⟪a, D.P u⟫ ≤ c) (hi : ⟪a, D.P i⟫ = c) (hj : ⟪a, D.P j⟫ = c)
    (hother : ∀ u < D.n, u ≠ i → u ≠ j → ⟪a, D.P u⟫ ≠ c) : False := by
  unfold certOk at hc
  split at hc
  · rename_i d ν _
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq,
      beq_iff_eq] at hc
    obtain ⟨⟨⟨hd, hν⟩, hsum⟩, hvec⟩ := hc
    have hsumR : (ν.map fun uc => toReal uc.2).sum = 2 * d := by
      rw [← toReal_sumZ, hsum, toReal_ofInt]; push_cast; ring
    have hvecR := congrArg (fun v => ⟪a, V.toR3 v⟫) hvec
    rw [inner_sumV, V.toR3_smul, V.toR3_add, inner_smul_right, inner_add_right] at hvecR
    change toReal (ofInt d) * (⟪a, D.P i⟫ + ⟪a, D.P j⟫) = _ at hvecR
    rw [hi, hj, toReal_ofInt] at hvecR
    have hlt := sum_lt_of_forall (c := c) ν (fun u => ⟪a, D.P u⟫) (fun uc huc => by
      obtain ⟨⟨⟨⟨hu, hui⟩, huj⟩, hneg⟩, h2⟩ := hν uc huc
      exact ⟨sgn_nonneg hneg h2, lt_of_le_of_ne (hle _ hu) (hother _ hu hui huj)⟩)
      (by rw [hsumR]; have : (0 : ℝ) < d := by exact_mod_cast hd
          linarith)
    rw [hsumR, ← hvecR] at hlt
    linarith
  · simp at hc

/-! ## The classification -/

lemma exists_three_sorted {W : Finset ℕ} (h : 2 < W.card) :
    ∃ i ∈ W, ∃ j ∈ W, ∃ k ∈ W, i < j ∧ j < k := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 h
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases lt_or_gt_of_ne hbc with h3 | h3
  all_goals first
    | exact ⟨a, ha, b, hb, c, hc, by omega, by omega⟩
    | exact ⟨a, ha, c, hc, b, hb, by omega, by omega⟩
    | exact ⟨b, hb, a, ha, c, hc, by omega, by omega⟩
    | exact ⟨b, hb, c, hc, a, ha, by omega, by omega⟩
    | exact ⟨c, hc, a, ha, b, hb, by omega, by omega⟩
    | exact ⟨c, hc, b, hb, a, ha, by omega, by omega⟩

/-- **The face lattice of an explicit polytope.** If the checker accepts the data, every face
of the body is empty, the body, a single point, a listed edge, or a listed facet. -/
theorem face_cases (h : D.checkAll = true) {F : Set R3} (hF : IsFaceOf D.body F) :
    F = ∅ ∨ F = D.body ∨ (∃ i < D.n, F = D.hull [i]) ∨ (∃ e ∈ D.edges, F = D.hull e) ∨
      (∃ f ∈ D.facets, F = D.hull f) := by
  classical
  obtain ⟨hv, ht, hp, -, -, -⟩ := checkAll_parts h
  rcases F.eq_empty_or_nonempty with hFe | hne
  · exact Or.inl hFe
  obtain ⟨a, c, hle, hFeq⟩ := face_eq_convexHull_argmax D.verts_finite hF hne
  have hle' : ∀ u < D.n, ⟪a, D.P u⟫ ≤ c := fun u hu => hle _ ⟨u, hu, rfl⟩
  set W := (Finset.range D.n).filter (fun u => ⟪a, D.P u⟫ = c) with hW
  have hmemW : ∀ u, u ∈ W ↔ u < D.n ∧ ⟪a, D.P u⟫ = c := by
    intro u; simp [hW]
  have hset : {v ∈ D.verts | ⟪a, v⟫ = c} = D.P '' (W : Set ℕ) := by
    ext x
    simp only [verts, mem_ofPred_eq, mem_image, Finset.mem_coe, hmemW]
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hc⟩; exact ⟨u, ⟨hu, hc⟩, rfl⟩
    · rintro ⟨u, ⟨hu, hc⟩, rfl⟩; exact ⟨⟨u, hu, rfl⟩, hc⟩
  rw [hset] at hFeq
  -- turning an index list into the hull
  have hullOf : ∀ L : List ℕ, (∀ u, u ∈ W ↔ u ∈ L) → F = D.hull L := by
    intro L hL
    rw [hFeq, hull]
    congr 1
    ext x; simp only [mem_image, Finset.mem_coe, mem_ofPred_eq, hL]
  rcases Nat.lt_or_ge W.card 3 with hc3 | hc3
  · interval_cases hcard : W.card
    · -- no maximiser
      rw [Finset.card_eq_zero] at hcard
      rw [hcard, Finset.coe_empty, image_empty, convexHull_empty] at hFeq
      exact Or.inl hFeq
    · -- one maximiser: a vertex
      obtain ⟨i, hi⟩ := Finset.card_eq_one.1 hcard
      have hiW : i ∈ W := by rw [hi]; exact Finset.mem_singleton_self i
      refine Or.inr (Or.inr (Or.inl ⟨i, ((hmemW i).1 hiW).1, hullOf [i] fun u => ?_⟩))
      rw [hi]; simp
    · -- two maximisers: an edge, or a certificate contradiction
      obtain ⟨x, y, hxy, hxyW⟩ := Finset.card_eq_two.1 hcard
      have key : ∀ i j, i < j → W = {i, j} → F = ∅ ∨ F = D.body ∨ (∃ i < D.n, F = D.hull [i]) ∨
          (∃ e ∈ D.edges, F = D.hull e) ∨ (∃ f ∈ D.facets, F = D.hull f) := by
        intro i j hij hWij
        have hiW : i ∈ W := by rw [hWij]; simp
        have hjW : j ∈ W := by rw [hWij]; simp
        have hjn := ((hmemW j).1 hjW).1
        simp only [checkPairs, List.all_eq_true, List.mem_range, Bool.or_eq_true,
          Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at hp
        rcases hp i (by omega) j hjn with (hji | hed) | hcert
        · omega
        · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨[i, j], List.elem_iff.1 hed, hullOf _ fun u => ?_⟩)))
          rw [hWij]; simp
        · exfalso
          refine not_argmax_of_certOk hcert hle' ((hmemW i).1 hiW).2 ((hmemW j).1 hjW).2 ?_
          intro u hu hui huj hc
          have : u ∈ W := (hmemW u).2 ⟨hu, hc⟩
          rw [hWij] at this; simp at this; omega
      rcases lt_or_gt_of_ne hxy with hl | hl
      · exact key x y hl hxyW
      · exact key y x hl (by rw [hxyW, Finset.pair_comm])
  · -- three or more maximisers: the body or a facet
    obtain ⟨i, hiW, j, hjW, k, hkW, hij, hjk⟩ := exists_three_sorted (by omega : 2 < W.card)
    have hin := ((hmemW i).1 hiW).1
    have hjn := ((hmemW j).1 hjW).1
    have hkn := ((hmemW k).1 hkW).1
    simp only [checkTriples, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at ht
    have htr : D.tripleOk i j k = true := by
      rcases ht i hin j hjn k hkn with (h1 | h1) | h1
      · omega
      · omega
      · exact h1
    simp only [tripleOk, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at htr
    obtain ⟨⟨hw, h2⟩, hmix⟩ := htr
    set w := D.nrm i j k with hwdef
    set nR := R3.crs (D.P j - D.P i) (D.P k - D.P i) with hnR
    have hwR : w.toR3 = nR := nrm_toR3 i j k
    have hnpos : 0 < ⟪nR, nR⟫ := R3.inner_self_crs_pos (nrm_ne_zero hw)
    have hci := ((hmemW i).1 hiW).2
    have hax : ⟪a, D.P j - D.P i⟫ = 0 := by
      rw [inner_sub_right, ((hmemW j).1 hjW).2, hci, sub_self]
    have hay : ⟪a, D.P k - D.P i⟫ = 0 := by
      rw [inner_sub_right, ((hmemW k).1 hkW).2, hci, sub_self]
    have hid := fun z => R3.inner_mul_crs hax hay z
    -- `⟪a, P u⟫ - c` in terms of the side of `u`
    have hsideEq : ∀ u, (⟪a, D.P u⟫ - c) * ⟪nR, nR⟫ = ⟪a, nR⟫ * ⟪w.toR3, D.P u - D.P i⟫ := by
      intro u
      rw [hwR, ← hci, ← inner_sub_right]
      exact hid _
    by_cases han : ⟪a, nR⟫ = 0
    · -- every vertex is a maximiser: the whole body
      refine Or.inr (Or.inl ?_)
      rw [hFeq, body]
      congr 1
      ext x
      simp only [verts, mem_image, Finset.mem_coe, hmemW, mem_ofPred_eq]
      constructor
      · rintro ⟨u, ⟨hu, -⟩, rfl⟩; exact ⟨u, hu, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        refine ⟨u, ⟨hu, ?_⟩, rfl⟩
        have := hsideEq u
        rw [han, zero_mul] at this
        have := (mul_eq_zero.1 this).resolve_right hnpos.ne'
        linarith
    · rcases hmix with ⟨hpos, hneg⟩ | hfac
      · -- both sides occur: impossible for a maximiser
        exfalso
        obtain ⟨u, hu, hsu⟩ := hasPos_spec hpos
        obtain ⟨u', hu', hsu'⟩ := hasNeg_spec hneg
        have e1 := hsideEq u
        have e2 := hsideEq u'
        have p1 := side_pos hsu
        have p2 := side_neg hsu'
        have l1 : (⟪a, D.P u⟫ - c) * ⟪nR, nR⟫ ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith [hle' u hu]) hnpos.le
        have l2 : (⟪a, D.P u'⟫ - c) * ⟪nR, nR⟫ ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith [hle' u' hu']) hnpos.le
        rw [e1] at l1
        rw [e2] at l2
        rcases lt_or_gt_of_ne han with hlt | hgt
        · nlinarith
        · nlinarith
      · -- a listed facet
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨_, List.elem_iff.1 hfac, hullOf _ fun u => ?_⟩)))
        rw [hmemW, mem_zeroSet]
        constructor
        · rintro ⟨hu, hc⟩
          refine ⟨hu, (side_zero_iff (noTwo_spec h2 hu)).1 ?_⟩
          have := hsideEq u
          rw [hc, sub_self, zero_mul] at this
          exact (mul_eq_zero.1 this.symm).resolve_left han
        · rintro ⟨hu, hs⟩
          refine ⟨hu, ?_⟩
          have := hsideEq u
          rw [(side_zero_iff (noTwo_spec h2 hu)).2 hs, mul_zero] at this
          have := (mul_eq_zero.1 this).resolve_right hnpos.ne'
          linarith

end Data

end Explicit

end EulersGem
