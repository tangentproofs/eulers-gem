/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.Embed
import EulersGem.LatticeArea
import EulersGem.PlatonicOfEuler
import EulersGem.Picks

/-!
# Paper-facing results

Three theorems, each proved in `EulersGem.*` and restated here:

* the Euler characteristic of a full-dimensional convex polytope,
* `V − E + F = 2` in dimension 3, from that characteristic,
* Pick's theorem for a strictly convex lattice polygon,
* the five Platonic solids, by Euler's formula in dimension 3.

Proofs of the supporting lemmas stay in the `EulersGem` modules.
-/

open scoped RealInnerProductSpace

namespace Results

/-! ## Euler characteristic -/

/-- **Euler characteristic.** A full-dimensional convex polytope, given by
finitely many closed half-spaces and as the convex hull of finitely many
points, has Euler–Poincaré characteristic `1`: the alternating sum of its
face counts, from vertices through the body, equals `1`. In dimension `3`
this is `V − E + F = 2`. -/
theorem results_euler_characteristic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {H : Set (EulersGem.Hyperplane E)} {p : Set E}
    (hH : H.Finite)
    (hp : p = ⋂ h ∈ H, EulersGem.closedHalfspace h.1 h.2)
    (hP : EulersGem.IsPolytope p)
    (hdim : EulersGem.affDim p = Module.finrank ℝ E)
    (hn : 1 ≤ Module.finrank ℝ E) :
    EulersGem.faceEulerSum p (Module.finrank ℝ E) = 1 :=
  EulersGem.Euler_Poincare_full hH hp hP hdim hn

/-- **Euler's formula** (Euler's polyhedron formula; Paulson `Euler_relation`).
For a convex polytope in dimension 3, `V − E + F = 2`. Proved from the
Euler characteristic `1`: the only 3-face is the body itself, and removing
it from the alternating sum leaves `2`. -/
theorem results_euler_relation_dimension_three
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {H : Set (EulersGem.Hyperplane E)} {p : Set E}
    (hH : H.Finite)
    (hp : p = ⋂ h ∈ H, EulersGem.closedHalfspace h.1 h.2)
    (hP : EulersGem.IsPolytope p)
    (hdim : EulersGem.affDim p = 3)
    (hE : Module.finrank ℝ E = 3) :
    ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 0}.ncard : ℤ) -
        ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 1}.ncard : ℤ) +
        ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 2}.ncard : ℤ) =
      2 := by
  have hn : 1 ≤ Module.finrank ℝ E := by rw [hE]; norm_num
  have hdim' : EulersGem.affDim p = Module.finrank ℝ E := by simpa [hE] using hdim
  have hsum := results_euler_characteristic hH hp hP hdim' hn
  rw [hE] at hsum
  have hConv : Convex ℝ p := by
    obtain ⟨V, _, rfl⟩ := hP
    exact convex_convexHull ℝ V
  have hSolid :
      ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 3}.ncard) = 1 := by
    have hEq :
        {f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 3} =
          {f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = Module.finrank ℝ E} := by
      simp [hE]
    rw [hEq, EulersGem.faces_dim_eq_finrank_eq_singleton hConv hdim', Set.ncard_singleton]
  exact EulersGem.euler_relation_of_faceEulerSum p _ _ _ hsum rfl rfl rfl hSolid

/-! ## Pick's theorem -/

/-- **Pick's count is Euler's formula for a triangulation.**
`A = T/2`, `V = I + B`, `F = T + 1`, `2E = 3T + B`, and `V − E + F = 2`
give `A = I + B/2 − 1`. The Euler input is not a bare hypothesis: a caller
passes `results_euler_relation_dimension_three` when those `(V, E, F)` are the
face counts of a convex 3-polytope, or the same numeral proved for a disk
triangulation. -/
theorem results_pick_count_of_euler
    (I B V E T F : ℕ) (A : ℚ)
    (hV : V = I + B)
    (hF : F = T + 1)
    (heuler : (V : ℤ) - E + F = 2)
    (hshake : 2 * E = 3 * T + B)
    (harea : A = (T : ℚ) / 2) :
    A = (I : ℚ) + (B : ℚ) / 2 - 1 :=
  EulersGem.Picks.triangulation_count_identity_nat I B V E T F A hV hF heuler hshake harea

/-- **Pick's theorem** for a strictly convex counterclockwise lattice polygon
with distinct vertices. The area is the Haar measure of the convex hull. The
count `I + B/2 − 1` is proved by cutting the polygon into a fan of ears and
inducting on the interior lattice points. `results_pick_count_of_euler` is the
same count read off Euler's formula when a triangulation's handshaking data
are given; this polygon proof does not go through that lemma, because a
primitive triangulation of a general lattice polygon is not yet identified
with the face lattice of a convex 3-polytope. -/
theorem results_picks_theorem
    (P : EulersGem.Picks.LatticePolygon) (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hverts : Function.Injective P.vertex)
    (hsc : EulersGem.Picks.LatticeFan.StrictlyConvexCCW P) :
    MeasureTheory.volume P.convexHullRegion =
      ENNReal.ofReal ((S.card : ℚ) + (P.B : ℚ) / 2 - 1) := by
  exact EulersGem.Picks.LatticeArea.volume_eq_ofReal_cardI_add_B_div_two_sub_one_no_pe
    P S hS hverts hsc

/-! ## The five Platonic solids -/

private lemma schlafli_vef
    (R : EulersGem.Platonic.RegularNumbers) {s m : ℕ}
    (hs : R.s = s) (hm : R.m = m) :
    s * R.F = 2 * R.E ∧ m * R.V = 2 * R.E ∧ (R.V : ℤ) - R.E + R.F = 2 ∧ 0 < R.E := by
  refine ⟨?_, ?_, R.hEuler, R.hE⟩
  · simpa [hs] using R.hFace
  · simpa [hm] using R.hVert

/-- **Euler's formula leaves five Platonic solids.** A convex 3-polytope whose
faces are `s`-gons, with `m` faces at each vertex and two faces along each
edge, has `(s, m)` in the list below. The count `V − E + F = 2` in that
argument is `results_euler_relation_dimension_three`. The five pairs are the
tetrahedron, cube, octahedron, dodecahedron, and icosahedron, with `(V, E, F)`
the solution of that formula together with the double-counting identities. -/
theorem results_five_platonic_solids :
    (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [Nonempty E]
        {H : Set (EulersGem.Hyperplane E)} {p : Set E} {s m : ℕ},
        H.Finite →
        p = ⋂ h ∈ H, EulersGem.closedHalfspace h.1 h.2 →
        EulersGem.IsPolytope p →
        EulersGem.affDim p = 3 →
        Module.finrank ℝ E = 3 →
        3 ≤ s → 3 ≤ m →
        (∀ f ∈ EulersGem.Platonic.facesOfDim p 2,
          {e ∈ EulersGem.Platonic.facesOfDim p 1 | e ⊆ f}.ncard = s) →
        (∀ e ∈ EulersGem.Platonic.facesOfDim p 1,
          {f ∈ EulersGem.Platonic.facesOfDim p 2 | e ⊆ f}.ncard = 2) →
        (∀ v ∈ EulersGem.Platonic.facesOfDim p 0,
          {e ∈ EulersGem.Platonic.facesOfDim p 1 | v ⊆ e}.ncard = m) →
        (s, m) ∈ EulersGem.Platonic.schlafliPairs) ∧
      (EulersGem.Platonic.tetrahedron.V, EulersGem.Platonic.tetrahedron.E,
          EulersGem.Platonic.tetrahedron.F, EulersGem.Platonic.tetrahedron.s,
          EulersGem.Platonic.tetrahedron.m) = (4, 6, 4, 3, 3) ∧
      (EulersGem.Platonic.cube.V, EulersGem.Platonic.cube.E,
          EulersGem.Platonic.cube.F, EulersGem.Platonic.cube.s,
          EulersGem.Platonic.cube.m) = (8, 12, 6, 4, 3) ∧
      (EulersGem.Platonic.octahedron.V, EulersGem.Platonic.octahedron.E,
          EulersGem.Platonic.octahedron.F, EulersGem.Platonic.octahedron.s,
          EulersGem.Platonic.octahedron.m) = (6, 12, 8, 3, 4) ∧
      (EulersGem.Platonic.dodecahedron.V, EulersGem.Platonic.dodecahedron.E,
          EulersGem.Platonic.dodecahedron.F, EulersGem.Platonic.dodecahedron.s,
          EulersGem.Platonic.dodecahedron.m) = (20, 30, 12, 5, 3) ∧
      (EulersGem.Platonic.icosahedron.V, EulersGem.Platonic.icosahedron.E,
          EulersGem.Platonic.icosahedron.F, EulersGem.Platonic.icosahedron.s,
          EulersGem.Platonic.icosahedron.m) = (12, 30, 20, 3, 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro E _ _ _ _ H p s m hH hp hP hdim hEdim hs hm hface hedge hvert
    have hVEF := results_euler_relation_dimension_three hH hp hP hdim hEdim
    obtain ⟨hFace, hVert, _⟩ :=
      EulersGem.Platonic.regular_polytope_counts hH hp hP hdim hEdim hface hedge hvert
    have hEuler :
        ((EulersGem.Platonic.facesOfDim p 0).ncard : ℤ) -
            (EulersGem.Platonic.facesOfDim p 1).ncard +
            (EulersGem.Platonic.facesOfDim p 2).ncard = 2 := by
      simpa [EulersGem.Platonic.facesOfDim] using hVEF
    exact EulersGem.Platonic.schlafli_pair_mem
      { V := (EulersGem.Platonic.facesOfDim p 0).ncard
        E := (EulersGem.Platonic.facesOfDim p 1).ncard
        F := (EulersGem.Platonic.facesOfDim p 2).ncard
        s := s, m := m, hs := hs, hm := hm
        hE := EulersGem.Platonic.pos_edges_of_euler hs hm hFace hVert hEuler
        hFace := hFace, hVert := hVert, hEuler := hEuler }
  · obtain ⟨hF, hV, hEul, hpos⟩ :=
      schlafli_vef EulersGem.Platonic.tetrahedron (s := 3) (m := 3) rfl rfl
    have : EulersGem.Platonic.tetrahedron.V = 4 ∧
        EulersGem.Platonic.tetrahedron.E = 6 ∧
        EulersGem.Platonic.tetrahedron.F = 4 := by omega
    simp [this]; exact ⟨rfl, rfl⟩
  · obtain ⟨hF, hV, hEul, hpos⟩ :=
      schlafli_vef EulersGem.Platonic.cube (s := 4) (m := 3) rfl rfl
    have : EulersGem.Platonic.cube.V = 8 ∧
        EulersGem.Platonic.cube.E = 12 ∧
        EulersGem.Platonic.cube.F = 6 := by omega
    simp [this]; exact ⟨rfl, rfl⟩
  · obtain ⟨hF, hV, hEul, hpos⟩ :=
      schlafli_vef EulersGem.Platonic.octahedron (s := 3) (m := 4) rfl rfl
    have : EulersGem.Platonic.octahedron.V = 6 ∧
        EulersGem.Platonic.octahedron.E = 12 ∧
        EulersGem.Platonic.octahedron.F = 8 := by omega
    simp [this]; exact ⟨rfl, rfl⟩
  · obtain ⟨hF, hV, hEul, hpos⟩ :=
      schlafli_vef EulersGem.Platonic.dodecahedron (s := 5) (m := 3) rfl rfl
    have : EulersGem.Platonic.dodecahedron.V = 20 ∧
        EulersGem.Platonic.dodecahedron.E = 30 ∧
        EulersGem.Platonic.dodecahedron.F = 12 := by omega
    simp [this]; exact ⟨rfl, rfl⟩
  · obtain ⟨hF, hV, hEul, hpos⟩ :=
      schlafli_vef EulersGem.Platonic.icosahedron (s := 3) (m := 5) rfl rfl
    have : EulersGem.Platonic.icosahedron.V = 12 ∧
        EulersGem.Platonic.icosahedron.E = 30 ∧
        EulersGem.Platonic.icosahedron.F = 20 := by omega
    simp [this]; exact ⟨rfl, rfl⟩

end Results
