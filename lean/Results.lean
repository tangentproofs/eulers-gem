/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.DiskEuler
import EulersGem.UnconditionalEuler
import EulersGem.LatticeArea
import EulersGem.PickFromEuler
import EulersGem.PlatonicOfEuler
import EulersGem.Picks
import EulersGem.RegularCentre

/-!
# Paper-facing results

Public results, proved in `EulersGem.*` and restated here:

* the Euler characteristic of a full-dimensional convex polytope,
* `V − E + F = 2` in dimension 3, including the two-hypothesis real-three-space theorem,
* Pick's theorem for a strictly convex lattice polygon,
* the five Platonic solids, by Euler's formula in dimension 3,
* the five Platonic solids constructed in `ℝ³` and proved regular (flag-transitive),
* the face data of a regular polyhedron, **conditional** on general face-lattice facts
  (`FaceLatticeFacts`), and the pairwise non-similarity of the five solids.

Proofs of the supporting lemmas stay in the `EulersGem` modules.
-/

open scoped RealInnerProductSpace

namespace Results

/-! ## Euler characteristic -/

/-- **Euler characteristic.** A full-dimensional convex polytope, given as
the convex hull of finitely many points, has Euler–Poincaré characteristic `1`: the alternating sum of its
face counts, from vertices through the body, equals `1`. In dimension `3`
this is `V − E + F = 2`. -/
theorem results_euler_characteristic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {p : Set E}
    (hP : EulersGem.IsPolytope p)
    (hdim : EulersGem.affDim p = Module.finrank ℝ E)
    (hn : 1 ≤ Module.finrank ℝ E) :
    EulersGem.faceEulerSum p (Module.finrank ℝ E) = 1 :=
  EulersGem.Euler_Poincare_of_isPolytope hP hdim hn

/-- **Euler's formula** (Euler's polyhedron formula; Paulson `Euler_relation`).
For a convex polytope in dimension 3, `V − E + F = 2`. Proved from the
Euler characteristic `1`: the only 3-face is the body itself, and removing
it from the alternating sum leaves `2`. -/
theorem results_euler_relation_dimension_three
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {p : Set E}
    (hP : EulersGem.IsPolytope p)
    (hdim : EulersGem.affDim p = 3)
    (hE : Module.finrank ℝ E = 3) :
    ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 0}.ncard : ℤ) -
        ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 1}.ncard : ℤ) +
        ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 2}.ncard : ℤ) =
      2 :=
  EulersGem.euler_relation_of_isPolytope hP hdim hE

/-- **Euler's polyhedron formula in real three-space.** The only geometric
hypotheses are that `p` is a finite convex hull and has affine dimension three. -/
theorem results_euler_polyhedron {p : Set (EuclideanSpace ℝ (Fin 3))}
    (hP : EulersGem.IsPolytope p) (hdim : EulersGem.affDim p = 3) :
    ({f : Set (EuclideanSpace ℝ (Fin 3)) |
      EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 0}.ncard : ℤ) -
    ({f : Set (EuclideanSpace ℝ (Fin 3)) |
      EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 1}.ncard : ℤ) +
    ({f : Set (EuclideanSpace ℝ (Fin 3)) |
      EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 2}.ncard : ℤ) = 2 :=
  EulersGem.euler_polyhedron hP hdim

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

/-- **Empty-fan Pick count, from the Euler characteristic.** A fan of an `n`-gon
has disk Euler number `2` because a triangle does (`triangle_disk_euler`, the
characteristic plus the exterior face) and each added vertex preserves it.
With area `T/2` and `I = 0`, that is `n/2 − 1`. -/
theorem results_fan_pick_of_euler (n : ℕ) (hn : 3 ≤ n) :
    ((n - 2 : ℕ) : ℚ) / 2 = (n : ℚ) / 2 - 1 :=
  EulersGem.Picks.FanDiskTriangulation.fan_pick_count_from_characteristic n hn

/-- **Pick's count for a triangulated disk, from the characteristic.**
The corner cycle's Euler number is the fan's, which is the triangle's
characteristic plus the exterior face. Boundary insertions, diagonals, and
stellar subdivisions preserve it, so `V = I + B`, `T = 2I + B − 2` and area
`T/2` give `I + B/2 − 1`. -/
theorem results_disk_pick_of_euler
    (n B I : ℕ) (A : ℚ) (hn : 3 ≤ n) (hnB : n ≤ B)
    (harea : A = ((2 * I + B - 2 : ℕ) : ℚ) / 2) :
    A = (I : ℚ) + (B : ℚ) / 2 - 1 :=
  EulersGem.Picks.pick_count_of_disk_from_characteristic n B I A hn hnB harea

/-- **Pick for an empty primitive polygon, from the characteristic.** The corner
fan is a primitive triangulation (`T = B − 2`). Its Euler number is the disk
Euler number, so the area is `B/2 − 1`. -/
theorem results_picks_of_empty_primitive_fan
    (P : EulersGem.Picks.LatticePolygon)
    (hverts : Function.Injective P.vertex)
    (hedge : EulersGem.Picks.LatticeFan.PrimitiveEdges P)
    (hsc : EulersGem.Picks.LatticeFan.StrictlyConvexCCW P)
    (hI : EulersGem.Picks.LatticeFan.EmptyInterior P) :
    MeasureTheory.volume P.convexHullRegion =
      ENNReal.ofReal ((P.B : ℚ) / 2 - 1) :=
  EulersGem.Picks.LatticeFan.volume_pick_of_empty_primitive_from_characteristic
    P hverts hedge hsc hI

/-- **Pick's theorem** for a strictly convex counterclockwise lattice polygon
with distinct vertices. The area is the Haar measure of the convex hull.
A primitive triangulation has `T = 2I + B − 2` triangles of shoelace `1/2`,
so the polygon shoelace is `T/2`. Those counts have disk Euler number `2`
by `triangulated_disk_euler_from_characteristic` (the triangle's
characteristic, kept by the fan and the later moves). `results_pick_count_of_euler`
turns `T/2` and that Euler number into `I + B/2 − 1`. -/
theorem results_picks_theorem
    (P : EulersGem.Picks.LatticePolygon) (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hverts : Function.Injective P.vertex)
    (hsc : EulersGem.Picks.LatticeFan.StrictlyConvexCCW P) :
    MeasureTheory.volume P.convexHullRegion =
      ENNReal.ofReal ((S.card : ℚ) + (P.B : ℚ) / 2 - 1) := by
  have harea :=
    EulersGem.Picks.LatticeFan.shoelace_eq_two_cardI_add_B_sub_two_div_two
      P S hS hverts hsc
  have hn : 3 ≤ P.nVertices := P.length_ge
  have hnB : P.nVertices ≤ P.B :=
    EulersGem.Picks.LatticeFan.nVertices_le_B P hverts
  let I := S.card
  let B := P.B
  let V := I + B
  let T := 2 * I + B - 2
  let E := 3 * I + 2 * B - 3
  let F := T + 1
  have hEuler :=
    EulersGem.Picks.triangulated_disk_euler_from_characteristic P.nVertices B I hn hnB
  have hFnat : 2 * I + B - 2 + 1 = F := by omega
  have hEuler' : (V : ℤ) - ↑E + ↑F = 2 := by
    simpa [V, E, F, hFnat] using hEuler
  have hshake : 2 * E = 3 * T + B := by
    have hB3 : 3 ≤ B := by omega
    omega
  have hareaT : P.shoelace = (T : ℚ) / 2 := by
    simpa [T, I, B] using harea
  have hcount :=
    results_pick_count_of_euler I B V E T F P.shoelace rfl rfl hEuler' hshake hareaT
  have hvol :=
    EulersGem.Picks.LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace P hsc hverts
  rw [hvol]
  refine congrArg ENNReal.ofReal ?_
  calc
    (P.shoelace : ℝ) = (((I : ℚ) + (B : ℚ) / 2 - 1 : ℚ) : ℝ) := congrArg Rat.cast hcount
    _ = (S.card : ℝ) + (P.B : ℝ) / 2 - 1 := by
      simp only [I, B]
      push_cast
      ring

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
        [FiniteDimensional ℝ E]
        {p : Set E} {s m : ℕ},
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
  · intro E _ _ _ p s m hP hdim hEdim hs hm hface hedge hvert
    obtain ⟨H, hH, hp⟩ := hP.isPolyhedron
    have hVEF := results_euler_relation_dimension_three hP hdim hEdim
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

/-! ## The five Platonic solids, constructed in `ℝ³` -/

/-- **The five Platonic solids exist.** The tetrahedron, cube, octahedron, dodecahedron and
icosahedron, each the convex hull of explicit points with coordinates in `ℤ[φ]`
(`φ = Real.goldenRatio`), are regular polyhedra — 3-dimensional convex polytopes whose
isometries act transitively on flags — with the classical vertex, edge and facet counts and
face type `{s, m}`. The face lattices are computed by the kernel (`decide +kernel`). -/
theorem results_five_platonic_solids_constructed :
    (EulersGem.IsRegularPolyhedron EulersGem.Platonic3.tetrahedron ∧
      EulersGem.Platonic3.HasFaceData EulersGem.Platonic3.tetrahedron 4 6 4 3 3) ∧
    (EulersGem.IsRegularPolyhedron EulersGem.Platonic3.cube ∧
      EulersGem.Platonic3.HasFaceData EulersGem.Platonic3.cube 8 12 6 4 3) ∧
    (EulersGem.IsRegularPolyhedron EulersGem.Platonic3.octahedron ∧
      EulersGem.Platonic3.HasFaceData EulersGem.Platonic3.octahedron 6 12 8 3 4) ∧
    (EulersGem.IsRegularPolyhedron EulersGem.Platonic3.dodecahedron ∧
      EulersGem.Platonic3.HasFaceData EulersGem.Platonic3.dodecahedron 20 30 12 5 3) ∧
    (EulersGem.IsRegularPolyhedron EulersGem.Platonic3.icosahedron ∧
      EulersGem.Platonic3.HasFaceData EulersGem.Platonic3.icosahedron 12 30 20 3 5) :=
  EulersGem.Platonic3.five_platonic_solids_exist

/-- **The face data of a regular polyhedron — CONDITIONAL on `FaceLatticeFacts`.** A regular
polyhedron (flag-transitive convex 3-polytope in `ℝ³`) that satisfies the general
face-lattice facts `FaceLatticeFacts` has the counts `(V, E, F)` and type `{s, m}` of one of
the five Platonic solids. `FaceLatticeFacts` holds for every convex 3-polytope classically,
but that is **not proved** in this repository (it is the gap
`PlatonicGaps.GAP_faceLatticeFacts`); it is proved for the five constructed solids. This is
not uniqueness up to similarity. -/
theorem results_regular_polyhedron_face_data {P : Set EulersGem.R3}
    (hP : EulersGem.IsRegularPolyhedron P) (hL : EulersGem.FaceLatticeFacts P) :
    EulersGem.Platonic3.HasFaceData P 4 6 4 3 3 ∨
      EulersGem.Platonic3.HasFaceData P 8 12 6 4 3 ∨
      EulersGem.Platonic3.HasFaceData P 6 12 8 3 4 ∨
      EulersGem.Platonic3.HasFaceData P 20 30 12 5 3 ∨
      EulersGem.Platonic3.HasFaceData P 12 30 20 3 5 := by
  obtain ⟨t, ht, hd⟩ := hP.faceData hL
  simp only [EulersGem.platonicTypes, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl hd
  · exact Or.inr (Or.inl hd)
  · exact Or.inr (Or.inr (Or.inl hd))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hd)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hd)))

/-- **The five constructed solids are pairwise non-similar** (they have 4, 8, 6, 20 and 12
vertices), so a polyhedron is similar to at most one of them. -/
theorem results_platonic_solids_not_similar {i j : Fin 5} (hij : i ≠ j) :
    ¬ EulersGem.Similar (EulersGem.platonicSolid i) (EulersGem.platonicSolid j) :=
  EulersGem.platonic_not_similar hij

end Results
