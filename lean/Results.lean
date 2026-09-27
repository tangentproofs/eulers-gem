/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.Embed
import EulersGem.LatticeArea
import EulersGem.Platonic

/-!
# Paper-facing results

Three theorems, each proved in `EulersGem.*` and restated here:

* the Euler characteristic of a full-dimensional convex polytope,
* `V − E + F = 2` in dimension 3, from that characteristic,
* Pick's theorem for a strictly convex lattice polygon,
* the five Platonic solids: tetrahedron, cube, octahedron, dodecahedron, icosahedron.

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

/-- **Pick's theorem** for a strictly convex counterclockwise lattice polygon
with distinct vertices. If `S` is the set of interior lattice points, the
Lebesgue area of the convex hull is `I + B/2 − 1`, where `I = #S` and `B` is
the number of boundary lattice points. -/
theorem results_picks_theorem
    (P : EulersGem.Picks.LatticePolygon) (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hverts : Function.Injective P.vertex)
    (hsc : EulersGem.Picks.LatticeFan.StrictlyConvexCCW P) :
    MeasureTheory.volume P.convexHullRegion =
      ENNReal.ofReal ((S.card : ℚ) + (P.B : ℚ) / 2 - 1) :=
  EulersGem.Picks.LatticeArea.volume_eq_ofReal_cardI_add_B_div_two_sub_one_no_pe
    P S hS hverts hsc

/-! ## The five Platonic solids -/

/-- **The five Platonic solids** are the tetrahedron, the cube, the octahedron,
the dodecahedron, and the icosahedron. Each line is `(V, E, F, s, m)`: `s` sides
per face, `m` faces at each vertex. These five Schläfli pairs are all of them:
every combinatorially regular polyhedron, with `V − E + F = 2`, is one of these. -/
theorem results_five_platonic_solids :
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
        EulersGem.Platonic.icosahedron.m) = (12, 30, 20, 3, 5) ∧
      EulersGem.Platonic.schlafliPairs.card = 5 ∧
      (∀ R : EulersGem.Platonic.RegularNumbers,
        (R.s, R.m) ∈ EulersGem.Platonic.schlafliPairs) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, EulersGem.Platonic.card_schlafliPairs,
    fun R => EulersGem.Platonic.schlafli_pair_mem R⟩

end Results
