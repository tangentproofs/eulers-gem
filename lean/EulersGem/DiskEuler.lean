/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.FanDisk
import EulersGem.GeometricPlatonic
import EulersGem.Picks
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Planar disk Euler from the Euler characteristic

A convex polygon, as a full-dimensional polytope in the plane, has Euler
characteristic `1`: `V − E + 1 = 1`, counting the polygon itself as the unique
2-face. The disk obtained by adding the exterior face therefore satisfies
`V − E + F = 2`.

A combinatorial fan is that disk with diagonals added. Each diagonal raises the
edge count and the face count by one, so the Euler number is unchanged. The
triangle, the fan on three vertices, is a geometric 2-simplex, so its disk
Euler number is the characteristic. Every larger fan reduces to that triangle.
-/

open Finset
open scoped RealInnerProductSpace

namespace EulersGem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma faceEulerSum_two_expand (p : Set E) :
    faceEulerSum p 2 =
      ({f : Set E | IsFaceOf p f ∧ affDim f = 0}.ncard : ℤ) -
        ({f : Set E | IsFaceOf p f ∧ affDim f = 1}.ncard : ℤ) +
        ({f : Set E | IsFaceOf p f ∧ affDim f = 2}.ncard : ℤ) := by
  unfold faceEulerSum
  rw [show range 3 = ({0, 1, 2} : Finset ℕ) from by decide]
  simp [Finset.sum_insert, Finset.sum_singleton, pow_succ]
  ring

/-- **Disk Euler from the characteristic.** If a set has Euler characteristic `1`
through dimension `2` and a unique 2-face, then counting one exterior face as
well gives `V − E + F = 2`. -/
theorem diskEuler_of_faceEulerSum (p : Set E)
    (hsum : faceEulerSum p 2 = 1)
    (hTop : ({f : Set E | IsFaceOf p f ∧ affDim f = 2}.ncard) = 1) :
    ({f : Set E | IsFaceOf p f ∧ affDim f = 0}.ncard : ℤ) -
        ({f : Set E | IsFaceOf p f ∧ affDim f = 1}.ncard : ℤ) +
        (({f : Set E | IsFaceOf p f ∧ affDim f = 2}.ncard) + 1) = 2 := by
  have hexpand := faceEulerSum_two_expand p
  rw [hexpand, hTop, Nat.cast_one] at hsum
  omega

section Triangle

variable [FiniteDimensional ℝ E] [Nonempty E]

/-- **A geometric triangle has disk Euler number `2`.** The triangle is a
2-simplex, so `faceEulerSum = 1` by `Euler_Poincare_full`. It has three
vertices, three edges, and one 2-face; the exterior face makes `3 − 3 + 2 = 2`. -/
theorem triangle_disk_euler (b : AffineBasis (Fin 3) ℝ E) :
    ((Platonic.facesOfDim (Simplex.body b) 0).ncard : ℤ) -
        (Platonic.facesOfDim (Simplex.body b) 1).ncard +
        ((Platonic.facesOfDim (Simplex.body b) 2).ncard + 1) = 2 := by
  have hcard : Module.finrank ℝ E + 1 = 3 := by
    simpa using b.card_eq_finrank_add_one
  have hfin : Module.finrank ℝ E = 2 := by omega
  have hsum := Simplex.faceEulerSum_body_eq_one b (by omega)
  rw [hfin] at hsum
  have hTop : (Platonic.facesOfDim (Simplex.body b) ((2 : ℕ) : ℤ)).ncard = 1 := by
    rw [Simplex.ncard_facesOfDim_body_eq_choose b 2]
    simp [Fintype.card_fin]
  exact diskEuler_of_faceEulerSum (Simplex.body b) hsum (by
    simpa [Platonic.facesOfDim] using hTop)

end Triangle

/-- Every 2-dimensional real inner product space contains a geometric triangle. -/
theorem exists_triangle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 2) :
    Nonempty (AffineBasis (Fin 3) ℝ E) :=
  AffineBasis.exists_affineBasis_of_finiteDimensional (ι := Fin 3) (k := ℝ) (V := E) (P := E)
    (by simp [hE, Fintype.card_fin])

namespace Picks.FanDiskTriangulation

lemma fan_eulerChar_succ (k : ℕ) (hk : 3 ≤ k) :
    ((fan (k + 1) (by omega)).planarCounts).eulerChar =
      ((fan k hk).planarCounts).eulerChar := by
  have hF (m : ℕ) (hm : 3 ≤ m) :
      ((fan m hm).planarCounts).F = (fan m hm).T + 1 :=
    (fan m hm).planarCounts.hF
  have hV (m : ℕ) (hm : 3 ≤ m) : ((fan m hm).planarCounts).V = (fan m hm).V := rfl
  have hE (m : ℕ) (hm : 3 ≤ m) : ((fan m hm).planarCounts).E = (fan m hm).E := rfl
  simp only [PlanarDiskEulerCounts.eulerChar]
  rw [hF (k + 1) (by omega), hF k hk, hV (k + 1) (by omega), hV k hk,
    hE (k + 1) (by omega), hE k hk, fan_V, fan_V, fan_E, fan_E, fan_T, fan_T]
  omega

/-- **Every fan has disk Euler number `2`, from the characteristic.** The fan on
three vertices has the same `(V, E, F)` as a geometric triangle with its
exterior face, and that number is `2` by `triangle_disk_euler`. Adding a vertex
to a fan adds one vertex, two edges, and one face, which preserves the Euler
number. -/
theorem fan_eulerChar_from_characteristic (n : ℕ) (hn : 3 ≤ n) :
    ((fan n hn).planarCounts).eulerChar = 2 := by
  let E2 := EuclideanSpace ℝ (Fin 2)
  have hE : Module.finrank ℝ E2 = 2 := finrank_euclideanSpace_fin
  obtain ⟨b⟩ := exists_triangle (E := E2) hE
  have hTri : ((fan 3 (by omega)).planarCounts).eulerChar = 2 := by
    have h0 : (Platonic.facesOfDim (Simplex.body b) 0).ncard = 3 := by
      simpa [Fintype.card_fin] using Simplex.ncard_facesOfDim_body_eq_choose b 0
    have h1 : (Platonic.facesOfDim (Simplex.body b) 1).ncard = 3 := by
      simpa [Fintype.card_fin] using Simplex.ncard_facesOfDim_body_eq_choose b 1
    have h2 : (Platonic.facesOfDim (Simplex.body b) 2).ncard = 1 := by
      simpa [Fintype.card_fin] using Simplex.ncard_facesOfDim_body_eq_choose b 2
    have hFan :
        ((fan 3 (by omega)).planarCounts).eulerChar =
          ((Platonic.facesOfDim (Simplex.body b) 0).ncard : ℤ) -
            (Platonic.facesOfDim (Simplex.body b) 1).ncard +
            ((Platonic.facesOfDim (Simplex.body b) 2).ncard + 1) := by
      have hF : ((fan 3 (by omega)).planarCounts).F = (fan 3 (by omega)).T + 1 :=
        (fan 3 (by omega)).planarCounts.hF
      have hV : ((fan 3 (by omega)).planarCounts).V = (fan 3 (by omega)).V := rfl
      have hE : ((fan 3 (by omega)).planarCounts).E = (fan 3 (by omega)).E := rfl
      simp only [PlanarDiskEulerCounts.eulerChar]
      rw [hF, hV, hE, fan_V, fan_E, fan_T, h0, h1, h2]
      norm_num
    exact hFan.trans (triangle_disk_euler b)
  refine Nat.le_induction hTri ?step n hn
  intro k hk ih
  rw [fan_eulerChar_succ k hk, ih]

/-- **Pick's count for an empty fan, from the characteristic.** The fan is a
triangulation with `I = 0`, `B = n`, `T = n − 2`, and area `T/2`. Its
`V − E + F = 2` is `fan_eulerChar_from_characteristic`, so
`T/2 = n/2 − 1`. -/
theorem fan_pick_count_from_characteristic (n : ℕ) (hn : 3 ≤ n) :
    ((n - 2 : ℕ) : ℚ) / 2 = (n : ℚ) / 2 - 1 := by
  have hEul := fan_eulerChar_from_characteristic n hn
  have hVc : ((fan n hn).planarCounts).V = (fan n hn).V := rfl
  have hEc : ((fan n hn).planarCounts).E = (fan n hn).E := rfl
  have hTc : ((fan n hn).planarCounts).T = (fan n hn).T := rfl
  have hF : ((fan n hn).planarCounts).F = n - 1 := by
    rw [(fan n hn).planarCounts.hF, hTc, fan_T]
    omega
  have hEuler : (n : ℤ) - ↑(2 * n - 3) + ↑(n - 1) = 2 := by
    have hchar :
        ((fan n hn).planarCounts.V : ℤ) - (fan n hn).planarCounts.E +
          (fan n hn).planarCounts.F = 2 := hEul
    rw [hVc, hEc, fan_V, fan_E, hF] at hchar
    simpa [Nat.cast_sub (show 3 ≤ 2 * n by omega), Nat.cast_sub (show 1 ≤ n by omega),
      Nat.cast_mul] using hchar
  have hcount :=
    triangulation_count_identity_nat 0 n n (2 * n - 3) (n - 2) (n - 1)
      (((n - 2 : ℕ) : ℚ) / 2)
      (by omega) (by omega) hEuler (by omega) rfl
  simpa using hcount

end Picks.FanDiskTriangulation

end EulersGem
