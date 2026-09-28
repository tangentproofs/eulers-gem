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

namespace Picks

open PlanarDiskEulerCounts

/-- Adding one diagonal: `E` and `F` each rise by `1`, so the disk Euler number
is unchanged. -/
theorem eulerChar_add_diagonal (V E F : ℕ) :
    ((V : ℤ) - ↑(E + 1) + ↑(F + 1)) = (V : ℤ) - ↑E + ↑F := by
  rw [Nat.cast_add, Nat.cast_add]
  omega

/-- Inserting one vertex in the interior of a boundary edge: `V` and `E` each
rise by `1`, `F` stays put. -/
theorem eulerChar_insert_boundary (V E F : ℕ) :
    (↑(V + 1) - ↑(E + 1) + (F : ℤ)) = (V : ℤ) - ↑E + (F : ℤ) := by
  rw [Nat.cast_add, Nat.cast_add]
  omega

/-- Stellar subdivision at an interior lattice point of one triangle: that
triangle is replaced by three, so `V + 1`, `E + 3`, `T + 2`. -/
theorem eulerChar_stellar (V E T : ℕ) :
    (↑(V + 1) - ↑(E + 3) + ↑(T + 2 + 1)) = (V : ℤ) - ↑E + ↑(T + 1) := by
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_add]
  omega

theorem eulerChar_add_diagonal_iter (d V E F : ℕ) :
    ((V : ℤ) - ↑(E + d) + ↑(F + d)) = (V : ℤ) - ↑E + ↑F := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hE : E + (d + 1) = (E + d) + 1 := by omega
    have hF : F + (d + 1) = (F + d) + 1 := by omega
    rw [hE, hF]
    exact (eulerChar_add_diagonal V (E + d) (F + d)).trans ih

theorem eulerChar_insert_boundary_iter (k V E F : ℕ) :
    (↑(V + k) - ↑(E + k) + (F : ℤ)) = (V : ℤ) - ↑E + (F : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hV : V + (k + 1) = (V + k) + 1 := by omega
    have hE : E + (k + 1) = (E + k) + 1 := by omega
    rw [hV, hE]
    exact (eulerChar_insert_boundary (V + k) (E + k) F).trans ih

theorem eulerChar_stellar_iter (i V E T : ℕ) :
    (↑(V + i) - ↑(E + 3 * i) + ↑(T + 2 * i + 1)) = (V : ℤ) - ↑E + ↑(T + 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hV : V + (i + 1) = (V + i) + 1 := by omega
    have hE : E + 3 * (i + 1) = (E + 3 * i) + 3 := by omega
    have hT : T + 2 * (i + 1) + 1 = (T + 2 * i) + 2 + 1 := by omega
    rw [hV, hE, hT]
    exact (eulerChar_stellar (V + i) (E + 3 * i) (T + 2 * i)).trans ih

/-- **Corner cycle, from the characteristic.** Deleting the `n − 3` diagonals of
a fan leaves the boundary `n`-cycle (`V = n`, `E = n`, one interior face and
the exterior face). Each deletion preserves the Euler number, which the fan
inherited from the triangle. -/
theorem corner_cycle_euler_from_characteristic (n : ℕ) (hn : 3 ≤ n) :
    (n : ℤ) - ↑n + 2 = 2 := by
  have hFan := FanDiskTriangulation.fan_eulerChar_from_characteristic n hn
  have hVc : ((FanDiskTriangulation.fan n hn).planarCounts).V =
      (FanDiskTriangulation.fan n hn).V := rfl
  have hEc : ((FanDiskTriangulation.fan n hn).planarCounts).E =
      (FanDiskTriangulation.fan n hn).E := rfl
  have hTc : ((FanDiskTriangulation.fan n hn).planarCounts).T =
      (FanDiskTriangulation.fan n hn).T := rfl
  have hF : ((FanDiskTriangulation.fan n hn).planarCounts).F = n - 1 := by
    rw [(FanDiskTriangulation.fan n hn).planarCounts.hF, hTc,
      FanDiskTriangulation.fan_T]
    omega
  have hFanEq : (n : ℤ) - ↑(2 * n - 3) + ↑(n - 1) = 2 := by
    have hchar :
        ((FanDiskTriangulation.fan n hn).planarCounts.V : ℤ) -
          (FanDiskTriangulation.fan n hn).planarCounts.E +
          (FanDiskTriangulation.fan n hn).planarCounts.F = 2 := hFan
    rw [hVc, hEc, FanDiskTriangulation.fan_V, FanDiskTriangulation.fan_E, hF] at hchar
    simpa [Nat.cast_sub (show 3 ≤ 2 * n by omega), Nat.cast_sub (show 1 ≤ n by omega),
      Nat.cast_mul] using hchar
  have hEq : (n : ℤ) - ↑n + 2 = (n : ℤ) - ↑(2 * n - 3) + ↑(n - 1) := by
    have hEn : (2 * n - 3 : ℕ) = n + (n - 3) := by omega
    have hFn : (n - 1 : ℕ) = 2 + (n - 3) := by omega
    rw [hEn, hFn, Nat.cast_add, Nat.cast_add]
    omega
  exact hEq.trans hFanEq

/-- **Triangulated disk, from the characteristic.** Start from the corner
`n`-cycle, insert `B − n` boundary vertices, add `B − 3` diagonals, then perform
`I` stellar subdivisions. The Euler number stays `2`, so the classical counts
`V = I + B`, `T = 2I + B − 2`, `E = 3I + 2B − 3` satisfy `V − E + F = 2`. -/
theorem triangulated_disk_euler_from_characteristic
    (n B I : ℕ) (hn : 3 ≤ n) (hB : n ≤ B) :
    ((I + B : ℕ) : ℤ) - ↑(3 * I + 2 * B - 3) + ↑(2 * I + B - 2 + 1) = 2 := by
  have hCycle := corner_cycle_euler_from_characteristic n hn
  have hIns : (↑B - ↑B + (2 : ℤ)) = (↑n - ↑n + (2 : ℤ)) := by
    have h := eulerChar_insert_boundary_iter (B - n) n n 2
    have hBn : n + (B - n) = B := by omega
    rw [hBn] at h
    exact h
  have hDiag : (↑B - ↑(2 * B - 3) + ↑(B - 1)) = (↑B - ↑B + (2 : ℤ)) := by
    have h := eulerChar_add_diagonal_iter (B - 3) B B 2
    have hE : B + (B - 3) = 2 * B - 3 := by omega
    have hF : 2 + (B - 3) = B - 1 := by omega
    rw [← hE, ← hF]
    exact h
  have hStar := eulerChar_stellar_iter I B (2 * B - 3) (B - 2)
  have hVI : I + B = B + I := by omega
  have hE : 3 * I + 2 * B - 3 = (2 * B - 3) + 3 * I := by omega
  have hT : 2 * I + B - 1 = (B - 2) + 2 * I + 1 := by omega
  have hBase : B - 1 = (B - 2) + 1 := by omega
  have hFcast : (2 * I + B - 2 + 1 : ℕ) = 2 * I + B - 1 := by omega
  rw [hFcast]
  calc
    ((I + B : ℕ) : ℤ) - ↑(3 * I + 2 * B - 3) + ↑(2 * I + B - 1)
        = ↑(B + I) - ↑((2 * B - 3) + 3 * I) + ↑((B - 2) + 2 * I + 1) := by
          rw [hVI, hE, hT]
    _ = ↑B - ↑(2 * B - 3) + ↑((B - 2) + 1) := hStar
    _ = ↑B - ↑(2 * B - 3) + ↑(B - 1) := by rw [← hBase]
    _ = ↑B - ↑B + (2 : ℤ) := hDiag
    _ = ↑n - ↑n + (2 : ℤ) := hIns
    _ = 2 := hCycle

/-- **Pick's count for any triangulated disk with those counts.** Area `T/2`
and the Euler number from `triangulated_disk_euler_from_characteristic` give
`I + B/2 − 1`. -/
theorem pick_count_of_disk_from_characteristic
    (n B I : ℕ) (A : ℚ) (hn : 3 ≤ n) (hB : n ≤ B)
    (harea : A = ((2 * I + B - 2 : ℕ) : ℚ) / 2) :
    A = (I : ℚ) + (B : ℚ) / 2 - 1 := by
  have hEuler := triangulated_disk_euler_from_characteristic n B I hn hB
  have hEcast : (3 * I + 2 * B - 3 : ℕ) = 3 * I + 2 * B - 3 := rfl
  have hT : (2 * I + B - 2 + 1 : ℕ) = 2 * I + B - 1 := by omega
  have hEuler' :
      ((I + B : ℕ) : ℤ) - ↑(3 * I + 2 * B - 3) + ↑(2 * I + B - 1) = 2 := by
    simpa [hT] using hEuler
  have hcount :=
    triangulation_count_identity_nat I B (I + B) (3 * I + 2 * B - 3)
      (2 * I + B - 2) (2 * I + B - 1) A
      (by omega) (by omega) hEuler' (by omega) harea
  exact hcount

end Picks

end EulersGem
