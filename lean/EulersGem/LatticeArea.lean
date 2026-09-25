/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Measure
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import EulersGem.LatticeTriangle
import EulersGem.LatticePolygon
import EulersGem.LatticeFan
import EulersGem.LatticeFanInterior
import EulersGem.LatticeFanTrianglePick

/-!
# Lattice triangle Haar area bridge (not classical Pick)

Lebesgue / Haar on `ℝ × ℝ`:
* `(Basis.finTwoProd ℝ).addHaar = volume`
* parallelepiped volume = `|det|`
* unit triangle volume = `1/2`
* origin triangle volume = `|det|/2`
* lattice shoelace `ℚ` coerces to `|latticeDet|/2` as `ℝ`
* arbitrary lattice triangle volume = `ofReal(triangleShoelace)`
  (translate to origin + origin theorem)

Also: `trianglePolygon` volume = `ofReal(shoelace)`; fan triangle volumes sum to
`ofReal(P.shoelace)` under `FanDetsNonneg`; under `StrictlyConvexCCW` + injective
vertices, `P.convexHullRegion = ⋃ᵢ fanTriangleRegion i`; pairwise AEDisjoint of
fan ears (shared spokes Haar-null); `volume(P) = ∑ volume(ears) = ofReal(shoelace)`,
discharging `hvol`; compose with combinatorial Pick-form.
**Not** classical Pick — see `PICKS_CLAUDE_AUDIT.md`.
-/

open MeasureTheory Measure Module Set Matrix
open scoped Pointwise

namespace EulersGem
namespace Picks
namespace LatticeArea

noncomputable section

abbrev V := ℝ × ℝ

/-! ## Standard Haar = product Lebesgue -/

lemma parallelepiped_finTwoProd :
    (↑(Basis.finTwoProd ℝ).parallelepiped : Set V) =
      Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  ext x
  rw [Basis.coe_parallelepiped, parallelepiped_basis_eq]
  simp only [Basis.coe_finTwoProd_repr, mem_ofPred_eq, mem_prod, mem_Icc,
    Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]

lemma finTwoProd_addHaar_eq_volume :
    (Basis.finTwoProd ℝ).addHaar = (volume : Measure V) := by
  have : IsAddLeftInvariant (volume : Measure V) := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [Basis.addHaar_eq_iff, parallelepiped_finTwoProd,
    Measure.volume_eq_prod, Measure.prod_prod]
  simp [Real.volume_Icc]

lemma finTwoProd_det (u v : V) :
    (Basis.finTwoProd ℝ).det ![u, v] = u.1 * v.2 - u.2 * v.1 := by
  rw [Basis.det_apply, det_fin_two]
  simp [Basis.toMatrix_apply, Basis.coe_finTwoProd_repr]; ring

theorem volume_parallelepiped_eq_ofReal_abs_det (u v : V) :
    volume (parallelepiped ![u, v]) = ENNReal.ofReal |u.1 * v.2 - u.2 * v.1| := by
  have h := addHaar_parallelepiped (Basis.finTwoProd ℝ) ![u, v]
  rwa [finTwoProd_addHaar_eq_volume, finTwoProd_det] at h

/-! ## Unit triangle volume = 1/2 -/

def unitTriangleCoords : Set V :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

lemma measurableSet_unitTriangleCoords : MeasurableSet unitTriangleCoords := by
  have h1 : MeasurableSet {p : V | 0 ≤ p.1} := measurable_fst measurableSet_Ici
  have h2 : MeasurableSet {p : V | 0 ≤ p.2} := measurable_snd measurableSet_Ici
  have h3 : MeasurableSet {p : V | p.1 + p.2 ≤ 1} :=
    (continuous_fst.add continuous_snd).measurable measurableSet_Iic
  simpa [unitTriangleCoords, ofPred_and] using h1.inter (h2.inter h3)

lemma volume_fiber_unitTriangleCoords (x : ℝ) :
    volume (Prod.mk x ⁻¹' unitTriangleCoords) =
      if 0 ≤ x ∧ x ≤ 1 then ENNReal.ofReal (1 - x) else 0 := by
  change volume {y : ℝ | 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1} = _
  by_cases hx0 : 0 ≤ x
  · by_cases hx1 : x ≤ 1
    · have hset : {y : ℝ | 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1} = Icc 0 (1 - x) := by
        ext y; simp only [mem_ofPred_eq, mem_Icc]
        exact ⟨fun ⟨_, hy0, hxy⟩ => ⟨hy0, by linarith⟩,
               fun ⟨hy0, hy1⟩ => ⟨hx0, hy0, by linarith⟩⟩
      rw [ite_eq_left ⟨hx0, hx1⟩, hset, Real.volume_Icc]; simp
    · have hset : {y : ℝ | 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1} = ∅ := by
        ext y; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro ⟨_, hy0, hxy⟩; linarith
      rw [ite_eq_right (fun h => hx1 h.2), hset, measure_empty]
  · have hset : {y : ℝ | 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1} = ∅ := by
      ext y; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro ⟨hx0', _, _⟩; exact hx0 hx0'
    rw [ite_eq_right (fun h => hx0 h.1), hset, measure_empty]

private lemma integral_one_sub :
    ∫ x in (0 : ℝ)..1, (1 - x) = (1 : ℝ) / 2 := by
  have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
    intervalIntegrable_const
  have h2 : IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
    Continuous.intervalIntegrable continuous_id 0 1
  calc ∫ x in (0 : ℝ)..1, (1 - x)
      = (∫ x in (0 : ℝ)..1, (1 : ℝ)) - ∫ x in (0 : ℝ)..1, x :=
          intervalIntegral.integral_sub h1 h2
    _ = (1 - 0 : ℝ) • (1 : ℝ) - (1 ^ 2 - 0 ^ 2) / 2 := by
          rw [intervalIntegral.integral_const, integral_id]
    _ = 1 / 2 := by norm_num

theorem volume_unitTriangleCoords :
    volume unitTriangleCoords = ENNReal.ofReal (1 / 2) := by
  have hvol : (volume : Measure V) = (volume : Measure ℝ).prod (volume : Measure ℝ) :=
    Measure.volume_eq_prod _ _
  rw [hvol, Measure.prod_apply measurableSet_unitTriangleCoords]
  have hcongr :
      (fun x => volume (Prod.mk x ⁻¹' unitTriangleCoords)) =ᵐ[volume]
        (Icc (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (1 - x)) := by
    filter_upwards with x
    rw [volume_fiber_unitTriangleCoords x]
    by_cases hx : 0 ≤ x ∧ x ≤ 1
    · rw [ite_eq_left hx, indicator_of_mem (Iff.mpr mem_Icc ⟨hx.1, hx.2⟩)]
    · rw [ite_eq_right hx, indicator_of_notMem (by simpa [mem_Icc] using hx)]
  rw [lintegral_congr_ae hcongr, lintegral_indicator measurableSet_Icc]
  have hint : IntegrableOn (fun x : ℝ => (1 : ℝ) - x) (Icc 0 1) :=
    (continuous_const.sub continuous_id).continuousOn.integrableOn_compact isCompact_Icc
  have hnonneg : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) 1), 0 ≤ ((1 : ℝ) - x) :=
    (ae_restrict_iff' measurableSet_Icc).2 <| .of_forall fun x hx => sub_nonneg.mpr hx.2
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  congr 1
  have : NullSingletonClass (volume : Measure ℝ) := inferInstance
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact integral_one_sub

def unitTriangle : Set V :=
  convexHull ℝ ({(0 : V), (1, 0), (0, 1)} : Set V)

lemma mem_unitTriangle_iff (p : V) :
    p ∈ unitTriangle ↔ 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1 := by
  constructor
  · intro hp
    rw [unitTriangle, convexHull_eq] at hp
    obtain ⟨ι, t, w, z, hw0, hw1, hz, rfl⟩ := hp
    have hz' : ∀ i ∈ t, z i = (0 : V) ∨ z i = (1, 0) ∨ z i = (0, 1) := by
      intro i hi; simpa using hz i hi
    have hcm : t.centerMass w z = ∑ i ∈ t, w i • z i :=
      Finset.centerMass_eq_of_sum_1 _ _ hw1
    rw [hcm]
    refine ⟨?_, ?_, ?_⟩
    · rw [Prod.fst_sum]
      refine Finset.sum_nonneg fun i hi => ?_
      simp only [Prod.smul_def, smul_eq_mul]
      exact mul_nonneg (hw0 i hi) (by rcases hz' i hi with h | h | h <;> simp [h])
    · rw [Prod.snd_sum]
      refine Finset.sum_nonneg fun i hi => ?_
      simp only [Prod.smul_def, smul_eq_mul]
      exact mul_nonneg (hw0 i hi) (by rcases hz' i hi with h | h | h <;> simp [h])
    · have hf : (∑ i ∈ t, w i • z i).1 = ∑ i ∈ t, w i * (z i).1 := by
        simp [Prod.fst_sum, Prod.smul_def]
      have hs : (∑ i ∈ t, w i • z i).2 = ∑ i ∈ t, w i * (z i).2 := by
        simp [Prod.snd_sum, Prod.smul_def]
      rw [hf, hs, ← Finset.sum_add_distrib]; simp_rw [← mul_add]
      have hle : ∀ i ∈ t, (z i).1 + (z i).2 ≤ (1 : ℝ) := by
        intro i hi; rcases hz' i hi with h | h | h <;> simp [h]
      calc
        ∑ i ∈ t, w i * ((z i).1 + (z i).2)
            ≤ ∑ i ∈ t, w i * 1 :=
          Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_left (hle i hi) (hw0 i hi)
        _ = ∑ i ∈ t, w i := by simp
        _ = 1 := hw1
  · intro ⟨h1, h2, h3⟩
    exact mem_convexHull_of_exists_fintype
      (w := ![1 - p.1 - p.2, p.1, p.2])
      (z := ![(0 : V), (1, 0), (0, 1)])
      (by intro i; fin_cases i <;> simp <;> linarith)
      (by simp [Fin.sum_univ_three]; ring)
      (by intro i; fin_cases i <;> simp)
      (by simp [Fin.sum_univ_three, Prod.smul_def]; try ring)

lemma unitTriangle_eq_coords : unitTriangle = unitTriangleCoords := by
  ext p; simpa [unitTriangleCoords] using (mem_unitTriangle_iff p)

theorem volume_unitTriangle :
    volume unitTriangle = ENNReal.ofReal (1 / 2) := by
  rw [unitTriangle_eq_coords, volume_unitTriangleCoords]

/-! ## Origin triangle = linear image of unit triangle -/

def basisMap (u v : V) : V →ₗ[ℝ] V :=
  (Basis.finTwoProd ℝ).constr ℕ ![u, v]

lemma det_basisMap_eq_finTwoProd_det (u v : V) :
    LinearMap.det (basisMap u v) = (Basis.finTwoProd ℝ).det ![u, v] := by
  let b := Basis.finTwoProd ℝ
  let f : V →ₗ[ℝ] V := basisMap u v
  have h1 : LinearMap.det f = (LinearMap.toMatrix b b f).det :=
    LinearMap.det_toMatrix b f |>.symm
  have h2 : LinearMap.toMatrix b b f = b.toMatrix ![u, v] :=
    (Basis.toMatrix_eq_toMatrix_constr b ![u, v]).symm
  rw [h1, h2, Basis.det_apply]

lemma image_basisMap_unitPts (u v : V) :
    basisMap u v '' ({(0 : V), (1, 0), (0, 1)} : Set V) =
      ({(0 : V), u, v} : Set V) := by
  ext p
  constructor
  · intro ⟨q, hq, hqeq⟩
    have hq' : q = 0 ∨ q = (1, 0) ∨ q = (0, 1) := by
      simpa [mem_insert_iff, mem_singleton_iff] using hq
    rcases hq' with rfl | rfl | rfl <;> simp [← hqeq, basisMap]
  · intro hp
    have hp' : p = 0 ∨ p = u ∨ p = v := by
      simpa [mem_insert_iff, mem_singleton_iff] using hp
    rcases hp' with rfl | rfl | rfl
    · exact ⟨0, by simp, by simp [basisMap]⟩
    · exact ⟨(1, 0), by simp, by simp [basisMap]⟩
    · exact ⟨(0, 1), by simp, by simp [basisMap]⟩

lemma image_basisMap_unitTriangle (u v : V) :
    basisMap u v '' unitTriangle =
      convexHull ℝ ({(0 : V), u, v} : Set V) := by
  rw [unitTriangle, LinearMap.image_convexHull, image_basisMap_unitPts]

/-- Origin-triangle Haar volume equals `|det(u,v)|/2`. -/
theorem volume_convexHull_origin_triangle (u v : V) :
    volume (convexHull ℝ ({(0 : V), u, v} : Set V)) =
      ENNReal.ofReal (|u.1 * v.2 - u.2 * v.1| / 2) := by
  have : IsAddHaarMeasure (volume : Measure V) := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [← image_basisMap_unitTriangle,
    Measure.addHaar_image_linearMap volume (basisMap u v) unitTriangle,
    volume_unitTriangle, det_basisMap_eq_finTwoProd_det, finTwoProd_det]
  have hnonneg : (0 : ℝ) ≤ |u.1 * v.2 - u.2 * v.1| := abs_nonneg _
  rw [← ENNReal.ofReal_mul hnonneg]
  congr 1; ring

/-! ## Lattice shoelace as ℝ and Haar of an arbitrary lattice triangle -/

open LatticeTriangle

lemma toReal_sub (p q : ℤ × ℤ) : toReal (p - q) = toReal p - toReal q := by
  cases p; cases q
  simp [LatticeTriangle.toReal, Prod.sub_def]

lemma latticeDet_coe_eq_real_cross (a b c : ℤ × ℤ) :
    (latticeDet a b c : ℝ) =
      (toReal (b - a)).1 * (toReal (c - a)).2 -
        (toReal (b - a)).2 * (toReal (c - a)).1 := by
  cases a; cases b; cases c
  simp [latticeDet, LatticeTriangle.toReal, Prod.sub_def]

/-- Combinatorial shoelace `ℚ` coerces to `|latticeDet|/2` as `ℝ`. -/
theorem triangleShoelace_coe_eq_abs_det_div_two (a b c : ℤ × ℤ) :
    (triangleShoelace a b c : ℝ) = |(latticeDet a b c : ℝ)| / 2 := by
  simp only [triangleShoelace, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  rw [Nat.cast_natAbs, Int.cast_abs]

lemma triangleShoelace_nonneg (a b c : ℤ × ℤ) :
    0 ≤ (triangleShoelace a b c : ℝ) := by
  rw [triangleShoelace_coe_eq_abs_det_div_two]; positivity

lemma ofReal_triangleShoelace_eq_ofReal_abs_det_div_two (a b c : ℤ × ℤ) :
    ENNReal.ofReal (triangleShoelace a b c) =
      ENNReal.ofReal (|(latticeDet a b c : ℝ)| / 2) := by
  rw [← triangleShoelace_coe_eq_abs_det_div_two]

private lemma neg_toReal_add_eq_toReal_sub (a b : ℤ × ℤ) :
    -toReal a + toReal b = toReal (b - a) := by
  rw [toReal_sub, sub_eq_add_neg, add_comm]

lemma vadd_neg_triangle_pts (a b c : ℤ × ℤ) :
    (-toReal a) +ᵥ ({toReal a, toReal b, toReal c} : Set V) =
      ({(0 : V), toReal (b - a), toReal (c - a)} : Set V) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hq' : q = toReal a ∨ q = toReal b ∨ q = toReal c := by
      simpa [mem_insert_iff, mem_singleton_iff] using hq
    rcases hq' with rfl | rfl | rfl
    · simp [vadd_eq_add]
    · simp [vadd_eq_add, neg_toReal_add_eq_toReal_sub]
    · simp [vadd_eq_add, neg_toReal_add_eq_toReal_sub]
  · intro hp
    have hp' : p = (0 : V) ∨ p = toReal (b - a) ∨ p = toReal (c - a) := by
      simpa [mem_insert_iff, mem_singleton_iff] using hp
    rcases hp' with rfl | rfl | rfl
    · exact ⟨toReal a, by simp, by simp [vadd_eq_add]⟩
    · exact ⟨toReal b, by simp, by simp [vadd_eq_add, neg_toReal_add_eq_toReal_sub]⟩
    · exact ⟨toReal c, by simp, by simp [vadd_eq_add, neg_toReal_add_eq_toReal_sub]⟩

lemma convexHull_triangle_translate (a b c : ℤ × ℤ) :
    (-toReal a) +ᵥ convexHull ℝ ({toReal a, toReal b, toReal c} : Set V) =
      convexHull ℝ ({(0 : V), toReal (b - a), toReal (c - a)} : Set V) := by
  rw [← convexHull_vadd, vadd_neg_triangle_pts]

/-- Translation invariance of Lebesgue measure on `ℝ × ℝ`. -/
lemma volume_vadd (x : V) (s : Set V) :
    volume (x +ᵥ s) = volume s := by
  have : IsAddLeftInvariant (volume : Measure V) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have h : x +ᵥ s = (fun y : V => (-x) + y) ⁻¹' s := by
    ext z
    simp only [mem_vadd_set, mem_preimage, vadd_eq_add]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [add_assoc, neg_add_cancel, zero_add] using hy
    · intro hz
      refine ⟨(-x) + z, hz, ?_⟩
      abel
  rw [h, measure_preimage_add]

/-- Arbitrary lattice triangle Haar volume equals combinatorial shoelace. -/
theorem volume_convexHull_lattice_triangle (a b c : ℤ × ℤ) :
    volume (convexHull ℝ ({toReal a, toReal b, toReal c} : Set V)) =
      ENNReal.ofReal (triangleShoelace a b c) := by
  have htrans :=
    volume_vadd (-toReal a) (convexHull ℝ ({toReal a, toReal b, toReal c} : Set V))
  rw [← htrans, convexHull_triangle_translate, volume_convexHull_origin_triangle,
    ofReal_triangleShoelace_eq_ofReal_abs_det_div_two]
  congr 2
  exact congrArg abs (latticeDet_coe_eq_real_cross a b c).symm

/-! ## trianglePolygon bridge -/

open LatticeFan
open LatticeFan.InteriorFan

lemma shoelace_trianglePolygon_eq_triangleShoelace (a b c : ℤ × ℤ) :
    (trianglePolygon a b c).shoelace = triangleShoelace a b c := by
  simp [LatticePolygon.shoelace, triangleShoelace, shoelaceSum_trianglePolygon]

/-- `trianglePolygon` convex hull has Haar volume equal to its combinatorial shoelace. -/
theorem volume_convexHull_trianglePolygon (a b c : ℤ × ℤ) :
    volume (trianglePolygon a b c).convexHullRegion =
      ENNReal.ofReal (trianglePolygon a b c).shoelace := by
  rw [trianglePolygon_convexHullRegion, shoelace_trianglePolygon_eq_triangleShoelace,
    volume_convexHull_lattice_triangle]

/-! ## Polygon shoelace as ℝ + fan ear volume sum -/

theorem shoelace_coe_eq_abs_shoelaceSum_div_two (P : LatticePolygon) :
    (P.shoelace : ℝ) = |(P.shoelaceSum : ℝ)| / 2 := by
  simp only [LatticePolygon.shoelace, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  rw [Nat.cast_natAbs, Int.cast_abs]

lemma volume_fanTriangle (P : LatticePolygon) (i : ℕ) (hi : i < P.nVertices - 2) :
    volume (convexHull ℝ
        ({toReal (fanTriangle P i hi).a,
          toReal (fanTriangle P i hi).b,
          toReal (fanTriangle P i hi).c} : Set V)) =
      ENNReal.ofReal (fanTriangle P i hi).shoelace :=
  volume_convexHull_lattice_triangle _ _ _

/-- Under nonneg fan dets, summed fan-ear Haar volumes equal `ofReal(P.shoelace)`.

Does **not** yet identify `volume(P.convexHullRegion)` with this sum — hull-union
almost-disjointness remains open. -/
theorem sum_volume_fanTriangles_eq_ofReal_shoelace
    (P : LatticePolygon) (hnn : FanDetsNonneg P)
    (hverts : Function.Injective P.vertex) :
    (∑ t ∈ fanTriangles P,
        volume (convexHull ℝ ({toReal t.a, toReal t.b, toReal t.c} : Set V))) =
      ENNReal.ofReal P.shoelace := by
  have hsum := shoelace_eq_sum_fan_shoelace P hnn hverts
  have hterm : ∀ t ∈ fanTriangles P,
      volume (convexHull ℝ ({toReal t.a, toReal t.b, toReal t.c} : Set V)) =
        ENNReal.ofReal t.shoelace := fun t _ =>
    volume_convexHull_lattice_triangle t.a t.b t.c
  have hvol :
      (∑ t ∈ fanTriangles P,
          volume (convexHull ℝ ({toReal t.a, toReal t.b, toReal t.c} : Set V))) =
        ∑ t ∈ fanTriangles P, ENNReal.ofReal t.shoelace :=
    Finset.sum_congr rfl hterm
  rw [hvol]
  have hnonneg : ∀ t ∈ fanTriangles P, 0 ≤ (t.shoelace : ℝ) := fun t _ =>
    triangleShoelace_nonneg t.a t.b t.c
  rw [← ENNReal.ofReal_sum_of_nonneg hnonneg]
  congr 1
  rw [← Rat.cast_sum, hsum]

/-- Conditional compose: if polygon Haar equals shoelace, combinatorial Pick-form
lifts to a volume identity. Not classical Pick (hyp `hvol` / EP open). -/
theorem volume_eq_ofReal_cardI_add_B_div_two_sub_one_of_shoelace
    (P : LatticePolygon) (S : Finset (ℤ × ℤ))
    (hvol : volume P.convexHullRegion = ENNReal.ofReal P.shoelace)
    (hcomb : P.shoelace = (S.card : ℚ) + (P.B : ℚ) / 2 - 1) :
    volume P.convexHullRegion =
      ENNReal.ofReal ((S.card : ℚ) + (P.B : ℚ) / 2 - 1) := by
  rw [hvol, hcomb]; norm_cast

/-! ## Fan triangle regions (convex hulls of ears) -/

/-- Euclidean region of fan ear `i`. -/
def fanTriangleRegion (P : LatticePolygon) (i : ℕ) (hi : i < P.nVertices - 2) : Set V :=
  convexHull ℝ
    ({toReal (fanTriangle P i hi).a,
      toReal (fanTriangle P i hi).b,
      toReal (fanTriangle P i hi).c} : Set V)

lemma fanTriangleRegion_eq_convexHull_trianglePolygon
    (P : LatticePolygon) (i : ℕ) (hi : i < P.nVertices - 2) :
    fanTriangleRegion P i hi =
      (trianglePolygon (fanTriangle P i hi).a (fanTriangle P i hi).b
        (fanTriangle P i hi).c).convexHullRegion := by
  rw [fanTriangleRegion, trianglePolygon_convexHullRegion]

/-- Each fan-ear region sits inside the polygon convex hull. -/
theorem fanTriangleRegion_subset_convexHullRegion
    (P : LatticePolygon) (i : ℕ) (hi : i < P.nVertices - 2) :
    fanTriangleRegion P i hi ⊆ P.convexHullRegion := by
  intro p hp
  have hv := fanTriangle_vertices_mem_vertexFinset P i hi
  have hsub :
      ({toReal (fanTriangle P i hi).a,
        toReal (fanTriangle P i hi).b,
        toReal (fanTriangle P i hi).c} : Set V) ⊆
        toReal '' (P.vertexFinset : Set (ℤ × ℤ)) := by
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem_image_of_mem toReal hv.1
    · exact mem_image_of_mem toReal hv.2.1
    · exact mem_image_of_mem toReal hv.2.2
  have : p ∈ convexHull ℝ (toReal '' (P.vertexFinset : Set (ℤ × ℤ))) :=
    (convexHull_mono hsub) hp
  simpa [LatticePolygon.convexHullRegion] using this

/-! ## Real half-planes + barycentric triangle membership -/

lemma detR_area_sum (a b c p : V) :
    detR a b c = detR b c p + detR a p c + detR a b p := by
  dsimp [detR]; ring

lemma detR_swap_right' (a b c : V) : detR a b c = -detR a c b := by
  dsimp [detR]; ring

lemma detR_cycle (a b c : V) : detR a b c = detR b c a := by
  dsimp [detR]; ring

lemma detR_swap_first (a b c : V) : detR a b c = -detR b a c := by
  calc
    detR a b c = detR b c a := detR_cycle a b c
    _ = -detR b a c := detR_swap_right' b c a

lemma detR_barycentric_x (a b c p : V) :
    detR a b c * p.1 =
      detR b c p * a.1 + detR a p c * b.1 + detR a b p * c.1 := by
  dsimp [detR]; ring

lemma detR_barycentric_y (a b c p : V) :
    detR a b c * p.2 =
      detR b c p * a.2 + detR a p c * b.2 + detR a b p * c.2 := by
  dsimp [detR]; ring

/-- Oriented areas nonneg ⇒ point lies in the Euclidean triangle. -/
theorem mem_convexHull_of_detR_nonneg (a b c p : V)
    (hD : 0 < detR a b c)
    (hα : 0 ≤ detR b c p)
    (hβ : 0 ≤ detR a p c)
    (hγ : 0 ≤ detR a b p) :
    p ∈ convexHull ℝ ({a, b, c} : Set V) := by
  set α : ℝ := detR b c p / detR a b c
  set β : ℝ := detR a p c / detR a b c
  set γ : ℝ := detR a b p / detR a b c
  have hD0 : detR a b c ≠ 0 := ne_of_gt hD
  have hα0 : 0 ≤ α := div_nonneg hα (le_of_lt hD)
  have hβ0 : 0 ≤ β := div_nonneg hβ (le_of_lt hD)
  have hγ0 : 0 ≤ γ := div_nonneg hγ (le_of_lt hD)
  have hsum : α + β + γ = 1 := by
    dsimp [α, β, γ]
    have : (detR b c p + detR a p c + detR a b p) / detR a b c = 1 := by
      rw [← detR_area_sum a b c p, div_self hD0]
    convert this using 1; ring
  have heq : α • a + β • b + γ • c = p := by
    apply Prod.ext
    · change α * a.1 + β * b.1 + γ * c.1 = p.1
      dsimp [α, β, γ]
      have hid := detR_barycentric_x a b c p
      have :
          (detR b c p * a.1 + detR a p c * b.1 + detR a b p * c.1) / detR a b c =
            p.1 := by
        calc
          _ = (detR a b c * p.1) / detR a b c := by congr 1; linarith
          _ = p.1 := by field_simp [hD0]
      convert this using 1; ring
    · change α * a.2 + β * b.2 + γ * c.2 = p.2
      dsimp [α, β, γ]
      have hid := detR_barycentric_y a b c p
      have :
          (detR b c p * a.2 + detR a p c * b.2 + detR a b p * c.2) / detR a b c =
            p.2 := by
        calc
          _ = (detR a b c * p.2) / detR a b c := by congr 1; linarith
          _ = p.2 := by field_simp [hD0]
      convert this using 1; ring
  refine mem_convexHull_of_exists_fintype
    (w := ![α, β, γ]) (z := ![a, b, c]) ?_ ?_ ?_ ?_
  · intro i; fin_cases i <;> simp [hα0, hβ0, hγ0]
  · simp [Fin.sum_univ_three, hsum]
  · intro i; fin_cases i <;> simp
  · simpa [Fin.sum_univ_three] using heq

/-- Hull points lie weakly left of every directed edge (real form). -/
theorem detR_edge_nonneg_of_ConvexCCW_of_mem_hull
    (P : LatticePolygon) (h : ConvexCCW P) {p : V}
    (hp : p ∈ P.convexHullRegion) (i : Fin P.nVertices) :
    0 ≤ detR (toReal (P.vertex i)) (toReal (P.vertex (P.nextIdx i))) p := by
  classical
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ :=
    (mem_convexHull_iff_exists_fintype (R := ℝ) (E := V)).1 hp
  set A := toReal (P.vertex i)
  set B := toReal (P.vertex (P.nextIdx i))
  have hφ_nonneg : ∀ j : Fin P.nVertices, 0 ≤ detR A B (toReal (P.vertex j)) := by
    intro j
    have hZ := h i j
    have : (0 : ℝ) ≤ (latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j) : ℝ) :=
      Int.cast_nonneg hZ
    simpa [A, B, detR_toReal] using this
  have hz' : ∀ k, ∃ j : Fin P.nVertices, z k = toReal (P.vertex j) := by
    intro k
    obtain ⟨pt, hpt, heq⟩ := (mem_image _ _ _).1 (hz k)
    have hpV : pt ∈ (Finset.univ : Finset (Fin P.nVertices)).image P.vertex := by
      rw [← vertexFinset_eq_univ_image P]; exact hpt
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hpV
    exact ⟨j, by rw [← heq, ← hj]⟩
  have hφz : ∀ k, 0 ≤ detR A B (z k) := by
    intro k; obtain ⟨j, hj⟩ := hz' k; simpa [hj] using hφ_nonneg j
  have hφ_sum : detR A B p = ∑ k, w k * detR A B (z k) := by
    have := detR_sum_smul A B w z hw1
    simpa [hsum] using this
  have hnn : 0 ≤ ∑ k, w k * detR A B (z k) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hw0 k) (hφz k)
  simpa [hφ_sum] using hnn

/-- Collinear hull point on a polygon edge lies on that edge segment. -/
theorem mem_segment_of_detR_eq_zero_of_mem_hull
    (P : LatticePolygon) (hsc : StrictlyConvexCCW P)
    (hinj : Function.Injective P.vertex) {p : V}
    (hp : p ∈ P.convexHullRegion) (i : Fin P.nVertices)
    (hdet : detR (toReal (P.vertex i)) (toReal (P.vertex (P.nextIdx i))) p = 0) :
    p ∈ segment ℝ (toReal (P.vertex i)) (toReal (P.vertex (P.nextIdx i))) := by
  classical
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ :=
    (mem_convexHull_iff_exists_fintype (R := ℝ) (E := V)).1 hp
  set A := toReal (P.vertex i)
  set B := toReal (P.vertex (P.nextIdx i))
  have hext := VerticesExtreme_of_strictlyConvexCCW P hsc hinj
  have hABne : A ≠ B := by
    intro h
    have hv : P.vertex i = P.vertex (P.nextIdx i) :=
      toReal_injective (by simpa [A, B] using h)
    exact (InteriorFan.nextIdx_ne P i) (Eq.symm (hinj hv))
  have hφ_nonneg : ∀ j : Fin P.nVertices, 0 ≤ detR A B (toReal (P.vertex j)) := by
    intro j
    have hZ := hsc.1 i j
    have : (0 : ℝ) ≤ (latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j) : ℝ) :=
      Int.cast_nonneg hZ
    simpa [A, B, detR_toReal] using this
  have hz' : ∀ k, ∃ j : Fin P.nVertices, z k = toReal (P.vertex j) := by
    intro k
    obtain ⟨pt, hpt, heq⟩ := (mem_image _ _ _).1 (hz k)
    have hpV : pt ∈ (Finset.univ : Finset (Fin P.nVertices)).image P.vertex := by
      rw [← vertexFinset_eq_univ_image P]; exact hpt
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hpV
    exact ⟨j, by rw [← heq, ← hj]⟩
  have hφz : ∀ k, 0 ≤ detR A B (z k) := by
    intro k; obtain ⟨j, hj⟩ := hz' k; simpa [hj] using hφ_nonneg j
  have hφ_sum : ∑ k, w k * detR A B (z k) = 0 := by
    have := detR_sum_smul A B w z hw1
    simpa [hsum, hdet] using this.symm
  have hφ_term : ∀ k, w k * detR A B (z k) = 0 := by
    intro k
    have hnn : ∀ k ∈ (Finset.univ : Finset ι), 0 ≤ w k * detR A B (z k) :=
      fun k _ => mul_nonneg (hw0 k) (hφz k)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hφ_sum k (Finset.mem_univ k)
  have hsupp : ∀ k, 0 < w k → z k = A ∨ z k = B := by
    intro k hwk
    have hdetz : detR A B (z k) = 0 :=
      (mul_eq_zero.mp (hφ_term k)).resolve_left (ne_of_gt hwk)
    obtain ⟨j, hj⟩ := hz' k
    have hdetj : latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j) = 0 := by
      have : (latticeDet (P.vertex i) (P.vertex (P.nextIdx i)) (P.vertex j) : ℝ) = 0 := by
        simpa [A, B, hj, detR_toReal] using hdetz
      exact_mod_cast this
    by_cases hij : j = i
    · exact Or.inl (by simp [hj, hij, A])
    · by_cases hijn : j = P.nextIdx i
      · exact Or.inr (by simp [hj, hijn, B])
      · exact (not_collinear_of_VerticesExtreme P hext hinj i (P.nextIdx i) j
            (InteriorFan.nextIdx_ne P i).symm (Ne.symm hij) (Ne.symm hijn) hdetj).elim
  have hterm : ∀ k, w k • z k =
      (if z k = A then w k else 0) • A + (if z k = B then w k else 0) • B := by
    intro k
    by_cases hw : w k = 0
    · simp [hw]
    · have hwp : 0 < w k := lt_of_le_of_ne (hw0 k) (Ne.symm hw)
      rcases hsupp k hwp with hzA | hzB
      · rw [hzA]; simp [hABne]
      · rw [hzB]; simp [show ¬ B = A from fun h => hABne h.symm]
  have hsumAB :
      p =
        (∑ k, if z k = A then w k else 0) • A +
          (∑ k, if z k = B then w k else 0) • B := by
    calc
      p = ∑ k, w k • z k := hsum.symm
      _ = ∑ k, ((if z k = A then w k else 0) • A +
            (if z k = B then w k else 0) • B) := by
              refine Finset.sum_congr rfl fun k _ => hterm k
      _ = (∑ k, (if z k = A then w k else 0) • A) +
            (∑ k, (if z k = B then w k else 0) • B) := by
              simp only [Finset.sum_add_distrib]
      _ = (∑ k, if z k = A then w k else 0) • A +
            (∑ k, if z k = B then w k else 0) • B := by
              simp only [Finset.sum_smul]
  set wA := ∑ k, if z k = A then w k else 0
  set wB := ∑ k, if z k = B then w k else 0
  have hwA0 : 0 ≤ wA :=
    Finset.sum_nonneg fun k _ => by split_ifs <;> simp [hw0 k]
  have hwB0 : 0 ≤ wB :=
    Finset.sum_nonneg fun k _ => by split_ifs <;> simp [hw0 k]
  have hwAB1 : wA + wB = 1 := by
    have : wA + wB = ∑ k, w k := by
      dsimp [wA, wB]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hA : z k = A
      · simp [hA, hABne]
      · by_cases hB : z k = B
        · have hBA : ¬ B = A := fun h => hABne h.symm
          simp [hB, hBA]
        · by_cases hw : 0 < w k
          · exact (hsupp k hw).elim (fun h => (hA h).elim) (fun h => (hB h).elim)
          · have hw0' : w k = 0 := le_antisymm (le_of_not_gt hw) (hw0 k)
            simp [hA, hB, hw0']
    simpa [this] using hw1
  refine ⟨wA, wB, hwA0, hwB0, hwAB1, ?_⟩
  simpa [wA, wB] using hsumAB.symm

/-! ## Continuous fan covering under StrictlyConvexCCW -/

private lemma nextIdx_zero (P : LatticePolygon) :
    P.nextIdx ⟨0, P.nVertices_pos⟩ =
      ⟨1, by
        have hn : 3 ≤ P.nVertices := P.length_ge
        omega⟩ := by
  apply Fin.ext
  have hn : 3 ≤ P.nVertices := P.length_ge
  have h1 : 1 < P.nVertices := by omega
  simp [LatticePolygon.nextIdx, Nat.mod_eq_of_lt h1]

private lemma nextIdx_last (P : LatticePolygon) :
    P.nextIdx ⟨P.nVertices - 1, by
        have hn : 3 ≤ P.nVertices := P.length_ge
        omega⟩ =
      ⟨0, P.nVertices_pos⟩ := by
  apply Fin.ext
  have hn : 3 ≤ P.nVertices := P.length_ge
  have : P.nVertices - 1 + 1 = P.nVertices := by omega
  simp [LatticePolygon.nextIdx, this]

private lemma nextIdx_val_of_lt (P : LatticePolygon) (i : Fin P.nVertices)
    (h : i.val + 1 < P.nVertices) :
    (P.nextIdx i).val = i.val + 1 := by
  simp [LatticePolygon.nextIdx, Nat.mod_eq_of_lt h]

private lemma fanTriangleRegion_eq_of_vertices
    (P : LatticePolygon) (j : ℕ) (hj : j < P.nVertices - 2)
    (b c : ℤ × ℤ)
    (hb : P.vertex ⟨j + 1, by omega⟩ = b)
    (hc : P.vertex ⟨j + 2, by omega⟩ = c) :
    fanTriangleRegion P j hj =
      convexHull ℝ ({toReal (P.vertex ⟨0, P.nVertices_pos⟩), toReal b, toReal c} : Set V) := by
  dsimp [fanTriangleRegion, fanTriangle]
  have hb' : toReal (P.vertex ⟨j + 1, by omega⟩) = toReal b := congrArg toReal hb
  have hc' : toReal (P.vertex ⟨j + 2, by omega⟩) = toReal c := congrArg toReal hc
  rw [hb', hc']

/-- Every hull point lies in some apex-`v₀` fan-ear region. -/
theorem exists_mem_fanTriangleRegion_of_mem_hull
    (P : LatticePolygon) (hsc : StrictlyConvexCCW P)
    (hinj : Function.Injective P.vertex) {p : V}
    (hp : p ∈ P.convexHullRegion) :
    ∃ (i : ℕ) (hi : i < P.nVertices - 2), p ∈ fanTriangleRegion P i hi := by
  classical
  set A : V := toReal (P.vertex ⟨0, P.nVertices_pos⟩)
  set f : Fin P.nVertices → ℝ := fun i => detR A (toReal (P.vertex i)) p
  have hf0 : f ⟨0, P.nVertices_pos⟩ = 0 := by
    dsimp [f, A, detR]; ring
  have hge : ∃ i, 0 ≤ f i := ⟨⟨0, P.nVertices_pos⟩, by simp [hf0]⟩
  have hle : ∃ i, f i ≤ 0 := ⟨⟨0, P.nVertices_pos⟩, by simp [hf0]⟩
  obtain ⟨i, hi_ge, hi_le⟩ := exists_cyclic_nonneg_nonpos_transition P f hge hle
  have hpos := FanDetsPos_of_strictlyConvexCCW P hsc hinj
  by_cases hi0 : i.val = 0
  · -- Spoke `v₀v₁`.
    have hi_eq : i = ⟨0, P.nVertices_pos⟩ := Fin.ext hi0
    have hnext := nextIdx_zero P
    have hedge : 0 ≤ f ⟨1, by have hn : 3 ≤ P.nVertices := P.length_ge; omega⟩ := by
      have h := detR_edge_nonneg_of_ConvexCCW_of_mem_hull P hsc.1 hp
        ⟨0, P.nVertices_pos⟩
      simpa [f, A, hnext] using h
    have hf1' : f ⟨1, by have hn : 3 ≤ P.nVertices := P.length_ge; omega⟩ = 0 := by
      have hle' : f ⟨1, by have hn : 3 ≤ P.nVertices := P.length_ge; omega⟩ ≤ 0 := by
        simpa [hi_eq, hnext] using hi_le
      exact le_antisymm hle' hedge
    have hdet0 : detR A (toReal (P.vertex (P.nextIdx ⟨0, P.nVertices_pos⟩))) p = 0 := by
      simpa [A, f, hnext] using hf1'
    have hseg : p ∈
        segment ℝ A (toReal (P.vertex ⟨1, by have hn : 3 ≤ P.nVertices := P.length_ge; omega⟩)) := by
      have h := mem_segment_of_detR_eq_zero_of_mem_hull P hsc hinj hp
        ⟨0, P.nVertices_pos⟩ hdet0
      simpa [A, hnext] using h
    have hi_fan : (0 : ℕ) < P.nVertices - 2 := by have hn : 3 ≤ P.nVertices := P.length_ge; omega
    refine ⟨0, hi_fan, ?_⟩
    have ha : A ∈ fanTriangleRegion P 0 hi_fan :=
      subset_convexHull _ _ (by simp [fanTriangle, A])
    have hb : toReal (P.vertex ⟨1, by have hn : 3 ≤ P.nVertices := P.length_ge; omega⟩) ∈
        fanTriangleRegion P 0 hi_fan :=
      subset_convexHull _ _ (by simp [fanTriangle])
    exact (convex_convexHull ℝ _).segment_subset ha hb hseg
  · by_cases hilast : i.val = P.nVertices - 1
    · -- Closing spoke `v_{n-1}v₀`.
      have hi_eq : i = ⟨P.nVertices - 1, by have hn : 3 ≤ P.nVertices := P.length_ge; omega⟩ :=
        Fin.ext hilast
      have hnext := nextIdx_last P
      have hedge : 0 ≤ detR (toReal (P.vertex i)) A p := by
        have h := detR_edge_nonneg_of_ConvexCCW_of_mem_hull P hsc.1 hp i
        simpa [hi_eq, hnext, A] using h
      have hswap : detR (toReal (P.vertex i)) A p = -f i := by
        dsimp [f]; exact detR_swap_first _ _ _
      have hf0' : f i = 0 := by linarith
      have hseg : p ∈ segment ℝ (toReal (P.vertex i)) A := by
        have h := mem_segment_of_detR_eq_zero_of_mem_hull P hsc hinj hp i (by
          have : detR (toReal (P.vertex i)) A p = 0 := by
            rw [hswap, hf0', neg_zero]
          simpa [hi_eq, hnext, A] using this)
        simpa [hi_eq, hnext, A] using h
      set j : ℕ := P.nVertices - 3
      have hj : j < P.nVertices - 2 := by have hn : 3 ≤ P.nVertices := P.length_ge; omega
      refine ⟨j, hj, ?_⟩
      have hA : A ∈ fanTriangleRegion P j hj :=
        subset_convexHull _ _ (by simp [fanTriangle, A])
      have hVi : toReal (P.vertex i) ∈ fanTriangleRegion P j hj := by
        apply subset_convexHull
        have hj2 : j + 2 = i.val := by
          simp only [j, hi_eq]; omega
        have hc : P.vertex ⟨j + 2, by
            have hn : 3 ≤ P.nVertices := P.length_ge; omega⟩ = P.vertex i := by
          apply congrArg; exact Fin.ext hj2
        simp only [fanTriangle, mem_insert_iff, mem_singleton_iff]
        exact Or.inr (Or.inr (congrArg toReal hc.symm))
      exact (convex_convexHull ℝ _).segment_subset hVi hA hseg
    · -- Generic outer-edge transition.
      have hi_lt : i.val + 1 < P.nVertices := by
        have : i.val ≠ P.nVertices - 1 := hilast
        have : i.val < P.nVertices := i.isLt
        omega
      have hnext_val := nextIdx_val_of_lt P i hi_lt
      set j : ℕ := i.val - 1
      have hj : j < P.nVertices - 2 := by omega
      have hj1 : j + 1 = i.val := by omega
      have hj2 : j + 2 = i.val + 1 := by omega
      have hγ : 0 ≤ detR A (toReal (P.vertex i)) p := by simpa [f] using hi_ge
      have hβ : 0 ≤ detR A p (toReal (P.vertex (P.nextIdx i))) := by
        have hfn : f (P.nextIdx i) ≤ 0 := hi_le
        have hswap : detR A p (toReal (P.vertex (P.nextIdx i))) =
            -f (P.nextIdx i) := by
          dsimp [f]
          exact detR_swap_right' A p (toReal (P.vertex (P.nextIdx i)))
        linarith
      have hα : 0 ≤ detR (toReal (P.vertex i)) (toReal (P.vertex (P.nextIdx i))) p :=
        detR_edge_nonneg_of_ConvexCCW_of_mem_hull P hsc.1 hp i
      have hb_vert : P.vertex ⟨j + 1, by omega⟩ = P.vertex i := by
        apply congrArg; exact Fin.ext hj1
      have hc_vert : P.vertex ⟨j + 2, by omega⟩ = P.vertex (P.nextIdx i) := by
        apply congrArg
        apply Fin.ext
        calc
          j + 2 = i.val + 1 := hj2
          _ = (P.nextIdx i).val := hnext_val.symm
      have hD : 0 < detR A (toReal (P.vertex i)) (toReal (P.vertex (P.nextIdx i))) := by
        have hfan : 0 < fanDet P j hj := hpos j hj
        have hdet : fanDet P j hj =
            latticeDet (P.vertex ⟨0, P.nVertices_pos⟩) (P.vertex i)
              (P.vertex (P.nextIdx i)) := by
          simp only [fanDet, Triangle.det, fanTriangle, hb_vert, hc_vert]
        have : (0 : ℝ) <
            (latticeDet (P.vertex ⟨0, P.nVertices_pos⟩) (P.vertex i)
              (P.vertex (P.nextIdx i)) : ℝ) :=
          by exact_mod_cast (hdet ▸ hfan)
        simpa [A, detR_toReal] using this
      refine ⟨j, hj, ?_⟩
      have hmem := mem_convexHull_of_detR_nonneg A
        (toReal (P.vertex i)) (toReal (P.vertex (P.nextIdx i))) p hD hα hβ hγ
      have hreg := fanTriangleRegion_eq_of_vertices P j hj
        (P.vertex i) (P.vertex (P.nextIdx i)) hb_vert hc_vert
      simpa [hreg, A] using hmem

/-- Under `StrictlyConvexCCW` + injective vertices, the polygon hull equals the
union of apex-`v₀` fan-ear regions. -/
theorem convexHullRegion_eq_iUnion_fanTriangleRegion
    (P : LatticePolygon) (hsc : StrictlyConvexCCW P)
    (hinj : Function.Injective P.vertex) :
    P.convexHullRegion =
      ⋃ (i : ℕ) (hi : i < P.nVertices - 2), fanTriangleRegion P i hi := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi, hmem⟩ := exists_mem_fanTriangleRegion_of_mem_hull P hsc hinj hp
    exact mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hi, hmem⟩⟩
  · intro hp
    rcases mem_iUnion.1 hp with ⟨i, hi'⟩
    rcases mem_iUnion.1 hi' with ⟨hi, hmem⟩
    exact fanTriangleRegion_subset_convexHullRegion P i hi hmem


/-! ## Pairwise AEDisjoint of fan ears + discharge `hvol` -/

lemma detR_plucker (q a b c r : V) :
    detR q a b * detR q c r - detR q a c * detR q b r + detR q a r * detR q b c = 0 := by
  dsimp [detR]; ring

lemma detR_linear_of_affine_combo {ι : Type*} [Fintype ι]
    (u v : V) (w : ι → ℝ) (z : ι → V) (hw1 : ∑ i, w i = 1)
    (p : V) (hp : p = ∑ i, w i • z i) :
    detR u v p = ∑ i, w i * detR u v (z i) := by
  have := detR_sum_smul u v w z hw1
  simpa [hp] using this

/-- Oriented-area weights are nonnegative on a positively oriented Euclidean triangle. -/
theorem detR_nonneg_of_mem_convexHull_of_pos (a b c p : V)
    (hD : 0 < detR a b c) (hp : p ∈ convexHull ℝ ({a, b, c} : Set V)) :
    0 ≤ detR b c p ∧ 0 ≤ detR a p c ∧ 0 ≤ detR a b p := by
  classical
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ :=
    (mem_convexHull_iff_exists_fintype (R := ℝ) (E := V)).1 hp
  have hz' : ∀ i, z i = a ∨ z i = b ∨ z i = c := by
    intro i
    simpa [mem_insert_iff, mem_singleton_iff] using hz i
  have hα : 0 ≤ detR b c p := by
    have hlin := detR_linear_of_affine_combo b c w z hw1 p hsum.symm
    have hterm : ∀ i, 0 ≤ w i * detR b c (z i) := by
      intro i
      rcases hz' i with hza | hzb | hzc
      · rw [hza]
        have : detR b c a = detR a b c := by dsimp [detR]; ring
        exact mul_nonneg (hw0 i) (by simpa [this] using le_of_lt hD)
      · rw [hzb]; exact mul_nonneg (hw0 i) (le_of_eq (by dsimp [detR]; ring))
      · rw [hzc]; exact mul_nonneg (hw0 i) (le_of_eq (by dsimp [detR]; ring))
    have : 0 ≤ ∑ i, w i * detR b c (z i) := Finset.sum_nonneg fun i _ => hterm i
    simpa [hlin] using this
  have hγ : 0 ≤ detR a b p := by
    have hlin := detR_linear_of_affine_combo a b w z hw1 p hsum.symm
    have hterm : ∀ i, 0 ≤ w i * detR a b (z i) := by
      intro i
      rcases hz' i with hza | hzb | hzc
      · rw [hza]; exact mul_nonneg (hw0 i) (le_of_eq (by dsimp [detR]; ring))
      · rw [hzb]; exact mul_nonneg (hw0 i) (le_of_eq (by dsimp [detR]; ring))
      · rw [hzc]; exact mul_nonneg (hw0 i) (le_of_lt hD)
    have : 0 ≤ ∑ i, w i * detR a b (z i) := Finset.sum_nonneg fun i _ => hterm i
    simpa [hlin] using this
  have hβ : 0 ≤ detR a p c := by
    have hswap : detR a p c = -detR a c p := by dsimp [detR]; ring
    have hlin := detR_linear_of_affine_combo a c w z hw1 p hsum.symm
    have hterm : ∀ i, w i * detR a c (z i) ≤ 0 := by
      intro i
      rcases hz' i with hza | hzb | hzc
      · rw [hza]; exact mul_nonpos_of_nonneg_of_nonpos (hw0 i)
          (le_of_eq (by dsimp [detR]; ring))
      · rw [hzb]
        have : detR a c b = -detR a b c := by dsimp [detR]; ring
        exact mul_nonpos_of_nonneg_of_nonpos (hw0 i)
          (by simpa [this] using (neg_nonpos.mpr (le_of_lt hD)))
      · rw [hzc]; exact mul_nonpos_of_nonneg_of_nonpos (hw0 i)
          (le_of_eq (by dsimp [detR]; ring))
    have hsum_le : ∑ i, w i * detR a c (z i) ≤ 0 :=
      Finset.sum_nonpos fun i _ => hterm i
    have : detR a c p ≤ 0 := by simpa [hlin] using hsum_le
    linarith
  exact ⟨hα, hβ, hγ⟩

private lemma finrank_V_eq_two : Module.finrank ℝ V = 2 := by
  simp [V, Module.finrank_prod]

/-- Segments are Haar-null in `ℝ × ℝ`. -/
theorem volume_segment_eq_zero (a b : V) :
    volume (segment ℝ a b) = 0 := by
  rw [← convexHull_pair]
  have hsub : (convexHull ℝ ({a, b} : Set V)) ⊆
      (affineSpan ℝ ({a, b} : Set V) : Set V) :=
    convexHull_min (subset_affineSpan ℝ _) (affineSpan ℝ ({a, b} : Set V)).convex
  refine measure_mono_null hsub ?_
  have : IsAddHaarMeasure (volume : Measure V) :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  refine Measure.addHaar_affineSubspace (volume : Measure V) _ ?_
  intro htop
  have hne : ((affineSpan ℝ ({a, b} : Set V) : Set V)).Nonempty :=
    ⟨a, left_mem_affineSpan_pair _ _ _⟩
  have hdir : (affineSpan ℝ ({a, b} : Set V)).direction = (⊤ : Submodule ℝ V) :=
    (AffineSubspace.direction_eq_top_iff_of_nonempty hne).2 htop
  have hspan : Module.finrank ℝ (affineSpan ℝ ({a, b} : Set V)).direction ≤ 1 := by
    rw [direction_affineSpan, vectorSpan_pair]
    by_cases hv : (a -ᵥ b) = (0 : V)
    · rw [show a -ᵥ b = (0 : V) from hv, Submodule.span_zero_singleton, finrank_bot]
      decide
    · have h1 : Module.finrank ℝ (ℝ ∙ (a -ᵥ b)) = 1 := finrank_span_singleton hv
      omega
  have hV : Module.finrank ℝ V ≤ 1 := by
    rwa [hdir, finrank_top ℝ V] at hspan
  have h22 : Module.finrank ℝ V = 2 := finrank_V_eq_two
  lia

theorem volume_singleton_eq_zero (a : V) : volume ({a} : Set V) = 0 := by
  convert volume_segment_eq_zero a a
  exact (segment_same ℝ a).symm


set_option maxHeartbeats 800000 in
/-- Fan chord from apex `v₀` through listed vertices is positively oriented. -/
theorem fan_chord_detR_pos
    (P : LatticePolygon) (hsc : StrictlyConvexCCW P)
    (hinj : Function.Injective P.vertex)
    (r s : Fin P.nVertices)
    (hr : 1 ≤ r.val) (hrs : r.val < s.val) :
    0 < detR (toReal (P.vertex ⟨0, P.nVertices_pos⟩))
      (toReal (P.vertex r)) (toReal (P.vertex s)) := by
  classical
  set A : V := toReal (P.vertex ⟨0, P.nVertices_pos⟩)
  have hpos := FanDetsPos_of_strictlyConvexCCW P hsc hinj
  have hext := VerticesExtreme_of_strictlyConvexCCW P hsc hinj
  have h1lt : 1 < P.nVertices := by have hn : 3 ≤ P.nVertices := P.length_ge; omega
  have hfrom1 : ∀ t : Fin P.nVertices, 2 ≤ t.val →
      0 < detR A (toReal (P.vertex ⟨1, h1lt⟩)) (toReal (P.vertex t)) := by
    intro t ht2
    have hnext : P.nextIdx ⟨0, P.nVertices_pos⟩ = ⟨1, h1lt⟩ := nextIdx_zero P
    have hge : 0 ≤ latticeDet (P.vertex ⟨0, P.nVertices_pos⟩)
        (P.vertex ⟨1, h1lt⟩) (P.vertex t) := by
      simpa [hnext] using hsc.1 ⟨0, P.nVertices_pos⟩ t
    have hz0 : (0 : ℕ) ≠ 1 := by decide
    have h1lt_t : (1 : ℕ) < t.val := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) ht2
    have h0lt_t : (0 : ℕ) < t.val := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) ht2
    have h1t : (1 : ℕ) ≠ t.val := ne_of_lt h1lt_t
    have h0t : (0 : ℕ) ≠ t.val := ne_of_lt h0lt_t
    have hne : latticeDet (P.vertex ⟨0, P.nVertices_pos⟩)
        (P.vertex ⟨1, h1lt⟩) (P.vertex t) ≠ 0 := by
      intro h0
      exact (not_collinear_of_VerticesExtreme P hext hinj
        ⟨0, P.nVertices_pos⟩ ⟨1, h1lt⟩ t
        (Fin.ne_of_val_ne hz0) (Fin.ne_of_val_ne h0t) (Fin.ne_of_val_ne h1t) h0).elim
    have hZ : 0 < latticeDet (P.vertex ⟨0, P.nVertices_pos⟩)
        (P.vertex ⟨1, h1lt⟩) (P.vertex t) :=
      lt_of_le_of_ne hge (Ne.symm hne)
    have : (0 : ℝ) <
        (latticeDet (P.vertex ⟨0, P.nVertices_pos⟩)
          (P.vertex ⟨1, h1lt⟩) (P.vertex t) : ℝ) := by exact_mod_cast hZ
    simpa [A, detR_toReal] using this
  have hcons : ∀ (k : ℕ) (hk0 : 1 ≤ k) (hk1 : k + 1 < P.nVertices),
      0 < detR A (toReal (P.vertex ⟨k, Nat.lt_of_succ_lt hk1⟩))
        (toReal (P.vertex ⟨k + 1, hk1⟩)) := by
    intro k hk0 hk1
    have hklt : k < P.nVertices := Nat.lt_of_succ_lt hk1
    have hi : k - 1 < P.nVertices - 2 := by omega
    have hfan : 0 < fanDet P (k - 1) hi := hpos (k - 1) hi
    have hkb : (k - 1) + 1 = k := by omega
    have hkc : (k - 1) + 2 = k + 1 := by omega
    have hb : P.vertex ⟨(k - 1) + 1, by omega⟩ = P.vertex ⟨k, hklt⟩ := by
      apply congrArg; exact Fin.ext hkb
    have hc : P.vertex ⟨(k - 1) + 2, by omega⟩ = P.vertex ⟨k + 1, hk1⟩ := by
      apply congrArg; exact Fin.ext hkc
    have hdet : fanDet P (k - 1) hi =
        latticeDet (P.vertex ⟨0, P.nVertices_pos⟩)
          (P.vertex ⟨k, hklt⟩) (P.vertex ⟨k + 1, hk1⟩) := by
      simp only [fanDet, Triangle.det, fanTriangle, hb, hc]
    have : (0 : ℝ) <
        (latticeDet (P.vertex ⟨0, P.nVertices_pos⟩)
          (P.vertex ⟨k, hklt⟩) (P.vertex ⟨k + 1, hk1⟩) : ℝ) := by
      exact_mod_cast (by rw [← hdet]; exact hfan)
    simpa [A, detR_toReal] using this
  -- Induction on difference d = s.val - r.val
  have hdiff : ∀ d : ℕ, ∀ (r s : Fin P.nVertices),
      1 ≤ r.val → s.val = r.val + d → 0 < d →
      0 < detR A (toReal (P.vertex r)) (toReal (P.vertex s)) := by
    intro d
    refine Nat.strong_induction_on d fun d IH => ?_
    intro r s hr hs hdpos
    have hrs : r.val < s.val := by omega
    by_cases hr1 : r.val = 1
    · -- Chord from v₁: edge half-plane
      have hs2 : 2 ≤ s.val := by omega
      have hr_eq : r = ⟨1, h1lt⟩ := Fin.ext hr1
      simpa [hr_eq] using hfrom1 s hs2
    · by_cases hadj : d = 1
      · subst hadj
        have hk1 : r.val + 1 < P.nVertices := by
          have := s.isLt; omega
        have hs' : s = ⟨r.val + 1, hk1⟩ := Fin.ext (by omega)
        simpa [hs'] using hcons r.val hr hk1
      · have hd2 : 2 ≤ d := by omega
        have hrv2 : 2 ≤ r.val := by omega
        have hsval : s.val = r.val + d := hs
        have hs1lt : s.val - 1 < P.nVertices := by
          have := s.isLt; omega
        have hspred_lt : s.val - 1 < P.nVertices := hs1lt
        set spred : Fin P.nVertices := ⟨s.val - 1, hspred_lt⟩
        have hspred_eq : spred.val = s.val - 1 := rfl
        have h1 : 0 < detR A (toReal (P.vertex r)) (toReal (P.vertex spred)) := by
          have hseq : spred.val = r.val + (d - 1) := by
            rw [hspred_eq, hs]; omega
          exact IH (d - 1) (by omega) r spred hr hseq (by omega)
        have h2 : 0 < detR A (toReal (P.vertex spred)) (toReal (P.vertex s)) := by
          have hk0 : 1 ≤ spred.val := by rw [hspred_eq]; omega
          have hk1 : spred.val + 1 < P.nVertices := by
            rw [hspred_eq]; have := s.isLt; omega
          have hs' : s = ⟨spred.val + 1, hk1⟩ := by
            apply Fin.ext
            change s.val = spred.val + 1
            rw [hspred_eq]; omega
          simpa [hs'] using hcons spred.val hk0 hk1
        have he_r : 0 < detR A (toReal (P.vertex ⟨1, h1lt⟩)) (toReal (P.vertex r)) :=
          hfrom1 r hrv2
        have he_y : 0 < detR A (toReal (P.vertex ⟨1, h1lt⟩)) (toReal (P.vertex spred)) := by
          have : 2 ≤ spred.val := by rw [hspred_eq]; omega
          exact hfrom1 spred this
        have he_z : 0 < detR A (toReal (P.vertex ⟨1, h1lt⟩)) (toReal (P.vertex s)) := by
          have : 2 ≤ s.val := by omega
          exact hfrom1 s this
        set e := toReal (P.vertex ⟨1, h1lt⟩)
        set x := toReal (P.vertex r)
        set y := toReal (P.vertex spred)
        set z := toReal (P.vertex s)
        have hpl := detR_plucker A e x y z
        have hrhs :
            0 < detR A e x * detR A y z + detR A e z * detR A x y := by
          nlinarith [he_r, h2, he_z, h1]
        have : 0 < detR A x z := by
          have hmul :
              detR A e y * detR A x z =
                detR A e x * detR A y z + detR A e z * detR A x y := by
            linarith [hpl]
          have hpos' : 0 < detR A e y * detR A x z := by
            simpa [hmul] using hrhs
          exact pos_of_mul_pos_right hpos' (le_of_lt he_y)
        exact this
  exact hdiff (s.val - r.val) r s hr (by omega) (by omega)

/-- Point of a CCW triangle on the AC line lies on segment AC. -/
lemma mem_segment_of_mem_convexHull_of_detR_AC_eq_zero
    (a b c p : V) (hD : 0 < detR a b c)
    (hp : p ∈ convexHull ℝ ({a, b, c} : Set V))
    (hAC : detR a c p = 0) :
    p ∈ segment ℝ a c := by
  obtain ⟨hα, hβ, hγ⟩ := detR_nonneg_of_mem_convexHull_of_pos a b c p hD hp
  have hβ0 : detR a p c = 0 := by
    have : detR a p c = -detR a c p := by dsimp [detR]; ring
    linarith
  set α : ℝ := detR b c p / detR a b c
  set γ : ℝ := detR a b p / detR a b c
  have hα0 : 0 ≤ α := div_nonneg hα (le_of_lt hD)
  have hγ0 : 0 ≤ γ := div_nonneg hγ (le_of_lt hD)
  have hD0 : detR a b c ≠ 0 := ne_of_gt hD
  have hsum : α + γ = 1 := by
    dsimp [α, γ]
    have harea := detR_area_sum a b c p
    have : (detR b c p + detR a b p) / detR a b c = 1 := by
      have : detR b c p + detR a b p = detR a b c := by linarith [harea, hβ0]
      rw [this, div_self hD0]
    convert this using 1; ring
  have heq : α • a + γ • c = p := by
    apply Prod.ext
    · change α * a.1 + γ * c.1 = p.1
      dsimp [α, γ]
      have hid := detR_barycentric_x a b c p
      have hid' : detR a b c * p.1 = detR b c p * a.1 + detR a b p * c.1 := by
        rw [hβ0, zero_mul, add_zero] at hid
        -- hid became D*p.1 = detR b c p * a.1 + 0 + detR a b p * c.1
        -- need to reassociate: X + 0 + Y = X + Y
        simpa [add_zero] using hid
      have :
          (detR b c p * a.1 + detR a b p * c.1) / detR a b c = p.1 := by
        rw [← hid', mul_div_cancel_left₀ _ hD0]
      convert this using 1; ring
    · change α * a.2 + γ * c.2 = p.2
      dsimp [α, γ]
      have hid := detR_barycentric_y a b c p
      have hid' : detR a b c * p.2 = detR b c p * a.2 + detR a b p * c.2 := by
        rw [hβ0, zero_mul, add_zero] at hid
        simpa [add_zero] using hid
      have :
          (detR b c p * a.2 + detR a b p * c.2) / detR a b c = p.2 := by
        rw [← hid', mul_div_cancel_left₀ _ hD0]
      convert this using 1; ring
  exact ⟨α, γ, hα0, hγ0, hsum, heq⟩


private lemma fanTriangleRegion_eq_vertices
    (P : LatticePolygon) (i : ℕ) (hi : i < P.nVertices - 2) :
    fanTriangleRegion P i hi =
      convexHull ℝ
        ({toReal (P.vertex ⟨0, P.nVertices_pos⟩),
          toReal (P.vertex ⟨i + 1, by omega⟩),
          toReal (P.vertex ⟨i + 2, by omega⟩)} : Set V) := by
  dsimp [fanTriangleRegion, fanTriangle]

private lemma detR_fan_pos
    (P : LatticePolygon) (hsc : StrictlyConvexCCW P)
    (hinj : Function.Injective P.vertex)
    (i : ℕ) (hi : i < P.nVertices - 2) :
    0 < detR (toReal (P.vertex ⟨0, P.nVertices_pos⟩))
      (toReal (P.vertex ⟨i + 1, by omega⟩))
      (toReal (P.vertex ⟨i + 2, by omega⟩)) := by
  have hpos := FanDetsPos_of_strictlyConvexCCW P hsc hinj
  have hfan : 0 < fanDet P i hi := hpos i hi
  have : (0 : ℝ) < (fanDet P i hi : ℝ) := by exact_mod_cast hfan
  simpa [fanDet, Triangle.det, fanTriangle, detR_toReal] using this

/-- Adjacent fan ears meet only on the shared spoke from the apex. -/
theorem inter_fanTriangleRegion_adjacent_subset_spoke
    (P : LatticePolygon) (hsc : StrictlyConvexCCW P)
    (hinj : Function.Injective P.vertex)
    (i : ℕ) (hi : i + 1 < P.nVertices - 2) :
    fanTriangleRegion P i (by omega) ∩ fanTriangleRegion P (i + 1) hi ⊆
      segment ℝ (toReal (P.vertex ⟨0, P.nVertices_pos⟩))
        (toReal (P.vertex ⟨i + 2, by omega⟩)) := by
  classical
  set A := toReal (P.vertex ⟨0, P.nVertices_pos⟩)
  set B := toReal (P.vertex ⟨i + 1, by omega⟩)
  set C := toReal (P.vertex ⟨i + 2, by omega⟩)
  set D := toReal (P.vertex ⟨i + 3, by omega⟩)
  intro p hp
  have hp1 : p ∈ convexHull ℝ ({A, B, C} : Set V) := by
    simpa [fanTriangleRegion_eq_vertices] using hp.1
  have hp2 : p ∈ convexHull ℝ ({A, C, D} : Set V) := by
    simpa [fanTriangleRegion_eq_vertices] using hp.2
  have hD1 : 0 < detR A B C := detR_fan_pos P hsc hinj i (by omega)
  have hD2 : 0 < detR A C D := detR_fan_pos P hsc hinj (i + 1) hi
  obtain ⟨_, hβ1, _⟩ := detR_nonneg_of_mem_convexHull_of_pos A B C p hD1 hp1
  obtain ⟨_, _, hγ2⟩ := detR_nonneg_of_mem_convexHull_of_pos A C D p hD2 hp2
  have hAC_le : detR A C p ≤ 0 := by
    have : detR A p C = -detR A C p := by dsimp [detR]; ring
    linarith
  have hAC0 : detR A C p = 0 := le_antisymm hAC_le hγ2
  exact mem_segment_of_mem_convexHull_of_detR_AC_eq_zero A B C p hD1 hp1 hAC0

/-- Non-adjacent fan ears meet only at the apex. -/
theorem inter_fanTriangleRegion_nonadjacent_subset_apex
    (P : LatticePolygon) (hsc : StrictlyConvexCCW P)
    (hinj : Function.Injective P.vertex)
    {i j : ℕ} (hi : i < P.nVertices - 2) (hj : j < P.nVertices - 2)
    (hij : i + 1 < j) :
    fanTriangleRegion P i hi ∩ fanTriangleRegion P j hj ⊆
      ({toReal (P.vertex ⟨0, P.nVertices_pos⟩)} : Set V) := by
  classical
  set A := toReal (P.vertex ⟨0, P.nVertices_pos⟩)
  set Bi := toReal (P.vertex ⟨i + 1, by omega⟩)
  set Ci := toReal (P.vertex ⟨i + 2, by omega⟩)
  set Bj := toReal (P.vertex ⟨j + 1, by omega⟩)
  set Cj := toReal (P.vertex ⟨j + 2, by omega⟩)
  intro p hp
  have hp1 : p ∈ convexHull ℝ ({A, Bi, Ci} : Set V) := by
    simpa [fanTriangleRegion_eq_vertices] using hp.1
  have hp2 : p ∈ convexHull ℝ ({A, Bj, Cj} : Set V) := by
    simpa [fanTriangleRegion_eq_vertices] using hp.2
  have hDi : 0 < detR A Bi Ci := detR_fan_pos P hsc hinj i hi
  have hDj : 0 < detR A Bj Cj := detR_fan_pos P hsc hinj j hj
  -- Chord positivity: Bi, Ci before Bj
  have hBi_lt : i + 1 < P.nVertices := by omega
  have hCi_lt : i + 2 < P.nVertices := by omega
  have hBj_lt : j + 1 < P.nVertices := by omega
  have hBiBj : 0 < detR A Bi Bj :=
    fan_chord_detR_pos P hsc hinj ⟨i + 1, hBi_lt⟩ ⟨j + 1, hBj_lt⟩
      (by omega : 1 ≤ i + 1) (by omega : i + 1 < j + 1)
  have hCiBj : 0 < detR A Ci Bj :=
    fan_chord_detR_pos P hsc hinj ⟨i + 2, hCi_lt⟩ ⟨j + 1, hBj_lt⟩
      (by omega : 1 ≤ i + 2) (by omega : i + 2 < j + 1)
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ :=
    (mem_convexHull_iff_exists_fintype (R := ℝ) (E := V)).1 hp1
  have hz' : ∀ k, z k = A ∨ z k = Bi ∨ z k = Ci := by
    intro k; simpa [mem_insert_iff, mem_singleton_iff] using hz k
  have hlin := detR_linear_of_affine_combo A Bj w z hw1 p hsum.symm
  -- detR A Bj p = ∑ w * detR A Bj (z k) ≤ 0 with =0 iff no Bi/Ci weight
  have hterm_le : ∀ k, w k * detR A Bj (z k) ≤ 0 := by
    intro k
    rcases hz' k with hA | hB | hC
    · rw [hA]; exact mul_nonpos_of_nonneg_of_nonpos (hw0 k)
        (le_of_eq (by dsimp [detR]; ring))
    · rw [hB]
      have : detR A Bj Bi = -detR A Bi Bj := by dsimp [detR]; ring
      exact mul_nonpos_of_nonneg_of_nonpos (hw0 k)
        (by simpa [this] using neg_nonpos.mpr (le_of_lt hBiBj))
    · rw [hC]
      have : detR A Bj Ci = -detR A Ci Bj := by dsimp [detR]; ring
      exact mul_nonpos_of_nonneg_of_nonpos (hw0 k)
        (by simpa [this] using neg_nonpos.mpr (le_of_lt hCiBj))
  have hABj_le : detR A Bj p ≤ 0 := by
    have : ∑ k, w k * detR A Bj (z k) ≤ 0 :=
      Finset.sum_nonpos fun k _ => hterm_le k
    simpa [hlin] using this
  obtain ⟨_, _, hγj⟩ := detR_nonneg_of_mem_convexHull_of_pos A Bj Cj p hDj hp2
  -- hγj : 0 ≤ detR A Bj p
  have hABj0 : detR A Bj p = 0 := le_antisymm hABj_le hγj
  -- Hence all Bi/Ci weights vanish (strictly negative crosses)
  have hterm0 : ∀ k, w k * detR A Bj (z k) = 0 := by
    intro k
    have hnn : ∀ k ∈ (Finset.univ : Finset ι),
        w k * detR A Bj (z k) ≤ 0 := fun k _ => hterm_le k
    -- sum = 0 and each ≤ 0 ⇒ each = 0
    have hsum0 : ∑ k, w k * detR A Bj (z k) = 0 := by rw [← hlin, hABj0]
    exact (Finset.sum_eq_zero_iff_of_nonpos hnn).mp hsum0 k (Finset.mem_univ k)
  have hsupp : ∀ k, 0 < w k → z k = A := by
    intro k hwk
    have hdet0 : detR A Bj (z k) = 0 :=
      (mul_eq_zero.mp (hterm0 k)).resolve_left (ne_of_gt hwk)
    rcases hz' k with hA | hB | hC
    · exact hA
    · rw [hB] at hdet0
      have : detR A Bj Bi = -detR A Bi Bj := by dsimp [detR]; ring
      have : detR A Bi Bj = 0 := by linarith
      exact absurd this (ne_of_gt hBiBj)
    · rw [hC] at hdet0
      have : detR A Bj Ci = -detR A Ci Bj := by dsimp [detR]; ring
      have : detR A Ci Bj = 0 := by linarith
      exact absurd this (ne_of_gt hCiBj)
  -- p is convex combination of only A
  have htermA : ∀ k, w k • z k = w k • A := by
    intro k
    by_cases hw : w k = 0
    · simp [hw]
    · have hwp : 0 < w k := lt_of_le_of_ne (hw0 k) (Ne.symm hw)
      rw [hsupp k hwp]
  have hpA : p = A := by
    calc
      p = ∑ k, w k • z k := hsum.symm
      _ = ∑ k, w k • A := Finset.sum_congr rfl fun k _ => htermA k
      _ = (∑ k, w k) • A := by rw [← Finset.sum_smul]
      _ = A := by rw [hw1, one_smul]
  simp [hpA]

/-- Pairwise AEDisjoint of apex-`v₀` fan-ear regions under `StrictlyConvexCCW`. -/
theorem pairwise_AEDisjoint_fanTriangleRegion
    (P : LatticePolygon) (hsc : StrictlyConvexCCW P)
    (hinj : Function.Injective P.vertex) :
    Pairwise fun (i j : Fin (P.nVertices - 2)) =>
      volume (fanTriangleRegion P i.val i.isLt ∩
        fanTriangleRegion P j.val j.isLt) = 0 := by
  classical
  intro i j hij
  have hij_val : i.val ≠ j.val := Fin.val_injective.ne hij
  -- Prove for ordered pair, then use inter_comm
  have hordered : ∀ (a b : Fin (P.nVertices - 2)), a.val < b.val →
      volume (fanTriangleRegion P a.val a.isLt ∩
        fanTriangleRegion P b.val b.isLt) = 0 := by
    intro a b hlt
    by_cases hadj : b.val = a.val + 1
    · have hb : a.val + 1 < P.nVertices - 2 := by
        have := b.isLt; omega
      have hbeq : b = ⟨a.val + 1, hb⟩ := Fin.ext hadj
      rw [hbeq]
      exact measure_mono_null
        (inter_fanTriangleRegion_adjacent_subset_spoke P hsc hinj a.val hb)
        (volume_segment_eq_zero _ _)
    · exact measure_mono_null
        (inter_fanTriangleRegion_nonadjacent_subset_apex P hsc hinj
          a.isLt b.isLt (by omega))
        (volume_singleton_eq_zero _)
  rcases lt_or_gt_of_ne hij_val with hlt | hgt
  · exact hordered i j hlt
  · simpa [inter_comm] using hordered j i hgt



private lemma convexHullRegion_eq_iUnion_fin
    (P : LatticePolygon) (hsc : StrictlyConvexCCW P)
    (hinj : Function.Injective P.vertex) :
    P.convexHullRegion =
      ⋃ i : Fin (P.nVertices - 2), fanTriangleRegion P i.val i.isLt := by
  rw [convexHullRegion_eq_iUnion_fanTriangleRegion P hsc hinj]
  ext p
  constructor
  · intro hp
    rcases mem_iUnion.1 hp with ⟨i, hi'⟩
    rcases mem_iUnion.1 hi' with ⟨hi, hmem⟩
    refine mem_iUnion.2 ⟨⟨i, hi⟩, ?_⟩
    simpa using hmem
  · intro hp
    rcases mem_iUnion.1 hp with ⟨i, hmem⟩
    refine mem_iUnion.2 ⟨i.val, mem_iUnion.2 ⟨i.isLt, ?_⟩⟩
    simpa using hmem

private lemma nullMeasurableSet_fanTriangleRegion
    (P : LatticePolygon) (i : ℕ) (hi : i < P.nVertices - 2) :
    NullMeasurableSet (fanTriangleRegion P i hi) (volume : Measure V) := by
  have : IsAddHaarMeasure (volume : Measure V) :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  exact (convex_convexHull ℝ _).nullMeasurableSet volume

/-- Polygon hull Haar equals the sum of fan-ear volumes. -/
theorem volume_convexHullRegion_eq_sum_volume_fanTriangleRegion
    (P : LatticePolygon) (hsc : StrictlyConvexCCW P)
    (hinj : Function.Injective P.vertex) :
    volume P.convexHullRegion =
      ∑ i : Fin (P.nVertices - 2),
        volume (fanTriangleRegion P i.val i.isLt) := by
  classical
  have hU := convexHullRegion_eq_iUnion_fin P hsc hinj
  have hd : Pairwise fun (i j : Fin (P.nVertices - 2)) =>
      AEDisjoint (volume : Measure V)
        (fanTriangleRegion P i.val i.isLt)
        (fanTriangleRegion P j.val j.isLt) :=
    pairwise_AEDisjoint_fanTriangleRegion P hsc hinj
  have hm : ∀ i : Fin (P.nVertices - 2),
      NullMeasurableSet (fanTriangleRegion P i.val i.isLt) (volume : Measure V) :=
    fun i => nullMeasurableSet_fanTriangleRegion P i.val i.isLt
  have hd' : Pairwise
      (Function.onFun (AEDisjoint (volume : Measure V))
        fun i : Fin (P.nVertices - 2) => fanTriangleRegion P i.val i.isLt) := hd
  rw [hU, measure_iUnion₀ hd' hm, tsum_fintype]

/-- Under `StrictlyConvexCCW` + injective vertices, polygon Haar equals
`ofReal(P.shoelace)`. Discharges the `hvol` hyp of the conditional compose. -/
theorem volume_convexHullRegion_eq_ofReal_shoelace
    (P : LatticePolygon) (hsc : StrictlyConvexCCW P)
    (hinj : Function.Injective P.vertex) :
    volume P.convexHullRegion = ENNReal.ofReal P.shoelace := by
  classical
  have hnn := FanDetsNonneg_of_ConvexCCW P hsc.1
  rw [volume_convexHullRegion_eq_sum_volume_fanTriangleRegion P hsc hinj]
  have hterm : ∀ i : Fin (P.nVertices - 2),
      volume (fanTriangleRegion P i.val i.isLt) =
        ENNReal.ofReal (fanTriangle P i.val i.isLt).shoelace := fun i => by
    have h := volume_convexHull_lattice_triangle
      (fanTriangle P i.val i.isLt).a
      (fanTriangle P i.val i.isLt).b
      (fanTriangle P i.val i.isLt).c
    simpa [fanTriangleRegion, Triangle.shoelace] using h
  simp_rw [hterm]
  have hnonneg : ∀ i : Fin (P.nVertices - 2),
      0 ≤ ((fanTriangle P i.val i.isLt).shoelace : ℝ) := fun i =>
    triangleShoelace_nonneg _ _ _
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hnonneg i]
  congr 1
  -- ∑ᵢ (fanTriangle i).shoelace = P.shoelace
  have hadd := shoelace_eq_sum_fan_shoelace P hnn hinj
  -- Reindex fanTriangles Finset sum to Fin sum
  have hre :
      ∑ t ∈ fanTriangles P, t.shoelace =
        ∑ i : Fin (P.nVertices - 2), (fanTriangle P i.val i.isLt).shoelace := by
    dsimp [fanTriangles]
    have hinj' : Function.Injective
        (fun i : { x // x ∈ Finset.range (P.nVertices - 2) } =>
          fanTriangle P i.1 (Finset.mem_range.mp i.2)) := fun a b h =>
      Subtype.ext (fanTriangle_eq_of_eq P (Finset.mem_range.mp a.2)
        (Finset.mem_range.mp b.2) hinj h)
    rw [Finset.sum_image (fun _ _ _ _ h => hinj' h)]
    let e : Fin (P.nVertices - 2) ≃
        { x // x ∈ Finset.range (P.nVertices - 2) } :=
      { toFun := fun i => ⟨i.val, Finset.mem_range.mpr i.isLt⟩
        invFun := fun ⟨i, hi⟩ => ⟨i, Finset.mem_range.mp hi⟩
        left_inv := fun _ => Fin.ext rfl
        right_inv := fun _ => rfl }
    exact (Fintype.sum_equiv e
      (fun i => (fanTriangle P i.val i.isLt).shoelace)
      (fun i => (fanTriangle P i.1 (Finset.mem_range.mp i.2)).shoelace)
      (fun _ => rfl)).symm
  have hcast :
      (∑ i : Fin (P.nVertices - 2),
          ((fanTriangle P i.val i.isLt).shoelace : ℝ)) =
        ((∑ i : Fin (P.nVertices - 2),
          (fanTriangle P i.val i.isLt).shoelace : ℚ) : ℝ) := by
    simp only [Rat.cast_sum]
  rw [hcast, ← hre, ← hadd]


/-- Geometric volume Pick-form: Haar = `ofReal(#I + B/2 − 1)` under
`StrictlyConvexCCW` + injective + `PrimitiveEdges` + combinatorial interior Finset.
Not classical Pick (EP→planar / triangulation existence still open). -/
theorem volume_eq_ofReal_cardI_add_B_div_two_sub_one
    (P : LatticePolygon) (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hverts : Function.Injective P.vertex)
    (hedge : PrimitiveEdges P)
    (hsc : StrictlyConvexCCW P) :
    volume P.convexHullRegion =
      ENNReal.ofReal ((S.card : ℚ) + (P.B : ℚ) / 2 - 1) := by
  refine volume_eq_ofReal_cardI_add_B_div_two_sub_one_of_shoelace P S ?hvol ?hcomb
  · exact volume_convexHullRegion_eq_ofReal_shoelace P hsc hverts
  · exact LatticeFan.InteriorFan.shoelace_eq_cardI_add_B_div_two_sub_one
      P S hS hverts hedge hsc


/-- Geometric volume Pick-form without `PrimitiveEdges`: Haar =
`ofReal(#I + B/2 − 1)` under `StrictlyConvexCCW` + injective + combinatorial
interior Finset. Composes PE-free Haar(=shoelace) with PE-free combinatorial
Pick-form. Not classical Pick (finiteness / simple nonconvex still open). -/
theorem volume_eq_ofReal_cardI_add_B_div_two_sub_one_no_pe
    (P : LatticePolygon) (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hverts : Function.Injective P.vertex)
    (hsc : StrictlyConvexCCW P) :
    volume P.convexHullRegion =
      ENNReal.ofReal ((S.card : ℚ) + (P.B : ℚ) / 2 - 1) := by
  refine volume_eq_ofReal_cardI_add_B_div_two_sub_one_of_shoelace P S ?hvol ?hcomb
  · exact volume_convexHullRegion_eq_ofReal_shoelace P hsc hverts
  · exact LatticeFan.InteriorFan.shoelace_eq_cardI_add_B_div_two_sub_one_no_pe
      P S hS hverts hsc


end
end LatticeArea
end Picks
end EulersGem
