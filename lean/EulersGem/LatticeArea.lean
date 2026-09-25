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
import EulersGem.LatticeTriangle
import EulersGem.LatticePolygon
import EulersGem.LatticeFan
import EulersGem.LatticeFanInterior

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
`ofReal(P.shoelace)` under `FanDetsNonneg`. Polygon hull = fan-union (measure
additivity) and full compose with combinatorial Finset Pick-form remain open.
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

/- Polygon hull = almost-disjoint fan union (⇒ discharge `hvol` above) remains open.
Classical Pick still FAIL. -/

end
end LatticeArea
end Picks
end EulersGem
