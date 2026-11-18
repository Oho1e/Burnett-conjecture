import Burnett.Counterexamples.HarmonicShear.Bounds
import Burnett.Geometry.FlatRigidity

set_option autoImplicit false

noncomputable section

namespace Burnett.HarmonicShear.Bounds

open Filter MeasureTheory Burnett.RicciSymbol Burnett.HarmonicShear Burnett.HarmonicShear.Reference
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldMetricSequence Burnett.Geometry.CovariantTensorNorm
open Burnett.Geometry.FlatRigidity Burnett.Geometry.IntrinsicRicciTrace
open Burnett.Geometry.CurvatureDifference
open scoped ContDiff Manifold Topology ENNReal BigOperators

theorem shearField_isFlat (n : ℕ) : IsFlat (shearField n) := by
  apply (isFlat_iff_coordinateFlat (shearField n) (shearField_isSmooth n)
    (IsSymmetric_of_hasMinkowskiSignature _ (shearField_hasMinkowskiSignature n))
    (IsNondegenerate_of_hasMinkowskiSignature _ (shearField_hasMinkowskiSignature n))).mpr
  intro c x _ d e
  rw [coordinateBilinear_shearField]
  exact metric_riemann_zero n x d e

theorem flatField_isFlat : IsFlat flatField := by
  apply (isFlat_iff_coordinateFlat flatField flatField_isSmooth
    (IsSymmetric_of_hasMinkowskiSignature _ flatField_hasMinkowskiSignature)
    (IsNondegenerate_of_hasMinkowskiSignature _ flatField_hasMinkowskiSignature)).mpr
  intro c x _ d e
  rw [coordinateBilinear_flatField]
  have h : computedConnection (fun _ => minkowski) = 0 := funext minkowski_connection_zero
  rw [h]
  have hMatrix (k : Index) : connectionMatrix (0 : Connection) k = 0 := rfl
  have hDerivative (k l : Index) : connectionMatrixDerivative (0 : CoordinateSpace → Connection) x k l = 0 := by
    ext a b
    simp [connectionMatrixDerivative, coordinateConnectionJet]
  simp [Burnett.Geometry.FlatRigidity.coordinateRiemann, hMatrix, hDerivative]

theorem vacuum_of_intrinsic_flatness (g : Field (M := CoordinateSpace)) (h : IsFlat g) : IsVacuum g := by
  intro x u v
  have hZero : curvatureEnd g x u v = 0 := by
    ext w
    rw [curvatureEnd_apply, h x]
    rfl
  simp only [Burnett.Geometry.IntrinsicRicciTrace.ricci, hZero, map_zero]

theorem shearField_gauge_zero (n : ℕ) (c x : CoordinateSpace) (a : Index) :
    gauge (coordinateBilinear (shearField n) c) x a = 0 := by
  rw [coordinateBilinear_shearField]
  exact metric_gauge_zero n x a

theorem flatField_gauge_zero (c x : CoordinateSpace) (a : Index) :
    gauge (coordinateBilinear flatField c) x a = 0 := by
  rw [coordinateBilinear_flatField]
  exact minkowski_gauge_zero x a

theorem flatField_time_direction (x : CoordinateSpace) :
    flatField x (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) = -1 := by
  rw [flatField, fieldOfMetricComponents_apply]
  change minkowskiPair _ _ = _
  norm_num [minkowskiPair, EuclideanSpace.single_apply, Fin.ext_iff]

/-- The componentwise flat background wave operator in the Euclidean model chart. -/
def minkowskiBoxField (B : Field (M := CoordinateSpace)) (x : CoordinateSpace) : Tensor2 :=
  fun a b => box (fun y => metricComponents (coordinateBilinear B 0) y a b) x

theorem minkowskiBoxField_shear_difference (n : ℕ) :
    minkowskiBoxField (shearField n - flatField) = tensorBoxSource n := by
  unfold minkowskiBoxField shearField flatField
  rw [coordinateComponents_field_difference]
  rfl

theorem tensorBoxSource_component_contDiff (n : ℕ) (a b : Index) :
    ContDiff ℝ ∞ (fun x => tensorBoxSource n x a b) := by
  have hPert : ContDiff ℝ ∞ (fun x => perturbation n x a b) := by
    simp only [perturbation_eq_components]
    exact (components_contDiff n a b).sub contDiff_const
  have hPartial (d : Index) {f : CoordinateSpace → ℝ} (hf : ContDiff ℝ ∞ f) :
      ContDiff ℝ ∞ (coordPartial d f) := (hf.fderiv_right (by simp)).clm_apply contDiff_const
  change ContDiff ℝ ∞ (fun x => ∑ d : Index, sign d *
    coordPartial d (coordPartial d (fun y => perturbation n y a b)) x)
  exact ContDiff.sum fun d _ => contDiff_const.mul (hPartial d (hPartial d hPert))

theorem tensorBoxSource_euclidean_memLp (n : ℕ) :
    MemLp (fun x => norm2 (1 : Matrix Index Index ℝ) (tensorBoxSource n x)) 2
      ((Burnett.Geometry.ManifoldVolume.geometricMeasure flatField).restrict
        Burnett.Geometry.HarmonicShearL2.fixedBox) := by
  rw [flatField_geometricMeasure]
  let q (x : CoordinateSpace) := norm2 (1 : Matrix Index Index ℝ) (tensorBoxSource n x)
  have hq : Continuous q := by
    have hSum : ContDiff ℝ ∞ (fun x => ∑ i : Index, ∑ j : Index, tensorBoxSource n x i j ^ 2) :=
      ContDiff.sum fun i _ => ContDiff.sum fun j _ => (tensorBoxSource_component_contDiff n i j).pow 2
    simpa only [q, euclidean_norm2_eq_sqrt_sum] using Real.continuous_sqrt.comp hSum.continuous
  let K := Burnett.Geometry.HarmonicShearL2.fixedBox
  have hK : IsCompact K := Burnett.Geometry.HarmonicShearL2.isCompact_fixedBox
  haveI : IsFiniteMeasure ((volume : Measure CoordinateSpace).restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨C, hC, hb⟩ := (hK.image hq).isBounded.exists_pos_norm_le
  refine (memLp_const C).mono' hq.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  simpa only [Real.norm_eq_abs, abs_of_pos hC] using hb _ (Set.mem_image_of_mem _ hx)

/-- The actual harmonic-coordinate counterexample on one fixed compact set. -/
theorem harmonic_coordinate_source_counterexample :
    ∃ (g : ℕ → Field (M := CoordinateSpace)) (K : Set CoordinateSpace),
      IsCompact K ∧
      (∀ n, IsSmooth (g n) ∧ HasMinkowskiSignature (g n) ∧ IsFlat (g n) ∧ IsVacuum (g n)) ∧
      LocallyUniformlyConverges euclideanMetric g flatField ∧
      (∀ S : Set CoordinateSpace, IsCompact S → ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
        eLpNorm (Burnett.Geometry.IntrinsicDhMeasure.normScalar euclideanMetric (g n - flatField))
          ⊤ ((Burnett.Geometry.ManifoldVolume.geometricMeasure flatField).restrict S) ≤ ENNReal.ofReal D) ∧
      (∀ n (c x : CoordinateSpace) (a : Index), gauge (coordinateBilinear (g n) c) x a = 0) ∧
      (∀ (c x : CoordinateSpace) (a : Index), gauge (coordinateBilinear flatField c) x a = 0) ∧
      (∀ n, MemLp (fun x => norm2 (1 : Matrix Index Index ℝ) (minkowskiBoxField (g n - flatField) x)) 2
        ((Burnett.Geometry.ManifoldVolume.geometricMeasure flatField).restrict K)) ∧
      Tendsto (fun n => eLpNorm (fun x => norm2 (1 : Matrix Index Index ℝ)
          (minkowskiBoxField (g n - flatField) x)) 2
          ((Burnett.Geometry.ManifoldVolume.geometricMeasure flatField).restrict K)) atTop (𝓝 ⊤) := by
  refine ⟨shearField, Burnett.Geometry.HarmonicShearL2.fixedBox, ?_, ?_,
    shearField_locallyUniformlyConverges, shearField_intrinsicDh_compact_bound,
    shearField_gauge_zero, flatField_gauge_zero, ?_, ?_⟩
  · exact Burnett.Geometry.HarmonicShearL2.isCompact_fixedBox
  · intro n
    exact ⟨shearField_isSmooth n, shearField_hasMinkowskiSignature n, shearField_isFlat n,
      vacuum_of_intrinsic_flatness _ (shearField_isFlat n)⟩
  · intro n
    simpa only [minkowskiBoxField_shear_difference] using tensorBoxSource_euclidean_memLp n
  · simpa only [minkowskiBoxField_shear_difference] using tensorBoxSource_euclidean_L2_tendsto_top

end Burnett.HarmonicShear.Bounds
