import Burnett.Geometry.ManifoldCov3Norm
import Burnett.Geometry.ManifoldVolumeRegularity
import Burnett.Analysis.LocalAeBound
import Burnett.Analysis.UniformLInfinity

/-!
# IntrinsicDhMeasure

Paper-specific intrinsic derivative and physical norm support.
See docs/statements/intrinsic-dh-geometry.md for scope and remaining obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Burnett.Geometry.IntrinsicDhMeasure
open Bundle Set Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff Topology ENNReal
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.CovariantTensorNorm

theorem continuousOn_norm3_of_inverse {X : Type*} [TopologicalSpace X]
    (R : X → Tensor2) (T : X → FirstJet) (U : Set X)
    (hI : ContinuousOn (fun x => InverseField.matrixInverse (R x)) U)
    (hT : ContinuousOn T U) : ContinuousOn (fun x => norm3 (R x) (T x)) U := by
  have hi (a b : Index) : ContinuousOn (fun x => InverseField.matrixInverse (R x) a b) U :=
    continuousOn_pi.mp (continuousOn_pi.mp hI a) b
  have ht (a b c : Index) : ContinuousOn (fun x => T x a b c) U :=
    continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_pi.mp hT a) b) c
  change ContinuousOn (fun x => Real.sqrt (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
    InverseField.matrixInverse (R x) i a * InverseField.matrixInverse (R x) j b *
      InverseField.matrixInverse (R x) k c * T x i j k * T x a b c)) U
  exact (continuousOn_finset_sum Finset.univ (fun i _ =>
    continuousOn_finset_sum Finset.univ (fun j _ =>
    continuousOn_finset_sum Finset.univ (fun k _ =>
    continuousOn_finset_sum Finset.univ (fun a _ =>
    continuousOn_finset_sum Finset.univ (fun b _ =>
    continuousOn_finset_sum Finset.univ (fun c _ =>
      ((((hi i a).mul (hi j b)).mul (hi k c)).mul (ht i j k)).mul (ht a b c)))))))).sqrt

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

def coordinateDerivativeTensor (r : Metric (M := M)) (H : ManifoldBilinear.Field (M := M))
    (c : M) (y : CoordinateSpace) : FirstJet :=
  covariantJet (BackgroundConnection.computedConnection (coordinateMetric r c) y)
    (metricComponents (coordinateBilinear H c) y)
    (coordinateJet (metricComponents (coordinateBilinear H c)) y)

theorem continuousOn_coordinateDerivativeTensor (r : Metric (M := M))
    (H : ManifoldBilinear.Field (M := M)) (hH : ManifoldBilinear.IsSmooth H) (c : M) :
    ContinuousOn (coordinateDerivativeTensor r H c) (chartAt CoordinateSpace c).target := by
  have hΓ := (SmoothMetricConnection.contDiffOn_coordinateBilinear_connection r.inner
    (ManifoldBilinear.isSmooth_inner r) (GlobalLeviCivita.inner_nondegenerate r) c).continuousOn
  have hJ : ContinuousOn (coordinateJet (metricComponents (coordinateBilinear H c)))
      (chartAt CoordinateSpace c).target := by
    apply continuousOn_pi.mpr
    intro b
    apply continuousOn_pi.mpr
    intro e
    apply continuousOn_pi.mpr
    intro f
    exact (SmoothMetricConnection.contDiffOn_coordinateJet _ _
      (chartAt CoordinateSpace c).open_target (ManifoldBilinear.contDiffOn_metricComponents H hH c)
      b e f).continuousOn
  exact AuxiliaryConnection.continuousOn_covariantJet _ _ _ _ hΓ
    (ManifoldBilinear.continuousOn_components H hH c) hJ

theorem continuousOn_coordinatePhysicalNorm (r : Metric (M := M))
    (H : ManifoldBilinear.Field (M := M)) (hH : ManifoldBilinear.IsSmooth H) (c : M) :
    ContinuousOn (fun y => norm3 (metricComponents (coordinateMetric r c) y)
      (coordinateDerivativeTensor r H c y)) (chartAt CoordinateSpace c).target := by
  apply continuousOn_norm3_of_inverse
  · exact InverseField.continuousOn_matrixInverse _ _
      (ManifoldBilinear.continuousOn_components r.inner (ManifoldBilinear.isSmooth_inner r) c)
      (fun y hy => ManifoldVolumeRegularity.coordinate_det_ne_zero r.inner
        (GlobalLeviCivita.inner_nondegenerate r) c hy)
  · exact continuousOn_coordinateDerivativeTensor r H hH c

def normScalar (r : Metric (M := M)) (H : ManifoldBilinear.Field (M := M)) : M → ℝ :=
  ManifoldCov3Norm.physicalNorm3 r (IntrinsicCov2.tensor r.inner H)

theorem intrinsic_components (r : Metric (M := M))
    (H : ManifoldBilinear.Field (M := M)) (hH : ManifoldBilinear.IsSmooth H)
    (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source) :
    ManifoldCov3Norm.frameComponents3 (IntrinsicCov2.tensor r.inner H) c m =
      coordinateDerivativeTensor r H c (chartAt CoordinateSpace c m) := by
  funext b e f
  rw [ManifoldCov3Norm.frameComponents3_apply,
    IntrinsicCov2.tensor_eq_tensorInChart r.inner H (ManifoldBilinear.isSmooth_inner r) r.symm
      (GlobalLeviCivita.inner_nondegenerate r) hH c m hm]
  simp only [IntrinsicCov2.tensorInChart, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    IntrinsicCov2.coordinateTrilinear_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  change AffineConnection.cov2Differential _ _ _
    (mfderiv Model Model (chartAt CoordinateSpace c) m (tangentFrame c m (coordinateBasis b)))
    (mfderiv Model Model (chartAt CoordinateSpace c) m (tangentFrame c m (coordinateBasis e)))
    (mfderiv Model Model (chartAt CoordinateSpace c) m (tangentFrame c m (coordinateBasis f))) = _
  rw [IntrinsicCov2.mfderiv_chart_tangentFrame c m hm,
    IntrinsicCov2.mfderiv_chart_tangentFrame c m hm,
    IntrinsicCov2.mfderiv_chart_tangentFrame c m hm]
  exact IntrinsicCov2.cov2Differential_coordinateBasis _ _ _ b e f

theorem normScalar_eq_chart (r : Metric (M := M))
    (H : ManifoldBilinear.Field (M := M)) (hH : ManifoldBilinear.IsSmooth H)
    (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source) :
    normScalar r H m = norm3 (metricComponents (coordinateMetric r c) (chartAt CoordinateSpace c m))
      (coordinateDerivativeTensor r H c (chartAt CoordinateSpace c m)) := by
  rw [normScalar, ManifoldCov3Norm.physicalNorm3_eq_frame r _ c m hm,
    ManifoldTensorNorm.frameComponents_eq_coordinate r.inner c m hm,
    intrinsic_components r H hH c m hm]
  rfl

theorem continuous_normScalar (r : Metric (M := M))
    (H : ManifoldBilinear.Field (M := M)) (hH : ManifoldBilinear.IsSmooth H) :
    Continuous (normScalar r H) := by
  apply continuous_iff_continuousAt.mpr
  intro m
  have h := (continuousOn_coordinatePhysicalNorm r H hH m).comp
    (chartAt CoordinateSpace m).continuousOn (chartAt CoordinateSpace m).mapsTo
  have hg : ContinuousOn (normScalar r H) (chartAt CoordinateSpace m).source :=
    h.congr (fun n hn => normScalar_eq_chart r H hH m n hn)
  exact hg.continuousAt ((chartAt CoordinateSpace m).open_source.mem_nhds (mem_chart_source _ m))

theorem measurable_normScalar [MeasurableSpace M] [BorelSpace M]
    (r : Metric (M := M)) (H : ManifoldBilinear.Field (M := M))
    (hH : ManifoldBilinear.IsSmooth H) : Measurable (normScalar r H) :=
  (continuous_normScalar r H hH).measurable

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

set_option maxHeartbeats 1000000 in
theorem exists_auxiliary_coordinate_bound_of_intrinsic_LInfinity
    (r : Metric (M := M)) (g₀ : ManifoldBilinear.Field (M := M))
    (g : ℕ → ManifoldBilinear.Field (M := M))
    (h₀ : ManifoldBilinear.IsSmooth g₀) (hg : ∀ n, ManifoldBilinear.IsSmooth (g n))
    (hn₀ : ManifoldBilinear.IsNondegenerate g₀)
    (c : M) (K : Set CoordinateSpace) (hK : IsCompact K)
    (hKt : K ⊆ (chartAt CoordinateSpace c).target)
    (hb : ∀ S : Set M, IsCompact S → ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      eLpNorm (normScalar r (fun m => g n m - g₀ m)) ∞
        ((ManifoldVolume.geometricMeasure g₀).restrict S) ≤ ENNReal.ofReal D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n y, y ∈ K →
      ‖AuxiliaryConnection.auxiliaryPerturbationJet (coordinateMetric r c)
        (coordinateBilinear g₀ c) (coordinateBilinear (g n) c) y‖ ≤ C := by
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace CoordinateSpace M
  let μ := ManifoldVolume.geometricMeasure g₀
  letI : μ.IsOpenPosMeasure :=
    ManifoldVolumeRegularity.geometricMeasure_isOpenPosMeasure g₀ h₀ hn₀
  let J := (chartAt CoordinateSpace c).symm '' K
  have hJ : IsCompact J :=
    hK.image_of_continuousOn ((chartAt CoordinateSpace c).continuousOn_symm.mono hKt)
  obtain ⟨S, hS, hJS, _⟩ := exists_compact_between hJ isOpen_univ (subset_univ J)
  obtain ⟨D, hD, hbS⟩ := hb S hS
  let f : ℕ → M → ℝ := fun n => normScalar r (fun m => g n m - g₀ m)
  have hc (n : ℕ) : Continuous (f n) :=
    continuous_normScalar r _ (IntrinsicCov2.isSmooth_difference (g n) g₀ (hg n) h₀)
  have hpoint (n : ℕ) (m : M) (hm : m ∈ J) : f n m ≤ D := by
    have h := Burnett.Analysis.LocalAeBound.norm_le_on_of_eLpNorm_top_le μ
      isOpen_interior hJS interior_subset (hc n).norm.continuousOn hD (hbS n)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using h m hm)
  obtain ⟨A, hA, hcontrol⟩ := ManifoldCov3Norm.exists_uniform_component_control r c K hK hKt
  refine ⟨A * D, mul_nonneg hA.le hD, ?_⟩
  intro n y hy
  have hm := (chartAt CoordinateSpace c).symm_mapsTo (hKt hy)
  have heq := ManifoldCov3Norm.intrinsic_frameComponents3_auxiliary r (g n) g₀
    (hg n) h₀ c ((chartAt CoordinateSpace c).symm y) hm
  rw [(chartAt CoordinateSpace c).right_inv (hKt hy)] at heq
  have h := hcontrol y hy (IntrinsicCov2.tensor r.inner (fun m => g n m - g₀ m))
  rw [heq] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (hpoint n _ (mem_image_of_mem _ hy)) hA.le)

end Burnett.Geometry.IntrinsicDhMeasure
