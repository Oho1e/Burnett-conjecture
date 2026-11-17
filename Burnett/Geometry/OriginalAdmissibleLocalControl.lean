import Burnett.Geometry.IntrinsicDhMeasure
import Burnett.Geometry.ManifoldMetricSequence
import Burnett.Geometry.ConnectionErrorLInfinity

/-!
# OriginalAdmissibleLocalControl

Paper-specific intrinsic derivative and physical norm support.
See docs/statements/intrinsic-dh-geometry.md for scope and remaining obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Burnett.Geometry.OriginalAdmissibleLocalControl
open Bundle Set Filter Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff Topology ENNReal
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ConnectionError

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

theorem exists_eventual_rawJet_bound_of_original
    (r : Metric (M := M)) (g₀ : ManifoldBilinear.Field (M := M))
    (g : ℕ → ManifoldBilinear.Field (M := M))
    (h₀ : ManifoldBilinear.IsSmooth g₀) (hg : ∀ n, ManifoldBilinear.IsSmooth (g n))
    (hn₀ : ManifoldBilinear.IsNondegenerate g₀)
    (hconv : ManifoldMetricSequence.LocallyUniformlyConverges r g g₀)
    (hb : ∀ S : Set M, IsCompact S → ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - g₀ m)) ∞
        ((ManifoldVolume.geometricMeasure g₀).restrict S) ≤ ENNReal.ofReal D)
    (c : M) (K : Set CoordinateSpace) (hK : IsCompact K)
    (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n in atTop, ∀ y ∈ K,
      ‖coordinateJet (fun x => metricComponents (coordinateBilinear (g n) c) x -
        metricComponents (coordinateBilinear g₀ c) x) y‖ ≤ D := by
  obtain ⟨D, hD, hcov⟩ := IntrinsicDhMeasure.exists_auxiliary_coordinate_bound_of_intrinsic_LInfinity
    r g₀ g h₀ hg hn₀ c K hK hKt hb
  have hu := ManifoldMetricSequence.components_uniform_of_physical_C0loc r g g₀ hconv c K hK hKt
  exact AuxiliaryConnection.exists_eventual_rawJet_bound_of_auxiliary_bound
    (chartAt CoordinateSpace c).target K (chartAt CoordinateSpace c).open_target hKt hK
    (coordinateMetric r c) (coordinateBilinear g₀ c) (fun n => coordinateBilinear (g n) c)
    (ManifoldMetric.contDiffOn_metricComponents_one r c)
    (fun y hy => coordinateMetric_nondegenerate r c (hKt hy))
    (fun y _ => coordinateMetric_symm r c y) hD (Eventually.of_forall hcov) hu

set_option maxHeartbeats 1000000 in
theorem computedError_uniform_of_original
    (r : Metric (M := M)) (g₀ : ManifoldBilinear.Field (M := M))
    (g : ℕ → ManifoldBilinear.Field (M := M))
    (h₀ : ManifoldBilinear.IsSmooth g₀) (hg : ∀ n, ManifoldBilinear.IsSmooth (g n))
    (hs₀ : ManifoldBilinear.IsSymmetric g₀) (hs : ∀ n, ManifoldBilinear.IsSymmetric (g n))
    (hn₀ : ManifoldBilinear.IsNondegenerate g₀) (hn : ∀ n, ManifoldBilinear.IsNondegenerate (g n))
    (hconv : ManifoldMetricSequence.LocallyUniformlyConverges r g g₀)
    (hb : ∀ S : Set M, IsCompact S → ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - g₀ m)) ∞
        ((ManifoldVolume.geometricMeasure g₀).restrict S) ≤ ENNReal.ofReal D)
    (c : M) (K : Set CoordinateSpace) (hK : IsCompact K)
    (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    TendstoUniformlyOn
      (fun n => ConnectionErrorLInfinity.computedError (coordinateBilinear g₀ c)
        (coordinateBilinear (g n) c)) (fun _ => 0) atTop K := by
  obtain ⟨D, hD, hraw⟩ := exists_eventual_rawJet_bound_of_original
    r g₀ g h₀ hg hn₀ hconv hb c K hK hKt
  obtain ⟨hc₀, hc, hN₀, hN, hS₀, hS, hu⟩ := ManifoldMetricSequence.chart_conditions_of_global
    r g g₀ h₀ hg hs₀ hs hn₀ hn hconv c K hK hKt
  have hd (n : ℕ) (y : CoordinateSpace) (hy : y ∈ K) :
      DifferentiableComponentsAt (metricComponents (coordinateBilinear (g n) c)) y := by
    intro a b
    exact ((hc n a b).differentiableOn (by simp) y (hKt hy)).differentiableAt
      ((chartAt CoordinateSpace c).open_target.mem_nhds (hKt hy))
  have hE := ConnectionErrorSequence.metricConnectionError_uniform_of_coordinate_bounds
    (chartAt CoordinateSpace c).target K (chartAt CoordinateSpace c).open_target hKt hK
    (coordinateBilinear g₀ c) (fun n => coordinateBilinear (g n) c)
    hN₀ hN hS₀ hS hc₀ hd hD hraw hu
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hE ε hε] with n hnE
  intro y hy
  have heq : ConnectionErrorLInfinity.computedError (coordinateBilinear g₀ c)
      (coordinateBilinear (g n) c) y =
      metricConnectionErrorOn K (coordinateBilinear g₀ c) (coordinateBilinear (g n) c) hN₀ (hN n) y := by
    rw [metricConnectionErrorOn_of_mem _ _ _ _ _ hy]
    exact ConnectionErrorLInfinity.computedError_eq_metricConnectionError _ _ y (hN₀ y hy) (hN n y hy)
      ((hS₀ y hy).self_of_nhds) ((hS n y hy).self_of_nhds)
  simpa only [← heq] using hnE y hy

set_option maxHeartbeats 1000000 in
theorem computedError_exists_tendstoLp_of_original
    (r : Metric (M := M)) (g₀ : ManifoldBilinear.Field (M := M))
    (g : ℕ → ManifoldBilinear.Field (M := M))
    (h₀ : ManifoldBilinear.IsSmooth g₀) (hg : ∀ n, ManifoldBilinear.IsSmooth (g n))
    (hs₀ : ManifoldBilinear.IsSymmetric g₀) (hs : ∀ n, ManifoldBilinear.IsSymmetric (g n))
    (hn₀ : ManifoldBilinear.IsNondegenerate g₀) (hn : ∀ n, ManifoldBilinear.IsNondegenerate (g n))
    (hconv : ManifoldMetricSequence.LocallyUniformlyConverges r g g₀)
    (hb : ∀ S : Set M, IsCompact S → ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - g₀ m)) ∞
        ((ManifoldVolume.geometricMeasure g₀).restrict S) ≤ ENNReal.ofReal D)
    (c : M) (K : Set CoordinateSpace) (hK : IsCompact K)
    (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    ∃ hf : ∀ n, MemLp
      (ConnectionErrorLInfinity.computedError (coordinateBilinear g₀ c) (coordinateBilinear (g n) c)) ∞
      ((ManifoldVolume.coordinateMeasure g₀ c).restrict K),
      Tendsto (fun n => (hf n).toLp
        (ConnectionErrorLInfinity.computedError (coordinateBilinear g₀ c) (coordinateBilinear (g n) c)))
        atTop (𝓝 0) := by
  obtain ⟨hc₀, hc, hN₀, hN, hS₀, hS, _⟩ := ManifoldMetricSequence.chart_conditions_of_global
    r g g₀ h₀ hg hs₀ hs hn₀ hn hconv c K hK hKt
  have hu := computedError_uniform_of_original r g₀ g h₀ hg hs₀ hs hn₀ hn hconv hb c K hK hKt
  let hf := fun n => Burnett.Analysis.LocalAeBound.memLp_top_restrict_of_continuousOn_isCompact
    (ManifoldVolume.coordinateMeasure g₀ c) hK hK.measurableSet
    (ConnectionErrorLInfinity.continuousOn_computedError
      (chartAt CoordinateSpace c).target K (chartAt CoordinateSpace c).open_target hKt
      (coordinateBilinear g₀ c) (coordinateBilinear (g n) c) hN₀ (hN n)
      (fun y hy => (hS₀ y hy).self_of_nhds) (fun y hy => (hS n y hy).self_of_nhds)
      hc₀ (hc n))
  exact ⟨hf, Burnett.Analysis.tendsto_toLp_top_of_uniformlyOn_zero hK.measurableSet _ hf hu⟩

end Burnett.Geometry.OriginalAdmissibleLocalControl
