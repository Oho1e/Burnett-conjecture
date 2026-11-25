import Burnett.Analysis.GaugeProjection.StrongCompactness.StrongChartRestriction
import Burnett.Analysis.GaugeProjection.StrongCompactness.StrongVacuum
import Burnett.Analysis.GaugeProjection.StrongCompactness.HomogeneousProjectionWeakDerivative

/-! State the strong criterion with the ordinary Euclidean norm and the manuscript's chart quantifier. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3900000

noncomputable section
namespace Burnett.P01

open Filter MeasureTheory Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

local notation "E" => CoordinateSpace

private theorem tendsto_nonneg_energy_iff_sqrt (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    Tendsto f atTop (𝓝 0) ↔ Tendsto (fun n => Real.sqrt (f n)) atTop (𝓝 0) := by
  constructor
  · intro h
    have hs := (Real.continuous_sqrt.tendsto 0).comp h
    change Tendsto (fun n => Real.sqrt (f n)) atTop (𝓝 (Real.sqrt 0)) at hs
    simpa only [Real.sqrt_zero] using hs
  · intro h
    simpa only [Real.sq_sqrt (hf _), zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h.pow 2

/-- For every open region, vacuum is equivalent to whole-sequence convergence
of the genuine homogeneous projected coordinate gradient in the unweighted
Euclidean norm, on every chart contained in that region and every test cutoff. -/
theorem vacuumOpen_iff_all_charts_homogeneousProjectedGradient_norm_tendsto_zero
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (U : Set M) (hU : IsOpen U) :
    (∀ x ∈ U, ∀ u v : TangentSpace Model x, IntrinsicRicciTrace.ricci B x u v = 0) ↔
      ∀ (c : AtlasChart M), c.chart.source ⊆ U → ∀ (χ : D)
        (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target),
        Tendsto (fun n => Real.sqrt (receivingStrongProjectionEnergy B g hB hg c χ hχ n)) atTop (𝓝 0) := by
  rw [vacuumOpen_iff_hasStrongProjectedGradientOn r B g hB hg hSig hsG hnG hconv hb hv U hU,
    hasStrongProjectedGradientOn_iff_all_charts_in_open B g hB hg U hU]
  have hEq (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) :=
    tendsto_nonneg_energy_iff_sqrt (receivingStrongProjectionEnergy B g hB hg c χ hχ)
      (fun _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  exact ⟨fun h c hc χ hχ => (hEq c χ hχ).mp (h c hc χ hχ),
    fun h c hc χ hχ => (hEq c χ hχ).mpr (h c hc χ hχ)⟩

end Burnett.P01
