import Burnett.Analysis.Microlocal.Overlap.LocalCutoffEntryMeasure
import Burnett.Analysis.Microlocal.Overlap.SameChartPhaseEmbedding
import Burnett.Analysis.Microlocal.Overlap.WeightedSetIntegralTransfer

set_option autoImplicit false
set_option maxHeartbeats 3700000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density integrable_density_entry)
open Burnett.Microlocal.SmoothBaseTests (BallData)
open Burnett.X02.SobolevTestJet (D test_smooth)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- A bounded measurable test on the ambient chart can be transported
through the exact same-chart cutoff square law on a smaller Borel set. -/
theorem sameChart_cutoffMul_setIntegral_on_image
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hbnd : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q : CompactChartInput M) (L : BallData) (hLK : L.closedBall ⊆ q.ball.closedBall)
    (χ' θ : D) (hχ' : tsupport (χ' : E → ℝ) ⊆ L.closedBall)
    (hCut : ∀ x : E, (χ' : E → ℝ) x = (θ : E → ℝ) x * (q.cutoff : E → ℝ) x)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (ν' : (JetSlot → ℂ) → Measure (Chart L)) (hfin' : ∀ v, IsFiniteMeasure (ν' v))
    (hR : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin)
    (hR' : RepresentsCompactJetPairings L
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center χ'
        (hχ'.trans (hLK.trans q.ball_in_chart))) σ ν' hfin')
    (a : Chart q.ball → ℂ) (ha : Measurable a) (A : ℝ) (hA : 0 ≤ A)
    (haBound : ∀ y, ‖a y‖ ≤ A) (S : Set (Chart L)) (hS : MeasurableSet S) (i j : JetSlot) :
    let I := sameChartBallInclusion hLK
    (∫ x in S, a (I x) * density ν' hfin' x i j ∂traceMeasure ν') =
      ∫ y in I '' S, a y * (((θ : E → ℝ) y.1 ^ 2 : ℝ) : ℂ) *
        density ν hfin y i j ∂traceMeasure ν := by
  intro I
  let W (y : Chart q.ball) : ℂ := (((θ : E → ℝ) y.1 ^ 2 : ℝ) : ℂ)
  have hWc : Continuous W := Complex.continuous_ofReal.comp
    (((test_smooth θ).continuous.comp (continuous_subtype_val.comp continuous_fst)).pow 2)
  have hW (y : Chart q.ball) : ‖W y‖ ≤ (physicalCoefficient θ).bound ^ 2 := by
    have he : W y = (physicalCoefficient θ y.1) ^ 2 := Complex.ofReal_pow _ _
    rw [he, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((physicalCoefficient θ).norm_le y.1) 2
  have hInt : Integrable (fun y => W y * density ν hfin y i j) (traceMeasure ν) :=
    (integrable_density_entry ν hfin i j).bdd_mul hWc.measurable.aestronglyMeasurable ⟨_, hW⟩
  have hI : MeasurableEmbedding I := measurableEmbedding_sameChartBallInclusion hLK
  have he (U : Set (Chart q.ball)) (hU : MeasurableSet U) :
      (∫ x in I ⁻¹' U, density ν' hfin' x i j ∂traceMeasure ν') =
        ∫ y in U, W y * density ν hfin y i j ∂traceMeasure ν := by
    rw [hR'.2.2.2.2.1 _ (hI.measurable hU) i j]
    exact sameChart_cutoffMul_entryMeasure_preimage_eq r B g hB hg hnB hconv hbnd
      q L hLK χ' θ hχ' hCut σ hσ ν hfin ν' hfin' hR hR' U hU i j
  have hWeightEq := setIntegral_mul_eq_of_setIntegral_preimage_eq
    (traceMeasure ν') (traceMeasure ν) I hI.measurable _ _
    (integrable_density_entry ν' hfin' i j) hInt he a ha A hA haBound (I '' S)
    (hI.measurableSet_image.mpr hS)
  rw [hI.injective.preimage_image S] at hWeightEq
  simpa only [W, mul_assoc] using hWeightEq

end Burnett.Microlocal.Overlap
