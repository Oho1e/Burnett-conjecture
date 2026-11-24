import Burnett.Analysis.Microlocal.Overlap.LocalCutoffPairing
import Burnett.Analysis.Microlocal.Overlap.LocalCutoffEntryExt

set_option autoImplicit false
set_option maxHeartbeats 450000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (entryMeasure traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density integrable_density_entry)
open Burnett.Microlocal.SmoothAngularTests
open Burnett.Microlocal.SmoothBaseTests
open Burnett.X02.SobolevTestJet (D test_smooth)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The entry of the multiplied cutoff on a Borel preimage in the
smaller chart ball equals the squared-cutoff weighted entry on the
original chart ball. -/
theorem sameChart_cutoffMul_entryMeasure_preimage_eq
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
    (S : Set (Chart q.ball)) (hS : MeasurableSet S) (i j : JetSlot) :
    entryMeasure ν' hfin' i j (sameChartBallInclusion hLK ⁻¹' S) =
      ∫ p in S, ↑((θ : E → ℝ) p.1 ^ 2) * density ν hfin p i j ∂traceMeasure ν := by
  let T := sameChartBallInclusion hLK
  have hT : Measurable T := (continuous_sameChartBallInclusion hLK).measurable
  let W (p : Chart q.ball) : ℂ := ↑((θ : E → ℝ) p.1 ^ 2)
  have hWC : Continuous W :=
    Complex.continuous_ofReal.comp
      (((test_smooth θ).continuous.comp (continuous_subtype_val.comp continuous_fst)).pow 2)
  have hWB (p : Chart q.ball) : ‖W p‖ ≤ (physicalCoefficient θ).bound ^ 2 := by
    have hW : W p = ((physicalCoefficient θ) p.1) ^ 2 := Complex.ofReal_pow ((θ : E → ℝ) p.1) 2
    rw [hW, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((physicalCoefficient θ).norm_le p.1) 2
  have hInt : Integrable (fun p => W p * density ν hfin p i j) (traceMeasure ν) :=
    (integrable_density_entry ν hfin i j).bdd_mul hWC.measurable.aestronglyMeasurable ⟨_, hWB⟩
  have hTest (t : TermParameters) :
      (∫ p : Chart L, baseSymbol q.ball t.1 p.1 * complexRationalAngularSymbol t.2 p.2 *
        density ν' hfin' p i j ∂traceMeasure ν') =
        ∫ p : Chart q.ball, baseSymbol q.ball t.1 p.1 * W p * complexRationalAngularSymbol t.2 p.2 *
          density ν hfin p i j ∂traceMeasure ν :=
    sameChart_cutoffMul_density_integral_eq r B g hB hg hnB hconv hbnd q L
      (hLK.trans q.ball_in_chart) χ' θ hχ' hCut σ hσ ν hfin ν' hfin' hR hR'
      (baseSymbol q.ball t.1) (complexRationalAngularSymbol t.2)
      (complexBase_contDiff q.ball t.1).continuous (complexRationalAngular_contDiffOn t.2)
      (complexRationalAngular_degreeZero t.2) i j
  have hSet := sameChart_weighted_setIntegral_eq_of_terms hLK (traceMeasure ν') (traceMeasure ν)
    (fun p => density ν' hfin' p i j) (fun p => density ν hfin p i j) W
    (integrable_density_entry ν' hfin' i j) hInt hTest S hS
  exact (hR'.2.2.2.2.1 (T ⁻¹' S) (hT hS) i j).symm.trans hSet

end Burnett.Microlocal.Overlap
