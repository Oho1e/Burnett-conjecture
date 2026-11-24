import Burnett.Analysis.Microlocal.Overlap.CompactAmplitudeTraceLift
import Burnett.Analysis.Microlocal.Overlap.AmplitudeDensityOnCommonControl

set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 1800000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (chartAuxiliaryAmplitude)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- On each compact part of the genuine overlap, the original normalized
amplitude matrices agree in the source frame after weighting each by the RN
derivative of its own lifted positive trace with respect to their sum. -/
theorem original_compactOverlap_amplitudeDensities_on_sum
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hbnd : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (q d : CompactChartInput M)
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (hRq : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ νq hfq)
    (hRd : RepresentsCompactJetPairings d.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB d.center d.cutoff
        (d.cutoff_support.trans d.ball_in_chart)) σ νd hfd)
    {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus ∩ d.nonzeroLocus) :
    let W := amplitudeCosphereWindow r K
    let μq := (chartCosphereControlMeasure r q νq).restrict W
    let μd := (chartCosphereControlMeasure r d νd).restrict W
    let A := liftChartAmplitude r q (chartAuxiliaryAmplitude r q νq hfq)
    let D := liftChartAmplitude r d (fun z i j => transportedAmplitudeEntry r q d νd hfd i j z)
    IsFiniteMeasure μq ∧ IsFiniteMeasure μd ∧
      (∀ i j, Integrable (fun p => A p i j) μq) ∧
      (∀ i j, Integrable (fun p => D p i j) μd) ∧
      (fun p => (μq.rnDeriv (μq + μd) p).toReal • A p)
        =ᵐ[μq + μd] fun p => (μd.rnDeriv (μq + μd) p).toReal • D p := by
  intro W μq μd A D
  let FQ := chartAuxiliaryAmplitude r q νq hfq
  let FD (z : Chart d.ball) (i j : Pair) := transportedAmplitudeEntry r q d νd hfd i j z
  letI : IsFiniteMeasure μq :=
    isFiniteMeasure_chartCosphereControlMeasure_restrict_compact r q νq hfq hK
      (hSub.trans inter_subset_left)
  letI : IsFiniteMeasure μd :=
    isFiniteMeasure_chartCosphereControlMeasure_restrict_compact r d νd hfd hK
      (hSub.trans inter_subset_right)
  have hEntry (i j : Pair) :
      Integrable (fun p => A p i j) μq ∧ Integrable (fun p => D p i j) μd ∧
        μq.withDensityᵥ (fun p => A p i j) = μd.withDensityᵥ (fun p => D p i j) := by
    obtain ⟨hQI, hDI, hEq⟩ := original_normalizedCosphereAmplitudeEntry_eq_on_compactOverlap r B g
      hB hg hsB hsG hnB hnG hconv hbnd hv σ hσ q d νq hfq νd hfd hRq hRd i j hK hSub
    obtain ⟨hQ, hQPush⟩ := normalizedCosphereChartEntryOn_eq_withDensity_liftChartAmplitude
      r q νq FQ hK.isClosed.measurableSet i j hQI
    obtain ⟨hD, hDPush⟩ := normalizedCosphereChartEntryOn_eq_withDensity_liftChartAmplitude
      r d νd FD hK.isClosed.measurableSet i j hDI
    exact ⟨hQ, hD, hQPush.symm.trans (hEq.trans hDPush)⟩
  refine ⟨inferInstance, inferInstance, fun i j => (hEntry i j).1,
    fun i j => (hEntry i j).2.1, ?_⟩
  apply ae_eq_amplitudeDensities_on_sum μq μd A D
    (fun i j => (hEntry i j).1) (fun i j => (hEntry i j).2.1)
  intro i j S hS
  obtain ⟨hQ, hD, hEq⟩ := hEntry i j
  have h := congrArg (fun ρ : ComplexMeasure (Cosphere r) => ρ S) hEq
  change (μq.withDensityᵥ (fun p => A p i j)) S =
    (μd.withDensityᵥ (fun p => D p i j)) S at h
  rwa [withDensityᵥ_apply hQ hS, withDensityᵥ_apply hD hS] at h

end Burnett.Microlocal.Overlap
