import Burnett.Analysis.Microlocal.ChartAuxiliaryEmbedding
import Burnett.Analysis.Microlocal.Overlap.CosphereAuxiliaryMeasureChange

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section
namespace Burnett.Microlocal.Overlap

open MeasureTheory Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open UnitCosphere (Cosphere)
open CotangentAngularExtension (cotangentNorm cotangentNorm_sq cotangentNormalize)
open CotangentUnitNormalization (unitShell_punctured unitShellHomeomorph)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude
  (ae_originalVolume_auxiliaryAmplitude chartAuxiliaryAmplitude)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.FixedChartGeometricDensity (roundCovector)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem measurableEmbedding_renormalizeUnitCosphere (r r' : Metric (M := M)) :
    MeasurableEmbedding (renormalizeUnitCosphere r r') := by
  let e : Cosphere r ≃ₜ Cosphere r' := unitShellHomeomorph r r'
  exact e.measurableEmbedding

/-- The two chart parametrizations select representatives on the same positive
cotangent ray. -/
theorem chartAuxiliaryCosphere_changeAuxiliary (r r' : Metric (M := M)) (q : CompactChartInput M) :
    chartAuxiliaryCosphere r' q = renormalizeUnitCosphere r r' ∘ chartAuxiliaryCosphere r q := by
  funext z
  apply Subtype.ext
  change chartAuxiliaryRay r' q z = cotangentNormalize r' (chartAuxiliaryRay r q z)
  exact congrFun (chartAuxiliaryRay_changeAuxiliary r r' q) z

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- Both sections compute the covariance from the same round amplitude on the
same original trace. The multiplier is the squared new norm of the old unit
covector, and the complex ordered entries are kept intact. -/
theorem ae_original_chartAuxiliaryAmplitude_changeAuxiliary
    (r r' : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin) :
    ∀ᵐ z ∂traceMeasure ν,
      chartAuxiliaryAmplitude r' q ν hfin z =
        ((cotangentNorm r' (chartAuxiliaryRay r q z) ^ 2 : ℝ) : ℂ) •
          chartAuxiliaryAmplitude r q ν hfin z := by
  have hconv' := AuxiliaryAdmissibility.locallyUniformlyConverges_changeAuxiliary r r' g B hconv
  have hb' := AuxiliaryAdmissibility.compactDhBound_changeAuxiliary r r' B g hB hg hconv hb
  have hData := ae_originalVolume_auxiliaryAmplitude r B g hB hg hSig.isSymmetric hsG
    hSig.isNondegenerate hnG hconv hb hv q σ hσ ν hfin hRep
  have hData' := ae_originalVolume_auxiliaryAmplitude r' B g hB hg hSig.isSymmetric hsG
    hSig.isNondegenerate hnG hconv' hb' hv q σ hσ ν hfin hRep
  filter_upwards [hData, hData'] with z hz hz'
  have hEnergy := cotangentNorm_sq r' (unitShell_punctured r (chartAuxiliaryRay_unit r q z))
  let a := symbolNorm (chartAuxiliaryInverse r q z.1) (roundCovector z)
  let b := symbolNorm (chartAuxiliaryInverse r' q z.1) (roundCovector z)
  have hProd : ((b / a : ℝ) : ℂ) * (a : ℂ) = (b : ℂ) := by
    rw [← Complex.ofReal_mul, div_mul_cancel₀ _ (chartAuxiliaryNorm_pos r q z).ne']
  rw [hz.2.2.1, hz'.2.2.1, hEnergy, chartAuxiliaryRay_changeWeight_eq_ratio, smul_smul, hProd]

end Burnett.Microlocal.Overlap
