import Burnett.Analysis.Microlocal.Overlap.CotangentPhysicalJetMeasure
import Burnett.Analysis.Microlocal.Overlap.ChartAuxiliaryPhysicalDensity
import Burnett.Geometry.ManifoldLorentzSignature

/-! The vacuum Ricci kernel gives positivity for the original chart witnesses. -/

set_option autoImplicit false
set_option maxHeartbeats 320000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence
open Burnett.Geometry.UnitNullCompactness (CotangentBundle)
open Burnett.F05.ActualChartAuxiliarySection (chartAuxiliaryRay)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude
  (ae_originalVolume_auxiliaryAmplitude chartAuxiliaryAmplitude)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.PhysicalDensity (physicalContraction)
open Burnett.Microlocal.RicciRow (backgroundInverse)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- The original vacuum sequence gives a real nonnegative density on its
actual auxiliary null shell, with the same represented trace. -/
theorem ae_original_chartPhysicalJetContraction_nonneg_real
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ a, IsFiniteMeasure (ν a))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin) :
    ∀ᵐ z ∂(traceMeasure ν).restrict (chartAuxiliaryNull r B hSig.isNondegenerate q),
      0 ≤ (chartPhysicalJetContraction r B q ν hfin z).re ∧
        (chartPhysicalJetContraction r B q ν hfin z).im = 0 := by
  have hData := ae_originalVolume_auxiliaryAmplitude r B g hB hg hSig.isSymmetric hsG
    hSig.isNondegenerate hnG hconv hb hv q σ hσ ν hfin hRep
  exact ae_chartPhysicalJetWeight_contraction_nonneg_real r B hB hSig.isSymmetric hSig.isNondegenerate
    q ν hfin
    (fun y => chartInverse_hasLorentzFrame B hSig q.center (q.ball_in_chart y.property))
    (hData.mono fun _ h => ⟨h.1, h.2.1, h.2.2.2⟩)

variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- On any Borel set of actual auxiliary covectors, the finite positive
physical measure is the quarter contraction of the same auxiliary amplitude
restricted to the null shell. -/
theorem original_cotangentPhysicalJetMeasure_apply_eq_setIntegral
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ a, IsFiniteMeasure (ν a))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin)
    {S : Set (CotangentBundle M)} (hS : MeasurableSet S) :
    (((cotangentPhysicalJetMeasure r B hSig.isNondegenerate q ν hfin) S).toReal : ℂ) =
      ∫ z in (chartAuxiliaryRay r q ⁻¹' S) ∩ chartAuxiliaryNull r B hSig.isNondegenerate q,
        (1 / 4 : ℂ) * physicalContraction (backgroundInverse B q.center z.1)
          (chartAuxiliaryAmplitude r q ν hfin z) ∂traceMeasure ν := by
  have hPos := ae_original_chartPhysicalJetContraction_nonneg_real r B g hB hg hSig hsG hnG
    hconv hb hv q σ hσ ν hfin hRep
  have hData := ae_originalVolume_auxiliaryAmplitude r B g hB hg hSig.isSymmetric hsG
    hSig.isNondegenerate hnG hconv hb hv q σ hσ ν hfin hRep
  rw [cotangentPhysicalJetMeasure_apply_eq_setIntegral r B hSig.isNondegenerate q ν hfin hB hPos hS]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hData] with z hz
  exact chartPhysicalJetWeight_contraction_eq_auxiliaryAmplitude r B q ν hfin z hz.2.1

end Burnett.Microlocal.Overlap
