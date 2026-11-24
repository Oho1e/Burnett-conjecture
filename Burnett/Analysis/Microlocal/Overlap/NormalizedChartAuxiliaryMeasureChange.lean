import Burnett.Analysis.Microlocal.Overlap.OriginalChartAuxiliaryMeasureChange
import Burnett.Analysis.Microlocal.Overlap.NormalizedCotangentPhysicalMeasure

/-! Auxiliary renormalization of the original cutoff-normalized physical measures. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension (cotangentNormalize cotangentNormalize_projection)
open Burnett.F05.ActualChartAuxiliarySection (chartAuxiliaryRay continuous_chartAuxiliaryRay)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (test_smooth)
open scoped ContDiff ENNReal Manifold


variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The squared target auxiliary norm as a weight on the old unit section. -/
def cotangentAuxiliaryWeight (r : Metric (M := M)) (p : CotangentBundle M) : ℝ≥0∞ :=
  ENNReal.ofReal (dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r) p)

variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

theorem measurable_cotangentAuxiliaryWeight (r : Metric (M := M)) :
    Measurable (cotangentAuxiliaryWeight r) :=
  ENNReal.measurable_ofReal.comp (continuous_auxiliaryDualSquare r).measurable

/-- Weight the old measure by the squared target norm and normalize each covector
with that target auxiliary metric. -/
def renormalizeCotangentPhysicalMeasure (r : Metric (M := M)) (μ : Measure (CotangentBundle M)) :
    Measure (CotangentBundle M) :=
  (μ.withDensity (cotangentAuxiliaryWeight r)).map (cotangentNormalize r)

/-- Renormalization preserves the base point, so restriction to a Borel base
domain commutes with weighting and radial pushforward. -/
theorem renormalizeCotangentPhysicalMeasure_restrict_base (r : Metric (M := M))
    (μ : Measure (CotangentBundle M)) {U : Set M}
    (hU : MeasurableSet ((fun p : CotangentBundle M => p.proj) ⁻¹' U)) :
    let S := (fun p : CotangentBundle M => p.proj) ⁻¹' U
    (renormalizeCotangentPhysicalMeasure r μ).restrict S =
      renormalizeCotangentPhysicalMeasure r (μ.restrict S) := by
  let S := (fun p : CotangentBundle M => p.proj) ⁻¹' U
  have hPre : cotangentNormalize r ⁻¹' S = S := by
    ext p
    change (cotangentNormalize r p).proj ∈ U ↔ p.proj ∈ U
    rw [cotangentNormalize_projection]
  change ((μ.withDensity (cotangentAuxiliaryWeight r)).map (cotangentNormalize r)).restrict S =
    ((μ.restrict S).withDensity (cotangentAuxiliaryWeight r)).map (cotangentNormalize r)
  rw [Measure.restrict_map (measurable_cotangentNormalize r) hU, hPre, restrict_withDensity hU]

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- Removing the same original cutoff square commutes with the auxiliary change.
Both normalized chart measures use the same represented original gradient witness. -/
theorem original_normalizedCotangentPhysicalMeasure_changeAuxiliary
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
    normalizedCotangentPhysicalMeasure q r' B hSig.isNondegenerate ν hfin =
      renormalizeCotangentPhysicalMeasure r' (normalizedCotangentPhysicalMeasure q r B
        hSig.isNondegenerate ν hfin) := by
  let C := chartPhysicalJetMeasure r B hSig.isNondegenerate q ν hfin
  let C' := chartPhysicalJetMeasure r' B hSig.isNondegenerate q ν hfin
  let d := chartInverseCutoffSquare q
  let w := cotangentAuxiliaryWeight r'
  have hRay := (continuous_chartAuxiliaryRay r q).measurable
  have hD : Measurable d := by
    have hCutoff : Continuous (fun p : Chart q.ball => (q.cutoff : CoordinateSpace → ℝ) p.1) :=
      (test_smooth q.cutoff).continuous.comp (continuous_subtype_val.comp continuous_fst)
    exact ENNReal.measurable_ofReal.comp (hCutoff.measurable.inv.pow_const 2)
  have hW : Measurable w := measurable_cotangentAuxiliaryWeight r'
  have hWray : Measurable (w ∘ chartAuxiliaryRay r q) := hW.comp hRay
  have hChart : C' = C.withDensity (w ∘ chartAuxiliaryRay r q) :=
    original_chartPhysicalJetMeasure_changeAuxiliary r r' B g hB hg hSig hsG hnG
      hconv hb hv q σ hσ ν hfin hRep
  have hSwap : ((C.withDensity (w ∘ chartAuxiliaryRay r q)).withDensity d) =
      (C.withDensity d).withDensity (w ∘ chartAuxiliaryRay r q) := by
    rw [← withDensity_mul C hWray hD, ← withDensity_mul C hD hWray, mul_comm]
  change (C'.withDensity d).map (chartAuxiliaryRay r' q) =
    (((C.withDensity d).map (chartAuxiliaryRay r q)).withDensity w).map (cotangentNormalize r')
  rw [hChart, hSwap, map_withDensity_comp _ hRay _ w hW,
    Measure.map_map (measurable_cotangentNormalize r') hRay, chartAuxiliaryRay_changeAuxiliary r r' q]

end Burnett.Microlocal.Overlap
