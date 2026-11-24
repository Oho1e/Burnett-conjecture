import Burnett.Analysis.Microlocal.Overlap.OriginalChartAuxiliaryDensityChange
import Burnett.Geometry.Cotangent.RadialExtension

/-! The same original chart measure under a change of auxiliary unit section. -/

set_option autoImplicit false
set_option maxHeartbeats 1100000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension (contMDiff_dualEnergy cotangentNorm cotangentNormalize)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.FixedChartGeometricDensity (auxiliaryScale auxiliaryUnitCovector roundCovector)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open scoped ContDiff ENNReal Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem continuous_auxiliaryDualSquare (r : Metric (M := M)) :
    Continuous (dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r)) :=
  (contMDiff_dualEnergy r.inner (ManifoldBilinear.isSmooth_inner r)
    (GlobalLeviCivita.inner_nondegenerate r) r.symm).continuous

/-- The new chart ray is the actual cotangent normalization of the old chart ray. -/
theorem chartAuxiliaryRay_changeAuxiliary (r r' : Metric (M := M)) (q : CompactChartInput M) :
    chartAuxiliaryRay r' q = cotangentNormalize r' ∘ chartAuxiliaryRay r q := by
  funext p
  have hr := chartAuxiliaryNorm_pos r q p
  have hr' := chartAuxiliaryNorm_pos r' q p
  have hscale : (cotangentNorm r' (chartAuxiliaryRay r q p))⁻¹ *
      auxiliaryScale (chartAuxiliaryInverse r q p.1) (roundCovector p) =
      auxiliaryScale (chartAuxiliaryInverse r' q p.1) (roundCovector p) := by
    rw [cotangentNorm, chartAuxiliaryRay_changeWeight_eq_ratio, Real.sqrt_div hr'.le]
    simp only [auxiliaryScale]
    field_simp [(Real.sqrt_pos.mpr hr).ne', (Real.sqrt_pos.mpr hr').ne']
  let u := chartAuxiliaryRay r' q p
  let v := cotangentNormalize r' (chartAuxiliaryRay r q p)
  have hcoords : cotangentCoords q.center v = cotangentCoords q.center u := by
    change cotangentCoords q.center (cotangentNormalize r' (chartAuxiliaryRay r q p)) =
      cotangentCoords q.center (chartAuxiliaryRay r' q p)
    simp only [cotangentNormalize, cotangentScale_coords, chartAuxiliaryRay_coords]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, auxiliaryUnitCovector]
    rw [← mul_assoc, hscale]
  change u = v
  let e := chartAt CoordinateSpace q.center
  have hu : u.1 ∈ e.source := e.symm_mapsTo (q.ball_in_chart p.1.property)
  have hv : v.1 ∈ e.source := hu
  calc
    u = cotangentAssemble q.center (u.1, cotangentCoords q.center u) :=
      (cotangentAssemble_coords q.center u hu).symm
    _ = cotangentAssemble q.center (v.1, cotangentCoords q.center v) :=
      congrArg (cotangentAssemble q.center) (Prod.ext rfl hcoords.symm)
    _ = v := cotangentAssemble_coords q.center v hv

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- The positive measures on the fixed round chart have the same reference
trace and null restriction. The density of the new chart measure relative to
the old one is the squared new norm of its old auxiliary unit ray. -/
theorem original_chartPhysicalJetMeasure_changeAuxiliary
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
    chartPhysicalJetMeasure r' B hSig.isNondegenerate q ν hfin =
      (chartPhysicalJetMeasure r B hSig.isNondegenerate q ν hfin).withDensity
        (fun p => ENNReal.ofReal (dualEnergy r'.inner (GlobalLeviCivita.inner_nondegenerate r')
          (chartAuxiliaryRay r q p))) := by
  let Z := chartAuxiliaryNull r B hSig.isNondegenerate q
  let τ := (traceMeasure ν).restrict Z
  let d (u : Metric (M := M)) (p : Chart q.ball) :=
    ENNReal.ofReal (chartPhysicalJetContraction u B q ν hfin p).re
  let w (p : Chart q.ball) :=
    dualEnergy r'.inner (GlobalLeviCivita.inner_nondegenerate r') (chartAuxiliaryRay r q p)
  have hw (p : Chart q.ball) : 0 ≤ w p := by
    change 0 ≤ dualEnergy r'.inner (GlobalLeviCivita.inner_nondegenerate r') (chartAuxiliaryRay r q p)
    rw [chartAuxiliaryRay_changeWeight_eq_ratio]
    exact (div_pos (chartAuxiliaryNorm_pos r' q p) (chartAuxiliaryNorm_pos r q p)).le
  have hW : AEMeasurable (fun p => ENNReal.ofReal (w p)) τ :=
    (ENNReal.measurable_ofReal.comp
      ((continuous_auxiliaryDualSquare r').comp (continuous_chartAuxiliaryRay r q)).measurable).aemeasurable
  have hD : AEMeasurable (d r) τ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (Complex.continuous_re.measurable.comp_aemeasurable
        (((integrable_chartPhysicalJetContraction r B hB hSig.isNondegenerate q ν hfin).mono_measure
          Measure.restrict_le_self).aestronglyMeasurable.aemeasurable))
  have hScale := ae_original_chartPhysicalJetContraction_changeAuxiliary
    r r' B g hB hg hSig hsG hnG hconv hb hv q σ hσ ν hfin hRep
  unfold chartPhysicalJetMeasure positiveMeasureOfComplexDensity
  rw [chartAuxiliaryNull_changeAuxiliary r r' B hSig.isSymmetric hSig.isNondegenerate q]
  change τ.withDensity (d r') = (τ.withDensity (d r)).withDensity (fun p => ENNReal.ofReal (w p))
  rw [← withDensity_mul₀ hD hW]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_of_ae hScale] with p hp
  change ENNReal.ofReal (chartPhysicalJetContraction r' B q ν hfin p).re =
    ENNReal.ofReal (chartPhysicalJetContraction r B q ν hfin p).re * ENNReal.ofReal (w p)
  change chartPhysicalJetContraction r' B q ν hfin p =
    (w p : ℂ) * chartPhysicalJetContraction r B q ν hfin p at hp
  rw [hp, Complex.re_ofReal_mul, ENNReal.ofReal_mul (hw p), mul_comm]

variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M] in
theorem measurable_cotangentNormalize (r : Metric (M := M)) :
    Measurable (cotangentNormalize r) := by
  have hNorm : Measurable (cotangentNorm r) :=
    (Real.continuous_sqrt.comp (continuous_auxiliaryDualSquare r)).measurable
  exact continuous_cotangentScale.measurable.comp (hNorm.inv.prodMk measurable_id)

theorem map_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) (μ : Measure X) (w : Y → ℝ≥0∞) (hw : Measurable w) :
    (μ.map f).withDensity w = (μ.withDensity (w ∘ f)).map f := by
  ext S hS
  rw [withDensity_apply _ hS, Measure.map_apply hf hS, withDensity_apply _ (hf hS)]
  exact setLIntegral_map hS hw hf

/-- On the actual cotangent bundle the new measure of the same original chart
is obtained by weighting its old measure and applying the new normalization. -/
theorem original_cotangentPhysicalJetMeasure_changeAuxiliary
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
    cotangentPhysicalJetMeasure r' B hSig.isNondegenerate q ν hfin =
      ((cotangentPhysicalJetMeasure r B hSig.isNondegenerate q ν hfin).withDensity
        (fun p => ENNReal.ofReal (dualEnergy r'.inner (GlobalLeviCivita.inner_nondegenerate r') p))).map
          (cotangentNormalize r') := by
  let w (p : CotangentBundle M) :=
    ENNReal.ofReal (dualEnergy r'.inner (GlobalLeviCivita.inner_nondegenerate r') p)
  have hw : Measurable w :=
    ENNReal.measurable_ofReal.comp (continuous_auxiliaryDualSquare r').measurable
  have hChart := original_chartPhysicalJetMeasure_changeAuxiliary
    r r' B g hB hg hSig hsG hnG hconv hb hv q σ hσ ν hfin hRep
  have hRay := (continuous_chartAuxiliaryRay r q).measurable
  change (chartPhysicalJetMeasure r' B hSig.isNondegenerate q ν hfin).map (chartAuxiliaryRay r' q) =
    (((chartPhysicalJetMeasure r B hSig.isNondegenerate q ν hfin).map
      (chartAuxiliaryRay r q)).withDensity w).map (cotangentNormalize r')
  rw [hChart, map_withDensity_comp _ hRay _ w hw,
    Measure.map_map (measurable_cotangentNormalize r') hRay, chartAuxiliaryRay_changeAuxiliary r r' q]
  rfl

end Burnett.Microlocal.Overlap
