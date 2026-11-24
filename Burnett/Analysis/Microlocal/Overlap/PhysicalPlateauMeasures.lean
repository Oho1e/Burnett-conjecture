import Burnett.Analysis.Microlocal.Overlap.ChartPhysicalJetMeasure
import Burnett.Analysis.Microlocal.Overlap.PositiveDensityTransport

/-! The positive measures of two original charts on their common plateau. -/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric
open Burnett.F05.OverlapCovectors
  (roundOverlap measurableSet_roundOverlap continuous_roundOverlapTransition)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.OverlapWindows (CommonCutoffPatch)
open Burnett.Microlocal.SmoothBaseTests (BallData)
open Burnett.X02.SobolevTestJet (D test_smooth)
open scoped ContDiff ENNReal Manifold

private theorem continuous_chartCutoffSquare {K : BallData} (a : D) :
    Continuous (fun z : Chart K => ((a : CoordinateSpace → ℝ) z.1 ^ 2 : ℝ)) :=
  ((test_smooth a).continuous.comp (continuous_subtype_val.comp continuous_fst)).pow 2

private theorem integrable_chartCutoffSquare_mul {K : BallData}
    (a : D) {μ : Measure (Chart K)} {f : Chart K → ℂ} (hf : Integrable f μ) :
    Integrable (fun z => (((a : CoordinateSpace → ℝ) z.1 ^ 2 : ℝ) : ℂ) * f z) μ := by
  have ha : Continuous (fun z : Chart K => (((a : CoordinateSpace → ℝ) z.1 ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_chartCutoffSquare a)
  obtain ⟨C, hC⟩ := (isCompact_univ.image ha).isBounded.exists_norm_le
  exact hf.bdd_mul ha.measurable.aestronglyMeasurable
    ⟨C, fun z => hC _ (mem_image_of_mem _ (mem_univ z))⟩

private theorem real_nonneg_mul {a : ℝ} (ha : 0 ≤ a) {z : ℂ}
    (hz : 0 ≤ z.re ∧ z.im = 0) :
    0 ≤ ((a : ℂ) * z).re ∧ ((a : ℂ) * z).im = 0 := by
  simp [Complex.mul_re, Complex.mul_im, hz.2, mul_nonneg ha hz.1]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable {q d : CompactChartInput M} {x : CoordinateSpace}
variable (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)

omit [IsManifold Model ∞ M] in
private theorem measurableSet_sourceRoundPlateau :
    MeasurableSet (sourceRoundPlateau p) :=
  (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).measurable
    Metric.isClosed_closedBall.measurableSet

variable (r : Metric (M := M)) (B : Field (M := M))
variable (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
variable (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))

/-- The ordered physical contraction on the source side times the local
normalizing cutoff factor squared. -/
def sourcePhysicalPlateauDensity (z : roundOverlap q d) : ℂ :=
  (((p.sourceFactor : CoordinateSpace → ℝ) z.1.1 ^ 2 : ℝ) : ℂ) *
    chartPhysicalJetContraction r B q νq hfq z.1

/-- The ordered physical contraction on the target side times the local
normalizing cutoff factor squared. -/
def targetPhysicalPlateauDensity (z : Chart d.ball) : ℂ :=
  (((p.targetFactor : CoordinateSpace → ℝ) z.1 ^ 2 : ℝ) : ℂ) *
    chartPhysicalJetContraction r B d νd hfd z

/-- Pull the original chart's positive measure to the overlap, restrict to
the source plateau and apply its own squared cutoff normalization. -/
def sourcePhysicalPlateauMeasure (hn : IsNondegenerate B) : Measure (roundOverlap q d) :=
  (((chartPhysicalJetMeasure r B hn q νq hfq).comap Subtype.val).restrict
    (sourceRoundPlateau p)).withDensity
      (fun z => ENNReal.ofReal ((p.sourceFactor : CoordinateSpace → ℝ) z.1.1 ^ 2))

/-- Restrict the receiving chart's positive measure to its plateau and apply
its own squared cutoff normalization. -/
def targetPhysicalPlateauMeasure (hn : IsNondegenerate B) : Measure (Chart d.ball) :=
  ((chartPhysicalJetMeasure r B hn d νd hfd).restrict p.targetPhasePlateau).withDensity
    (fun z => ENNReal.ofReal ((p.targetFactor : CoordinateSpace → ℝ) z.1 ^ 2))

/-- The source actually divides the original chart measure by its own cutoff
squared, with restriction to the source plateau before weighting. -/
theorem sourcePhysicalPlateauMeasure_eq_invCutoff (hn : IsNondegenerate B) :
    sourcePhysicalPlateauMeasure p r B νq hfq hn =
      (((chartPhysicalJetMeasure r B hn q νq hfq).comap Subtype.val).restrict
        (sourceRoundPlateau p)).withDensity
          (fun z => ENNReal.ofReal ((((q.cutoff : CoordinateSpace → ℝ) z.1.1)⁻¹) ^ 2)) := by
  unfold sourcePhysicalPlateauMeasure
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem
    (μ := (chartPhysicalJetMeasure r B hn q νq hfq).comap
      (Subtype.val : roundOverlap q d → Chart q.ball)) (measurableSet_sourceRoundPlateau p)] with z hz
  exact congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2)) (p.sourceFactor_on_halfBall hz)

/-- The target uses its own cutoff's inverse square on the transported plateau. -/
theorem targetPhysicalPlateauMeasure_eq_invCutoff (hn : IsNondegenerate B) :
    targetPhysicalPlateauMeasure p r B νd hfd hn =
      ((chartPhysicalJetMeasure r B hn d νd hfd).restrict p.targetPhasePlateau).withDensity
        (fun z => ENNReal.ofReal ((((d.cutoff : CoordinateSpace → ℝ) z.1)⁻¹) ^ 2)) := by
  unfold targetPhysicalPlateauMeasure
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem
    (μ := chartPhysicalJetMeasure r B hn d νd hfd) p.measurableSet_targetPhasePlateau] with z hz
  exact congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2)) (p.targetFactor_on_targetPlateau hz)

omit [IsManifold Model ∞ M] in
private theorem sourcePlateauTrace_restrict_preimage {Z : Set (Chart q.ball)} (hZ : MeasurableSet Z) :
    (sourcePlateauTrace p νq).restrict (Subtype.val ⁻¹' Z) =
      (((traceMeasure νq).restrict Z).comap (Subtype.val : roundOverlap q d → Chart q.ball)).restrict
        (sourceRoundPlateau p) := by
  rw [sourcePlateauTrace, (MeasurableEmbedding.subtype_coe (measurableSet_roundOverlap q d)).comap_restrict]
  exact Measure.restrict_comm (measurable_subtype_coe hZ)

private theorem integrable_source_contraction (hB : IsSmooth B) (hn : IsNondegenerate B) :
    Integrable (fun z : roundOverlap q d => chartPhysicalJetContraction r B q νq hfq z.1)
      (sourcePlateauTrace p νq) := by
  have hf := integrable_chartPhysicalJetContraction r B hB hn q νq hfq
  have hi : IntegrableOn (chartPhysicalJetContraction r B q νq hfq) (roundOverlap q d)
      (traceMeasure νq) := hf.integrableOn
  exact ((integrableOn_iff_comap_subtypeVal (measurableSet_roundOverlap q d)).mp hi).mono_measure
    Measure.restrict_le_self

private theorem integrable_sourcePhysicalPlateauDensity (hB : IsSmooth B) (hn : IsNondegenerate B) :
    Integrable (sourcePhysicalPlateauDensity p r B νq hfq)
      ((sourcePlateauTrace p νq).restrict (Subtype.val ⁻¹' chartAuxiliaryNull r B hn q)) := by
  have hf := integrable_chartPhysicalJetContraction r B hB hn q νq hfq
  have hi := integrable_chartCutoffSquare_mul p.sourceFactor hf
  have hOn : IntegrableOn
      (fun z : Chart q.ball => (((p.sourceFactor : CoordinateSpace → ℝ) z.1 ^ 2 : ℝ) : ℂ) *
        chartPhysicalJetContraction r B q νq hfq z)
      (roundOverlap q d) (traceMeasure νq) := hi.integrableOn
  have hPull := (integrableOn_iff_comap_subtypeVal (measurableSet_roundOverlap q d)).mp hOn
  exact (hPull.mono_measure (Measure.restrict_le_self (s := sourceRoundPlateau p))).mono_measure
    Measure.restrict_le_self

private theorem integrable_targetPhysicalPlateauDensity (hB : IsSmooth B) (hn : IsNondegenerate B) :
    Integrable (targetPhysicalPlateauDensity p r B νd hfd)
      (((traceMeasure νd).restrict p.targetPhasePlateau).restrict (chartAuxiliaryNull r B hn d)) := by
  have hf := integrable_chartPhysicalJetContraction r B hB hn d νd hfd
  have h := integrable_chartCutoffSquare_mul p.targetFactor hf
  exact (h.mono_measure (Measure.restrict_le_self (s := p.targetPhasePlateau))).mono_measure
    Measure.restrict_le_self

theorem sourcePhysicalPlateauMeasure_eq_density (hB : IsSmooth B) (hsB : IsSymmetric B)
    (hn : IsNondegenerate B) :
    sourcePhysicalPlateauMeasure p r B νq hfq hn =
      positiveMeasureOfComplexDensity
        ((sourcePlateauTrace p νq).restrict (Subtype.val ⁻¹' chartAuxiliaryNull r B hn q))
        (sourcePhysicalPlateauDensity p r B νq hfq) := by
  have hO := measurableSet_roundOverlap q d
  have hP := measurableSet_sourceRoundPlateau p
  have hZ := measurableSet_chartAuxiliaryNull r B hB hsB hn q
  have hC := (integrable_source_contraction p r B νq hfq hB hn).mono_measure
    (Measure.restrict_le_self (s := Subtype.val ⁻¹' chartAuxiliaryNull r B hn q))
  have hW := (continuous_chartCutoffSquare (K := q.ball) p.sourceFactor).measurable.comp
    (measurable_subtype_coe : Measurable (Subtype.val : roundOverlap q d → Chart q.ball))
  rw [sourcePhysicalPlateauMeasure, chartPhysicalJetMeasure,
    comap_positiveMeasureOfComplexDensity_subtype _ _ hO,
    restrict_positiveMeasureOfComplexDensity _ _ hP,
    ← sourcePlateauTrace_restrict_preimage p νq hZ]
  exact positiveMeasureOfComplexDensity_withDensity_ofReal _ _
    hC.aestronglyMeasurable.aemeasurable _ hW (fun z => sq_nonneg ((p.sourceFactor : CoordinateSpace → ℝ) z.1.1))

theorem targetPhysicalPlateauMeasure_eq_density (hB : IsSmooth B) (hn : IsNondegenerate B) :
    targetPhysicalPlateauMeasure p r B νd hfd hn =
      positiveMeasureOfComplexDensity
        (((traceMeasure νd).restrict p.targetPhasePlateau).restrict (chartAuxiliaryNull r B hn d))
        (targetPhysicalPlateauDensity p r B νd hfd) := by
  have hP := p.measurableSet_targetPhasePlateau
  have hC := ((integrable_chartPhysicalJetContraction r B hB hn d νd hfd).mono_measure
    (Measure.restrict_le_self (s := p.targetPhasePlateau))).mono_measure
    (Measure.restrict_le_self (s := chartAuxiliaryNull r B hn d))
  have hW := (continuous_chartCutoffSquare (K := d.ball) p.targetFactor).measurable
  rw [targetPhysicalPlateauMeasure, chartPhysicalJetMeasure,
    restrict_positiveMeasureOfComplexDensity _ _ hP, Measure.restrict_comm hP]
  exact positiveMeasureOfComplexDensity_withDensity_ofReal _ _
    hC.aestronglyMeasurable.aemeasurable _ hW (fun z => sq_nonneg ((p.targetFactor : CoordinateSpace → ℝ) z.1))

theorem isFiniteMeasure_sourcePhysicalPlateauMeasure (hB : IsSmooth B) (hsB : IsSymmetric B)
    (hn : IsNondegenerate B) : IsFiniteMeasure (sourcePhysicalPlateauMeasure p r B νq hfq hn) := by
  rw [sourcePhysicalPlateauMeasure_eq_density p r B νq hfq hB hsB hn]
  exact isFiniteMeasure_positiveMeasureOfComplexDensity
    (integrable_sourcePhysicalPlateauDensity p r B νq hfq hB hn)

theorem isFiniteMeasure_targetPhysicalPlateauMeasure (hB : IsSmooth B) (hn : IsNondegenerate B) :
    IsFiniteMeasure (targetPhysicalPlateauMeasure p r B νd hfd hn) := by
  rw [targetPhysicalPlateauMeasure_eq_density p r B νd hfd hB hn]
  exact isFiniteMeasure_positiveMeasureOfComplexDensity
    (integrable_targetPhysicalPlateauDensity p r B νd hfd hB hn)

private theorem ae_sourcePhysicalPlateauDensity_real_nonneg (hB : IsSmooth B) (hsB : IsSymmetric B)
    (hn : IsNondegenerate B)
    (hPos : ∀ᵐ z ∂(traceMeasure νq).restrict (chartAuxiliaryNull r B hn q),
      0 ≤ (chartPhysicalJetContraction r B q νq hfq z).re ∧
        (chartPhysicalJetContraction r B q νq hfq z).im = 0) :
    ∀ᵐ z ∂(sourcePlateauTrace p νq).restrict (Subtype.val ⁻¹' chartAuxiliaryNull r B hn q),
      0 ≤ (sourcePhysicalPlateauDensity p r B νq hfq z).re ∧
        (sourcePhysicalPlateauDensity p r B νq hfq z).im = 0 := by
  have hZ := measurableSet_chartAuxiliaryNull r B hB hsB hn q
  rw [sourcePlateauTrace_restrict_preimage p νq hZ]
  have hPull : ∀ᵐ (z : roundOverlap q d) ∂((traceMeasure νq).restrict
        (chartAuxiliaryNull r B hn q)).comap Subtype.val,
      0 ≤ (chartPhysicalJetContraction r B q νq hfq z.1).re ∧
        (chartPhysicalJetContraction r B q νq hfq z.1).im = 0 :=
    (ae_restrict_iff_subtype (measurableSet_roundOverlap q d)).mp (ae_restrict_of_ae hPos)
  filter_upwards [ae_restrict_of_ae hPull] with z hz
  exact real_nonneg_mul (sq_nonneg ((p.sourceFactor : CoordinateSpace → ℝ) z.1.1)) hz

private theorem ae_targetPhysicalPlateauDensity_real_nonneg (hn : IsNondegenerate B)
    (hPos : ∀ᵐ z ∂(traceMeasure νd).restrict (chartAuxiliaryNull r B hn d),
      0 ≤ (chartPhysicalJetContraction r B d νd hfd z).re ∧
        (chartPhysicalJetContraction r B d νd hfd z).im = 0) :
    ∀ᵐ z ∂((traceMeasure νd).restrict p.targetPhasePlateau).restrict (chartAuxiliaryNull r B hn d),
      0 ≤ (targetPhysicalPlateauDensity p r B νd hfd z).re ∧
        (targetPhysicalPlateauDensity p r B νd hfd z).im = 0 := by
  rw [← Measure.restrict_comm p.measurableSet_targetPhasePlateau]
  filter_upwards [ae_restrict_of_ae hPos] with z hz
  exact real_nonneg_mul (sq_nonneg ((p.targetFactor : CoordinateSpace → ℝ) z.1)) hz

/-- Once the two original shell contractions are positive and have the same
integrals on transported Borel sets, the normalized plateau measures agree. -/
theorem physicalPlateauMeasure_map_eq_of_setIntegral (hB : IsSmooth B) (hsB : IsSymmetric B)
    (hn : IsNondegenerate B)
    (hPosq : ∀ᵐ z ∂(traceMeasure νq).restrict (chartAuxiliaryNull r B hn q),
      0 ≤ (chartPhysicalJetContraction r B q νq hfq z).re ∧
        (chartPhysicalJetContraction r B q νq hfq z).im = 0)
    (hPosd : ∀ᵐ z ∂(traceMeasure νd).restrict (chartAuxiliaryNull r B hn d),
      0 ≤ (chartPhysicalJetContraction r B d νd hfd z).re ∧
        (chartPhysicalJetContraction r B d νd hfd z).im = 0)
    (hCov : ∀ S : Set (Chart d.ball), MeasurableSet S →
      (∫ z in (transportedRoundPoint q d ⁻¹' S) ∩ (Subtype.val ⁻¹' chartAuxiliaryNull r B hn q),
        sourcePhysicalPlateauDensity p r B νq hfq z ∂sourcePlateauTrace p νq) =
      ∫ y in S ∩ chartAuxiliaryNull r B hn d,
        targetPhysicalPlateauDensity p r B νd hfd y ∂(traceMeasure νd).restrict p.targetPhasePlateau) :
    (sourcePhysicalPlateauMeasure p r B νq hfq hn).map (transportedRoundPoint q d) =
      targetPhysicalPlateauMeasure p r B νd hfd hn := by
  have hT : Measurable (transportedRoundPoint q d) :=
    (continuous_subtype_val.comp (continuous_roundOverlapTransition q d)).measurable
  rw [sourcePhysicalPlateauMeasure_eq_density p r B νq hfq hB hsB hn,
    targetPhysicalPlateauMeasure_eq_density p r B νd hfd hB hn]
  exact map_positiveMeasureOfComplexDensity_eq_of_setIntegral _ _ _ _ _ hT _ _
    (integrable_sourcePhysicalPlateauDensity p r B νq hfq hB hn)
    (integrable_targetPhysicalPlateauDensity p r B νd hfd hB hn)
    (ae_sourcePhysicalPlateauDensity_real_nonneg p r B νq hfq hB hsB hn hPosq)
    (ae_targetPhysicalPlateauDensity_real_nonneg p r B νd hfd hn hPosd) hCov

end Burnett.Microlocal.Overlap
