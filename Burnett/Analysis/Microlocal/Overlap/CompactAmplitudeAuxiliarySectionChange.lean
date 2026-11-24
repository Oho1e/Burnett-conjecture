import Burnett.Analysis.Microlocal.Overlap.ChartAmplitudeAuxiliarySectionChange
import Burnett.Analysis.Microlocal.Overlap.CompactAmplitudeTraceLift

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 700000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open UnitCosphere (Cosphere projection)
open CotangentAngularExtension (cotangentNorm cotangentNorm_sq cotangentNormalize_projection)
open CotangentUnitNormalization (unitShell_punctured)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (chartAuxiliaryAmplitude)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open scoped ContDiff ENNReal Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M]

/-- On the same Borel base window, the unweighted original reference trace,
with the reciprocal cutoff already applied, is transported by the phase map. -/
theorem chartCosphereControlMeasure_restrict_changeAuxiliary (r r' : Metric (M := M))
    (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball))
    {K : Set M} (hK : MeasurableSet K) :
    (chartCosphereControlMeasure r' q ν).restrict (amplitudeCosphereWindow r' K) =
      ((chartCosphereControlMeasure r q ν).restrict (amplitudeCosphereWindow r K)).map
        (renormalizeUnitCosphere r r') := by
  have hProjection (p : Cosphere r) : projection (renormalizeUnitCosphere r r' p) = projection p :=
    cotangentNormalize_projection r' p.val
  have hBase : amplitudeChartWindow r' q K = amplitudeChartWindow r q K := by
    ext z
    change projection (chartAuxiliaryCosphere r' q z) ∈ K ↔
      projection (chartAuxiliaryCosphere r q z) ∈ K
    rw [congrFun (chartAuxiliaryCosphere_changeAuxiliary r r' q) z, Function.comp_apply, hProjection]
  let κ := ((traceMeasure ν).restrict (amplitudeChartWindow r q K)).withDensity
    (chartInverseCutoffSquare q)
  let κ' := ((traceMeasure ν).restrict (amplitudeChartWindow r' q K)).withDensity
    (chartInverseCutoffSquare q)
  have hκ : κ' = κ := congrArg (fun U => ((traceMeasure ν).restrict U).withDensity
    (chartInverseCutoffSquare q)) hBase
  have hF := (measurableEmbedding_renormalizeUnitCosphere r r').measurable
  calc
    _ = κ'.map (chartAuxiliaryCosphere r' q) := chartCosphereControlMeasure_restrict r' q ν hK
    _ = κ.map (chartAuxiliaryCosphere r' q) := congrArg (Measure.map (chartAuxiliaryCosphere r' q)) hκ
    _ = (κ.map (chartAuxiliaryCosphere r q)).map (renormalizeUnitCosphere r r') := by
      rw [Measure.map_map hF (continuous_chartAuxiliaryCosphere r q).measurable,
        ← chartAuxiliaryCosphere_changeAuxiliary r r' q]
    _ = _ := congrArg (Measure.map (renormalizeUnitCosphere r r'))
      (chartCosphereControlMeasure_restrict r q ν hK).symm

variable [SecondCountableTopology M] [T2Space M]

/-- Each complex oriented amplitude entry, from the same original sequence and
chart witness, changes by the squared new norm on the old cosphere followed by
positive radial normalization. Both densities use the same reciprocal cutoff.
The equivalent test identity holds for any bounded Borel complex test. -/
theorem original_normalizedCosphereAmplitudeEntry_changeAuxiliary
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
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin)
    (i j : Pair) {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus) :
    let τ := (chartCosphereControlMeasure r q ν).restrict (amplitudeCosphereWindow r K)
    let τ' := (chartCosphereControlMeasure r' q ν).restrict (amplitudeCosphereWindow r' K)
    let a (p : Cosphere r) := liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hfin) p i j
    let a' (p : Cosphere r') := liftChartAmplitude r' q (chartAuxiliaryAmplitude r' q ν hfin) p i j
    let F := renormalizeUnitCosphere r r'
    let normWeight (p : Cosphere r) := cotangentAuxiliaryWeight r' p.val
    let weighted (p : Cosphere r) := ((cotangentNorm r' p.val ^ 2 : ℝ) : ℂ) * a p
    normalizedCosphereAmplitudeEntryOn r q ν hfin i j K = τ.withDensityᵥ a ∧
    normalizedCosphereAmplitudeEntryOn r' q ν hfin i j K =
        ((τ.withDensity normWeight).withDensityᵥ a).map F ∧
    ∀ (ψ : Cosphere r' → ℂ), Measurable ψ → (∃ C : ℝ, ∀ p, ‖ψ p‖ ≤ C) →
      Integrable (fun p => ψ p * a' p) τ' ∧
      Integrable (fun p => ψ (F p) * weighted p) τ ∧
      (∫ p, ψ p * a' p ∂τ') = ∫ p, ψ (F p) * weighted p ∂τ := by
  intro τ τ' a a' F normWeight weighted
  have hKm := hK.isClosed.measurableSet
  have hF : MeasurableEmbedding F := measurableEmbedding_renormalizeUnitCosphere r r'
  have hMap : τ' = τ.map F := chartCosphereControlMeasure_restrict_changeAuxiliary r r' q ν hKm
  have hChart := ae_original_chartAuxiliaryAmplitude_changeAuxiliary r r' B g hB hg hSig hsG hnG
    hconv hb hv q σ hσ ν hfin hRep
  have hPhase (z : Chart q.ball) : F (chartAuxiliaryCosphere r q z) = chartAuxiliaryCosphere r' q z :=
    (congrFun (chartAuxiliaryCosphere_changeAuxiliary r r' q) z).symm
  have hMatch : (fun p => a' (F p)) =ᵐ[τ] weighted := by
    change (fun p => a' (F p)) =ᵐ[(chartCosphereControlMeasure r q ν).restrict
      (amplitudeCosphereWindow r K)] weighted
    rw [chartCosphereControlMeasure_restrict r q ν hKm]
    apply (measurableEmbedding_chartAuxiliaryCosphere r q).ae_map_iff.mpr
    have hChartRestricted := (withDensity_absolutelyContinuous
      ((traceMeasure ν).restrict (amplitudeChartWindow r q K)) (chartInverseCutoffSquare q)).ae_eq
        (ae_restrict_of_ae hChart)
    filter_upwards [hChartRestricted] with z hz
    change liftChartAmplitude r' q (chartAuxiliaryAmplitude r' q ν hfin)
      (F (chartAuxiliaryCosphere r q z)) i j =
      ((cotangentNorm r' (chartAuxiliaryCosphere r q z).val ^ 2 : ℝ) : ℂ) *
        liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hfin) (chartAuxiliaryCosphere r q z) i j
    rw [hPhase, liftChartAmplitude_apply, liftChartAmplitude_apply, hz, Matrix.smul_apply, smul_eq_mul]
    rfl
  obtain ⟨_, hOld⟩ := normalizedCosphereChartEntryOn_eq_withDensity_liftChartAmplitude r q ν
    (chartAuxiliaryAmplitude r q ν hfin) hKm i j
    (integrable_normalizedCosphereAmplitudeEntry_on_compact r q ν hfin i j hK hSub)
  obtain ⟨ha', hNew⟩ := normalizedCosphereChartEntryOn_eq_withDensity_liftChartAmplitude r' q ν
    (chartAuxiliaryAmplitude r' q ν hfin) hKm i j
    (integrable_normalizedCosphereAmplitudeEntry_on_compact r' q ν hfin i j hK hSub)
  have ha'Map : Integrable a' (τ.map F) := hMap ▸ ha'
  have hWeightedInt : Integrable weighted τ := (hF.integrable_map_iff.mp ha'Map).congr hMatch
  have hNormWeight : Measurable normWeight := ENNReal.measurable_ofReal.comp
    ((continuous_auxiliaryDualSquare r').comp continuous_subtype_val).measurable
  have hSmul : (fun p => (normWeight p).toReal • a p) = weighted := by
    funext p
    change (ENNReal.ofReal _).toReal • a p = weighted p
    rw [← cotangentNorm_sq r' (unitShell_punctured r p.property),
      ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul]
  have hWeighted : τ.withDensityᵥ weighted = (τ.withDensity normWeight).withDensityᵥ a := by
    rw [← hSmul]
    exact withDensityᵥ_smul_eq_withDensityᵥ_withDensity' hNormWeight.aemeasurable
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (hSmul.symm ▸ hWeightedInt)
  have hChange : τ'.withDensityᵥ a' = (τ.withDensityᵥ weighted).map F := by
    ext S hS
    rw [withDensityᵥ_apply (show Integrable a' τ' from ha') hS,
      VectorMeasure.map_apply _ hF.measurable hS, withDensityᵥ_apply hWeightedInt (hF.measurable hS),
      hMap, hF.setIntegral_map]
    exact integral_congr_ae (ae_restrict_of_ae hMatch)
  refine ⟨hOld, hNew.trans (hChange.trans (congrArg (fun m : ComplexMeasure (Cosphere r) => m.map F)
    hWeighted)), ?_⟩
  intro ψ hψ hBound
  obtain ⟨C, hC⟩ := hBound
  refine ⟨ha'.bdd_mul hψ.aestronglyMeasurable ⟨C, hC⟩,
    hWeightedInt.bdd_mul (hψ.comp hF.measurable).aestronglyMeasurable ⟨C, fun p => hC (F p)⟩, ?_⟩
  rw [hMap, hF.integral_map]
  exact integral_congr_ae (hMatch.mono fun p hp => congrArg (fun c : ℂ => ψ (F p) * c) hp)

end Burnett.Microlocal.Overlap
