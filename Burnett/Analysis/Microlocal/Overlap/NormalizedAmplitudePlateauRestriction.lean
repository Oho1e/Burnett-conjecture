import Burnett.Analysis.Microlocal.Overlap.CommonPhysicalBasePlateau
import Burnett.Analysis.Microlocal.Overlap.OriginalAmplitudePlateau

/-! Normalize the actual complex amplitude entries by the original chart cutoffs. -/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (chartAuxiliaryAmplitude)
open Burnett.F05.OverlapCovectors (roundOverlap measurableSet_roundOverlap tensorPairTransition)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.OverlapWindows (CommonCutoffPatch)
open scoped ContDiff Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def amplitudeCosphereWindow (r : Metric (M := M)) (K : Set M) : Set (UnitCosphere.Cosphere r) :=
  UnitCosphere.projection ⁻¹' K

def amplitudeChartWindow (r : Metric (M := M)) (q : CompactChartInput M) (K : Set M) :
    Set (Chart q.ball) :=
  chartUnitCospherePoint r q ⁻¹' amplitudeCosphereWindow r K

theorem continuous_amplitudeChartBase (r : Metric (M := M)) (q : CompactChartInput M) :
    Continuous (fun z : Chart q.ball => UnitCosphere.projection (chartUnitCospherePoint r q z)) :=
  (UnitCosphere.continuous_projection r).comp (continuous_chartUnitCospherePoint r q)

/-- The scalar reciprocal-square for the cutoff of this original chart. -/
def chartInverseCutoffComplexSquare (q : CompactChartInput M) (z : Chart q.ball) : ℂ :=
  ((((q.cutoff : CoordinateSpace → ℝ) z.1)⁻¹) ^ 2 : ℝ)

/-- First restrict the original trace to the base window, then form the finite
complex entry with the reciprocal cutoff square, and push it to the unit cosphere.
The application lemmas verify integrability on the chosen window. -/
def normalizedCosphereChartEntryOn (r : Metric (M := M)) (q : CompactChartInput M)
    (μ : Measure (Chart q.ball)) (F : Chart q.ball → ℂ) (K : Set M) :
    ComplexMeasure (UnitCosphere.Cosphere r) :=
  ((μ.restrict (amplitudeChartWindow r q K)).withDensityᵥ
    (fun z => chartInverseCutoffComplexSquare q z * F z)).map (chartUnitCospherePoint r q)

/-- The original receiving amplitude represented in the fixed source chart frame. -/
def transportedAmplitudeEntry (r : Metric (M := M)) (q d : CompactChartInput M)
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (u v : Pair) (y : Chart d.ball) : ℂ :=
  let D := tensorPairTransition (receivingToSourceCotangent q d y.1)
  (D * chartAuxiliaryAmplitude r d νd hfd y * Dᴴ) u v

def normalizedCosphereAmplitudeEntryOn (r : Metric (M := M)) (q : CompactChartInput M)
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
    (u v : Pair) (K : Set M) : ComplexMeasure (UnitCosphere.Cosphere r) :=
  normalizedCosphereChartEntryOn r q (traceMeasure νq)
    (fun z => chartAuxiliaryAmplitude r q νq hfq z u v) K

def normalizedCosphereTransportedAmplitudeEntryOn (r : Metric (M := M)) (q d : CompactChartInput M)
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (u v : Pair) (K : Set M) : ComplexMeasure (UnitCosphere.Cosphere r) :=
  normalizedCosphereChartEntryOn r d (traceMeasure νd) (transportedAmplitudeEntry r q d νd hfd u v) K

variable {q d : CompactChartInput M} {x : CoordinateSpace}
variable (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)
variable (r : Metric (M := M))

theorem source_amplitudeChartWindow_commonPatch :
    amplitudeChartWindow r q (commonPatchBasePlateau p) =
      {z : Chart q.ball | (z.1 : CoordinateSpace) ∈ Metric.closedBall x (p.sourceRadius / 2)} :=
  chartAuxiliaryRay_preimage_source_commonPatchPlateau p r

theorem target_amplitudeChartWindow_commonPatch :
    amplitudeChartWindow r d (commonPatchBasePlateau p) = p.targetPhasePlateau :=
  chartAuxiliaryRay_preimage_target_commonPatchPlateau p r

variable (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
variable (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))

private theorem sourcePlateauTrace_map :
    (sourcePlateauTrace p νq).map (Subtype.val : roundOverlap q d → Chart q.ball) =
      (traceMeasure νq).restrict (amplitudeChartWindow r q (commonPatchBasePlateau p)) := by
  let E := amplitudeChartWindow r q (commonPatchBasePlateau p)
  have hE : MeasurableSet E := by
    dsimp only [E]
    rw [source_amplitudeChartWindow_commonPatch p r]
    exact (continuous_subtype_val.comp continuous_fst).measurable Metric.isClosed_closedBall.measurableSet
  have hSub : E ⊆ roundOverlap q d := by
    dsimp only [E]
    rw [source_amplitudeChartWindow_commonPatch p r]
    exact sourcePlateau_subset_roundOverlap p
  have hPre : (Subtype.val : roundOverlap q d → Chart q.ball) ⁻¹' E = sourceRoundPlateau p := by
    dsimp only [E]
    rw [source_amplitudeChartWindow_commonPatch p r]
    rfl
  rw [sourcePlateauTrace, ← hPre, ← Measure.restrict_map measurable_subtype_coe hE,
    map_comap_subtype_coe (measurableSet_roundOverlap q d), Measure.restrict_restrict hE,
    inter_eq_left.mpr hSub]

/-- On the source plateau the previously integrated smooth factor is the reciprocal
of the original source cutoff. The integrability is transferred along the actual chart trace. -/
theorem sourceAmplitudePlateau_eq_normalized (u v : Pair)
    (hI : Integrable (fun z : roundOverlap q d => sourceNormalizedAmplitudeDensity p r νq hfq u v z.1)
      (sourcePlateauTrace p νq)) :
    let K := commonPatchBasePlateau p
    let f := fun z : Chart q.ball => chartInverseCutoffComplexSquare q z *
      chartAuxiliaryAmplitude r q νq hfq z u v
    Integrable f ((traceMeasure νq).restrict (amplitudeChartWindow r q K)) ∧
      ((sourcePlateauTrace p νq).withDensityᵥ
          (fun z : roundOverlap q d => sourceNormalizedAmplitudeDensity p r νq hfq u v z.1)).map
        (fun z => chartUnitCospherePoint r q z.1) =
        normalizedCosphereAmplitudeEntryOn r q νq hfq u v K := by
  intro K f
  let φ := chartUnitCospherePoint r q
  let μ := sourcePlateauTrace p νq
  let μ' := (traceMeasure νq).restrict (amplitudeChartWindow r q K)
  let F := sourceNormalizedAmplitudeDensity p r νq hfq u v
  let val : roundOverlap q d → Chart q.ball := Subtype.val
  have he : MeasurableEmbedding val := MeasurableEmbedding.subtype_coe (measurableSet_roundOverlap q d)
  have hμ : μ.map val = μ' := sourcePlateauTrace_map p r νq
  have hI' : Integrable (F ∘ val) μ := hI
  have hF : Integrable F μ' := hμ ▸ he.integrable_map_iff.mpr hI'
  have hE : MeasurableSet (amplitudeChartWindow r q K) := by
    change MeasurableSet (amplitudeChartWindow r q (commonPatchBasePlateau p))
    rw [source_amplitudeChartWindow_commonPatch p r]
    exact (continuous_subtype_val.comp continuous_fst).measurable Metric.isClosed_closedBall.measurableSet
  have hEq : F =ᵐ[μ'] f := by
    filter_upwards [ae_restrict_mem (μ := traceMeasure νq) hE] with z hz
    have hz' : (z.1 : CoordinateSpace) ∈ Metric.closedBall x (p.sourceRadius / 2) := by
      rw [source_amplitudeChartWindow_commonPatch p r] at hz
      exact hz
    simp only [F, f, sourceNormalizedAmplitudeDensity, chartInverseCutoffComplexSquare,
      p.sourceFactor_on_halfBall hz']
  have hf : Integrable f μ' := hF.congr hEq
  refine ⟨hf, ?_⟩
  have hφ : Measurable φ := (continuous_chartUnitCospherePoint r q).measurable
  ext S hS
  change ((μ.withDensityᵥ (F ∘ val)).map (φ ∘ val)) S = ((μ'.withDensityᵥ f).map φ) S
  rw [VectorMeasure.map_apply _ (hφ.comp he.measurable) hS,
    withDensityᵥ_apply hI' ((hφ.comp he.measurable) hS),
    VectorMeasure.map_apply _ hφ hS, withDensityᵥ_apply hf (hφ hS)]
  calc
    _ = ∫ z in φ ⁻¹' S, F z ∂μ.map val := by
      rw [he.setIntegral_map]
      rfl
    _ = _ := by
      rw [hμ]
      exact integral_congr_ae (ae_restrict_of_ae hEq)

/-- The target factor is removed using the target cutoff while preserving the
actual congruence that expresses its amplitude in the source coordinates. -/
theorem targetAmplitudePlateau_eq_normalized (u v : Pair)
    (hI : Integrable (targetTransformedAmplitudeDensity p r νd hfd u v)
      ((traceMeasure νd).restrict p.targetPhasePlateau)) :
    let K := commonPatchBasePlateau p
    let f := fun z : Chart d.ball => chartInverseCutoffComplexSquare d z *
      transportedAmplitudeEntry r q d νd hfd u v z
    Integrable f ((traceMeasure νd).restrict (amplitudeChartWindow r d K)) ∧
      (((traceMeasure νd).restrict p.targetPhasePlateau).withDensityᵥ
          (targetTransformedAmplitudeDensity p r νd hfd u v)).map (chartUnitCospherePoint r d) =
        normalizedCosphereTransportedAmplitudeEntryOn r q d νd hfd u v K := by
  intro K f
  let μ := (traceMeasure νd).restrict p.targetPhasePlateau
  let F := targetTransformedAmplitudeDensity p r νd hfd u v
  have hEq : F =ᵐ[μ] f := by
    filter_upwards [ae_restrict_mem (μ := traceMeasure νd) p.measurableSet_targetPhasePlateau] with y hy
    simp only [F, f, targetTransformedAmplitudeDensity, transportedAmplitudeEntry,
      chartInverseCutoffComplexSquare, p.targetFactor_on_targetPlateau hy]
  have hf : Integrable f μ := hI.congr hEq
  have hK : amplitudeChartWindow r d K = p.targetPhasePlateau := target_amplitudeChartWindow_commonPatch p r
  refine ⟨hK.symm ▸ hf, ?_⟩
  rw [normalizedCosphereTransportedAmplitudeEntryOn, normalizedCosphereChartEntryOn, hK]
  apply congrArg (fun n : ComplexMeasure (Chart d.ball) => n.map (chartUnitCospherePoint r d))
  ext S hS
  rw [withDensityᵥ_apply hI hS, withDensityᵥ_apply hf hS]
  exact integral_congr_ae (ae_restrict_of_ae hEq)

variable [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The two original complex amplitude entries on the actual plateau, divided by
the original cutoffs, agree in the fixed source coordinates. -/
theorem original_commonPatch_normalizedCosphereAmplitudeEntry_eq
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hbnd : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hRq : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ νq hfq)
    (hRd : RepresentsCompactJetPairings d.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB d.center d.cutoff
        (d.cutoff_support.trans d.ball_in_chart)) σ νd hfd) (u v : Pair) :
    let K := commonPatchBasePlateau p
    Integrable (fun z : Chart q.ball => chartInverseCutoffComplexSquare q z *
      chartAuxiliaryAmplitude r q νq hfq z u v)
      ((traceMeasure νq).restrict (amplitudeChartWindow r q K)) ∧
    Integrable (fun z : Chart d.ball => chartInverseCutoffComplexSquare d z *
      transportedAmplitudeEntry r q d νd hfd u v z)
      ((traceMeasure νd).restrict (amplitudeChartWindow r d K)) ∧
    normalizedCosphereAmplitudeEntryOn r q νq hfq u v K =
      normalizedCosphereTransportedAmplitudeEntryOn r q d νd hfd u v K := by
  intro K
  have h := original_commonPatch_amplitudeAgreement p r νq hfq νd hfd B g hB hg hsB hsG hnB hnG
    hconv hbnd hv σ hσ hRq hRd u v
  obtain ⟨hQ, hD, _⟩ := h.2 (fun _ => 1) measurable_const 1 zero_le_one (fun _ => by simp)
    univ MeasurableSet.univ
  simp only [one_mul] at hQ hD
  obtain ⟨hQI, hQeq⟩ := sourceAmplitudePlateau_eq_normalized p r νq hfq u v hQ
  obtain ⟨hDI, hDeq⟩ := targetAmplitudePlateau_eq_normalized p r νd hfd u v hD
  have hPlateau := roundOverlap_complexMeasure_map_cosphere_eq r q d _ _ h.1
  exact ⟨hQI, hDI, hQeq.symm.trans (hPlateau.trans hDeq)⟩

end Burnett.Microlocal.Overlap
