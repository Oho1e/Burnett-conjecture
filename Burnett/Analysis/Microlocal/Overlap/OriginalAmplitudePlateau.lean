import Burnett.Analysis.Microlocal.Overlap.AmplitudeEntryRecovery
import Burnett.Analysis.Microlocal.Overlap.NormalizedEntryWeightedTests
import Burnett.Analysis.Microlocal.Overlap.OriginalNormalizedEntryFromPlateau
import Burnett.Geometry.Cotangent.CosphereMeasure

/-! Borel amplitude transport on a common plateau of the original chart witnesses. -/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1500000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set Burnett.RicciSymbol
open Burnett.Geometry ChartVolume ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence
open Burnett.F05.ActualChartAuxiliarySection (chartAuxiliaryRay chartAuxiliaryRay_unit continuous_chartAuxiliaryRay)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (ae_originalVolume_auxiliaryAmplitude chartAuxiliaryAmplitude)
open Burnett.F05.OverlapCovectors
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.FixedChartGeometricDensity (chartPhysicalCovariance)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.OverlapWindows (CommonCutoffPatch)
open scoped BigOperators ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem measurable_roundPoint (q d : CompactChartInput M) : Measurable (transportedRoundPoint q d) :=
  (continuous_subtype_val.comp (continuous_roundOverlapTransition q d)).measurable

/-- A multiplier in source coordinates re-expressed on the original receiving chart. -/
private def receivingMultiplier (q d : CompactChartInput M) (f : Chart q.ball → ℂ) :
    Chart d.ball → ℂ :=
  Function.extend (Subtype.val : roundOverlap d q → Chart d.ball)
    (fun y => f (roundOverlapTransition d q y).1) (fun _ => 0)

private theorem receivingMultiplier_on_source (q d : CompactChartInput M)
    (f : Chart q.ball → ℂ) (z : roundOverlap q d) :
    receivingMultiplier q d f (transportedRoundPoint q d z) = f z.1 := by
  unfold receivingMultiplier transportedRoundPoint
  rw [Subtype.coe_injective.extend_apply, roundOverlapTransition_leftInverse q d z]

private theorem receivingMultiplier_on_target (q d : CompactChartInput M)
    (f : Chart q.ball → ℂ) (y : roundOverlap d q) :
    receivingMultiplier q d f y.1 = f (roundOverlapTransition d q y).1 :=
  Subtype.coe_injective.extend_apply _ _ _

private theorem measurable_receivingMultiplier (q d : CompactChartInput M)
    (f : Chart q.ball → ℂ) (hf : Continuous f) : Measurable (receivingMultiplier q d f) :=
  (MeasurableEmbedding.subtype_coe (measurableSet_roundOverlap d q)).measurable_extend
    (hf.measurable.comp (measurable_roundPoint d q)) measurable_const

private theorem bounded_receivingMultiplier (q d : CompactChartInput M)
    (f : Chart q.ball → ℂ) (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖receivingMultiplier q d f y‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image hf).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : y ∈ range (Subtype.val : roundOverlap d q → Chart d.ball)
  · obtain ⟨y', rfl⟩ := hy
    rw [receivingMultiplier_on_target]
    exact (hC _ (mem_image_of_mem f (mem_univ _))).trans (le_max_left _ _)
  · unfold receivingMultiplier
    rw [Function.extend_apply' _ _ _ hy, norm_zero]
    exact le_max_right _ _

variable {q d : CompactChartInput M} {x : CoordinateSpace}
variable (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)

omit [IsManifold Model ∞ M] in
private theorem receivingPhasePlateau_subset_overlap : p.targetPhasePlateau ⊆ roundOverlap d q := by
  intro y hy
  let e := chartTransition q.center d.center
  have hSymm : e.symm = chartTransition d.center q.center := by
    simp only [e, chartTransition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  obtain ⟨z, hz, hy⟩ := hy
  have hSub : Metric.closedBall x (p.sourceRadius / 2) ⊆ p.sourceInput.ball.closedBall :=
    Metric.closedBall_subset_closedBall (show p.sourceRadius / 2 ≤ p.sourceRadius by
      linarith [p.sourceRadius_pos])
  have hsrc : z ∈ e.source := p.sourceInput_ball_in_overlap (hSub hz)
  change e z = y.1 at hy
  change (y.1 : CoordinateSpace) ∈ (chartTransition d.center q.center).source ∧
    chartTransition d.center q.center y.1 ∈ q.ball.closedBall
  rw [← hy, ← hSymm, e.left_inv hsrc]
  exact ⟨e.mapsTo hsrc, interior_subset (p.sourceInput_ball_subset_interior (hSub hz))⟩

variable (r : Metric (M := M))
variable (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
variable (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))

/-- Contract the same original complex jet entries with the derivative-slot recovery weights.
Both chart trace measures are kept as supplied. -/
theorem normalizedAmplitudePlateau_weightedSetIntegral
    (hCov : ∀ i j : JetSlot, ((sourcePlateauTrace p νq).withDensityᵥ
        (fun z => sourceNormalizedDensity p νq hfq i j z.1)).map (transportedRoundPoint q d) =
      ((traceMeasure νd).restrict p.targetPhasePlateau).withDensityᵥ
        (targetTransformedDensity p νd hfd i j))
    (hFact : ∀ᵐ y ∂traceMeasure νd, ∀ i j : JetSlot, chartPhysicalCovariance d.ball νd hfd y i j =
      (chartUnitCovector r d y i.1 : ℂ) * (chartUnitCovector r d y j.1 : ℂ) *
        chartAuxiliaryAmplitude r d νd hfd y i.2 j.2)
    (u v : Pair)
    (a : Chart d.ball → ℂ) (ha : Measurable a) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ y, ‖a y‖ ≤ C)
    (S : Set (Chart d.ball)) (hS : MeasurableSet S) :
    let T := transportedRoundPoint q d
    let μq := sourcePlateauTrace p νq
    let μd := (traceMeasure νd).restrict p.targetPhasePlateau
    let f := fun z : roundOverlap q d => sourceNormalizedAmplitudeDensity p r νq hfq u v z.1
    let g := targetTransformedAmplitudeDensity p r νd hfd u v
    Integrable (fun z => a (T z) * f z) μq ∧ Integrable (fun y => a y * g y) μd ∧
      (∫ z in T ⁻¹' S, a (T z) * f z ∂μq) = ∫ y in S, a y * g y ∂μd := by
  classical
  intro T μq μd f g
  let c (i j : JetSlot) (z : Chart q.ball) :=
    amplitudeRecoveryCoefficient (chartUnitDual r q z) u v i j
  let b (i j : JetSlot) := receivingMultiplier q d (c i j)
  let w (i j : JetSlot) (y : Chart d.ball) := a y * b i j y
  have hc (i j : JetSlot) : Continuous (c i j) :=
    continuous_chartAmplitudeRecoveryCoefficient r q u v i j
  choose K hK hbK using fun i j : JetSlot => bounded_receivingMultiplier q d (c i j) (hc i j)
  have hw (i j : JetSlot) : Measurable (w i j) := ha.mul (measurable_receivingMultiplier q d (c i j) (hc i j))
  have hwB (i j : JetSlot) (y : Chart d.ball) : ‖w i j y‖ ≤ C * K i j := by
    rw [show w i j y = a y * b i j y from rfl, norm_mul]
    exact mul_le_mul (hb y) (hbK i j y) (norm_nonneg _) hC
  have hIQ (i j : JetSlot) :
      Integrable (fun z : roundOverlap q d => w i j (T z) * sourceNormalizedDensity p νq hfq i j z.1) μq :=
    (integrable_sourceNormalizedDensity p νq hfq i j).bdd_mul
      ((hw i j).comp (measurable_roundPoint q d)).aestronglyMeasurable
      ⟨C * K i j, fun z => hwB i j (T z)⟩
  have hID (i j : JetSlot) :
      Integrable (fun y => w i j y * targetTransformedDensity p νd hfd i j y) μd :=
    (integrable_targetTransformedDensity p νd hfd i j).bdd_mul
      (hw i j).aestronglyMeasurable ⟨C * K i j, hwB i j⟩
  have hQ : ∀ᵐ z ∂μq, (∑ i : JetSlot, ∑ j : JetSlot,
      w i j (T z) * sourceNormalizedDensity p νq hfq i j z.1) = a (T z) * f z := by
    apply Filter.Eventually.of_forall
    intro z
    have hB (i j : JetSlot) : b i j (T z) = c i j z.1 :=
      receivingMultiplier_on_source q d (c i j) z
    have hEntry := congrArg (fun w : ℂ => a (T z) * w)
      (sourceNormalizedAmplitudeDensity_recovery p r νq hfq u v z.1)
    simpa only [Finset.mul_sum, mul_assoc, w, hB, c, f] using hEntry
  have hD : ∀ᵐ y ∂μd, (∑ i : JetSlot, ∑ j : JetSlot,
      w i j y * targetTransformedDensity p νd hfd i j y) = a y * g y := by
    filter_upwards [ae_restrict_mem (μ := traceMeasure νd) p.measurableSet_targetPhasePlateau,
      ae_restrict_of_ae hFact] with y hy hyF
    let y' : roundOverlap d q := ⟨y, receivingPhasePlateau_subset_overlap p hy⟩
    have hB (i j : JetSlot) : b i j y = c i j (roundOverlapTransition d q y').1 :=
      receivingMultiplier_on_target q d (c i j) y'
    have hEntry := congrArg (fun w : ℂ => a y * w)
      (targetTransformedAmplitudeDensity_recovery p r νd hfd y' hyF u v)
    change a y * (∑ i : JetSlot, ∑ j : JetSlot,
      c i j (roundOverlapTransition d q y').1 * targetTransformedDensity p νd hfd i j y) =
        a y * targetTransformedAmplitudeDensity p r νd hfd u v y at hEntry
    simpa only [Finset.mul_sum, mul_assoc, w, hB, g] using hEntry
  refine ⟨(integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hIQ i j).congr hQ,
    (integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hID i j).congr hD, ?_⟩
  have hEq := normalizedJet_contractedSetIntegral p νq hfq νd hfd hCov w hw
    (fun i j => C * K i j) (fun i j => mul_nonneg hC (hK i j)) hwB S hS
  exact (integral_congr_ae (ae_restrict_of_ae hQ)).symm.trans
    (hEq.trans (integral_congr_ae (ae_restrict_of_ae hD)))

theorem normalizedAmplitudePlateau_map_eq
    (hCov : ∀ i j : JetSlot, ((sourcePlateauTrace p νq).withDensityᵥ
        (fun z => sourceNormalizedDensity p νq hfq i j z.1)).map (transportedRoundPoint q d) =
      ((traceMeasure νd).restrict p.targetPhasePlateau).withDensityᵥ
        (targetTransformedDensity p νd hfd i j))
    (hFact : ∀ᵐ y ∂traceMeasure νd, ∀ i j : JetSlot, chartPhysicalCovariance d.ball νd hfd y i j =
      (chartUnitCovector r d y i.1 : ℂ) * (chartUnitCovector r d y j.1 : ℂ) *
        chartAuxiliaryAmplitude r d νd hfd y i.2 j.2)
    (u v : Pair) :
    ((sourcePlateauTrace p νq).withDensityᵥ
        (fun z => sourceNormalizedAmplitudeDensity p r νq hfq u v z.1)).map (transportedRoundPoint q d) =
      ((traceMeasure νd).restrict p.targetPhasePlateau).withDensityᵥ
        (targetTransformedAmplitudeDensity p r νd hfd u v) := by
  ext S hS
  have hT := measurable_roundPoint q d
  obtain ⟨hQ, hD, hEq⟩ := normalizedAmplitudePlateau_weightedSetIntegral p r νq hfq νd hfd
    hCov hFact u v (fun _ => 1) measurable_const 1 zero_le_one (fun _ => by simp) S hS
  simp only [one_mul] at hQ hD hEq
  rw [VectorMeasure.map_apply _ hT hS, withDensityᵥ_apply hQ (hT hS), withDensityᵥ_apply hD hS]
  exact hEq

/-- The chart's normalized ray, viewed as a point of the production unit cosphere. -/
def chartUnitCospherePoint (r : Metric (M := M)) (q : CompactChartInput M) (z : Chart q.ball) :
    UnitCosphere.Cosphere r :=
  ⟨chartAuxiliaryRay r q z, chartAuxiliaryRay_unit r q z⟩

theorem continuous_chartUnitCospherePoint (r : Metric (M := M)) (q : CompactChartInput M) :
    Continuous (chartUnitCospherePoint r q) :=
  (continuous_chartAuxiliaryRay r q).subtype_mk (chartAuxiliaryRay_unit r q)

/-- A round overlap entry equality gives the same equality on the actual unit cosphere. -/
theorem roundOverlap_complexMeasure_map_cosphere_eq (r : Metric (M := M)) (q d : CompactChartInput M)
    (μ : ComplexMeasure (roundOverlap q d)) (ν : ComplexMeasure (Chart d.ball))
    (h : μ.map (transportedRoundPoint q d) = ν) :
    μ.map (fun z => chartUnitCospherePoint r q z.1) = ν.map (chartUnitCospherePoint r d) := by
  let T := transportedRoundPoint q d
  let Q := fun z : roundOverlap q d => chartUnitCospherePoint r q z.1
  let D := chartUnitCospherePoint r d
  have hQ : Measurable Q := ((continuous_chartUnitCospherePoint r q).comp continuous_subtype_val).measurable
  have hD : Measurable D := (continuous_chartUnitCospherePoint r d).measurable
  have hComm (z : roundOverlap q d) : D (T z) = Q z :=
    Subtype.ext (chartAuxiliaryRay_roundOverlapTransition r q d z)
  ext S hS
  change (μ.map Q) S = (ν.map D) S
  rw [VectorMeasure.map_apply _ hQ hS, VectorMeasure.map_apply _ hD hS]
  have hPre : Q ⁻¹' S = T ⁻¹' (D ⁻¹' S) := by
    ext z
    change Q z ∈ S ↔ D (T z) ∈ S
    rw [hComm z]
  have he := congrArg (fun w : ComplexMeasure (Chart d.ball) => w (D ⁻¹' S)) h
  change (μ.map T) (D ⁻¹' S) = ν (D ⁻¹' S) at he
  rw [VectorMeasure.map_apply _ (measurable_roundPoint q d) (hD hS)] at he
  rw [hPre]
  exact he

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- The original witnesses on one subsequence give equal complex amplitude
entry measures on a common plateau and agree on all bounded receiving-chart tests. -/
theorem original_commonPatch_amplitudeAgreement
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
    let T := transportedRoundPoint q d
    let μq := sourcePlateauTrace p νq
    let μd := (traceMeasure νd).restrict p.targetPhasePlateau
    let f := fun z : roundOverlap q d => sourceNormalizedAmplitudeDensity p r νq hfq u v z.1
    let g := targetTransformedAmplitudeDensity p r νd hfd u v
    ((μq.withDensityᵥ f).map T = μd.withDensityᵥ g) ∧
      ∀ (a : Chart d.ball → ℂ), Measurable a → ∀ C : ℝ, 0 ≤ C →
        (∀ y, ‖a y‖ ≤ C) → ∀ S : Set (Chart d.ball), MeasurableSet S →
        Integrable (fun z => a (T z) * f z) μq ∧ Integrable (fun y => a y * g y) μd ∧
          (∫ z in T ⁻¹' S, a (T z) * f z ∂μq) = ∫ y in S, a y * g y ∂μd := by
  intro T μq μd f target
  have hCov := original_commonPatch_normalized_roundJetMeasure
    r B g hB hg hnB hconv hbnd q d x p σ hσ νq hfq νd hfd hRq hRd
  have hFactor := (ae_originalVolume_auxiliaryAmplitude r B g hB hg hsB hsG hnB hnG hconv hbnd hv
    d σ hσ νd hfd hRd).mono (fun _ h => h.2.1)
  exact ⟨normalizedAmplitudePlateau_map_eq p r νq hfq νd hfd hCov hFactor u v,
    normalizedAmplitudePlateau_weightedSetIntegral p r νq hfq νd hfd hCov hFactor u v⟩

end Burnett.Microlocal.Overlap
