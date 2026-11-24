import Burnett.Analysis.Microlocal.Overlap.NormalizedAmplitudePlateauRestriction
import Burnett.Analysis.Microlocal.PhysicalChartCover
import Burnett.Analysis.Microlocal.ChartAmplitudeMeasure
import Burnett.Geometry.VectorMeasureCover

/-! Compatibility of normalized complex amplitude entries on compact bases in the real overlap. -/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1500000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set Matrix Burnett.RicciSymbol
open Burnett.Geometry ChartVolume ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence
open Burnett.Geometry.MetricJetNaturality (derivativeMatrix_apply)
open Burnett.Geometry.MeasureGluing (vectorMeasure_restrict_iUnion_eq_of_restrict_eq)
open Burnett.F05.ActualChartAuxiliarySection
  (chartAuxiliaryInverse continuous_chartAuxiliaryInverse chartAuxiliaryNorm_pos)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (chartAuxiliaryAmplitude)
open Burnett.F05.OverlapCovectors (tensorPairTransition)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.FixedChartGeometricDensity (integrable_chartAmplitudeDensity_entry)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.OverlapGradient (overlapTransition overlapTransition_eq)
open Burnett.Microlocal.OverlapWindows
open Burnett.X02.SobolevTestJet (test_smooth)
open scoped BigOperators ComplexConjugate ContDiff Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [T2Space M] [MeasurableSpace M] [BorelSpace M]

omit [T2Space M] in
theorem measurableSet_amplitudeCosphereWindow (r : Metric (M := M)) {K : Set M}
    (hK : MeasurableSet K) : MeasurableSet (amplitudeCosphereWindow r K) :=
  (UnitCosphere.continuous_projection r).measurable hK

omit [T2Space M] in
theorem measurableSet_amplitudeChartWindow (r : Metric (M := M)) (q : CompactChartInput M)
    {K : Set M} (hK : MeasurableSet K) : MeasurableSet (amplitudeChartWindow r q K) :=
  (continuous_amplitudeChartBase r q).measurable hK

omit [T2Space M] in
theorem normalizedCosphereChartEntryOn_restrict (r : Metric (M := M)) (q : CompactChartInput M)
    (μ : Measure (Chart q.ball)) (F : Chart q.ball → ℂ) {K L : Set M}
    (hL : MeasurableSet L)
    (hI : Integrable (fun z => chartInverseCutoffComplexSquare q z * F z)
      (μ.restrict (amplitudeChartWindow r q K))) :
    (normalizedCosphereChartEntryOn r q μ F K).restrict (amplitudeCosphereWindow r L) =
      normalizedCosphereChartEntryOn r q μ F (K ∩ L) := by
  let φ := chartUnitCospherePoint r q
  let U := amplitudeChartWindow r q K
  let V := amplitudeChartWindow r q L
  let f (z : Chart q.ball) := chartInverseCutoffComplexSquare q z * F z
  have hφ : Measurable φ := (continuous_chartUnitCospherePoint r q).measurable
  have hVL : MeasurableSet (amplitudeCosphereWindow r L) := measurableSet_amplitudeCosphereWindow r hL
  have hInter : Integrable f (μ.restrict (U ∩ V)) :=
    hI.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  ext S hS
  change (((μ.restrict U).withDensityᵥ f).map φ).restrict (amplitudeCosphereWindow r L) S =
    (((μ.restrict (U ∩ V)).withDensityᵥ f).map φ) S
  rw [VectorMeasure.restrict_apply _ hVL hS, VectorMeasure.map_apply _ hφ (hS.inter hVL),
    VectorMeasure.map_apply _ hφ hS, withDensityᵥ_apply hI (hφ (hS.inter hVL)),
    withDensityᵥ_apply hInter (hφ hS), Measure.restrict_restrict (hφ (hS.inter hVL)),
    Measure.restrict_restrict (hφ hS)]
  rw [show φ ⁻¹' (S ∩ amplitudeCosphereWindow r L) = (φ ⁻¹' S) ∩ V from rfl]
  rw [show ((φ ⁻¹' S) ∩ V) ∩ U = (φ ⁻¹' S) ∩ (U ∩ V) by ac_rfl]

omit [MeasurableSpace M] [BorelSpace M] in
private theorem isCompact_amplitudeChartWindow (r : Metric (M := M)) (q : CompactChartInput M)
    {K : Set M} (hK : IsCompact K) : IsCompact (amplitudeChartWindow r q K) :=
  (hK.isClosed.preimage (continuous_amplitudeChartBase r q)).isCompact

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] in
private theorem continuousOn_chartInverseCutoffComplexSquare (r : Metric (M := M))
    (q : CompactChartInput M) {K : Set M} (hK : K ⊆ q.nonzeroLocus) :
    ContinuousOn (chartInverseCutoffComplexSquare q) (amplitudeChartWindow r q K) := by
  have hχ : Continuous (fun z : Chart q.ball => (q.cutoff : CoordinateSpace → ℝ) z.1) :=
    (test_smooth q.cutoff).continuous.comp (continuous_subtype_val.comp continuous_fst)
  have hNZ (z : Chart q.ball) (hz : z ∈ amplitudeChartWindow r q K) :
      (q.cutoff : CoordinateSpace → ℝ) z.1 ≠ 0 := by
    have hm := (hK hz).2
    change (q.cutoff : CoordinateSpace → ℝ)
      (chartAt CoordinateSpace q.center ((chartAt CoordinateSpace q.center).symm z.1)) ≠ 0 at hm
    rwa [(chartAt CoordinateSpace q.center).right_inv (q.ball_in_chart z.1.property)] at hm
  exact Complex.continuous_ofReal.comp_continuousOn ((hχ.continuousOn.inv₀ hNZ).pow 2)

private theorem integrableOn_boundedChartMultiplier {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] {U : Set X} (hU : IsCompact U) (hUm : MeasurableSet U)
    {f g : X → ℂ} {μ : Measure X} (hf : ContinuousOn f U) (hg : Integrable g μ) :
    Integrable (fun z => f z * g z) (μ.restrict U) := by
  obtain ⟨C, hC⟩ := (hU.image_of_continuousOn hf).isBounded.exists_norm_le
  apply (hg.mono_measure Measure.restrict_le_self).bdd_mul'
    (hf.aestronglyMeasurable_of_isCompact hU hUm)
  exact (ae_restrict_mem (μ := μ) hUm).mono fun z hz => hC _ (mem_image_of_mem f hz)

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] in
theorem integrable_chartAuxiliaryAmplitude_entry (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v)) (u v : Pair) :
    Integrable (fun z => chartAuxiliaryAmplitude r q ν hfin z u v) (traceMeasure ν) :=
  integrable_chartAmplitudeDensity_entry q.ball (chartAuxiliaryInverse r q)
    (fun i j => (continuous_apply j).comp ((continuous_apply i).comp (continuous_chartAuxiliaryInverse r q)))
    (chartAuxiliaryNorm_pos r q) ν hfin u v

theorem integrable_normalizedCosphereAmplitudeEntry_on_compact (r : Metric (M := M))
    (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball))
    (hfin : ∀ v, IsFiniteMeasure (ν v)) (u v : Pair) {K : Set M}
    (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus) :
    Integrable (fun z : Chart q.ball => chartInverseCutoffComplexSquare q z *
      chartAuxiliaryAmplitude r q ν hfin z u v)
      ((traceMeasure ν).restrict (amplitudeChartWindow r q K)) :=
  integrableOn_boundedChartMultiplier (isCompact_amplitudeChartWindow r q hK)
    (measurableSet_amplitudeChartWindow r q hK.isClosed.measurableSet)
    (continuousOn_chartInverseCutoffComplexSquare r q hSub)
    (integrable_chartAuxiliaryAmplitude_entry r q ν hfin u v)

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] in
private theorem continuousOn_receivingToSourceCotangent_entry (q d : CompactChartInput M) (i j : Index) :
    ContinuousOn (fun y => receivingToSourceCotangent q d y i j)
      (chartTransition q.center d.center).target := by
  let e := chartTransition q.center d.center
  have hsymm : e.symm = chartTransition d.center q.center := by
    simp only [e, chartTransition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  have hD : ContinuousOn (fderiv ℝ e) e.source :=
    (ActualChartSecondJet.contDiffOn_chartTransition_infty q.center d.center).continuousOn_fderiv_of_isOpen
      e.open_source (by simp)
  have hEntry : ContinuousOn (fun y => derivativeMatrix (fderiv ℝ e y) j i) e.source := by
    simp only [derivativeMatrix_apply]
    exact (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp_continuousOn
      (hD.clm_apply continuousOn_const)
  refine (hEntry.comp e.continuousOn_symm (fun _ hy => e.symm_mapsTo hy)).congr ?_
  intro y hy
  have hyt : y ∈ (chartTransition d.center q.center).source := by
    rw [← hsymm]
    exact hy
  change derivativeMatrix (fderiv ℝ (chartTransition q.center d.center)
    (overlapTransition d.center q.center y)) j i = derivativeMatrix (fderiv ℝ e (e.symm y)) j i
  rw [overlapTransition_eq _ _ hyt, ← hsymm]

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] in
private theorem mapsTo_amplitudeChartWindow_overlap (r : Metric (M := M)) (q d : CompactChartInput M)
    {K : Set M} (hK : K ⊆ q.nonzeroLocus) :
    MapsTo (fun z : Chart d.ball => (z.1 : CoordinateSpace)) (amplitudeChartWindow r d K)
      (chartTransition q.center d.center).target := by
  let e := chartTransition q.center d.center
  have hsymm : e.symm = chartTransition d.center q.center := by
    simp only [e, chartTransition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  intro z hz
  change (z.1 : CoordinateSpace) ∈ e.symm.source
  rw [hsymm]
  exact ⟨d.ball_in_chart z.1.property, (hK hz).1⟩

theorem integrable_normalizedCosphereTransportedAmplitudeEntry_on_compact
    (r : Metric (M := M)) (q d : CompactChartInput M)
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (u v : Pair) {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus ∩ d.nonzeroLocus) :
    Integrable (fun z : Chart d.ball => chartInverseCutoffComplexSquare d z *
      transportedAmplitudeEntry r q d νd hfd u v z)
      ((traceMeasure νd).restrict (amplitudeChartWindow r d K)) := by
  let U := amplitudeChartWindow r d K
  let D (z : Chart d.ball) := tensorPairTransition (receivingToSourceCotangent q d z.1)
  let A := chartAuxiliaryAmplitude r d νd hfd
  let w := chartInverseCutoffComplexSquare d
  let C (i j : Pair) (z : Chart d.ball) := w z * D z u j * conj (D z v i)
  have hT (i j : Index) : ContinuousOn (fun z : Chart d.ball => receivingToSourceCotangent q d z.1 i j) U :=
    (continuousOn_receivingToSourceCotangent_entry q d i j).comp
      (continuous_subtype_val.comp continuous_fst).continuousOn
      (mapsTo_amplitudeChartWindow_overlap r q d (hSub.trans inter_subset_left))
  have hD (a b : Pair) : ContinuousOn (fun z => D z a b) U :=
    (Complex.continuous_ofReal.comp_continuousOn (hT a.1 b.1)).mul
      (Complex.continuous_ofReal.comp_continuousOn (hT a.2 b.2))
  have hW : ContinuousOn w U := continuousOn_chartInverseCutoffComplexSquare r d (hSub.trans inter_subset_right)
  have hC (i j : Pair) : ContinuousOn (C i j) U :=
    (hW.mul (hD u j)).mul (Complex.continuous_conj.comp_continuousOn (hD v i))
  have hInt (i j : Pair) : Integrable (fun z => C i j z * A z j i) ((traceMeasure νd).restrict U) :=
    integrableOn_boundedChartMultiplier (isCompact_amplitudeChartWindow r d hK)
      (measurableSet_amplitudeChartWindow r d hK.isClosed.measurableSet)
      (hC i j) (integrable_chartAuxiliaryAmplitude_entry r d νd hfd j i)
  apply (integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hInt i j).congr
  apply Filter.Eventually.of_forall
  intro z
  change (∑ i : Pair, ∑ j : Pair, C i j z * A z j i) = w z * (D z * A z * (D z)ᴴ) u v
  simp only [C, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [IsManifold Model ∞ M] [T2Space M] [MeasurableSpace M] [BorelSpace M] in
private theorem amplitudeNonzeroOverlap_eq_image (q d : CompactChartInput M) :
    q.nonzeroLocus ∩ d.nonzeroLocus = (chartAt CoordinateSpace q.center).symm ''
      nonzeroCutoffOverlap q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff := by
  ext m
  let eq := chartAt CoordinateSpace q.center
  let ed := chartAt CoordinateSpace d.center
  constructor
  · rintro ⟨hq, hd⟩
    have hqS : m ∈ eq.source := hq.1
    have hdS : m ∈ ed.source := hd.1
    have hPoint : eq.symm (eq m) = m := eq.left_inv hqS
    have hT : chartTransition q.center d.center (eq m) = ed m := by
      change ed (eq.symm (eq m)) = ed m
      rw [hPoint]
    have hSrc : eq m ∈ (chartTransition q.center d.center).source := by
      refine ⟨eq.map_source hqS, ?_⟩
      change eq.symm (eq m) ∈ ed.source
      rwa [hPoint]
    refine ⟨eq m, ⟨⟨hSrc, ?_⟩, ⟨q.chart_mem_interior_of_mem_nonzeroLocus hq, hq.2⟩⟩, hPoint⟩
    change chartTransition q.center d.center (eq m) ∈
      interior d.ball.closedBall ∩ Function.support (d.cutoff : CoordinateSpace → ℝ)
    rw [hT]
    exact ⟨d.chart_mem_interior_of_mem_nonzeroLocus hd, hd.2⟩
  · rintro ⟨y, hy, rfl⟩
    have hqT : y ∈ eq.target := hy.1.1.1
    refine ⟨⟨eq.symm_mapsTo hqT, ?_⟩, ⟨hy.1.1.2, hy.1.2.2⟩⟩
    change eq (eq.symm y) ∈ Function.support (q.cutoff : CoordinateSpace → ℝ)
    rw [eq.right_inv hqT]
    exact hy.2.2

omit [IsManifold Model ∞ M] [T2Space M] [MeasurableSpace M] [BorelSpace M] in
private theorem amplitudeNonzeroOverlap_eq_union_commonPlateaus (q d : CompactChartInput M)
    (p : ∀ y : nonzeroCutoffOverlap q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff,
      CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff y.1)
    (centers : Set (nonzeroCutoffOverlap q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff))
    (cover : nonzeroCutoffOverlap q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff =
      ⋃ y ∈ centers, Metric.ball y.1 ((p y).sourceRadius / 2)) :
    q.nonzeroLocus ∩ d.nonzeroLocus = ⋃ y : centers, commonPatchBasePlateau (p y.1) := by
  rw [iUnion_subtype]
  have hClosed : nonzeroCutoffOverlap q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff =
      ⋃ y ∈ centers, Metric.closedBall y.1 ((p y).sourceRadius / 2) := by
    refine Subset.antisymm (cover.le.trans (iUnion₂_mono fun _ _ => Metric.ball_subset_closedBall)) ?_
    refine iUnion₂_subset fun y _ => ?_
    have hRadius : (p y).sourceRadius / 2 ≤ (p y).sourceRadius := by
      linarith [(p y).sourceRadius_pos]
    exact (Metric.closedBall_subset_closedBall hRadius).trans (p y).sourceWindow_subset_nonzeroCutoffOverlap
  calc
    _ = _ := amplitudeNonzeroOverlap_eq_image q d
    _ = (chartAt CoordinateSpace q.center).symm ''
        (⋃ y ∈ centers, Metric.closedBall y.1 ((p y).sourceRadius / 2)) :=
      congrArg (fun s => (chartAt CoordinateSpace q.center).symm '' s) hClosed
    _ = _ := by simp only [image_iUnion, commonPatchBasePlateau]

variable [SecondCountableTopology M]

/-- On any compact base contained in the full nonzero overlap, the two original
normalized complex entries agree, expressed in the fixed source chart. -/
theorem original_normalizedCosphereAmplitudeEntry_eq_on_compactOverlap
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
    (u v : Pair) {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus ∩ d.nonzeroLocus) :
    Integrable (fun z : Chart q.ball => chartInverseCutoffComplexSquare q z *
      chartAuxiliaryAmplitude r q νq hfq z u v)
      ((traceMeasure νq).restrict (amplitudeChartWindow r q K)) ∧
    Integrable (fun z : Chart d.ball => chartInverseCutoffComplexSquare d z *
      transportedAmplitudeEntry r q d νd hfd u v z)
      ((traceMeasure νd).restrict (amplitudeChartWindow r d K)) ∧
    normalizedCosphereAmplitudeEntryOn r q νq hfq u v K =
      normalizedCosphereTransportedAmplitudeEntryOn r q d νd hfd u v K := by
  have hQI := integrable_normalizedCosphereAmplitudeEntry_on_compact r q νq hfq u v hK
    (hSub.trans inter_subset_left)
  have hDI := integrable_normalizedCosphereTransportedAmplitudeEntry_on_compact r q d νd hfd u v hK hSub
  refine ⟨hQI, hDI, ?_⟩
  let FQ := fun z => chartAuxiliaryAmplitude r q νq hfq z u v
  let FD := transportedAmplitudeEntry r q d νd hfd u v
  let Q := normalizedCosphereChartEntryOn r q (traceMeasure νq) FQ K
  let D := normalizedCosphereChartEntryOn r d (traceMeasure νd) FD K
  let O := q.nonzeroLocus ∩ d.nonzeroLocus
  have hOm : MeasurableSet O := (q.isOpen_nonzeroLocus.inter d.isOpen_nonzeroLocus).measurableSet
  obtain ⟨p, centers, hCountable, hCover⟩ :=
    exists_countable_commonCutoffPatches q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff
  letI : Countable centers := hCountable.to_subtype
  let U (y : centers) := amplitudeCosphereWindow r (commonPatchBasePlateau (p y.1))
  have hU (y : centers) : MeasurableSet (U y) :=
    measurableSet_amplitudeCosphereWindow r (isCompact_commonPatchBasePlateau (p y.1)).isClosed.measurableSet
  have hPatches (y : centers) : Q.restrict (U y) = D.restrict (U y) := by
    let P := commonPatchBasePlateau (p y.1)
    have hPm : MeasurableSet P := (isCompact_commonPatchBasePlateau (p y.1)).isClosed.measurableSet
    obtain ⟨hQP, hDP, hPatch⟩ :=
      original_commonPatch_normalizedCosphereAmplitudeEntry_eq (p y.1) r νq hfq νd hfd B g
        hB hg hsB hsG hnB hnG hconv hbnd hv σ hσ hRq hRd u v
    have h := congrArg (fun m : ComplexMeasure (UnitCosphere.Cosphere r) =>
      m.restrict (amplitudeCosphereWindow r K)) hPatch
    change (normalizedCosphereChartEntryOn r q (traceMeasure νq) FQ P).restrict
      (amplitudeCosphereWindow r K) = (normalizedCosphereChartEntryOn r d (traceMeasure νd) FD P).restrict
        (amplitudeCosphereWindow r K) at h
    rw [normalizedCosphereChartEntryOn_restrict r q _ _ hK.isClosed.measurableSet hQP,
      normalizedCosphereChartEntryOn_restrict r d _ _ hK.isClosed.measurableSet hDP] at h
    change (normalizedCosphereChartEntryOn r q (traceMeasure νq) FQ K).restrict
      (amplitudeCosphereWindow r P) = (normalizedCosphereChartEntryOn r d (traceMeasure νd) FD K).restrict
        (amplitudeCosphereWindow r P)
    rw [normalizedCosphereChartEntryOn_restrict r q _ _ hPm hQI,
      normalizedCosphereChartEntryOn_restrict r d _ _ hPm hDI, inter_comm K P]
    exact h
  have hUnion : amplitudeCosphereWindow r O = ⋃ y, U y := by
    have hO : O = ⋃ y : centers, commonPatchBasePlateau (p y.1) :=
      amplitudeNonzeroOverlap_eq_union_commonPlateaus q d p centers hCover
    simp only [amplitudeCosphereWindow, hO, preimage_iUnion, U]
  have hEq := vectorMeasure_restrict_iUnion_eq_of_restrict_eq Q D U hU hPatches
  rw [← hUnion] at hEq
  change ((normalizedCosphereChartEntryOn r q (traceMeasure νq) FQ K).restrict (amplitudeCosphereWindow r O)) =
    ((normalizedCosphereChartEntryOn r d (traceMeasure νd) FD K).restrict (amplitudeCosphereWindow r O)) at hEq
  rw [normalizedCosphereChartEntryOn_restrict r q _ _ hOm hQI,
    normalizedCosphereChartEntryOn_restrict r d _ _ hOm hDI, inter_eq_left.mpr hSub] at hEq
  exact hEq

end Burnett.Microlocal.Overlap
