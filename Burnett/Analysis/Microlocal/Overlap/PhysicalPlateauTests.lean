import Burnett.Analysis.Microlocal.Overlap.NormalizedEntryWeightedTests
import Burnett.Analysis.Microlocal.Overlap.ChartJetPhysicalWeight

/-! The physical scalar contraction of the original ordered entries on an overlap. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ChartVolume ConnectionDifference ManifoldBilinear ManifoldMetric
open Burnett.F05.OverlapCovectors
  (roundOverlap measurableSet_roundOverlap roundOverlapTransition roundOverlapTransition_leftInverse
    continuous_roundOverlapTransition)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.OverlapWindows (CommonCutoffPatch)
open Burnett.Microlocal.RicciRow (backgroundInverse)
open scoped BigOperators ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem continuous_chartPhysicalJetWeight (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (hn : IsNondegenerate B) (q : CompactChartInput M) (i j : JetSlot) :
    Continuous (fun z : Chart q.ball => (chartPhysicalJetWeight r B q.center z.1 i j : ℂ)) := by
  have hInverse (A : Field (M := M)) (hsA : IsSmooth A) (hnA : IsNondegenerate A)
      (a b : Burnett.RicciSymbol.Index) :
      Continuous (fun z : Chart q.ball => backgroundInverse A q.center z.1 a b) := by
    have h := SmoothMetricConnection.contDiffOn_matrixInverse _ _
      (ManifoldBilinear.contDiffOn_metricComponents A hsA q.center)
      (fun y hy => ManifoldVolumeRegularity.coordinate_det_ne_zero A hnA q.center hy) a b
    exact ((h.continuousOn.mono q.ball_in_chart).restrict).comp continuous_fst
  have hR := hInverse r.inner (isSmooth_inner r) (GlobalLeviCivita.inner_nondegenerate r) i.1 j.1
  have hG := hInverse B hB hn
  simp only [chartPhysicalJetWeight, orderedPhysicalJetWeight_apply]
  exact Complex.continuous_ofReal.comp ((continuous_const.mul hR).mul
    (((hG j.2.1 i.2.1).mul (hG j.2.2 i.2.2)).sub
      (((hG j.2.1 j.2.2).mul (hG i.2.1 i.2.2)).div_const 2)))

private def transportedWeight (r : Metric (M := M)) (B : Field (M := M))
    (q d : CompactChartInput M) (i j : JetSlot) : Chart d.ball → ℂ :=
  Function.extend (Subtype.val : roundOverlap d q → Chart d.ball)
    (fun y => (chartPhysicalJetWeight r B q.center (roundOverlapTransition d q y).1.1 i j : ℂ))
    (fun _ => 0)

private theorem transportedWeight_on_source (r : Metric (M := M)) (B : Field (M := M))
    (q d : CompactChartInput M) (i j : JetSlot) (z : roundOverlap q d) :
    transportedWeight r B q d i j (transportedRoundPoint q d z) =
      (chartPhysicalJetWeight r B q.center z.1.1 i j : ℂ) := by
  unfold transportedWeight transportedRoundPoint
  rw [Subtype.coe_injective.extend_apply, roundOverlapTransition_leftInverse q d z]

private theorem measurable_transportedWeight (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (hn : IsNondegenerate B) (q d : CompactChartInput M) (i j : JetSlot) :
    Measurable (transportedWeight r B q d i j) :=
  (MeasurableEmbedding.subtype_coe (measurableSet_roundOverlap d q)).measurable_extend
    ((continuous_chartPhysicalJetWeight r B hB hn q i j).measurable.comp
      (continuous_subtype_val.comp (continuous_roundOverlapTransition d q)).measurable) measurable_const

private theorem bounded_transportedWeight (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (hn : IsNondegenerate B) (q d : CompactChartInput M) (i j : JetSlot) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖transportedWeight r B q d i j y‖ ≤ C := by
  let w (z : Chart q.ball) : ℂ := chartPhysicalJetWeight r B q.center z.1 i j
  obtain ⟨C, hC⟩ := (isCompact_univ.image (continuous_chartPhysicalJetWeight r B hB hn q i j)).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : y ∈ range (Subtype.val : roundOverlap d q → Chart d.ball)
  · obtain ⟨y', rfl⟩ := hy
    unfold transportedWeight
    rw [Subtype.coe_injective.extend_apply]
    exact (hC (w (roundOverlapTransition d q y').1) (mem_image_of_mem w (mem_univ _))).trans (le_max_left _ _)
  · unfold transportedWeight
    rw [Function.extend_apply' _ _ _ hy, norm_zero]
    exact le_max_right _ _

variable {q d : CompactChartInput M} {x : CoordinateSpace}
variable (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)

omit [IsManifold Model ∞ M] in
private theorem targetPhasePlateau_in_overlap {y : Chart d.ball} (hy : y ∈ p.targetPhasePlateau) :
    y ∈ roundOverlap d q := by
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

variable (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
variable (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))

private theorem targetPhysicalContraction (r : Metric (M := M)) (B : Field (M := M))
    (y : Chart d.ball) (hy : y ∈ p.targetPhasePlateau) :
    ∑ i : JetSlot, ∑ j : JetSlot, transportedWeight r B q d i j y *
        targetTransformedDensity p νd hfd i j y =
      ∑ i : JetSlot, ∑ j : JetSlot, (chartPhysicalJetWeight r B d.center y.1 i j : ℂ) *
        (((p.targetFactor : CoordinateSpace → ℝ) y.1 ^ 2 : ℝ) : ℂ) * density νd hfd y i j := by
  let y' : roundOverlap d q := ⟨y, targetPhasePlateau_in_overlap p hy⟩
  let z := roundOverlapTransition d q y'
  have hT : transportedRoundPoint q d z = y :=
    congrArg Subtype.val (roundOverlapTransition_leftInverse d q y')
  have hCoeff (i j : JetSlot) : transportedWeight r B q d i j y =
      (chartPhysicalJetWeight r B q.center z.1.1 i j : ℂ) := by
    rw [← hT, transportedWeight_on_source]
  have h := chartPhysicalJetWeight_contraction_change r B q.center d.center z.property.1
    (fun i j => (((p.targetFactor : CoordinateSpace → ℝ) y.1 ^ 2 : ℝ) : ℂ) * density νd hfd y i j)
  have hBase : chartTransition q.center d.center z.1.1 = y.1 := by
    exact congrArg (fun v : Chart d.ball => (v.1 : CoordinateSpace)) hT
  dsimp only at h
  rw [hBase] at h
  simpa only [targetTransformedDensity, hCoeff, mul_assoc] using h

/-- The full physical scalar contraction of the *same* represented jet entries
agrees under transport on a common plateau, tested against any bounded Borel
scalar. Null restriction uses the actual cotangent ray and the background metric. -/
theorem normalizedPhysicalPlateauTest
    (r : Metric (M := M)) (B : Field (M := M)) (hB : IsSmooth B)
    (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (hCov : ∀ i j : JetSlot, ((sourcePlateauTrace p νq).withDensityᵥ
        (fun z => sourceNormalizedDensity p νq hfq i j z.1)).map (transportedRoundPoint q d) =
      ((traceMeasure νd).restrict p.targetPhasePlateau).withDensityᵥ
        (targetTransformedDensity p νd hfd i j))
    (a : Chart d.ball → ℂ) (ha : Measurable a) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ y, ‖a y‖ ≤ C)
    (S : Set (Chart d.ball)) (hS : MeasurableSet S) :
    (∫ z in (transportedRoundPoint q d ⁻¹' S) ∩ (Subtype.val ⁻¹' chartAuxiliaryNull r B hn q),
      a (transportedRoundPoint q d z) * (∑ i : JetSlot, ∑ j : JetSlot,
        (chartPhysicalJetWeight r B q.center z.1.1 i j : ℂ) * sourceNormalizedDensity p νq hfq i j z.1)
          ∂sourcePlateauTrace p νq) =
      ∫ y in S ∩ chartAuxiliaryNull r B hn d, a y * (∑ i : JetSlot, ∑ j : JetSlot,
        (chartPhysicalJetWeight r B d.center y.1 i j : ℂ) *
        (((p.targetFactor : CoordinateSpace → ℝ) y.1 ^ 2 : ℝ) : ℂ) * density νd hfd y i j)
          ∂(traceMeasure νd).restrict p.targetPhasePlateau := by
  classical
  let A (i j : JetSlot) (y : Chart d.ball) := a y * transportedWeight r B q d i j y
  choose K hK hKb using fun i j : JetSlot => bounded_transportedWeight r B hB hn q d i j
  have hA (i j : JetSlot) : Measurable (A i j) :=
    ha.mul (measurable_transportedWeight r B hB hn q d i j)
  have hAb (i j : JetSlot) (y : Chart d.ball) : ‖A i j y‖ ≤ C * K i j := by
    rw [show A i j y = a y * transportedWeight r B q d i j y from rfl, norm_mul]
    exact mul_le_mul (hb y) (hKb i j y) (norm_nonneg _) hC
  have hZ : MeasurableSet (S ∩ chartAuxiliaryNull r B hn d) :=
    hS.inter (measurableSet_chartAuxiliaryNull r B hB hs hn d)
  have hTest := normalizedJet_contractedSetIntegral p νq hfq νd hfd hCov A hA
    (fun i j => C * K i j) (fun i j => mul_nonneg hC (hK i j)) hAb _ hZ
  have hPreimage : transportedRoundPoint q d ⁻¹' (S ∩ chartAuxiliaryNull r B hn d) =
      (transportedRoundPoint q d ⁻¹' S) ∩ (Subtype.val ⁻¹' chartAuxiliaryNull r B hn q) := by
    ext z
    exact and_congr_right (fun _ => chartAuxiliaryNull_roundTransition r B hn q d z)
  rw [← hPreimage]
  refine Eq.trans ?_ (hTest.trans ?_)
  · apply integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [A, transportedWeight_on_source, Finset.mul_sum, mul_assoc]
  · apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (ae_restrict_mem (μ := traceMeasure νd) p.measurableSet_targetPhasePlateau)] with y hy
    have h := congrArg (fun z : ℂ => a y * z) (targetPhysicalContraction p νd hfd r B y hy)
    simpa only [A, Finset.mul_sum, mul_assoc] using h

end Burnett.Microlocal.Overlap
