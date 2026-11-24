import Burnett.Analysis.Microlocal.Overlap.AmbientPlateauPhaseSets
import Burnett.Analysis.Microlocal.Overlap.AuxiliaryRay
import Burnett.Analysis.Microlocal.Overlap.TransportedJetCoefficients
import Burnett.Analysis.Microlocal.OriginalVolumeMatrixMeasure

/-! Ordered complex measures on a common plateau of two original charts. -/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry.ChartVolume (chartTransition)
open Burnett.Geometry.ConnectionDifference (CoordinateSpace)
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.F05.OverlapCovectors
open Burnett.F05.OverlapCovariantGradient
  (exists_overlapJetCoefficient_tests overlapJetCoefficient)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (entryMeasure traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density integrable_density_entry)
open Burnett.Microlocal.SmoothBaseTests (BallData)
open Burnett.X02.SobolevTestJet (D Space test_smooth)
open Burnett.Fourier (ComplexL2)
open Burnett.Microlocal.OverlapWindows (CommonCutoffPatch)
open scoped BigOperators ComplexConjugate ContDiff Manifold

private theorem integrable_continuous_mul_density {K : BallData}
    (ν : (JetSlot → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (i j : JetSlot) {a : Chart K → ℂ} (ha : Continuous a) :
    Integrable (fun z => a z * density ν hfin z i j) (traceMeasure ν) := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image ha).isBounded.exists_norm_le
  apply (integrable_density_entry ν hfin i j).bdd_mul ha.measurable.aestronglyMeasurable
  exact ⟨C, fun z => hC (a z) (mem_image_of_mem a (mem_univ z))⟩

/-- A represented ordered entry is the complex vector measure of its actual trace density. -/
theorem entryMeasure_eq_trace_withDensity {K : BallData} {w : ℕ → JetSlot → ComplexL2 Space}
    {σ : ℕ → ℕ} {ν : (JetSlot → ℂ) → Measure (Chart K)}
    {hfin : ∀ v, IsFiniteMeasure (ν v)} (hRep : RepresentsCompactJetPairings K w σ ν hfin)
    (i j : JetSlot) :
    entryMeasure ν hfin i j = (traceMeasure ν).withDensityᵥ (fun z => density ν hfin z i j) := by
  ext S hS
  rw [withDensityᵥ_apply (integrable_density_entry ν hfin i j) hS]
  exact (hRep.2.2.2.2.1 S hS i j).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable {q d : CompactChartInput M} {x : CoordinateSpace}
variable (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)

/-- The round source plateau inside the domain of the actual overlap transition. -/
def sourceRoundPlateau : Set (roundOverlap q d) :=
  {z | (z.1.1 : CoordinateSpace) ∈ Metric.closedBall x (p.sourceRadius / 2)}

omit [IsManifold Model ∞ M] in
private theorem measurable_sourceRoundPlateau : MeasurableSet (sourceRoundPlateau p) :=
  (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).measurable
    Metric.isClosed_closedBall.measurableSet

/-- The target chart phase point of an actual source overlap phase point. -/
def transportedRoundPoint (q d : CompactChartInput M) (z : roundOverlap q d) : Chart d.ball :=
  (roundOverlapTransition q d z).1

private theorem measurable_transportedRoundPoint (q d : CompactChartInput M) :
    Measurable (transportedRoundPoint q d) :=
  (continuous_subtype_val.comp (continuous_roundOverlapTransition q d)).measurable

private theorem continuous_cutoffSquare {K : BallData} (f : D) :
    Continuous (fun z : Chart K => (((f : CoordinateSpace → ℝ) z.1 ^ 2 : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp
    (((test_smooth f).continuous.comp (continuous_subtype_val.comp continuous_fst)).pow 2)

variable (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
variable (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))

/-- Divide an original source entry by the square of its cutoff on the plateau,
using the corresponding globally smooth factor. -/
def sourceNormalizedDensity (i j : JetSlot) (z : Chart q.ball) : ℂ :=
  (((p.sourceFactor : CoordinateSpace → ℝ) z.1 ^ 2 : ℝ) : ℂ) * density νq hfq z i j

/-- The original target entries, divided by their own squared cutoff on the plateau,
and changed by the actual three-slot Jacobian in each of the two tensor slots. -/
def targetTransformedDensity (i j : JetSlot) (y : Chart d.ball) : ℂ :=
  ∑ k : JetSlot, ∑ l : JetSlot,
    conj (↑(overlapJetCoefficient q.center d.center i k y.1) : ℂ) *
      (↑(overlapJetCoefficient q.center d.center j l y.1) : ℂ) *
      (((p.targetFactor : CoordinateSpace → ℝ) y.1 ^ 2 : ℝ) : ℂ) * density νd hfd y k l

/-- The source trace on the actual overlap, restricted to the source plateau. -/
def sourcePlateauTrace : Measure (roundOverlap q d) :=
  (Measure.comap (Subtype.val : roundOverlap q d → Chart q.ball) (traceMeasure νq)).restrict
    (sourceRoundPlateau p)

omit [IsManifold Model ∞ M] in
theorem integrable_sourceNormalizedDensity (i j : JetSlot) :
    Integrable (fun z : roundOverlap q d => sourceNormalizedDensity p νq hfq i j z.1)
      (sourcePlateauTrace p νq) := by
  have h := integrable_continuous_mul_density νq hfq i j (continuous_cutoffSquare p.sourceFactor)
  have he := MeasurableEmbedding.subtype_coe (measurableSet_roundOverlap q d)
  apply Integrable.mono_measure _ Measure.restrict_le_self
  have hMap : Integrable (sourceNormalizedDensity p νq hfq i j)
      (Measure.map (Subtype.val : roundOverlap q d → Chart q.ball)
        (Measure.comap Subtype.val (traceMeasure νq))) := by
    rw [map_comap_subtype_coe (measurableSet_roundOverlap q d)]
    exact h.mono_measure Measure.restrict_le_self
  exact he.integrable_map_iff.mp hMap

theorem integrable_targetTransformedDensity (i j : JetSlot) :
    Integrable (targetTransformedDensity p νd hfd i j)
      ((traceMeasure νd).restrict p.targetPhasePlateau) := by
  have hSub : Metric.closedBall x (p.sourceRadius / 2) ⊆ p.sourceInput.ball.closedBall :=
    Metric.closedBall_subset_closedBall (show p.sourceRadius / 2 ≤ p.sourceRadius by
      linarith [p.sourceRadius_pos])
  obtain ⟨_, w, _, _, _, hw⟩ := exists_overlapJetCoefficient_tests q.center d.center
    p.sourceInput.ball.closedBall (isCompact_closedBall _ _) p.sourceInput_ball_in_overlap
  let a (k l : JetSlot) (y : Chart d.ball) : ℂ :=
    conj (physicalCoefficient (w i k) y.1) * physicalCoefficient (w j l) y.1 *
      (((p.targetFactor : CoordinateSpace → ℝ) y.1 ^ 2 : ℝ) : ℂ)
  have ha (k l : JetSlot) : Continuous (a k l) := by
    have hbase : Continuous (fun z : Chart d.ball => (z.1 : CoordinateSpace)) :=
      continuous_subtype_val.comp continuous_fst
    have hCoeff (v : D) : Continuous (fun z : Chart d.ball => physicalCoefficient v z.1) :=
      Complex.continuous_ofReal.comp ((test_smooth v).continuous.comp hbase)
    exact ((Complex.continuous_conj.comp (hCoeff (w i k))).mul (hCoeff (w j l))).mul
      (continuous_cutoffSquare p.targetFactor)
  have hInt : Integrable (fun y => ∑ k : JetSlot, ∑ l : JetSlot, a k l y * density νd hfd y k l)
      (traceMeasure νd) :=
    integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ =>
      integrable_continuous_mul_density νd hfd k l (ha k l)
  apply (hInt.mono_measure Measure.restrict_le_self).congr
  filter_upwards [ae_restrict_mem p.measurableSet_targetPhasePlateau] with y hy
  have hImage : (y.1 : CoordinateSpace) ∈ chartTransition q.center d.center '' p.sourceInput.ball.closedBall :=
    image_mono hSub hy
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change conj (↑((w i k : CoordinateSpace → ℝ) y.1) : ℂ) *
      (↑((w j l : CoordinateSpace → ℝ) y.1) : ℂ) * _ * _ = _
  rw [hw i k hImage, hw j l hImage]

private theorem setIntegral_comap_subtype_image {X : Type*} [MeasurableSpace X]
    {S : Set X} (hS : MeasurableSet S) (μ : Measure X) (f : X → ℂ)
    (A : Set S) (hA : MeasurableSet A) :
    (∫ z in A, f z.1 ∂Measure.comap Subtype.val μ) = ∫ y in Subtype.val '' A, f y ∂μ := by
  have he := MeasurableEmbedding.subtype_coe hS
  have hImage : MeasurableSet (Subtype.val '' A) := he.measurableSet_image.mpr hA
  have hSubset : Subtype.val '' A ⊆ S := fun _ ⟨z, _, hz⟩ => hz ▸ z.property
  calc
    _ = ∫ y in Subtype.val '' A, f y ∂(Measure.comap (Subtype.val : S → X) μ).map Subtype.val := by
      rw [he.setIntegral_map, he.injective.preimage_image]
    _ = _ := by
      rw [map_comap_subtype_coe hS, Measure.restrict_restrict hImage, inter_eq_left.mpr hSubset]

/-- The patch's Borel entry identity is an equality of actual complex measures.
Both sides use the existing chart trace and density of the supplied witnesses. -/
theorem map_normalizedEntry_eq_target_of_borel (i j : JetSlot)
    (hCov : ∀ S : Set (Chart d.ball), MeasurableSet S →
      (∫ z in (Subtype.val : roundOverlap q d → Chart q.ball) ''
          ((transportedRoundPoint q d ⁻¹' S) ∩ sourceRoundPlateau p),
          sourceNormalizedDensity p νq hfq i j z ∂traceMeasure νq) =
        ∫ y in S ∩ p.targetPhasePlateau, targetTransformedDensity p νd hfd i j y ∂traceMeasure νd) :
    ((sourcePlateauTrace p νq).withDensityᵥ
        (fun z => sourceNormalizedDensity p νq hfq i j z.1)).map (transportedRoundPoint q d) =
      ((traceMeasure νd).restrict p.targetPhasePlateau).withDensityᵥ
        (targetTransformedDensity p νd hfd i j) := by
  ext S hS
  have hT := measurable_transportedRoundPoint q d
  rw [VectorMeasure.map_apply _ hT hS,
    withDensityᵥ_apply (integrable_sourceNormalizedDensity p νq hfq i j) (hT hS),
    withDensityᵥ_apply (integrable_targetTransformedDensity p νd hfd i j) hS]
  unfold sourcePlateauTrace
  rw [Measure.restrict_restrict (hT hS), Measure.restrict_restrict hS,
    setIntegral_comap_subtype_image (measurableSet_roundOverlap q d) _ _ _
      ((hT hS).inter (measurable_sourceRoundPlateau p))]
  exact hCov S hS

end Burnett.Microlocal.Overlap
