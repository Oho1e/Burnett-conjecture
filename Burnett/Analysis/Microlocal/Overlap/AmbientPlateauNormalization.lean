import Burnett.Analysis.Microlocal.Overlap.AmbientPlateauPhaseSets
import Burnett.Analysis.Microlocal.Overlap.CommonPatchPhase
import Burnett.Analysis.Microlocal.Overlap.TransportedJetCoefficients
import Burnett.Analysis.Microlocal.BesselLocalization
import Burnett.Analysis.Microlocal.MatrixMeasure.TraceDensity

set_option autoImplicit false
set_option maxHeartbeats 180000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldMetric
open Burnett.Geometry.ChartVolume (chartTransition)
open Burnett.F05.OverlapCovariantGradient (overlapJetCoefficient)
open Burnett.F05.OverlapCovectors (roundOverlap roundOverlapTransition continuous_roundOverlapTransition
  measurableSet_roundOverlap)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.OverlapWindows (CommonCutoffPatch)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ComplexConjugate ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem setIntegral_transport {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (f : α → ℂ) (g : β → ℂ)
    {U U' : Set α} {V V' : Set β} (hU : U = U') (hV : V = V')
    (h : (∫ z in U, f z ∂μ) = ∫ y in V, g y ∂ν) :
    (∫ z in U', f z ∂μ) = ∫ y in V', g y ∂ν :=
  (congrArg (fun W => ∫ z in W, f z ∂μ) hU).symm.trans
    (h.trans (congrArg (fun W => ∫ y in W, g y ∂ν) hV))

private theorem source_plateau_integral
    (q d : CompactChartInput M) (x : E)
    (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)
    (μ : Measure (Chart q.ball)) (f : Chart q.ball → ℂ)
    (S : Set (Chart d.ball)) (hU : MeasurableSet (p.sourcePhasePlateauPreimage S)) :
    (∫ z in p.sourcePhasePlateauPreimage S,
      (((((q.cutoff : E → ℝ) z.1)⁻¹) ^ 2 : ℝ) : ℂ) * f z ∂μ) =
    ∫ z in p.sourcePhasePlateauPreimage S, (((p.sourceFactor : E → ℝ) z.1 ^ 2 : ℝ) : ℂ) * f z ∂μ := by
  apply setIntegral_congr_fun hU
  rintro _ ⟨z, hz, rfl⟩
  exact congrArg (fun t : ℝ => ((t ^ 2 : ℝ) : ℂ) * f z.1)
    (p.sourceFactor_on_halfBall hz.1).symm

omit [IsManifold Model ∞ M] in
private theorem target_plateau_integral
    (q d : CompactChartInput M) (x : E)
    (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)
    (μ : Measure (Chart d.ball)) (f : Chart d.ball → JetSlot → JetSlot → ℂ)
    (w : JetSlot → JetSlot → D)
    (hw : ∀ i k, EqOn (w i k : E → ℝ) (overlapJetCoefficient q.center d.center i k)
      (chartTransition q.center d.center '' p.sourceInput.ball.closedBall))
    (V : Set (Chart d.ball)) (hV : MeasurableSet V) (hVP : V ⊆ p.targetPhasePlateau)
    (i j : JetSlot) :
    (∫ y in V, ∑ k : JetSlot, ∑ l : JetSlot,
      conj (physicalCoefficient (w i k) y.1) * physicalCoefficient (w j l) y.1 *
        (((p.targetFactor : E → ℝ) y.1 ^ 2 : ℝ) : ℂ) * f y k l ∂μ) =
    ∫ y in V, ∑ k : JetSlot, ∑ l : JetSlot,
      conj (↑(overlapJetCoefficient q.center d.center i k y.1) : ℂ) *
        (↑(overlapJetCoefficient q.center d.center j l y.1) : ℂ) *
        (((((d.cutoff : E → ℝ) y.1)⁻¹) ^ 2 : ℝ) : ℂ) * f y k l ∂μ := by
  apply setIntegral_congr_fun hV
  intro y hy
  have hyP : (y.1 : E) ∈ p.targetPlateau := hVP hy
  have hImage : (y.1 : E) ∈ chartTransition q.center d.center '' p.sourceInput.ball.closedBall :=
    interior_subset (p.targetPlateau_subset_interior_image hyP)
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  have hiw : physicalCoefficient (w i k) y.1 = (↑(overlapJetCoefficient q.center d.center i k y.1) : ℂ) :=
    congrArg Complex.ofReal (hw i k hImage)
  have hjw : physicalCoefficient (w j l) y.1 = (↑(overlapJetCoefficient q.center d.center j l y.1) : ℂ) :=
    congrArg Complex.ofReal (hw j l hImage)
  rw [hiw, hjw, p.targetFactor_on_targetPlateau hyP]

private theorem source_plateau_preimage_measurable
    (q d : CompactChartInput M) (x : E)
    (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)
    (S : Set (Chart d.ball)) (hS : MeasurableSet S) : MeasurableSet (p.sourcePhasePlateauPreimage S) := by
  let T : roundOverlap q d → Chart d.ball := fun z => (roundOverlapTransition q d z).1
  have hT : Measurable T := (continuous_subtype_val.comp (continuous_roundOverlapTransition q d)).measurable
  have hB : MeasurableSet {z : roundOverlap q d | (z.1.1 : E) ∈ Metric.closedBall x (p.sourceRadius / 2)} :=
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).measurable
      Metric.isClosed_closedBall.measurableSet
  exact (MeasurableEmbedding.subtype_coe (measurableSet_roundOverlap q d)).measurableSet_image.mpr
    (hB.inter (hT hS))

omit [IsManifold Model ∞ M] in
private theorem target_window_inclusion_base
    (q d : CompactChartInput M) (x : E)
    (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)
    (y : Chart p.targetInput.ball) :
    Subtype.val (p.targetPhaseInclusion y).1 = Subtype.val y.1 := by
  rcases y with ⟨⟨y, hy⟩, ξ⟩
  change y = y
  rfl

omit [IsManifold Model ∞ M] in
private theorem small_window_target_preimage_mem
    (q d : CompactChartInput M) (x : E)
    (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)
    (S : Set (Chart d.ball)) :
    ∀ y ∈ p.targetPhaseInclusion ⁻¹' (S ∩ p.targetPhasePlateau), (y.1 : E) ∈ p.targetPlateau := by
  intro y hy
  have hp : p.targetPhaseInclusion y ∈ p.targetPhasePlateau := hy.2
  exact Eq.mp (congrArg (fun z : E => z ∈ p.targetPlateau)
    (target_window_inclusion_base q d x p y)) hp

omit [IsManifold Model ∞ M] in
private theorem small_window_target_preimage_measurable
    (q d : CompactChartInput M) (x : E)
    (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)
    (S : Set (Chart d.ball)) (hS : MeasurableSet S) :
    MeasurableSet (p.targetPhaseInclusion ⁻¹' (S ∩ p.targetPhasePlateau)) :=
  p.continuous_targetPhaseInclusion.measurable (hS.inter p.measurableSet_targetPhasePlateau)

private theorem small_window_source_plateau_eq
    (q d : CompactChartInput M) (x : E)
    (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)
    (S : Set (Chart d.ball)) :
    p.sourcePhaseInclusion '' ((roundChartWindowMap p.sourceInput p.targetInput
      p.sourceInput_ball_in_overlap p.sourceInput_mapsTo_targetInput) ⁻¹'
        (p.targetPhaseInclusion ⁻¹' (S ∩ p.targetPhasePlateau))) = p.sourcePhasePlateauPreimage S :=
  p.sourcePhaseInclusion_image_preimage_targetPlateau
    (roundChartWindowMap p.sourceInput p.targetInput p.sourceInput_ball_in_overlap
      p.sourceInput_mapsTo_targetInput) (fun z => p.roundChartWindowMap_inclusion z) S

/-- On the two plateaus the common-cutoff factors are reciprocals of the
original cutoffs, and the coefficient extensions agree with the actual
Jacobian entries. The small-window sets yield the ambient overlap sets. -/
theorem normalized_ambientEntries_of_commonPatch_factors
    (q d : CompactChartInput M) (x : E)
    (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (w : JetSlot → JetSlot → D)
    (hw : ∀ i k, EqOn (w i k : E → ℝ) (overlapJetCoefficient q.center d.center i k)
      (chartTransition q.center d.center '' p.sourceInput.ball.closedBall))
    (he :
      let T := roundChartWindowMap p.sourceInput p.targetInput
        p.sourceInput_ball_in_overlap p.sourceInput_mapsTo_targetInput
      ∀ (S : Set (Chart p.targetInput.ball)) (_ : MeasurableSet S)
        (_ : ∀ y ∈ S, (y.1 : E) ∈ p.targetPlateau) (i j : JetSlot),
        (∫ z in p.sourcePhaseInclusion '' (T ⁻¹' S),
          (((p.sourceFactor : E → ℝ) z.1 ^ 2 : ℝ) : ℂ) * density νq hfq z i j ∂traceMeasure νq) =
        ∫ y in p.targetPhaseInclusion '' S, ∑ k : JetSlot, ∑ l : JetSlot,
          conj (physicalCoefficient (w i k) y.1) * physicalCoefficient (w j l) y.1 *
            (((p.targetFactor : E → ℝ) y.1 ^ 2 : ℝ) : ℂ) * density νd hfd y k l ∂traceMeasure νd)
    (S : Set (Chart d.ball)) (hS : MeasurableSet S) (i j : JetSlot) :
    (∫ z in p.sourcePhasePlateauPreimage S,
      (((((q.cutoff : E → ℝ) z.1)⁻¹) ^ 2 : ℝ) : ℂ) * density νq hfq z i j ∂traceMeasure νq) =
    ∫ y in S ∩ p.targetPhasePlateau, ∑ k : JetSlot, ∑ l : JetSlot,
      conj (↑(overlapJetCoefficient q.center d.center i k y.1) : ℂ) *
        (↑(overlapJetCoefficient q.center d.center j l y.1) : ℂ) *
        (((((d.cutoff : E → ℝ) y.1)⁻¹) ^ 2 : ℝ) : ℂ) * density νd hfd y k l ∂traceMeasure νd := by
  let V := S ∩ p.targetPhasePlateau
  have hV : MeasurableSet V := hS.inter p.measurableSet_targetPhasePlateau
  let f : Chart q.ball → ℂ :=
    fun z => (((p.sourceFactor : E → ℝ) z.1 ^ 2 : ℝ) : ℂ) * density νq hfq z i j
  let g : Chart d.ball → ℂ := fun y => ∑ k : JetSlot, ∑ l : JetSlot,
    conj (physicalCoefficient (w i k) y.1) * physicalCoefficient (w j l) y.1 *
      (((p.targetFactor : E → ℝ) y.1 ^ 2 : ℝ) : ℂ) * density νd hfd y k l
  have hSmall := he (p.targetPhaseInclusion ⁻¹' V)
    (small_window_target_preimage_measurable q d x p S hS)
    (small_window_target_preimage_mem q d x p S) i j
  have hEntry := setIntegral_transport (traceMeasure νq) (traceMeasure νd) f g
    (small_window_source_plateau_eq q d x p S)
    (p.targetPhaseInclusion_image_preimage_inter_plateau S)
    hSmall
  have hLeft := source_plateau_integral q d x p (traceMeasure νq)
    (fun z => density νq hfq z i j) S (source_plateau_preimage_measurable q d x p S hS)
  have hRight := target_plateau_integral q d x p (traceMeasure νd)
    (density νd hfd) w hw V hV inter_subset_right i j
  exact hLeft.trans (hEntry.trans hRight)

end Burnett.Microlocal.Overlap
