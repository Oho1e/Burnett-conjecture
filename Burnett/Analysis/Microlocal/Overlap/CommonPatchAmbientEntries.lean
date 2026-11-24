import Burnett.Analysis.Microlocal.Overlap.CommonPatchPhaseInclusion
import Burnett.Analysis.Microlocal.Overlap.LocalCutoffWeightedEntry
import Burnett.Analysis.Microlocal.Overlap.OriginalMatchingCutoffEntryMeasures
import Burnett.Analysis.Microlocal.Overlap.SubsequenceRefinement

/-!
# Ambient entry measures on a common cutoff patch

Two independently cut off windows can be compared on a patch where both
original cutoffs are nonzero. The matching-cutoff identity is applied on
the small windows and the same-chart cutoff square laws move the result
back to the original windows.
-/

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.ChartVolume (chartTransition)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OverlapCovariantGradient (overlapJetCoefficient)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts
  (CompactChartInput RepresentsCompactJetPairings exists_common_refinement_originalVolume_pairDensities)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density integrable_density_entry)
open Burnett.Microlocal.OverlapWindows (CommonCutoffPatch)
open Burnett.X02.SobolevTestJet (D test_smooth)
open scoped BigOperators ComplexConjugate ContDiff Manifold

private theorem integral_sum_jetSlots {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : JetSlot → JetSlot → X → ℂ) (hF : ∀ k l, Integrable (F k l) μ) :
    (∫ y, ∑ k, ∑ l, F k l y ∂μ) = ∑ k, ∑ l, ∫ y, F k l y ∂μ :=
  (integral_finset_sum _ (fun k _ => integrable_finset_sum _ (fun l _ => hF k l))).trans
    (Finset.sum_congr rfl (fun k _ => integral_finset_sum _ (fun l _ => hF k l)))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- On the plateau of a common patch, the original ambient matrix densities
obey the chart change law after reweighting each by its own squared cutoff
factor. The two input density witnesses are preserved. -/
theorem exists_commonPatch_ambientEntryMeasures
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hbnd : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q d : CompactChartInput M) (x : E)
    (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (hRq : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ νq hfq)
    (hRd : RepresentsCompactJetPairings d.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB d.center d.cutoff
        (d.cutoff_support.trans d.ball_in_chart)) σ νd hfd) :
    let T := roundChartWindowMap p.sourceInput p.targetInput
      p.sourceInput_ball_in_overlap p.sourceInput_mapsTo_targetInput
    ∃ w : JetSlot → JetSlot → D,
      (∀ i k, EqOn (w i k : E → ℝ) (overlapJetCoefficient q.center d.center i k)
        (chartTransition q.center d.center '' p.sourceInput.ball.closedBall)) ∧
      ∀ (S : Set (Chart p.targetInput.ball)) (_ : MeasurableSet S)
        (_ : ∀ y ∈ S, (y.1 : E) ∈ p.targetPlateau) (i j : JetSlot),
        (∫ z in p.sourcePhaseInclusion '' (T ⁻¹' S),
          (((p.sourceFactor : E → ℝ) z.1 ^ 2 : ℝ) : ℂ) * density νq hfq z i j ∂traceMeasure νq) =
        ∫ y in p.targetPhaseInclusion '' S, ∑ k : JetSlot, ∑ l : JetSlot,
          conj (physicalCoefficient (w i k) y.1) * physicalCoefficient (w j l) y.1 *
            (((p.targetFactor : E → ℝ) y.1 ^ 2 : ℝ) : ℂ) * density νd hfd y k l ∂traceMeasure νd := by
  intro T
  obtain ⟨τ, hτ, ⟨νq', hfq', hRq'⟩, ⟨νd', hfd', hRd'⟩⟩ :=
    exists_common_refinement_originalVolume_pairDensities r B g hB hg hnB hconv hbnd
      p.sourceInput p.targetInput σ hσ
  have hστ : StrictMono (σ ∘ τ) := hσ.comp hτ
  have hq : p.sourceInput.ball.closedBall ⊆ q.ball.closedBall :=
    p.sourceInput_ball_subset_interior.trans interior_subset
  have hd : p.targetInput.ball.closedBall ⊆ d.ball.closedBall :=
    p.targetInput_ball_subset_interior.trans interior_subset
  obtain ⟨w, hw, hEntries⟩ := exists_original_matchingCutoff_compactInteriorEntryMeasures
    r B g hB hg hnB hconv hbnd p.sourceInput p.targetInput p.sourceInput_ball_in_overlap
    p.sourceInput_mapsTo_targetInput p.targetInput_cutoff_support_image p.inputs_matching_cutoffs
    (σ ∘ τ) hστ νq' hfq' νd' hfd' hRq' hRd'
  refine ⟨w, hw, ?_⟩
  intro S hS hPlateau i j
  have hTS : MeasurableSet (T ⁻¹' S) :=
    (continuous_roundChartWindowMap p.sourceInput p.targetInput
      p.sourceInput_ball_in_overlap p.sourceInput_mapsTo_targetInput).measurable hS
  have hSource := sameChart_cutoffMul_setIntegral_on_image r B g hB hg hnB hconv hbnd q
    p.sourceInput.ball hq p.sourceInput.cutoff p.sourceFactor p.sourceInput.cutoff_support
    p.sourceCutoff_eq_mul (σ ∘ τ) hστ νq hfq νq' hfq' (hRq.comp_strictMono τ hτ) hRq'
    (fun _ => (1 : ℂ)) measurable_const 1 zero_le_one (fun _ => norm_one.le) (T ⁻¹' S) hTS i j
  simp only [one_mul] at hSource
  let a (k l : JetSlot) (z : Chart d.ball) : ℂ :=
    conj (physicalCoefficient (w i k) z.1) * physicalCoefficient (w j l) z.1
  let sq (z : Chart d.ball) : ℂ := (((p.targetFactor : E → ℝ) z.1 ^ 2 : ℝ) : ℂ)
  let A (k l : JetSlot) := (physicalCoefficient (w i k)).bound * (physicalCoefficient (w j l)).bound
  have ha (k l : JetSlot) : Continuous (a k l) := by
    have hbase : Continuous (fun z : Chart d.ball => (z.1 : E)) :=
      continuous_subtype_val.comp continuous_fst
    have hc (v : D) : Continuous (fun z : Chart d.ball => physicalCoefficient v z.1) :=
      Complex.continuous_ofReal.comp ((test_smooth v).continuous.comp hbase)
    exact (Complex.continuous_conj.comp (hc (w i k))).mul (hc (w j l))
  have hA (k l : JetSlot) : 0 ≤ A k l :=
    mul_nonneg (physicalCoefficient (w i k)).bound_nonneg (physicalCoefficient (w j l)).bound_nonneg
  have haBound (k l : JetSlot) (z : Chart d.ball) : ‖a k l z‖ ≤ A k l := by
    change ‖conj (physicalCoefficient (w i k) z.1) * physicalCoefficient (w j l) z.1‖ ≤ A k l
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul ((physicalCoefficient (w i k)).norm_le _) ((physicalCoefficient (w j l)).norm_le _)
      (norm_nonneg _) (physicalCoefficient (w i k)).bound_nonneg
  let F (k l : JetSlot) (y : Chart p.targetInput.ball) := a k l (p.targetPhaseInclusion y) * density νd' hfd' y k l
  let G (k l : JetSlot) (y : Chart d.ball) := (a k l y * sq y) * density νd hfd y k l
  have hF (k l : JetSlot) : Integrable (F k l) (traceMeasure νd') :=
    (integrable_density_entry νd' hfd' k l).bdd_mul
      ((ha k l).comp (continuous_sameChartBallInclusion hd)).measurable.aestronglyMeasurable
      ⟨A k l, fun y => haBound k l (p.targetPhaseInclusion y)⟩
  have hs : Continuous sq := Complex.continuous_ofReal.comp
    (((test_smooth p.targetFactor).continuous.comp (continuous_subtype_val.comp continuous_fst)).pow 2)
  have hsBound (y : Chart d.ball) : ‖sq y‖ ≤ (physicalCoefficient p.targetFactor).bound ^ 2 := by
    have he : sq y = (physicalCoefficient p.targetFactor y.1) ^ 2 := Complex.ofReal_pow _ _
    rw [he, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((physicalCoefficient p.targetFactor).norm_le y.1) 2
  have hG (k l : JetSlot) : Integrable (G k l) (traceMeasure νd) :=
    (integrable_density_entry νd hfd k l).bdd_mul ((ha k l).mul hs).measurable.aestronglyMeasurable
      ⟨A k l * (physicalCoefficient p.targetFactor).bound ^ 2, fun y => by
        rw [norm_mul]
        exact mul_le_mul (haBound k l y) (hsBound y) (norm_nonneg _) (hA k l)⟩
  have hTarget (k l : JetSlot) : (∫ y in S, F k l y ∂traceMeasure νd') =
      ∫ y in p.targetPhaseInclusion '' S, G k l y ∂traceMeasure νd :=
    sameChart_cutoffMul_setIntegral_on_image r B g hB hg hnB hconv hbnd d
      p.targetInput.ball hd p.targetInput.cutoff p.targetFactor p.targetInput.cutoff_support
      p.targetCutoff_eq_mul (σ ∘ τ) hστ νd hfd νd' hfd' (hRd.comp_strictMono τ hτ) hRd'
      (a k l) (ha k l).measurable (A k l) (hA k l) (haBound k l) S hS k l
  calc
    _ = ∫ z in T ⁻¹' S, density νq' hfq' z i j ∂traceMeasure νq' := hSource.symm
    _ = ∫ y in S, ∑ k, ∑ l, F k l y ∂traceMeasure νd' :=
      hEntries p.targetPlateau p.isCompact_targetPlateau p.targetPlateau_subset_interior_image
        S hS hPlateau i j
    _ = ∑ k, ∑ l, ∫ y in S, F k l y ∂traceMeasure νd' :=
      integral_sum_jetSlots _ F (fun k l => (hF k l).integrableOn)
    _ = ∑ k, ∑ l, ∫ y in p.targetPhaseInclusion '' S, G k l y ∂traceMeasure νd :=
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hTarget k l
    _ = _ := (integral_sum_jetSlots _ G (fun k l => (hG k l).integrableOn)).symm

end Burnett.Microlocal.Overlap
