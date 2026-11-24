import Burnett.Analysis.Microlocal.Overlap.NormalizedEntryTransport
import Burnett.Analysis.Microlocal.Overlap.WeightedSetIntegralTransfer

/-! Bounded Borel tensor tests of the ordered measures on a common plateau. -/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry.ConnectionDifference (CoordinateSpace)
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.F05.OverlapCovectors (roundOverlap continuous_roundOverlapTransition)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.OverlapWindows (CommonCutoffPatch)
open scoped BigOperators ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable {q d : CompactChartInput M} {x : CoordinateSpace}
variable (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)

variable (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
variable (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))

/-- Use the actual tensor-measure identity to test an ordered entry with a
bounded measurable coefficient. The same coefficient is pulled back in the source. -/
theorem normalizedEntry_weightedSetIntegral (i j : JetSlot)
    (hCov : ((sourcePlateauTrace p νq).withDensityᵥ
        (fun z => sourceNormalizedDensity p νq hfq i j z.1)).map (transportedRoundPoint q d) =
      ((traceMeasure νd).restrict p.targetPhasePlateau).withDensityᵥ
        (targetTransformedDensity p νd hfd i j))
    (a : Chart d.ball → ℂ) (ha : Measurable a) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ y, ‖a y‖ ≤ C)
    (S : Set (Chart d.ball)) (hS : MeasurableSet S) :
    (∫ z in transportedRoundPoint q d ⁻¹' S,
      a (transportedRoundPoint q d z) * sourceNormalizedDensity p νq hfq i j z.1 ∂sourcePlateauTrace p νq) =
      ∫ y in S, a y * targetTransformedDensity p νd hfd i j y
        ∂(traceMeasure νd).restrict p.targetPhasePlateau := by
  have hT : Measurable (transportedRoundPoint q d) :=
    (continuous_subtype_val.comp (continuous_roundOverlapTransition q d)).measurable
  have hq := integrable_sourceNormalizedDensity p νq hfq i j
  have hd := integrable_targetTransformedDensity p νd hfd i j
  apply setIntegral_mul_eq_of_setIntegral_preimage_eq _ _ _ hT _ _ hq hd _ a ha C hC hb S hS
  intro U hU
  have h := congrArg (fun μ : ComplexMeasure (Chart d.ball) => μ U) hCov
  dsimp only at h
  rw [VectorMeasure.map_apply _ hT hU, withDensityᵥ_apply hq (hT hU), withDensityᵥ_apply hd hU] at h
  exact h

/-- A finite contraction of all ordered jet entries can be tested on the
same Borel event on the receiving phase space. Bounded measurable weights
include regular tensor tests multiplied by an indicator of a Borel shell. -/
theorem normalizedJet_contractedSetIntegral
    (hCov : ∀ i j : JetSlot, ((sourcePlateauTrace p νq).withDensityᵥ
        (fun z => sourceNormalizedDensity p νq hfq i j z.1)).map (transportedRoundPoint q d) =
      ((traceMeasure νd).restrict p.targetPhasePlateau).withDensityᵥ
        (targetTransformedDensity p νd hfd i j))
    (a : JetSlot → JetSlot → Chart d.ball → ℂ) (ha : ∀ i j, Measurable (a i j))
    (C : JetSlot → JetSlot → ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (hb : ∀ i j y, ‖a i j y‖ ≤ C i j) (S : Set (Chart d.ball)) (hS : MeasurableSet S) :
    (∫ z in transportedRoundPoint q d ⁻¹' S, ∑ i : JetSlot, ∑ j : JetSlot,
      a i j (transportedRoundPoint q d z) * sourceNormalizedDensity p νq hfq i j z.1
        ∂sourcePlateauTrace p νq) =
      ∫ y in S, ∑ i : JetSlot, ∑ j : JetSlot,
        a i j y * targetTransformedDensity p νd hfd i j y
          ∂(traceMeasure νd).restrict p.targetPhasePlateau := by
  have hT : Measurable (transportedRoundPoint q d) :=
    (continuous_subtype_val.comp (continuous_roundOverlapTransition q d)).measurable
  have hIq (i j : JetSlot) : IntegrableOn
      (fun z => a i j (transportedRoundPoint q d z) * sourceNormalizedDensity p νq hfq i j z.1)
      (transportedRoundPoint q d ⁻¹' S) (sourcePlateauTrace p νq) :=
    ((integrable_sourceNormalizedDensity p νq hfq i j).bdd_mul
      ((ha i j).comp hT).aestronglyMeasurable ⟨C i j, fun z => hb i j (transportedRoundPoint q d z)⟩).integrableOn
  have hId (i j : JetSlot) : IntegrableOn
      (fun y => a i j y * targetTransformedDensity p νd hfd i j y) S
      ((traceMeasure νd).restrict p.targetPhasePlateau) :=
    ((integrable_targetTransformedDensity p νd hfd i j).bdd_mul
      (ha i j).aestronglyMeasurable ⟨C i j, hb i j⟩).integrableOn
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hIq i j),
      integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hId i j)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _ => hIq i j), integral_finset_sum _ (fun j _ => hId i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact normalizedEntry_weightedSetIntegral p νq hfq νd hfd i j (hCov i j)
    (a i j) (ha i j) (C i j) (hC i j) (hb i j) S hS

end Burnett.Microlocal.Overlap
