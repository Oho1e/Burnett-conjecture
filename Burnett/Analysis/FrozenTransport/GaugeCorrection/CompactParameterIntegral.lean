import Burnett.Analysis.FrozenTransport.GaugeCorrection.DominatedIntegralJets
import Burnett.Analysis.PrincipalEnergy.Localization.ProductPartialJets
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false
set_option maxRecDepth 3700
set_option maxHeartbeats 4600000

noncomputable section

namespace Burnett.V08

open Filter Function MeasureTheory Metric Set Burnett.A03
open Burnett.Analysis.CarlesonEmbedding (contDiff_firstPartialJet)
open scoped ContDiff ENNReal

/-- Compact integration in the segment parameter preserves all real
Fréchet derivatives of a jointly smooth integrand. -/
theorem contDiff_unitIntervalIntegral
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
    (F : X × ℝ → ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x : X => ∫ t in (0 : ℝ)..1, F (x,t)) := by
  let J (n : ℕ) : X × ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => X) ℝ :=
    fun p => iteratedFDeriv ℝ n (fun x => F (x, p.2)) p.1
  have hJ (n : ℕ) : Continuous (J n) := (contDiff_firstPartialJet hF n).continuous
  let K : Set ℝ := Ioc 0 1
  let μ : Measure ℝ := volume.restrict K
  let cut (x : X) (t : ℝ) : ℝ := K.indicator (fun s => F (x,s)) t
  have hK : MeasurableSet K := measurableSet_Ioc
  have hμ : μ univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono Ioc_subset_Icc_self).trans_lt
      (isCompact_Icc.measure_lt_top (μ := (volume : Measure ℝ)))
  letI : IsFiniteMeasure μ := ⟨hμ⟩
  have hCutJet (n : ℕ) (x : X) (t : ℝ) :
      iteratedFDeriv ℝ n (fun y => cut y t) x =
        K.indicator (fun s => J n (x,s)) t := by
    by_cases ht : t ∈ K
    · simp only [cut, indicator_of_mem ht, J]
    · simp [cut, indicator_of_notMem ht]
  have dom : DominatedIntegralJets μ cut := by
    constructor
    · intro t
      by_cases ht : t ∈ K
      · simpa only [cut, indicator_of_mem ht] using hF.comp (contDiff_id.prodMk contDiff_const)
      · simpa only [cut, indicator_of_notMem ht] using (contDiff_const (c := (0 : ℝ)))
    · intro n x
      simp only [hCutJet]
      exact ((hJ n).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.indicator hK
    · intro n x
      obtain ⟨B, hB, hBound⟩ :=
        (((isCompact_closedBall x 1).prod isCompact_Icc).image (hJ n)).isBounded.exists_pos_norm_le
      refine ⟨1, zero_lt_one, fun _ => B, integrable_const _, ?_⟩
      intro y hy t
      rw [hCutJet]
      by_cases ht : t ∈ K
      · rw [indicator_of_mem ht]
        exact hBound _ (mem_image_of_mem _ ⟨ball_subset_closedBall hy, Ioc_subset_Icc_self ht⟩)
      · rw [indicator_of_notMem ht, norm_zero]
        exact hB.le
  have hSmooth := contDiff_integral_of_dominated_jets μ cut dom
  have heq (x : X) : (∫ t, cut x t ∂μ) = ∫ t in (0 : ℝ)..1, F (x,t) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK] with t ht
    exact indicator_of_mem ht _
  rwa [funext heq] at hSmooth

end Burnett.V08
