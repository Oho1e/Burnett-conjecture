import Burnett.Analysis.PrincipalEnergy.Localization.IntegratedSymbolJets

set_option autoImplicit false
set_option maxHeartbeats 650000

noncomputable section

namespace Burnett.V03

open MeasureTheory Filter
open Burnett.Analysis.CarlesonEmbedding (contDiff_integral_of_locally_dominated_jets)
open scoped ContDiff

/-- The exact differentiated integrals keep a parameter-dependent
inverse order when the majorant has one common integrable numerator. -/
theorem contDiff_integral_with_inverse_weighted_jets {X A : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace A]
    (μ : Measure A) (f : A → X → ℂ) (w : X → ℝ) (hw : ∀ p, 1 ≤ w p)
    (hSmooth : ∀ a, ContDiff ℝ ∞ (f a))
    (hMeas : ∀ n : ℕ, ∀ p, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (f a) p) μ)
    (M : ℕ → A → ℝ) (hM : ∀ n, Integrable (M n) μ) (hPos : ∀ n a, 0 ≤ M n a)
    (hBound : ∀ n a p, ‖iteratedFDeriv ℝ n (f a) p‖ ≤ M n a / w p) :
    ContDiff ℝ ∞ (fun p => ∫ a, f a p ∂μ) ∧
      ∀ n p, ‖iteratedFDeriv ℝ n (fun q => ∫ a, f a q ∂μ) p‖ ≤ (∫ a, M n a ∂μ) / w p := by
  have hDom (n : ℕ) (p : X) : ∃ B : A → ℝ, Integrable B μ ∧
      ∀ a q, q ∈ Metric.ball p 1 → ‖iteratedFDeriv ℝ n (f a) q‖ ≤ B a :=
    ⟨M n, hM n, fun a q _ => (hBound n a q).trans (div_le_self (hPos n a) (hw q))⟩
  obtain ⟨hs,hJets⟩ := contDiff_integral_of_locally_dominated_jets μ f hSmooth hMeas hDom
  refine ⟨hs,fun n p => ?_⟩
  rw [hJets]
  calc
    _ ≤ ∫ a, M n a / w p ∂μ :=
      norm_integral_le_of_norm_le ((hM n).div_const _) (.of_forall fun a => hBound n a p)
    _ = _ := by rw [integral_div]

end Burnett.V03
