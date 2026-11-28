import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualLowFields

set_option autoImplicit false
set_option maxRecDepth 6300
set_option maxHeartbeats 12500000
noncomputable section

namespace Burnett.C02

open Set Burnett.A05 Burnett.A02.FrequencySplit
open Burnett.RicciSymbol (Tensor2)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff

/-- The low-gauge Lie contractions, one-high-gauge term and both two-gauge
low-slot arrangements have the same actual C02 gradient estimate. -/
theorem exists_wardActualLowBranchesComponent_bounds (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16)
    (m : Tensor2) (w : ℝ) (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hOdd : ∀ ξ, a (-ξ) = -a ξ) (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (k : Fin 3 → OrderedPair) :
    let H₀ := wardTensorBasis (k 0)
    let H₁ := wardTensorBasis (k 1)
    let H₂ := wardTensorBasis (k 2)
    (∃ C : ℝ, 0 ≤ C ∧ WardActualLowComponentBound m ![false,true,true] k
      (wardActualLowCut ϑ κ (wardOneLowGaugeLieRaw m w a H₀ H₁ H₂)) C) ∧
    (∃ C : ℝ, 0 ≤ C ∧ WardActualLowComponentBound m ![true,true,false] k
      (wardActualLowCut ϑ κ (wardOneHighGaugeRaw m w a H₂ H₀ H₁)) C) ∧
    (∃ C : ℝ, 0 ≤ C ∧ WardActualLowComponentBound m ![true,false,false] k
      (wardActualLowCut ϑ κ (wardTwoGaugePhysicalLowRaw m w a H₁ H₂ H₀)) C) ∧
    (∃ C : ℝ, 0 ≤ C ∧ WardActualLowComponentBound m ![false,true,false] k
      (wardActualLowCut ϑ κ (wardTwoGaugeGaugeLowRaw m w a H₀ H₂ H₁)) C) := by
  intro H₀ H₁ H₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact exists_wardActualLowComponent_bound ϑ hϑ hCut κ hκ hSmall m _
      (wardOneLowGaugeLieProfiles m w a H₀ H₁ H₂)
      (wardOneLowGaugeLieProfiles_smooth m w a ha H₀ H₁ H₂) ![1,2] ![false,true,true] k
      (by intro j; fin_cases j <;> rfl)
      (wardOneLowGaugeLieRaw_normalized m w a ha hOdd hHom H₀ H₁ H₂)
  · exact exists_wardActualLowComponent_bound ϑ hϑ hCut κ hκ hSmall m _
      (wardOneHighGaugeProfiles m w a H₂ H₀ H₁)
      (wardOneHighGaugeProfiles_smooth m w a ha H₂ H₀ H₁) ![0,1] ![true,true,false] k
      (by intro j; fin_cases j <;> rfl)
      (wardOneHighGaugeRaw_normalized m w a ha hOdd hHom H₂ H₀ H₁)
  · refine exists_wardActualLowComponent_bound (ι := Fin 1) ϑ hϑ hCut κ hκ hSmall m _
      (fun _ => wardTwoGaugePhysicalLowProfile m w a H₁ H₂ H₀)
      (fun _ => (wardTwoGaugeLowProfiles_smooth m w a ha H₁ H₂ H₀).1) (fun _ => 0) ![true,false,false] k
      (fun _ => rfl) ?_
    intro x hx
    simpa only [Fin.sum_univ_one, wardPhaseCovector, Matrix.cons_val_zero] using
      (wardTwoGaugeLowRaw_normalized m w a ha hOdd hHom H₁ H₂ H₀ x hx).1
  · refine exists_wardActualLowComponent_bound (ι := Fin 1) ϑ hϑ hCut κ hκ hSmall m _
      (fun _ => wardTwoGaugeGaugeLowProfile m w a H₀ H₂ H₁)
      (fun _ => (wardTwoGaugeLowProfiles_smooth m w a ha H₀ H₂ H₁).2) (fun _ => 1) ![false,true,false] k
      (fun _ => rfl) ?_
    intro x hx
    simpa only [Fin.sum_univ_one, wardPhaseCovector, Matrix.cons_val_one, Matrix.cons_val_zero] using
      (wardTwoGaugeLowRaw_normalized m w a ha hOdd hHom H₀ H₂ H₁ x hx).2

end Burnett.C02
