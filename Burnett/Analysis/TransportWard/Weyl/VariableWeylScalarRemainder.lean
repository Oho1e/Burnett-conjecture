import Burnett.Analysis.TransportWard.Weyl.BaseDerivativeBounds
import Burnett.Analysis.TransportWard.Weyl.CoefficientCommutatorJointBound
import Burnett.Analysis.TransportWard.Weyl.FrozenWeylOperatorRemainder
import Burnett.Analysis.TransportWard.Weyl.VariableDensityWeylAction

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 1800

noncomputable section

namespace Burnett.V03

open Function Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic (FrequencyOrderOne)
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped ContDiff BigOperators

local notation "J" => Fin 4 × Fin 4
local notation "P" => RadianParameter
local notation "W" => radianFrequencyWeight
local notation "D" => frozenSchwartzCoordinatePartial

open private norm_physicalRadianCovector_le from Burnett.Analysis.TransportWard.Weyl.FourierCoordinateAction

theorem coefficientCommutatorLeading_smooth {a : E → E → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) (c : SchwartzMap E ℂ) :
    ContDiff ℝ ∞ (uncurry (coefficientCommutatorLeading a c)) := by
  change ContDiff ℝ ∞ (fun p : P => ∑ k : Fin 4,
    (tau : ℂ)⁻¹ * D k c p.1 * frequencyDirectionalSymbol a (coordinateDirection k) p.1 p.2)
  exact ContDiff.sum fun k _ => (contDiff_const.mul ((D k c).smooth'.comp contDiff_fst)).mul
    (frequencyDirectionalSymbol_smooth a ha (coordinateDirection k))

private theorem frequencyDirectionalSymbol_order_minus_one_of_scaled_zero {r : E → E → ℂ}
    (hs : ContDiff ℝ ∞ (uncurry r))
    (h : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P,
      ‖radianScaledParameterJet (uncurry r) n p‖ ≤ C) (e : E) :
    BaseDerivativeBounds (frequencyDirectionalSymbol r e) (fun ξ => (W ξ)⁻¹) := by
  apply BaseDerivativeBounds.of_joint (frequencyDirectionalSymbol_smooth r hs e)
  intro n
  obtain ⟨C,hC,hB⟩ := h (n+1)
  refine ⟨‖e‖*C,mul_nonneg (norm_nonneg _) hC,fun p => ?_⟩
  have hw := radian_frequency_weight_pos p.2
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hw).mpr
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (radian_parameter_jet_norm_le_scaled _ n p) hw.le).trans
    ((scaled_frequencyDirectionalSymbol_le r hs e n p).trans
      (mul_le_mul_of_nonneg_left (hB p) (norm_nonneg _)))

theorem coefficientCommutatorLeading_bounds {r : E → E → ℂ} {w : E → ℝ}
    (h : ∀ e, BaseDerivativeBounds (frequencyDirectionalSymbol r e) w)
    (c : SchwartzMap E ℂ) :
    BaseDerivativeBounds (coefficientCommutatorLeading r c) w := by
  let A (k : Fin 4) (x ξ : E) := (tau : ℂ)⁻¹ * D k c x *
    frequencyDirectionalSymbol r (coordinateDirection k) x ξ
  apply BaseDerivativeBounds.sum A
  intro k
  have hT := BaseDerivativeBounds.frequency_multiplier (fun _ => (tau : ℂ)⁻¹) (fun _ => 1)
    ‖(tau : ℂ)⁻¹‖ (norm_nonneg _) (fun _ => zero_le_one) (fun _ => by rw [mul_one])
  have hF := h (coordinateDirection k)
  exact ((hT.mul (BaseDerivativeBounds.schwartz_coefficient (D k c))
    (fun _ => zero_le_one)).mul hF (fun _ => by norm_num)).weight_congr (fun ξ => by simp)

theorem coefficientCommutatorSymbol_sub_normalizedWeylLeading_profile
    (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ) (c : SchwartzMap E ℂ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol β)) :
    let a := windowedWeylLeftSymbol θ β R h
    let b := normalizedWeylSymbol β
    let u (x ξ : E) := coefficientCommutatorSymbol a c x ξ - coefficientCommutatorLeading b c x ξ
    ContDiff ℝ ∞ (uncurry u) ∧ BaseDerivativeBounds u (fun ξ => (W ξ)⁻¹) := by
  intro a b u
  let r (x ξ : E) := a x ξ - b x ξ
  have ha : ScaledJointOrderOne a := windowedWeyl_leftSymbol_scaled_order_one θ β R h hAmp hPlateau hβ
  obtain ⟨hr, hR⟩ := windowedWeyl_leftSymbol_scaled_remainder θ β R h hAmp hPlateau
  obtain ⟨hRem,hB⟩ := coefficientCommutatorRemainder_joint_order_minus_one ha c
  have hf (x ξ : E) : fderiv ℝ (r x) ξ = fderiv ℝ (a x) ξ - fderiv ℝ (b x) ξ := by
    change fderiv ℝ (fun ζ => a x ζ - b x ζ) ξ = _
    rw [fderiv_fun_sub ((ha.firstBaseFrequency.frequency.smooth x).differentiable (by simp) ξ)
      ((hβ.firstBaseFrequency.frequency.smooth x).differentiable (by simp) ξ)]
  have hLead (x ξ : E) : coefficientCommutatorLeading r c x ξ =
      coefficientCommutatorLeading a c x ξ - coefficientCommutatorLeading b c x ξ := by
    simp only [coefficientCommutatorLeading,hf,ContinuousLinearMap.sub_apply,mul_sub,Finset.sum_sub_distrib]
  have he : u = fun x ξ => coefficientCommutatorRemainder a c x ξ +
      coefficientCommutatorLeading r c x ξ := by
    funext x ξ
    change coefficientCommutatorSymbol a c x ξ - _ = _
    rw [coefficientCommutatorSymbol_eq_leading_add_remainder ha.firstBaseFrequency.frequency,hLead]
    ring
  have hRemBounds : BaseDerivativeBounds (coefficientCommutatorRemainder a c) (fun ξ => (W ξ)⁻¹) :=
    BaseDerivativeBounds.of_joint hRem (by simpa only [div_eq_mul_inv] using hB)
  rw [he]
  exact ⟨hRem.add (coefficientCommutatorLeading_smooth hr c),
    hRemBounds.add (coefficientCommutatorLeading_bounds
      (frequencyDirectionalSymbol_order_minus_one_of_scaled_zero hr hR) c)⟩

namespace Palatini

def variableSecondWeylLeading (b : E → E → ℂ) (c : SchwartzMap E ℂ) (d : J)
    (x ξ : E) : ℂ :=
  -((physicalRadianCovector ξ d.1 : ℂ) * (physicalRadianCovector ξ d.2 : ℂ)) *
    coefficientCommutatorLeading b c x ξ

theorem variableCoefficientSecondSymbol_sub_normalizedWeylLeading_profile
    (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ) (c : SchwartzMap E ℂ) (d : J)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol β)) :
    let a := windowedWeylLeftSymbol θ β R h
    let b := normalizedWeylSymbol β
    let v (x ξ : E) := variableCoefficientSecondSymbol a c d x ξ - variableSecondWeylLeading b c d x ξ
    ContDiff ℝ ∞ (uncurry v) ∧ BaseDerivativeBounds v W := by
  intro a b v
  let k (ξ : E) := -((physicalRadianCovector ξ d.1 : ℂ) * (physicalRadianCovector ξ d.2 : ℂ))
  let u (x ξ : E) := coefficientCommutatorSymbol a c x ξ - coefficientCommutatorLeading b c x ξ
  obtain ⟨hSmooth,hBound⟩ := coefficientCommutatorSymbol_sub_normalizedWeylLeading_profile θ β R c h hAmp hPlateau hβ
  have hτ : 0 ≤ tau := (mul_pos (by norm_num) Real.pi_pos).le
  have hkVal (ξ : E) : ‖k ξ‖ ≤ tau^2 * (W ξ)^2 := by
    simp only [k,norm_neg,norm_mul,Complex.norm_real]
    calc
      _ ≤ (tau * W ξ) * (tau * W ξ) :=
        mul_le_mul (norm_physicalRadianCovector_le d.1 ξ) (norm_physicalRadianCovector_le d.2 ξ)
          (norm_nonneg _) (mul_nonneg hτ (radian_frequency_weight_pos ξ).le)
      _ = _ := by ring
  have hk := BaseDerivativeBounds.frequency_multiplier k (fun ξ => (W ξ)^2) (tau^2) (sq_nonneg _)
    (fun _ => sq_nonneg _) hkVal
  have hkSmooth : ContDiff ℝ ∞ k := ((physicalRadianCovector_complex_smooth d.1).mul
    (physicalRadianCovector_complex_smooth d.2)).neg
  have he : v = fun x ξ => k ξ * u x ξ := by
    funext x ξ
    simp only [v,variableCoefficientSecondSymbol,variableSecondWeylLeading,k,u,mul_sub]
  rw [he]
  refine ⟨(hkSmooth.comp contDiff_snd).mul hSmooth,?_⟩
  apply (hk.mul hBound (fun _ => sq_nonneg _)).weight_congr
  intro ξ
  change (W ξ)^2 * (W ξ)⁻¹ = W ξ
  rw [pow_two,mul_assoc,mul_inv_cancel₀ (radian_frequency_weight_pos ξ).ne',mul_one]

end Palatini
end Burnett.V03
