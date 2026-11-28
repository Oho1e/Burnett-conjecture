import Burnett.Analysis.TransportWard.Weyl.DensityWeylResidualBound

set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 1700

noncomputable section

namespace Burnett.V03.Palatini

open Function Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic (baseDirectionSymbol)
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped ContDiff

local notation "J" => Fin 4 × Fin 4
local notation "P" => RadianParameter
local notation "W" => radianFrequencyWeight

open private norm_physicalRadianCovector_le from Burnett.Analysis.TransportWard.Weyl.FourierCoordinateAction

private theorem coordinateSymbol_bounds (k : Fin 4) :
    BaseDerivativeBounds (fun _ ξ => (physicalRadianCovector ξ k : ℂ)) W :=
  BaseDerivativeBounds.frequency_multiplier _ W tau (mul_pos (by norm_num) Real.pi_pos).le
    (fun ξ => (radian_frequency_weight_pos ξ).le)
    (fun ξ => by simpa only [Complex.norm_real] using norm_physicalRadianCovector_le k ξ)

theorem frozenSecondWeylLeading_profile {b : E → E → ℂ} (hb : ScaledJointOrderOne b) (i j : Fin 4) :
    ContDiff ℝ ∞ (uncurry (frozenSecondWeylLeading b i j)) ∧
      BaseDerivativeBounds (frozenSecondWeylLeading b i j) (fun ξ => (W ξ)^2) := by
  let A (k : Fin 4) := baseDirectionSymbol b (coordinateDirection k)
  have hA (k : Fin 4) := hb.baseDirection (coordinateDirection k)
  have haB (k : Fin 4) : BaseDerivativeBounds (A k) W :=
    ⟨fun ξ => (hA k).smooth.comp (contDiff_id.prodMk contDiff_const),(hA k).pureBase⟩
  have hs (k l : Fin 4) :
      ContDiff ℝ ∞ (fun p : P => (physicalRadianCovector p.2 k : ℂ) * A l p.1 p.2) :=
    ((physicalRadianCovector_complex_smooth k).comp contDiff_snd).mul (hA l).smooth
  have hTerm (k l : Fin 4) :
      BaseDerivativeBounds (fun x ξ => (physicalRadianCovector ξ k : ℂ) * A l x ξ) (fun ξ => (W ξ)^2) :=
    ((coordinateSymbol_bounds k).mul (haB l) (fun ξ => (radian_frequency_weight_pos ξ).le)).weight_congr
      (fun ξ => (pow_two (W ξ)).symm)
  exact ⟨(hs j i).add (hs i j),(hTerm j i).add (hTerm i j)⟩

private theorem frequencyDirectionalSymbol_order_zero_of_scaled_one {b : E → E → ℂ}
    (hb : ScaledJointOrderOne b) (e : E) :
    BaseDerivativeBounds (frequencyDirectionalSymbol b e) (fun _ => 1) := by
  apply BaseDerivativeBounds.of_joint (frequencyDirectionalSymbol_smooth b hb.smooth e)
  intro n
  obtain ⟨C,hC,hJ⟩ := hb.bound (n+1)
  refine ⟨‖e‖*C,mul_nonneg (norm_nonneg _) hC,fun p => ?_⟩
  rw [mul_one]
  have hw := radian_frequency_weight_pos p.2
  apply (mul_le_mul_iff_right₀ hw).mp
  calc
    _ ≤ W p.2 * ‖radianScaledParameterJet (uncurry (frequencyDirectionalSymbol b e)) n p‖ :=
      mul_le_mul_of_nonneg_left (radian_parameter_jet_norm_le_scaled _ n p) hw.le
    _ ≤ ‖e‖ * ‖radianScaledParameterJet (uncurry b) (n+1) p‖ :=
      scaled_frequencyDirectionalSymbol_le b hb.smooth e n p
    _ ≤ ‖e‖ * (C * W p.2) := mul_le_mul_of_nonneg_left (hJ p) (norm_nonneg _)
    _ = _ := by ring

theorem variableSecondWeylLeading_profile {b : E → E → ℂ} (hb : ScaledJointOrderOne b)
    (c : SchwartzMap E ℂ) (d : J) :
    ContDiff ℝ ∞ (uncurry (variableSecondWeylLeading b c d)) ∧
      BaseDerivativeBounds (variableSecondWeylLeading b c d) (fun ξ => (W ξ)^2) := by
  let q (ξ : E) := -((physicalRadianCovector ξ d.1 : ℂ) * (physicalRadianCovector ξ d.2 : ℂ))
  have hτ : 0 ≤ tau := (mul_pos (by norm_num) Real.pi_pos).le
  have hq (ξ : E) : ‖q ξ‖ ≤ tau^2 * (W ξ)^2 := by
    simp only [q,norm_neg,norm_mul,Complex.norm_real]
    exact (mul_le_mul (norm_physicalRadianCovector_le d.1 ξ) (norm_physicalRadianCovector_le d.2 ξ)
      (norm_nonneg _) (mul_nonneg hτ (radian_frequency_weight_pos ξ).le)).trans_eq (by
        change (tau * W ξ) * (tau * W ξ) = tau^2 * (W ξ)^2
        ring)
  have hqB := BaseDerivativeBounds.frequency_multiplier q (fun ξ => (W ξ)^2) (tau^2) (sq_nonneg _)
    (fun ξ => sq_nonneg (W ξ)) hq
  have hqS : ContDiff ℝ ∞ q :=
    ((physicalRadianCovector_complex_smooth d.1).mul (physicalRadianCovector_complex_smooth d.2)).neg
  have hLead := coefficientCommutatorLeading_bounds (frequencyDirectionalSymbol_order_zero_of_scaled_one hb) c
  exact ⟨(hqS.comp contDiff_snd).mul (coefficientCommutatorLeading_smooth hb.smooth c),
    (hqB.mul hLead (fun ξ => sq_nonneg (W ξ))).weight_congr (fun ξ => mul_one ((W ξ)^2))⟩

end Burnett.V03.Palatini
