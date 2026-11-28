import Burnett.Analysis.TransportWard.Weyl.CoefficientIntegrandSections
import Burnett.Analysis.TransportWard.Weyl.WeightedParameterIntegration

set_option autoImplicit false
set_option maxHeartbeats 1250000
set_option maxRecDepth 1800

noncomputable section

namespace Burnett.V03

open Function Set Filter MeasureTheory Burnett.A03 Burnett.A02.FrequencySplit
open scoped ContDiff FourierTransform RealInnerProductSpace BigOperators

local notation "P" => RadianParameter
local notation "W" => radianFrequencyWeight

theorem coefficientTaylorIntegral_joint_order_minus_one {a : E → E → ℂ}
    (ha : ScaledJointOrderOne a) (c : SchwartzMap E ℂ) :
    ContDiff ℝ ∞ (fun p : P => ∫ e, coefficientTaylorIntegrand a c e p) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P,
        ‖iteratedFDeriv ℝ n (fun q : P => ∫ e, coefficientTaylorIntegrand a c e q) p‖ ≤ C / W p.2 := by
  obtain ⟨M,hM,hPos,hDom⟩ := coefficientTaylorIntegrand_integrable_majorants ha c
  have h := contDiff_integral_with_inverse_weighted_jets (X := P) (A := E)
    (volume : Measure E) (coefficientTaylorIntegrand a c) (fun p : P => W p.2)
    (fun p => radian_frequency_weight_one_le p.2)
    (coefficientTaylorIntegrand_section_smooth ha.smooth c)
    (coefficientTaylorIntegrand_section_measurable ha.smooth c) M hM hPos hDom
  exact ⟨h.1,fun n => ⟨∫ e, M n e,integral_nonneg (hPos n),h.2 n⟩⟩

/-- The exact Fourier-integrated scalar coefficient remainder has joint
symbol derivatives of order at most minus one in the original frequency. -/
theorem coefficientCommutatorRemainder_joint_order_minus_one {a : E → E → ℂ}
    (ha : ScaledJointOrderOne a) (c : SchwartzMap E ℂ) :
    ContDiff ℝ ∞ (uncurry (coefficientCommutatorRemainder a c)) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P,
        ‖iteratedFDeriv ℝ n (uncurry (coefficientCommutatorRemainder a c)) p‖ ≤ C / W p.2 := by
  let H (p : P) := ∫ e, coefficientTaylorIntegrand a c e p
  have hEq : uncurry (coefficientCommutatorRemainder a c) = Complex.I • H := rfl
  obtain ⟨hs,hJets⟩ := coefficientTaylorIntegral_joint_order_minus_one ha c
  have hH : ContDiff ℝ ∞ H := hs
  rw [hEq]
  refine ⟨hH.const_smul Complex.I, fun n => ?_⟩
  obtain ⟨C,hC,hB⟩ := hJets n
  refine ⟨C,hC,fun p => ?_⟩
  have hn : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  rw [iteratedFDeriv_const_smul_apply (hH.contDiffAt.of_le hn),norm_smul,Complex.norm_I,one_mul]
  exact hB p

end Burnett.V03
