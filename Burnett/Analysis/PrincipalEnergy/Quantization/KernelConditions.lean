import Burnett.Analysis.PrincipalEnergy.Quantization.TargetDifference
import Burnett.Analysis.PrincipalEnergy.Quantization.LipschitzSymbolKernel

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Burnett.Microlocal.AngularDyadicKernel

/-- A single constant for the size and the two off-diagonal smoothness
conditions of the actual infrared-regularized commutator kernel. -/
theorem exists_firstOrderHigh_commutatorKernel_conditions {a : E → E → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : E → ℂ) (L : NNReal), LipschitzWith L r →
      (∀ x y : E, x ≠ y → ‖coefficientKernel r (firstOrderKernel a) x y‖ ≤
        (L : ℝ) * C * (‖x-y‖ ^ 4)⁻¹) ∧
      (∀ x y y' : E, x ≠ y → ‖y-y'‖ ≤ ‖x-y‖ / 2 →
        ‖coefficientKernel r (firstOrderKernel a) x y - coefficientKernel r (firstOrderKernel a) x y'‖ ≤
          (L : ℝ) * C * ‖y-y'‖ * (‖x-y‖ ^ 5)⁻¹) ∧
      (∀ x x' y : E, x ≠ y → ‖x-x'‖ ≤ ‖x-y‖ / 2 →
        ‖coefficientKernel r (firstOrderKernel a) x y - coefficientKernel r (firstOrderKernel a) x' y‖ ≤
          (L : ℝ) * C * ‖x-x'‖ * (‖x-y‖ ^ 5)⁻¹) := by
  obtain ⟨S,hS,hSize⟩ := exists_firstOrderLipschitzKernel_bound ha.frequency
  obtain ⟨Y,hY,hSource⟩ := exists_firstOrderLipschitzKernel_sourceDifference ha.frequency
  obtain ⟨X,hX,hTarget⟩ := exists_firstOrderLipschitzKernel_targetDifference ha
  let C := S+Y+X
  have hCS : S ≤ C := by unfold C; linarith
  have hCY : Y ≤ C := by unfold C; linarith
  have hCX : X ≤ C := by unfold C; linarith
  refine ⟨C, by unfold C; positivity, fun r L hr => ⟨?_, ?_, ?_⟩⟩
  · intro x y hxy
    exact (hSize r L hr 0 x y hxy).2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hCS (by positivity)) (by positivity))
  · intro x y y' hxy hd
    exact (hSource r L hr x y y' hxy hd).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCY (by positivity)) (norm_nonneg _)) (by positivity))
  · intro x x' y hxy hd
    exact (hTarget r L hr x x' y hxy hd).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCX (by positivity)) (norm_nonneg _)) (by positivity))

end Burnett.Analysis.FirstOrderDyadic
