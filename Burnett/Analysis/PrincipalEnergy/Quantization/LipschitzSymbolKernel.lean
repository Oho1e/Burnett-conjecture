import Burnett.Analysis.PrincipalEnergy.Quantization.FirstOrderSymbol
import Burnett.Analysis.PrincipalEnergy.Quantization.LipschitzKernel

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Burnett.Microlocal.AngularDyadicKernel
open scoped BigOperators Topology

/-- The actual annular kernels of the given first-order symbol obey a single
Lipschitz coefficient bound for all choices of cutoff, pair, and coefficient. -/
theorem exists_firstOrderLipschitzKernel_bound {a : E → E → ℂ} (ha : FrequencyOrderOne a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : E → ℂ) (L : NNReal), LipschitzWith L r →
      ∀ (N : ℕ) (x y : E), x ≠ y →
        ‖coefficientKernel r (fun u z => ∑ j ∈ Finset.range N, firstOrderAnnularKernel a u j z) x y‖ ≤
          (L : ℝ) * C * (‖x-y‖ ^ 4)⁻¹ ∧
        ‖coefficientKernel r (firstOrderKernel a) x y‖ ≤ (L : ℝ) * C * (‖x-y‖ ^ 4)⁻¹ := by
  obtain ⟨p, C, hC, hp, hBound⟩ := exists_normalizedInverseProfiles ha
  exact ⟨34*C, by positivity, fun r L hr N x y hxy =>
    firstOrderCoefficientKernel_size a p hp C hC hBound r L hr N x y hxy⟩

end Burnett.Analysis.FirstOrderDyadic
