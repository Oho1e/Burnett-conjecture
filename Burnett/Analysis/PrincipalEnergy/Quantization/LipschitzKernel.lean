import Burnett.Analysis.PrincipalEnergy.Quantization.FirstOrderDyadic

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Burnett.Microlocal.AngularDyadicKernel
open scoped BigOperators FourierTransform Topology

def coefficientKernel (r : E → ℂ) (k : E → E → ℂ) (x y : E) : ℂ :=
  (r x - r y) * k x (x - y)

/-- A Lipschitz difference reduces the first-order kernel to critical size. -/
theorem coefficientKernel_size (r : E → ℂ) (k : E → E → ℂ) {L : NNReal}
    (hr : LipschitzWith L r) {C : ℝ}
    (hk : ∀ x z, z ≠ 0 → ‖k x z‖ ≤ C * (‖z‖ ^ 5)⁻¹)
    (x y : E) (hxy : x ≠ y) :
    ‖coefficientKernel r k x y‖ ≤ (L : ℝ) * C * (‖x - y‖ ^ 4)⁻¹ := by
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hLip : ‖r x - r y‖ ≤ (L : ℝ) * ‖x - y‖ := by
    simpa only [dist_eq_norm] using hr.dist_le_mul x y
  rw [coefficientKernel, norm_mul]
  calc
    _ ≤ ((L : ℝ) * ‖x-y‖) * (C * (‖x-y‖ ^ 5)⁻¹) :=
      mul_le_mul hLip (hk x (x-y) (sub_ne_zero.mpr hxy)) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [pow_succ (‖x-y‖) 4]
      field_simp [hpos.ne', pow_ne_zero 4 hpos.ne']

/-- This estimate applies both before and after sending the annular cutoff
to infinity. Only the off-diagonal kernel is compared here. -/
theorem firstOrderCoefficientKernel_size (a : E → E → ℂ) (p : E → ℕ → SchwartzMap E ℂ)
    (hp : ∀ x j, (p x j : E → ℂ) = 𝓕⁻ (normalizedFirstOrderAnnulus a x j))
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ x j, SchwartzMap.seminorm ℝ 0 0 (p x j) ≤ C ∧
      SchwartzMap.seminorm ℝ 6 0 (p x j) ≤ C)
    (r : E → ℂ) (L : NNReal) (hr : LipschitzWith L r) (N : ℕ) (x y : E) (hxy : x ≠ y) :
    ‖coefficientKernel r (fun u z => ∑ j ∈ Finset.range N, firstOrderAnnularKernel a u j z) x y‖ ≤
        (L : ℝ) * (34 * C) * (‖x-y‖ ^ 4)⁻¹ ∧
      ‖coefficientKernel r (firstOrderKernel a) x y‖ ≤ (L : ℝ) * (34 * C) * (‖x-y‖ ^ 4)⁻¹ := by
  exact ⟨coefficientKernel_size r _ hr
      (fun u z hz => ((firstOrderKernel_size a p hp C hC hBound u z hz).2 N).1) x y hxy,
    coefficientKernel_size r _ hr
      (fun u z hz => ((firstOrderKernel_size a p hp C hC hBound u z hz).2 0).2) x y hxy⟩

end Burnett.Analysis.FirstOrderDyadic
