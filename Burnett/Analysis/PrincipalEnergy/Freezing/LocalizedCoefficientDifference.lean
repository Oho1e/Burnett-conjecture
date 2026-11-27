import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianOrderOnePairing
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Metric Set
open scoped ContDiff ENNReal

/-- The coefficient difference extended by the same nested cutoff appearing
in the local freezing argument. -/
def localizedCoefficientDifference (χ C : E → ℝ) (x₀ : E) : E → ℝ :=
  χ * fun x => C x - C x₀

theorem localized_coefficient_difference_on_core (χ C : E → ℝ) (x₀ x : E) (hx : χ x = 1) :
    localizedCoefficientDifference χ C x₀ x = C x - C x₀ := by
  change χ x * (C x - C x₀) = _
  rw [hx, one_mul]

/-- At scale ℓ the zeroth coefficient difference gains one ℓ. A derivative
on the cutoff cancels that factor exactly once. -/
theorem localized_coefficient_difference_bounds
    (χ C : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hC : ContDiff ℝ ∞ C)
    (x₀ : E) (R ℓ L K : ℝ) (hR : 0 ≤ R) (hℓ : 0 < ℓ) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (support : tsupport χ ⊆ closedBall x₀ (R*ℓ))
    (cutBound : ∀ x, ‖χ x‖ ≤ 1)
    (cutGradient : ∀ x, ‖fderiv ℝ χ x‖ ≤ K/ℓ)
    (coefficientGradient : ∀ x ∈ closedBall x₀ (R*ℓ), ‖fderiv ℝ C x‖ ≤ L) :
    ∀ x, ‖localizedCoefficientDifference χ C x₀ x‖ ≤ L*(R*ℓ) ∧
      ‖fderiv ℝ (localizedCoefficientDifference χ C x₀) x‖ ≤ (1+R*K)*L := by
  have radius : 0 ≤ R*ℓ := mul_nonneg hR hℓ.le
  intro x
  have deriv : fderiv ℝ (localizedCoefficientDifference χ C x₀) x =
      χ x • fderiv ℝ C x + (C x - C x₀) • fderiv ℝ χ x := by
    unfold localizedCoefficientDifference
    rw [fderiv_mul ((hχ.differentiable (by simp)) x)
      (((hC.differentiable (by simp)) x).sub_const (C x₀)), fderiv_sub_const]
  by_cases hx : x ∈ closedBall x₀ (R*ℓ)
  · have step : ‖C x - C x₀‖ ≤ L*(R*ℓ) := by
      have via := (convex_closedBall x₀ (R*ℓ)).norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => (hC.differentiable (by simp)) z) coefficientGradient (mem_closedBall_self radius) hx
      exact via.trans (mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_eq_norm] using hx) hL)
    constructor
    · change ‖χ x * (C x - C x₀)‖ ≤ _
      rw [norm_mul]
      calc
        _ ≤ 1 * (L*(R*ℓ)) := mul_le_mul (cutBound x) step (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    · rw [deriv]
      calc
        _ ≤ ‖χ x‖ * ‖fderiv ℝ C x‖ + ‖C x-C x₀‖ * ‖fderiv ℝ χ x‖ := by
          simpa only [norm_smul] using
            norm_add_le (χ x • fderiv ℝ C x) ((C x-C x₀) • fderiv ℝ χ x)
        _ ≤ 1*L + (L*(R*ℓ))*(K/ℓ) := add_le_add
          (mul_le_mul (cutBound x) (coefficientGradient x hx) (norm_nonneg _) zero_le_one)
          (mul_le_mul step (cutGradient x) (norm_nonneg _) (mul_nonneg hL radius))
        _ = _ := by field_simp [hℓ.ne']
  · have hxs : x ∉ tsupport χ := fun hs => hx (support hs)
    have zero : χ x = 0 := image_eq_zero_of_notMem_tsupport hxs
    have dzero : fderiv ℝ χ x = 0 := fderiv_of_notMem_tsupport ℝ hxs
    rw [deriv]
    simp only [localizedCoefficientDifference, Pi.mul_apply, zero, zero_mul, zero_smul, dzero,
      smul_zero, add_zero, norm_zero]
    exact ⟨mul_nonneg hL radius, mul_nonneg (add_nonneg zero_le_one (mul_nonneg hR hK)) hL⟩

/-- The same bounds as actual L∞ seminorms, including the full gradient. -/
theorem localized_coefficient_difference_Linfty
    (χ C : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hC : ContDiff ℝ ∞ C)
    (x₀ : E) (R ℓ L K : ℝ) (hR : 0 ≤ R) (hℓ : 0 < ℓ) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (support : tsupport χ ⊆ closedBall x₀ (R*ℓ))
    (cutBound : ∀ x, ‖χ x‖ ≤ 1)
    (cutGradient : ∀ x, ‖fderiv ℝ χ x‖ ≤ K/ℓ)
    (coefficientGradient : ∀ x ∈ closedBall x₀ (R*ℓ), ‖fderiv ℝ C x‖ ≤ L) :
    eLpNorm (localizedCoefficientDifference χ C x₀) ⊤ volume ≤ ENNReal.ofReal (L*(R*ℓ)) ∧
      eLpNorm (fderiv ℝ (localizedCoefficientDifference χ C x₀)) ⊤ volume ≤ ENNReal.ofReal ((1+R*K)*L) := by
  have bounds := localized_coefficient_difference_bounds χ C hχ hC x₀ R ℓ L K hR hℓ hL hK
    support cutBound cutGradient coefficientGradient
  simp only [eLpNorm_exponent_top]
  exact ⟨eLpNormEssSup_le_of_ae_bound (.of_forall fun x => (bounds x).1),
    eLpNormEssSup_le_of_ae_bound (.of_forall fun x => (bounds x).2)⟩

end Burnett.A02.FrequencySplit
