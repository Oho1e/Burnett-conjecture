import Burnett.Analysis.CubicEnergy.CompleteEnergy.MikhlinKernelJet
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.DyadicSquare (rescaleSymbol)
open MeasureTheory Metric Set
open scoped ContDiff FourierTransform

def kernelDecayWeight (z : E) : ℝ := ((1 + ‖z‖)^5)⁻¹

theorem integrable_kernelDecayWeight : Integrable kernelDecayWeight := by
  have hd : (Module.finrank ℝ E : ℝ) < (5 : ℝ) := by
    rw [show Module.finrank ℝ E = 4 from finrank_euclideanSpace_fin]
    norm_num
  have hi := integrable_one_add_norm (μ := (volume : Measure E)) hd
  convert hi using 1
  ext z
  simp [kernelDecayWeight, Real.rpow_neg (by positivity : 0 ≤ 1 + ‖z‖)]

theorem kernelDecayWeight_nonneg (z : E) : 0 ≤ kernelDecayWeight z := by
  unfold kernelDecayWeight
  positivity

private theorem fderiv_norm_le_iterated (f : E → ℂ) (z : E) :
    ‖fderiv ℝ f z‖ ≤ ‖iteratedFDeriv ℝ 1 f z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  let w : Fin 1 → E := fun _ => v
  calc
    ‖fderiv ℝ f z v‖ = ‖iteratedFDeriv ℝ 1 f z w‖ := by
      rw [iteratedFDeriv_one_apply]
    _ ≤ ‖iteratedFDeriv ℝ 1 f z‖ * ∏ i, ‖w i‖ :=
      (iteratedFDeriv ℝ 1 f z).le_opNorm w
    _ = _ := by simp [w]

/-- Six environmental derivatives on the unit sphere suffice for all of the
annular kernel bounds used in the unmodulated Mikhlin estimate. -/
theorem mikhlin_profile_kernel_bounds : ∃ A : ℝ, 0 ≤ A ∧
    ∀ (m : E → ℝ), ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ ξ, m (t • ξ) = m ξ) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n m ξ‖ ≤ D) →
      ∀ (a : SchwartzMap E ℂ), (∀ ξ, a ξ = ((mikhlinWindow ξ * m ξ : ℝ) : ℂ)) →
      (∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) →
      let φ := (SchwartzMap.fourierTransformCLE ℂ).symm a
      (∀ ξ, ‖a ξ‖ ≤ A * D) ∧
      ((∫ z, ‖z‖ * ‖φ z‖) ≤ A * D) ∧
      (∀ z, (1+‖z‖)^5 * ‖fderiv ℝ φ z‖ ≤ A * D) := by
  obtain ⟨C, hC, profile⟩ := mikhlin_profile_derivative_bound 0 6
  obtain ⟨C₀, hC₀, decay₀⟩ := mikhlin_inverse_profile_decay 0 6
  obtain ⟨C₁, hC₁, decay₁⟩ := mikhlin_inverse_profile_decay 1 5
  let W : ℝ := ∫ z, kernelDecayWeight z
  have hW : 0 ≤ W := integral_nonneg kernelDecayWeight_nonneg
  let A := C + C₀ * C * W + C₁ * C
  refine ⟨A, by positivity, ?_⟩
  intro m smooth hom D hD jet a shape cut φ
  have bound := profile m smooth (fun t ht ξ => by simpa using hom t ht ξ) D hD jet a shape cut
  have support : tsupport (a : E → ℂ) ⊆ closedBall (0 : E) 2 :=
    closure_minimal (fun ξ hx => by simpa using (cut ξ hx).2.le) isClosed_closedBall
  have invForm : (φ : E → ℂ) = 𝓕⁻ (a : E → ℂ) := by
    funext z
    simp [φ]
  have decay_zero (z : E) : (1 + ‖z‖)^6 * ‖φ z‖ ≤ C₀ * (C * D) := by
    simpa only [← invForm, norm_iteratedFDeriv_zero] using
      decay₀ a support (C * D) (mul_nonneg hC hD) (fun n hn => (bound n hn).2) z
  have weight (z : E) : ‖z‖ * ‖φ z‖ ≤ (C₀ * (C * D)) * kernelDecayWeight z := by
    unfold kernelDecayWeight
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ = (‖z‖ * (1 + ‖z‖)^5) * ‖φ z‖ := by ring
      _ ≤ (1 + ‖z‖)^6 * ‖φ z‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc
          _ ≤ (1 + ‖z‖) * (1 + ‖z‖)^5 :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = _ := by ring
      _ ≤ _ := decay_zero z
  have moment : (∫ z, ‖z‖ * ‖φ z‖) ≤ C₀ * C * W * D := by
    calc
      _ ≤ ∫ z, (C₀ * (C * D)) * kernelDecayWeight z :=
        integral_mono (by simpa only [pow_one] using φ.integrable_pow_mul volume 1)
          (integrable_kernelDecayWeight.const_mul _) weight
      _ = _ := by rw [integral_const_mul]; unfold W; ring
  have hA₀ : C ≤ A := by
    dsimp only [A]
    linarith [mul_nonneg (mul_nonneg hC₀ hC) hW, mul_nonneg hC₁ hC]
  have hA₁ : C₀ * C * W ≤ A := by
    dsimp only [A]
    linarith [mul_nonneg hC₁ hC]
  have hA₂ : C₁ * C ≤ A := by
    dsimp only [A]
    linarith [mul_nonneg (mul_nonneg hC₀ hC) hW]
  refine ⟨fun ξ => ?_, moment.trans (mul_le_mul_of_nonneg_right hA₁ hD), fun z => ?_⟩
  · have hξ := (bound 0 (by decide)).1 ξ
    rw [norm_iteratedFDeriv_zero] at hξ
    exact hξ.trans (mul_le_mul_of_nonneg_right hA₀ hD)
  · have hl := decay₁ a support (C * D) (mul_nonneg hC hD)
      (fun n hn => (bound n (hn.trans (by decide))).2) z
    rw [← invForm] at hl
    calc
      _ ≤ (1+‖z‖)^5 * ‖iteratedFDeriv ℝ 1 φ z‖ :=
        mul_le_mul_of_nonneg_left (fderiv_norm_le_iterated φ z) (by positivity)
      _ ≤ C₁ * (C * D) := hl
      _ = C₁ * C * D := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hA₂ hD

end Burnett.A02.FrequencySplit
