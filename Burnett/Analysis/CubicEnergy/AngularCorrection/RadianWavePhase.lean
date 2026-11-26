import Burnett.Analysis.CubicEnergy.HighSlotCommutator.RadianHighDerivativeCommutator

set_option autoImplicit false
set_option maxHeartbeats 3300000

noncomputable section

namespace Burnett.A08

open MeasureTheory
open Burnett.A02.FrequencySplit (E Joint radianFourier radianFourier_scaled tau)
open Burnett.A06 (radianHighPair radianHighPairWeight)
open Burnett.A07 (coordinateDerivative radianFourier_coordinateDerivative
  integrable_radianHighPairWeight_of_orderOne)
open scoped BigOperators ComplexConjugate FourierTransform

/-- The manuscript's constant-coefficient principal polynomial. -/
def waveQuadratic (m : Fin 4 → Fin 4 → ℝ) (ξ : E) : ℝ :=
  ∑ a, ∑ b, m a b * ξ a * ξ b

/-- The operator `P₀ = -mᵃᵇ∂ₐ∂ᵦ` on genuine Schwartz fields. -/
def constantWave (m : Fin 4 → Fin 4 → ℝ) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  -(∑ a, ∑ b, (m a b : ℂ) • coordinateDerivative a (coordinateDerivative b f))

private def radianEvaluation (ξ : E) : SchwartzMap E ℂ →ₗ[ℂ] ℂ where
  toFun f := (SchwartzMap.fourierTransformCLM ℂ f) (tau⁻¹ • ξ)
  map_add' f g := by simp
  map_smul' a f := by simp

private theorem radianEvaluation_apply (ξ : E) (f : SchwartzMap E ℂ) :
    radianEvaluation ξ f = radianFourier f ξ := by
  change 𝓕 (f : E → ℂ) (tau⁻¹ • ξ) = radianFourier f ξ
  have ht : tau ≠ 0 := (mul_pos (show (0 : ℝ) < 2 by norm_num) Real.pi_pos).ne'
  rw [← radianFourier_scaled, smul_smul, mul_inv_cancel₀ ht, one_smul]

theorem radianFourier_constantWave (m : Fin 4 → Fin 4 → ℝ)
    (f : SchwartzMap E ℂ) (ξ : E) :
    radianFourier (constantWave m f) ξ = (waveQuadratic m ξ : ℂ) * radianFourier f ξ := by
  rw [← radianEvaluation_apply]
  unfold constantWave waveQuadratic
  simp only [map_neg, map_sum, map_smul, smul_eq_mul, radianEvaluation_apply,
    radianFourier_coordinateDerivative, Complex.ofReal_sum, Complex.ofReal_mul]
  simp only [Finset.sum_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = -((m a b : ℂ) * (ξ a : ℂ) * (ξ b : ℂ) * radianFourier f ξ *
        (Complex.I * Complex.I)) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

/-- The exact signed shift polynomial in the tested commutator with `P₀`. -/
theorem radianHighPair_constantWave_commutator
    (m : Fin 4 → Fin 4 → ℝ) (b : Joint → ℂ) (hb : Measurable b)
    (B : ℝ) (hB : 0 ≤ B) (bound : ∀ p : Joint, ‖b p‖ ≤ B * (1 + ‖p.1‖ + ‖p.2‖))
    (f u w : SchwartzMap E ℂ) :
    radianHighPair b f u (constantWave m w) - radianHighPair b f (constantWave m u) w =
      radianHighPair
        (fun p => ((waveQuadratic m (p.2 + p.1) - waveQuadratic m p.2 : ℝ) : ℂ) * b p)
        f u w := by
  have first := integrable_radianHighPairWeight_of_orderOne b hb B hB bound f u (constantWave m w)
  have second := integrable_radianHighPairWeight_of_orderOne b hb B hB bound f (constantWave m u) w
  have weights (p : Joint) :
      radianHighPairWeight b f u (constantWave m w) p -
        radianHighPairWeight b f (constantWave m u) w p =
      radianHighPairWeight
        (fun q => ((waveQuadratic m (q.2 + q.1) - waveQuadratic m q.2 : ℝ) : ℂ) * b q) f u w p := by
    simp only [radianHighPairWeight, radianFourier_constantWave, map_mul, Complex.conj_ofReal,
      Complex.ofReal_sub]
    ring
  unfold radianHighPair
  rw [← smul_sub, ← integral_sub first second]
  exact congrArg _ (integral_congr_ae (Filter.Eventually.of_forall weights))

end Burnett.A08
