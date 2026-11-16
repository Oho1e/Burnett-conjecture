import Mathlib.Analysis.Fourier.FourierTransform

noncomputable section

namespace Burnett.Fourier

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Modulation matched to mathlib's `exp(-2πi⟪x,ξ⟫)` convention. -/
def modulate (k : V) (f : V → ℂ) (x : V) : ℂ :=
  Real.fourierChar ⟪x, k⟫ • f x

theorem fourier_modulate (k : V) (f : V → ℂ) (ξ : V) :
    𝓕 (modulate k f) ξ = 𝓕 f (ξ - k) := by
  simp only [Real.fourierIntegral_eq, modulate, Circle.smul_def, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [← mul_assoc, ← Circle.coe_mul, ← Real.fourierChar.map_add_eq_mul]
  have hphase : -⟪x, ξ⟫ + ⟪x, k⟫ = -⟪x, ξ - k⟫ := by
    rw [inner_sub_right]
    ring
  rw [hphase]

end Burnett.Fourier
