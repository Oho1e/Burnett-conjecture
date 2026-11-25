import Burnett.Analysis.AllScaleTransfer.ActualRadialWindowSum
import Burnett.Analysis.AllScaleTransfer.ActualRadialWindowFourier

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.A05
open Burnett.Analysis.ShiftedFourierWindow

open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier (radianTrilinearForm)
open scoped ENNReal

/-- The actual trilinear Fourier forms of a fixed separated mode are
summable over arbitrary finite radial selections with a uniform bound.
The ratios can depend on the fixed radial gap and the third cutoff
remains on its true frequency in every summand. -/
theorem integer_radial_mode_trilinear_bound
    (a b d : SchwartzMap E ℂ) (ha : HasCompactSupport (a : E → ℂ))
    (hb : HasCompactSupport (b : E → ℂ)) (ca : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (cb : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (t u : ℝ), 0 < t → 0 < u → ∀ (q v : E) (n : ℕ) (j : Fin n ↪ ℤ)
      (sc : Fin n → ℝ), (∀ i, 0 < sc i) → ∀ (f g h : SchwartzMap E ℂ),
        ‖∑ i : Fin n, radianTrilinearForm
          (radianSeparatedWindowSymbol a b d ((2 : ℝ)^(-j i) * t) ((2 : ℝ)^(-j i) * u) (sc i) q v)
          f g h‖ₑ ≤
          C * ENNReal.ofReal (1 + ‖q‖) * ENNReal.ofReal (1 + ‖v‖) * triLpMass f g h 3 3 3 := by
  obtain ⟨C, hC, H⟩ := integer_radial_window_trilinear_bound a b d ha hb ca cb
  refine ⟨C, hC, ?_⟩
  intro t u ht hu q v n j sc hsc f g h
  have hEq (i : Fin n) :
      (∫ x, shiftedWindowOperator a f ((2 : ℝ)^(-j i) * t) q x *
        shiftedWindowOperator b g ((2 : ℝ)^(-j i) * u) v x * shiftedWindowOperator d h (sc i) 0 x) =
      radianTrilinearForm
        (radianSeparatedWindowSymbol a b d ((2 : ℝ)^(-j i) * t) ((2 : ℝ)^(-j i) * u) (sc i) q v) f g h :=
    shiftedWindowProduct_radianTrilinear a b d f g h _ _ (sc i) (hsc i) q v
  simpa only [hEq] using (H t u ht hu q v n j sc hsc f g h).2

end Burnett.A05
