import Burnett.Analysis.SignedFourierWindow.SignSquareIntegral
import Burnett.Analysis.SignedFourierWindow.SignWindowSum
import Burnett.Analysis.SignedFourierWindow.SignedWindowAllLp

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Finset
open scoped ENNReal

private theorem power_norm (f : Space → ℂ) (p : ℝ) (hp : 0<p) :
    (eLpNorm f (ENNReal.ofReal p) volume)^p = ∫⁻ x, ‖f x‖ₑ^p := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le,← ENNReal.rpow_mul,one_div_mul_cancel hp.ne',ENNReal.rpow_one]

/-- Littlewood–Paley upper square inequality for the concrete scaled and modulated
window. The finite family consists of any distinct dyadic scales. -/
theorem annular_square_all_Lp (a : SchwartzMap Space ℂ) (ha : HasCompactSupport (a : Space → ℂ))
    (cut : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) (p : ℝ) (hp : 1<p) :
    ∃ V : ℝ≥0∞, V < ⊤ ∧ ∀ (t : ℝ), 0<t → ∀ (q : Space) (n : ℕ) (e : Fin n ↪ ℕ)
      (f : Space → ℂ), MemLp f (ENNReal.ofReal p) volume →
      eLpNorm (annularSquare e a t q f) (ENNReal.ofReal p) volume ≤
        (V * ENNReal.ofReal (1+‖q‖))*eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C,hfin,operator⟩ := signed_window_all_Lp a ha cut p hp
  let H := ENNReal.ofReal (24*2^p)
  have hp0 : 0<p := by linarith
  have hi : 0≤1/p := (one_div_pos.mpr hp0).le
  refine ⟨H^(1/p)*C,ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hi ENNReal.ofReal_ne_top) hfin,?_⟩
  intro t ht q n e f hf
  let v := fun (i : Fin n) => kernelApply (annularKernel a t q (e i)) f
  let J := ENNReal.ofReal (1+‖q‖)
  let N := eLpNorm f (ENNReal.ofReal p) volume
  have meas (i : Fin n) : Measurable (v i) := by
    apply kernelApply_measurable_ae _ _ _ hf.1
    unfold annularKernel shiftedSpatialKernel
    fun_prop
  have signed (s : Fin n → Bool) : (∫⁻ x, ‖signedVector (fun i => v i x) s‖ₑ^p) ≤ ((C*J)*N)^p := by
    obtain ⟨c,hc,eq⟩ := window_sign_expansion e s a t ht q p hp.le f hf
    let K := finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) t q (univ.map e) c
    have he (x : Space) : signedVector (fun i => v i x) s = kernelApply K f x := eq x
    simp_rw [he]
    rw [← power_norm (kernelApply K f) p hp0]
    exact ENNReal.rpow_le_rpow (operator t ht q _ c hc f hf) hp0.le
  have h := square_integral_from_signs v meas p hp0 _ signed
  have he (x : Space) : ENNReal.ofReal ((Real.sqrt (vectorEnergy (fun i => v i x)))^p) =
      ‖annularSquare e a t q f x‖ₑ^p := by
    dsimp only [annularSquare,v]
    rw [← ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) hp0.le,← ofReal_norm_eq_enorm,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  simp_rw [he] at h
  rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  have h' := ENNReal.rpow_le_rpow h hi
  rw [ENNReal.mul_rpow_of_nonneg _ _ hi,← ENNReal.rpow_mul,mul_one_div_cancel hp0.ne',ENNReal.rpow_one] at h'
  exact h'.trans_eq (by dsimp only [H,J,N]; ac_rfl)

/-- For Schwartz input the square uses precisely the original modulated Fourier
window at each scale. -/
theorem annular_square_fourier {n : ℕ} (e : Fin n ↪ ℕ) (a f : SchwartzMap Space ℂ)
    (t : ℝ) (ht : 0<t) (q x : Space) :
    annularSquare e a t q f x =
      Real.sqrt (∑ i, ‖shiftedWindowOperator a f ((2:ℝ)^e i*t) q x‖^2) := by
  unfold annularSquare vectorEnergy
  congr 1
  apply sum_congr rfl
  intro i _
  rw [shifted_window_physical a f _ (mul_pos (by positivity) ht)]
  rfl

end Burnett.Analysis.SignedFourierWindow
