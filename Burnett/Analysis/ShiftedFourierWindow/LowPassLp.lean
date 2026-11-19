import Burnett.Analysis.ShiftedFourierWindow.LowPassFourier

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.ShiftedFourierWindow

open Burnett.Analysis.CenteredMaximal
open MeasureTheory Set
open scoped ENNReal FourierTransform

theorem shiftedWindow_continuous (a f : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s) (q : Space) :
    Continuous (shiftedWindowOperator a f s q) := by
  let φ := (SchwartzMap.fourierTransformCLE ℂ).symm a
  let H := fun (x y : Space) => ((s^4)⁻¹ • φ (s⁻¹ • (x-y)+q)) * f y
  have eq : shiftedWindowOperator a f s q = fun x => ∫ y, H x y :=
    funext (shifted_window_physical a f s hs q)
  rw [eq]
  let D := |(s^4)⁻¹| * SchwartzMap.seminorm ℝ 0 0 φ
  apply continuous_of_dominated (bound := fun y => D * ‖f y‖)
  · intro x
    exact (show Continuous (H x) by dsimp only [H]; fun_prop).aestronglyMeasurable
  · intro x
    filter_upwards with y
    dsimp only [H,D]
    rw [norm_mul,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ φ _) (abs_nonneg _)) (norm_nonneg _)
  · exact f.integrable.norm.const_mul D
  · filter_upwards with y
    dsimp only [H]
    fun_prop

/-- Supremum over every positive real dilation of the modulated Fourier window. -/
def maximalShiftedWindow (a f : SchwartzMap Space ℂ) (q x : Space) : ℝ≥0∞ :=
  ⨆ s : {s : ℝ // 0<s}, ‖shiftedWindowOperator a f s q x‖ₑ

theorem maximalShiftedWindow_measurable (a f : SchwartzMap Space ℂ) (q : Space) :
    Measurable (maximalShiftedWindow a f q) := by
  apply measurable_of_Ioi
  intro level
  have he : (maximalShiftedWindow a f q) ⁻¹' Ioi level =
      ⋃ s : {s : ℝ // 0<s}, {x | level < ‖shiftedWindowOperator a f s q x‖ₑ} := by
    ext x
    simp only [mem_preimage,mem_Ioi,maximalShiftedWindow,lt_iSup_iff,mem_iUnion,mem_setOf_eq]
  rw [he]
  exact (isOpen_iUnion fun s : {s : ℝ // 0<s} =>
    isOpen_lt continuous_const (shiftedWindow_continuous a f s s.2 q).enorm).measurableSet

/-- Low-frequency maximal estimate for the actual Fourier multiplier,
uniform in every dilation and with polynomial growth in its modulation. -/
theorem maximalShiftedWindow_Lp (a : SchwartzMap Space ℂ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (f : SchwartzMap Space ℂ) (q : Space) (p : ℝ), 1 < p →
      eLpNorm (maximalShiftedWindow a f q) (ENNReal.ofReal p) volume ≤
        (C * ENNReal.ofReal ((1+‖q‖)^5) * maximalConstant p ^ (1/p)) *
          eLpNorm (f : Space → ℂ) (ENNReal.ofReal p) volume := by
  let φ := (SchwartzMap.fourierTransformCLE ℂ).symm a
  obtain ⟨C,hC,h⟩ := shifted_schwartz_kernel_maximal φ
  refine ⟨C,hC,?_⟩
  intro f q p hp
  let g := fun y => ‖f y‖ₑ
  have hg : Measurable g := f.continuous.measurable.enorm
  let D := C * ENNReal.ofReal ((1+‖q‖)^5)
  have point (x : Space) : maximalShiftedWindow a f q x ≤ D * centeredMax g x := by
    refine iSup_le (fun s => ?_)
    rw [shifted_window_physical a f s s.2]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    apply le_trans _ (h g hg q x s s.2)
    apply lintegral_mono
    intro y
    change ‖((s.val^4)⁻¹ • φ (s.val⁻¹ • (x-y)+q)) * f y‖ₑ ≤ _
    rw [← ofReal_norm_eq_enorm,norm_mul,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (pow_pos s.2 _)),inv_mul_eq_div,ENNReal.ofReal_mul (by positivity)]
    simp [g]
  have hn := eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' (μ := (volume : Measure Space))
    (f := maximalShiftedWindow a f q) (g := centeredMax g) (c := D) (ENNReal.ofReal p)
    (centeredMax_measurable g).aestronglyMeasurable (Filter.Eventually.of_forall point)
  exact hn.trans ((mul_le_mul_left' (centeredMax_complex_Lp (f : Space → ℂ) f.continuous.measurable p hp) D).trans_eq
    (mul_assoc _ _ _).symm)

end Burnett.Analysis.ShiftedFourierWindow
