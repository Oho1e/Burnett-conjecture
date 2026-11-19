import Burnett.Analysis.ShiftedFourierWindow.SchwartzMaximal

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.ShiftedFourierWindow

open Burnett.Analysis.CenteredMaximal
open MeasureTheory
open scoped ENNReal FourierTransform RealInnerProductSpace

private def kernelPhase (t : ℝ) : ℂ := Complex.exp ((↑(2*Real.pi*t) : ℂ)*Complex.I)
private theorem kernelPhase_norm (t : ℝ) : ‖kernelPhase t‖ = 1 := by simp [kernelPhase,Complex.norm_exp]
private theorem kernelPhase_add (a b : ℝ) : kernelPhase (a+b) = kernelPhase a * kernelPhase b := by
  unfold kernelPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The multiplier is the dilated reference window with its Fourier-series
modulation at that same scale, using the unitary 2π Fourier convention. -/
def shiftedWindowOperator (a f : SchwartzMap Space ℂ) (s : ℝ) (q x : Space) : ℂ :=
  ∫ ξ : Space, (kernelPhase (inner ℝ ξ x) * kernelPhase (inner ℝ (s • ξ) q) * a (s • ξ)) *
    𝓕 (f : Space → ℂ) ξ

private theorem scaled_window_kernel (a : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s) (u q : Space) :
    (s^4)⁻¹ • ((SchwartzMap.fourierTransformCLE ℂ).symm a) (s⁻¹ • u + q) =
    ∫ ξ : Space, kernelPhase (inner ℝ ξ u) * kernelPhase (inner ℝ (s • ξ) q) * a (s • ξ) := by
  let z := s⁻¹ • u + q
  let F := fun η : Space => kernelPhase (inner ℝ η z) * a η
  have inv : (∫ η, F η) = ((SchwartzMap.fourierTransformCLE ℂ).symm a) z := by
    have hv : ((SchwartzMap.fourierTransformCLE ℂ).symm a : Space → ℂ) = 𝓕⁻ (a : Space → ℂ) :=
      SchwartzMap.fourierTransformCLE_symm_apply _ _
    simp only [hv,Real.fourierIntegralInv_eq',smul_eq_mul,kernelPhase,F]
  have sc := Measure.integral_comp_smul_of_nonneg volume F s (hR := hs.le)
  rw [show Module.finrank ℝ Space = 4 from finrank_euclideanSpace_fin, inv] at sc
  change (s^4)⁻¹ • ((SchwartzMap.fourierTransformCLE ℂ).symm a) z = _
  rw [← sc]
  apply integral_congr_ae
  filter_upwards with ξ
  dsimp only [F,z]
  rw [inner_add_right,real_inner_smul_right,real_inner_smul_left,← mul_assoc,inv_mul_cancel₀ hs.ne',one_mul,kernelPhase_add]

theorem shifted_window_physical (a f : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s) (q x : Space) :
    shiftedWindowOperator a f s q x =
    ∫ y : Space, ((s^4)⁻¹ • ((SchwartzMap.fourierTransformCLE ℂ).symm a) (s⁻¹ • (x-y)+q)) * f y := by
  let A := fun ξ : Space => kernelPhase (inner ℝ ξ x) * kernelPhase (inner ℝ (s • ξ) q) * a (s • ξ)
  let T := fun (y ξ : Space) => A ξ * (kernelPhase (-inner ℝ y ξ) * f y)
  have hc : Continuous (Function.uncurry T) := by
    change Continuous (fun p : Space × Space => kernelPhase (inner ℝ p.2 x) * kernelPhase (inner ℝ (s • p.2) q) *
      a (s • p.2) * (kernelPhase (-inner ℝ p.1 p.2) * f p.1))
    unfold kernelPhase
    fun_prop
  have hi : Integrable (Function.uncurry T) ((volume : Measure Space).prod volume) := by
    refine (f.integrable.norm.mul_prod (a.integrable.comp_smul hs.ne').norm).mono' hc.aestronglyMeasurable ?_
    filter_upwards with p
    rcases p with ⟨y,ξ⟩
    simp only [Function.uncurry_apply_pair,T,A,norm_mul,kernelPhase_norm,one_mul]
    exact le_of_eq (mul_comm _ _)
  have freq (ξ : Space) : A ξ * 𝓕 (f : Space → ℂ) ξ = ∫ y, T y ξ := by
    rw [Real.fourierIntegral_eq',← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    simp only [T,kernelPhase,smul_eq_mul,mul_neg,neg_mul]
  have phys (y : Space) : ((s^4)⁻¹ • ((SchwartzMap.fourierTransformCLE ℂ).symm a) (s⁻¹ • (x-y)+q)) * f y =
      ∫ ξ, T y ξ := by
    rw [scaled_window_kernel a s hs,← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with ξ
    rw [inner_sub_right,real_inner_comm y ξ,sub_eq_add_neg,kernelPhase_add]
    dsimp only [T,A]
    ring
  change (∫ ξ, A ξ * 𝓕 (f : Space → ℂ) ξ) = _
  simp_rw [freq,phys]
  exact (integral_integral_swap hi).symm

end Burnett.Analysis.ShiftedFourierWindow
