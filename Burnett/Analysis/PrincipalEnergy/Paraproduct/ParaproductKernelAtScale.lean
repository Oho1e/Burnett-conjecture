import Burnett.Analysis.PrincipalEnergy.Paraproduct.ActualParaproductResolution
import Burnett.Analysis.PrincipalEnergy.Paraproduct.ParaproductMassEstimates

set_option autoImplicit false
set_option maxHeartbeats 2700000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Function Filter

/-- Physical kernel of one double-window paraproduct scale. -/
def compactWaveletParaproductKernelAtScale (φ ψ θ : SchwartzMap Space ℂ) (s : ℝ)
    (b : Space → ℂ) (x y : Space) : ℂ :=
  ∫ z, compactWaveletKernel θ s (x-z)*
    (compactWaveletAction ψ s b z*compactWaveletKernel φ s (z-y))

private theorem scaled_window_continuous (φ : SchwartzMap Space ℂ) (s : ℝ) :
    Continuous (compactWaveletKernel φ s) :=
  continuous_const.smul (φ.continuous.comp (continuous_const.smul continuous_id))

theorem compactWaveletKernel_norm_le_scale (φ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s) (z : Space) :
    ‖compactWaveletKernel φ s z‖ ≤ (s^4)⁻¹*SchwartzMap.seminorm ℝ 0 0 φ := by
  rw [compactWaveletKernel,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hs.le _))]
  exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ φ _) (inv_nonneg.mpr (pow_nonneg hs.le _))

theorem compactWaveletKernel_zero_outside_scale (φ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z=0) (s : ℝ) (hs : 0<s) (z : Space) (hz : s<‖z‖) :
    compactWaveletKernel φ s z=0 := by
  have hNorm : 1<‖s⁻¹ • z‖ := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le),← div_eq_inv_mul]
    exact (lt_div_iff₀ hs).mpr (by simpa only [one_mul] using hz)
  rw [compactWaveletKernel,hφ _ hNorm,smul_zero]

theorem compactWaveletParaproductKernelAtScale_zero (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z=0) (hθ : ∀ z, 1<‖z‖ → θ z=0)
    (s : ℝ) (hs : 0<s) (b : Space → ℂ) (x y : Space) (hxy : 2*s < ‖x-y‖) :
    compactWaveletParaproductKernelAtScale φ ψ θ s b x y=0 := by
  unfold compactWaveletParaproductKernelAtScale
  apply integral_eq_zero_of_ae
  filter_upwards with z
  by_cases hz : s<‖x-z‖
  · rw [compactWaveletKernel_zero_outside_scale θ hθ s hs (x-z) hz,zero_mul,Pi.zero_apply]
  · have hTriangle := norm_add_le (x-z) (z-y)
    rw [show x-z+(z-y)=x-y by abel] at hTriangle
    have hz' : s<‖z-y‖ := by linarith [le_of_not_gt hz]
    rw [compactWaveletKernel_zero_outside_scale φ hφ s hs (z-y) hz',mul_zero,mul_zero,Pi.zero_apply]

/-- The one-scale physical kernel is of size $s^{-4}$ times the
uniform bound of the actual coefficient wavelet at that scale. -/
theorem compactWaveletParaproductKernelAtScale_size (φ ψ θ : SchwartzMap Space ℂ)
    (s : ℝ) (hs : 0<s) {b : Space → ℂ} {B : ℝ} (hB : 0≤B)
    (hQ : ∀ z, ‖compactWaveletAction ψ s b z‖≤B) (x y : Space) :
    ‖compactWaveletParaproductKernelAtScale φ ψ θ s b x y‖ ≤
      B*(SchwartzMap.seminorm ℝ 0 0 φ)*(∫ z, ‖θ z‖)*(s^4)⁻¹ := by
  let F (z : Space) := compactWaveletAction ψ s b z * compactWaveletKernel φ s (z-y)
  have hF (z : Space) : ‖F z‖≤B*((s^4)⁻¹*SchwartzMap.seminorm ℝ 0 0 φ) := by
    rw [show ‖F z‖ = ‖compactWaveletAction ψ s b z‖*‖compactWaveletKernel φ s (z-y)‖ from norm_mul _ _]
    exact mul_le_mul (hQ z) (compactWaveletKernel_norm_le_scale φ s hs _) (norm_nonneg _) hB
  exact (compactWaveletAction_norm_le_L1Mass_mul θ s hs hF x).trans_eq (by ring)

/-- Opening the nested physical paraproduct at one scale gives the actual
integral kernel on Schwartz inputs. -/
theorem compactWaveletParaproductAtScale_eq_integral_kernel (φ ψ θ : SchwartzMap Space ℂ)
    (s : ℝ) (hs : 0<s) {b : Space → ℂ} (hb : Integrable b volume)
    {B : ℝ} (hB : 0≤B) (hQ : ∀ z, ‖compactWaveletAction ψ s b z‖≤B)
    (f : SchwartzMap Space ℂ) (x : Space) :
    compactWaveletParaproductAtScale φ ψ θ s b f x =
      ∫ y, compactWaveletParaproductKernelAtScale φ ψ θ s b x y*f y := by
  let K := compactWaveletKernel θ s
  let P := compactWaveletKernel φ s
  let Q := compactWaveletAction ψ s b
  let C := (s^4)⁻¹*SchwartzMap.seminorm ℝ 0 0 φ
  let F (z y : Space) := (K (x-z)*(Q z*P (z-y)))*f y
  have hK : Integrable K (volume : Measure Space) := (θ.integrable.comp_smul (inv_ne_zero hs.ne')).smul _
  have hKx : Integrable (fun z => K (x-z)) volume :=
    ((volume : Measure Space).measurePreserving_sub_left x).integrable_comp_of_integrable hK
  have hQcont : Continuous Q := compactWaveletAction_continuous ψ s hs b hb
  have hKcont : Continuous K := scaled_window_continuous θ s
  have hPcont : Continuous P := scaled_window_continuous φ s
  have hCont : Continuous (uncurry F) :=
    ((hKcont.comp (continuous_const.sub continuous_fst)).mul
      ((hQcont.comp continuous_fst).mul (hPcont.comp (continuous_fst.sub continuous_snd)))).mul
      (f.continuous.comp continuous_snd)
  have hInt : Integrable (uncurry F) ((volume : Measure Space).prod volume) := by
    refine ((hKx.norm.mul_prod (f.integrable (μ := (volume : Measure Space))).norm).const_mul (B*C)).mono'
      hCont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    change ‖(K (x-p.1)*(Q p.1*P (p.1-p.2)))*f p.2‖ ≤
      (B*C)*(‖K (x-p.1)‖*‖f p.2‖)
    have hBound : ‖Q p.1‖*‖P (p.1-p.2)‖ ≤ B*C :=
      mul_le_mul (hQ p.1) (compactWaveletKernel_norm_le_scale φ s hs _) (norm_nonneg _) hB
    simp only [norm_mul]
    rw [show ‖K (x-p.1)‖*(‖Q p.1‖*‖P (p.1-p.2)‖)*‖f p.2‖ =
      (‖Q p.1‖*‖P (p.1-p.2)‖)*(‖K (x-p.1)‖*‖f p.2‖) by ring]
    exact mul_le_mul_of_nonneg_right hBound (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    _ = ∫ z, ∫ y, F z y := by
      change (∫ z, K (x-z)*(Q z*(∫ y, P (z-y)*f y))) = ∫ z, ∫ y, F z y
      apply congrArg (fun G : Space → ℂ => ∫ z, G z)
      funext z
      dsimp only [F]
      simp_rw [mul_assoc,integral_const_mul]
    _ = ∫ y, ∫ z, F z y := integral_integral_swap hInt
    _ = _ := by
      dsimp only [F,compactWaveletParaproductKernelAtScale,Q,K,P]
      simp_rw [integral_mul_const]

end Burnett.Analysis.CarlesonEmbedding
