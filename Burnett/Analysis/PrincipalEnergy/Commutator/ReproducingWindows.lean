import Burnett.Analysis.PrincipalEnergy.Commutator.WaveletOperator
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 2100000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Metric Set Filter
open Burnett.Microlocal.AngularDyadicKernel
  (inverseFourier_dilation inverseFourier_mul_fourier_eq_convolution)
open scoped FourierTransform ContDiff BigOperators Topology

private def normalizedHalfBump : SchwartzMap Space ℂ := by
  let χ : ContDiffBump (0 : Space) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  let h := (χ.hasCompactSupport_normed (μ := (volume : Measure Space))).comp_left Complex.ofReal_zero
  exact h.toSchwartzMap (Complex.ofRealCLM.contDiff.comp χ.contDiff_normed)

private theorem normalizedHalfBump_integral : (∫ x, normalizedHalfBump x) = 1 := by
  let χ : ContDiffBump (0 : Space) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  change (∫ x, (χ.normed volume x : ℂ)) = 1
  rw [integral_complex_ofReal,χ.integral_normed,Complex.ofReal_one]

private theorem normalizedHalfBump_outside (x : Space) (hx : 1/2<‖x‖) : normalizedHalfBump x = 0 := by
  let χ : ContDiffBump (0 : Space) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  have h : x ∉ Function.support (χ.normed volume) := by
    rw [χ.support_normed_eq (μ := (volume : Measure Space)),mem_ball,dist_zero_right]
    exact not_lt.mpr hx.le
  change (χ.normed volume x : ℂ) = 0
  rw [Function.notMem_support.mp h,Complex.ofReal_zero]

private theorem wavelet_frequency_zero (f : SchwartzMap Space ℂ) :
    compactWaveletFrequency f 0 = ∫ x, f x := by
  change 𝓕 (f : Space → ℂ) 0 = _
  simp [Real.fourierIntegral_eq]

private def rescaledFrequency (f : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearEquiv.smulOfNeZero (K := ℝ) (M := Space) (1/2) (by norm_num)).toContinuousLinearEquiv)
    (compactWaveletFrequency f)

private def smallerBump (f : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  (SchwartzMap.fourierTransformCLE ℂ).symm (rescaledFrequency f)

private theorem smallerBump_fourier (f : SchwartzMap Space ℂ) (ξ : Space) :
    compactWaveletFrequency (smallerBump f) ξ = compactWaveletFrequency f ((1/2:ℝ) • ξ) :=
  congrArg (fun a : SchwartzMap Space ℂ => a ξ)
    ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply (rescaledFrequency f))

private theorem smallerBump_apply (f : SchwartzMap Space ℂ) (x : Space) :
    smallerBump f x = (2:ℝ)^4 • f ((2:ℝ) • x) := by
  have hRec : 𝓕⁻ (compactWaveletFrequency f : Space → ℂ) = (f : Space → ℂ) :=
    f.continuous.fourier_inversion f.integrable (compactWaveletFrequency f).integrable
  have hF : (smallerBump f : Space → ℂ) = 𝓕⁻ (rescaledFrequency f : Space → ℂ) :=
    SchwartzMap.fourierTransformCLE_symm_apply _ _
  rw [show smallerBump f x = 𝓕⁻ (rescaledFrequency f : Space → ℂ) x from congrFun hF x]
  change 𝓕⁻ (fun ξ => compactWaveletFrequency f ((1/2:ℝ) • ξ)) x = _
  simpa only [show (2:ℝ)⁻¹=1/2 by norm_num,hRec] using
    inverseFourier_dilation 2 (by norm_num) (compactWaveletFrequency f : Space → ℂ) x

private theorem smallerBump_outside (x : Space) (hx : 1/4<‖x‖) :
    smallerBump normalizedHalfBump x = 0 := by
  rw [smallerBump_apply,normalizedHalfBump_outside _ (by
    rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
    linarith),smul_zero]

private def fourierProduct (f g : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
    (compactWaveletFrequency g).hasTemperateGrowth (compactWaveletFrequency f)

private def convolutionSchwartz (f g : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  (SchwartzMap.fourierTransformCLE ℂ).symm (fourierProduct f g)

private theorem convolutionSchwartz_fourier (f g : SchwartzMap Space ℂ) (ξ : Space) :
    compactWaveletFrequency (convolutionSchwartz f g) ξ =
      compactWaveletFrequency f ξ * compactWaveletFrequency g ξ :=
  congrArg (fun a : SchwartzMap Space ℂ => a ξ)
    ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply (fourierProduct f g))

private theorem convolutionSchwartz_apply (f g : SchwartzMap Space ℂ) (x : Space) :
    convolutionSchwartz f g x = ∫ y, f (x-y)*g y := by
  have hF : (convolutionSchwartz f g : Space → ℂ) =
      𝓕⁻ (fourierProduct f g : Space → ℂ) := SchwartzMap.fourierTransformCLE_symm_apply _ _
  have hRec : 𝓕⁻ (compactWaveletFrequency f : Space → ℂ) = (f : Space → ℂ) :=
    f.continuous.fourier_inversion f.integrable (compactWaveletFrequency f).integrable
  rw [show convolutionSchwartz f g x = 𝓕⁻ (fourierProduct f g : Space → ℂ) x from congrFun hF x]
  change 𝓕⁻ (fun ξ => compactWaveletFrequency f ξ * 𝓕 (g : Space → ℂ) ξ) x = _
  rw [inverseFourier_mul_fourier_eq_convolution (compactWaveletFrequency f : Space → ℂ)
    g (compactWaveletFrequency f).integrable g.integrable,hRec]

private theorem convolutionSchwartz_outside (f g : SchwartzMap Space ℂ) (r s : ℝ)
    (hf : ∀ z, r<‖z‖ → f z = 0) (hg : ∀ z, s<‖z‖ → g z = 0) (x : Space) (hx : r+s<‖x‖) :
    convolutionSchwartz f g x = 0 := by
  rw [convolutionSchwartz_apply]
  have h (y : Space) : f (x-y)*g y = 0 := by
    by_cases hy : s<‖y‖
    · rw [hg y hy,mul_zero]
    · have ht := norm_add_le (x-y) y
      rw [sub_add_cancel] at ht
      rw [hf (x-y) (by linarith [not_lt.mp hy]),zero_mul]
  simp only [h,integral_zero]

def waveletCubic (z : ℂ) : ℂ := 3*z^2-2*z^3

/-- Two actual unit-ball Schwartz windows with zero mean factor the exact
telescoping frequency difference of the same normalized compact bump. -/
theorem exists_compact_reproducing_windows :
    ∃ φ ψ θ : SchwartzMap Space ℂ,
      (∫ x, φ x) = 1 ∧ (∀ x, 1/2<‖x‖ → φ x = 0) ∧
      (∫ x, ψ x) = 0 ∧ (∀ x, 1<‖x‖ → ψ x = 0) ∧
      (∫ x, θ x) = 0 ∧ (∀ x, 1<‖x‖ → θ x = 0) ∧
      ∀ ξ : Space, compactWaveletFrequency ψ ξ * compactWaveletFrequency θ ξ =
        waveletCubic (compactWaveletFrequency φ ((1/2:ℝ) • ξ)) -
          waveletCubic (compactWaveletFrequency φ ξ) := by
  let φ := normalizedHalfBump
  let φ' := smallerBump φ
  let u := convolutionSchwartz φ' φ'
  let v := convolutionSchwartz φ' φ
  let w := convolutionSchwartz φ φ
  let ψ := φ'-φ
  let θ := (3:ℂ) • (φ'+φ) - (2:ℂ) • (u+v+w)
  have hψ (ξ : Space) : compactWaveletFrequency ψ ξ =
      compactWaveletFrequency φ ((1/2:ℝ) • ξ)-compactWaveletFrequency φ ξ := by
    change SchwartzMap.fourierTransformCLM ℂ (φ'-φ) ξ = _
    rw [map_sub,SchwartzMap.sub_apply]
    exact congrArg (fun z : ℂ => z-compactWaveletFrequency φ ξ) (smallerBump_fourier φ ξ)
  have hθ (ξ : Space) : compactWaveletFrequency θ ξ =
      3*(compactWaveletFrequency φ ((1/2:ℝ) • ξ)+compactWaveletFrequency φ ξ) -
        2*((compactWaveletFrequency φ ((1/2:ℝ) • ξ))^2 +
          compactWaveletFrequency φ ((1/2:ℝ) • ξ)*compactWaveletFrequency φ ξ +
            (compactWaveletFrequency φ ξ)^2) := by
    change SchwartzMap.fourierTransformCLM ℂ ((3:ℂ) • (φ'+φ)-(2:ℂ) • (u+v+w)) ξ = _
    simp only [map_sub,map_smul,map_add,SchwartzMap.sub_apply,SchwartzMap.smul_apply,
      SchwartzMap.add_apply,smul_eq_mul]
    change 3*(compactWaveletFrequency φ' ξ+compactWaveletFrequency φ ξ) -
      2*(compactWaveletFrequency u ξ + compactWaveletFrequency v ξ + compactWaveletFrequency w ξ) = _
    dsimp only [φ',u,v,w]
    simp only [convolutionSchwartz_fourier,smallerBump_fourier,pow_two]
  have h0 : compactWaveletFrequency φ 0 = 1 := (wavelet_frequency_zero φ).trans normalizedHalfBump_integral
  refine ⟨φ,ψ,θ,normalizedHalfBump_integral,normalizedHalfBump_outside,?_,?_,?_,?_,?_⟩
  · rw [← wavelet_frequency_zero,hψ,smul_zero,sub_self]
  · intro x hx
    change φ' x-φ x = 0
    rw [smallerBump_outside _ (by linarith),normalizedHalfBump_outside _ (by linarith),sub_zero]
  · rw [← wavelet_frequency_zero,hθ,smul_zero,h0]
    norm_num
  · intro x hx
    have hp : φ x = 0 := normalizedHalfBump_outside _ (by linarith)
    have hq : φ' x = 0 := smallerBump_outside _ (by linarith)
    have hu : u x = 0 := convolutionSchwartz_outside φ' φ' (1/4) (1/4) smallerBump_outside
      smallerBump_outside x (by linarith)
    have hv : v x = 0 := convolutionSchwartz_outside φ' φ (1/4) (1/2) smallerBump_outside
      normalizedHalfBump_outside x (by linarith)
    have hw : w x = 0 := convolutionSchwartz_outside φ φ (1/2) (1/2) normalizedHalfBump_outside
      normalizedHalfBump_outside x (by linarith)
    change 3*(φ' x+φ x)-2*(u x+v x+w x) = 0
    rw [hp,hq,hu,hv,hw]
    simp
  · intro ξ
    rw [hψ,hθ]
    unfold waveletCubic
    ring

end Burnett.Analysis.CarlesonEmbedding
