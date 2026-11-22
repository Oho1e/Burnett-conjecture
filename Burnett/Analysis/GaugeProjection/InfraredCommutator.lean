import Burnett.Analysis.GaugeProjection.InfraredConvolution
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.P01

open MeasureTheory
open Burnett.A02.FrequencySplit (E)
open Burnett.A07 (coordinateDerivative)
open scoped NNReal ContDiff

private abbrev direction (b : Fin 4) : E := EuclideanSpace.single b 1

/-- Actual differentiated commutator kernel of the fixed infrared factor.
The sign is for \(J=I-K*\) and \([J,f]=Jf-fJ\). -/
def projectionInfraredCommutatorKernel (b : Fin 4) (f : E → ℂ) (x y : E) : ℂ :=
  coordinateDerivative b projectionLowKernel (x - y) * (f x - f y) +
    projectionLowKernel (x - y) * fderiv ℝ f y (direction b)

theorem projectionInfraredCommutatorKernel_continuous (b : Fin 4) (f : E → ℂ)
    (hf : ContDiff ℝ 1 f) :
    Continuous (Function.uncurry (projectionInfraredCommutatorKernel b f)) := by
  have hf' : Continuous fun y => fderiv ℝ f y (direction b) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hK := projectionLowKernel.continuous
  have hDK := (coordinateDerivative b projectionLowKernel).continuous
  have hc := hf.continuous
  unfold Function.uncurry projectionInfraredCommutatorKernel
  fun_prop

theorem norm_projectionInfraredCommutatorKernel_le (b : Fin 4) (f : E → ℂ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (x y : E) :
    ‖projectionInfraredCommutatorKernel b f x y‖ ≤ (L : ℝ) * projectionLowMoment b (x - y) := by
  have hd : ‖fderiv ℝ f y (direction b)‖ ≤ (L : ℝ) := by
    have h := (fderiv ℝ f y).le_opNorm (direction b)
    rw [show ‖direction b‖ = 1 by simp [direction, EuclideanSpace.norm_single], mul_one] at h
    exact h.trans (norm_fderiv_le_of_lipschitz ℝ hf)
  have hc : ‖f x - f y‖ ≤ (L : ℝ) * ‖x - y‖ := hf.norm_sub_le x y
  unfold projectionInfraredCommutatorKernel projectionLowMoment
  calc
    _ ≤ ‖coordinateDerivative b projectionLowKernel (x - y) * (f x - f y)‖ +
        ‖projectionLowKernel (x - y) * fderiv ℝ f y (direction b)‖ := norm_add_le _ _
    _ ≤ ‖coordinateDerivative b projectionLowKernel (x - y)‖ * ((L : ℝ) * ‖x - y‖) +
        ‖projectionLowKernel (x - y)‖ * (L : ℝ) := by
      simp only [norm_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hc (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
    _ = _ := by ring

private theorem integrable_mul_schwartz {g : E → ℂ} (hg : Integrable g)
    (u : SchwartzMap E ℂ) : Integrable (fun y => g y * u y) := by
  have h := hg.bdd_mul u.continuous.aestronglyMeasurable
    ⟨SchwartzMap.seminorm ℝ 0 0 u, u.norm_le_seminorm ℝ⟩
  simpa only [mul_comm] using h

private theorem sourceDerivative_projectionLowKernel (x y : E) :
    HasFDerivAt (fun z => projectionLowKernel (x - z))
      (-fderiv ℝ (projectionLowKernel : E → ℂ) (x - y)) y := by
  have hy : HasFDerivAt (fun z => x - z) (-(ContinuousLinearMap.id ℝ E)) y := by
    simpa only [zero_sub] using
      (hasFDerivAt_const (𝕜 := ℝ) x y).sub (hasFDerivAt_id (𝕜 := ℝ) y)
  have h := (projectionLowKernel.differentiableAt (x := x - y)).hasFDerivAt.comp y hy
  convert h using 1
  ext z
  simp

/-- One genuine integration by parts for the fixed infrared action.
The coefficient may grow linearly, and its higher derivatives are unused. -/
theorem projectionInfraredKernelAction_commutator_derivative (b : Fin 4) (f : E → ℂ)
    (L : ℝ≥0) (hf : ContDiff ℝ 1 f) (hL : LipschitzWith L f)
    (w : SchwartzMap E ℂ) (x : E) :
    projectionInfraredKernelAction (fun y => f y * coordinateDerivative b w y) x -
      f x * projectionInfraredKernelAction (coordinateDerivative b w) x =
    ∫ y, projectionInfraredCommutatorKernel b f x y * w y := by
  let K := projectionLowKernel
  let v := coordinateDerivative b w
  let H : E → ℂ := fun y => K (x - y) * (f x - f y)
  let C := projectionInfraredCommutatorKernel b f x
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hHdiff : Differentiable ℝ H := by
    have hk := K.differentiable
    unfold H
    fun_prop
  have hC : Continuous C :=
    (projectionInfraredCommutatorKernel_continuous b f hf).comp (continuous_const.prodMk continuous_id)
  have hHc := hHdiff.continuous
  have hD (y : E) : fderiv ℝ H y (direction b) = -C y := by
    have hz := (hasFDerivAt_const (𝕜 := ℝ) (f x) y).sub (hfd y).hasFDerivAt
    have hkc := sourceDerivative_projectionLowKernel x y
    have ht := hkc.fun_mul hz
    change HasFDerivAt H _ y at ht
    rw [ht.fderiv]
    simp only [zero_sub, Pi.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, smul_eq_mul]
    dsimp only [C, projectionInfraredCommutatorKernel, coordinateDerivative, SchwartzMap.pderivCLM_apply]
    ring
  let mp := (volume : Measure E).measurePreserving_sub_left x
  have hI : Integrable H := by
    let weight : E → ℝ := fun z => ‖z‖ * ‖K z‖
    have hi : Integrable weight := by
      simpa only [weight, pow_one] using K.integrable_pow_mul volume 1
    have hb := (mp.integrable_comp_of_integrable hi).const_mul (L : ℝ)
    refine hb.mono' hHc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    change ‖K (x - y) * (f x - f y)‖ ≤ (L : ℝ) * (‖x - y‖ * ‖K (x - y)‖)
    rw [norm_mul]
    calc
      _ ≤ ‖K (x - y)‖ * ((L : ℝ) * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (hL.norm_sub_le x y) (norm_nonneg _)
      _ = _ := by ring
  have hCI : Integrable C := by
    have hb := (mp.integrable_comp_of_integrable (projectionLowMoment_integrable b)).const_mul (L : ℝ)
    exact hb.mono' hC.aestronglyMeasurable (Filter.Eventually.of_forall
      (norm_projectionInfraredCommutatorKernel_le b f L hL x))
  have hKV : Integrable (fun y => K (x - y) * v y) :=
    integrable_mul_schwartz (mp.integrable_comp_of_integrable K.integrable) v
  have hHV : Integrable (fun y => H y * v y) := integrable_mul_schwartz hI v
  have q (y : E) : K (x - y) * (f y * v y) = f x * (K (x - y) * v y) - H y * v y := by
    unfold H
    ring
  calc
    _ = ∫ y, H y * v y := by
      unfold projectionInfraredKernelAction
      change f x * v x - (∫ y, K (x - y) * (f y * v y)) -
        f x * (v x - ∫ y, K (x - y) * v y) = _
      simp_rw [q]
      rw [integral_sub (hKV.const_mul (f x)) hHV, integral_const_mul]
      ring
    _ = _ := by
      have hi : Integrable (fun y => fderiv ℝ H y (direction b) * w y) := by
        simp_rw [hD, neg_mul]
        exact (integrable_mul_schwartz hCI w).neg
      have ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := volume) hi hHV (integrable_mul_schwartz hI w) hHdiff w.differentiable
      simp_rw [hD, neg_mul, integral_neg, neg_neg] at ibp
      exact ibp

end Burnett.P01
