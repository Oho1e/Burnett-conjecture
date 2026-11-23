import Burnett.Analysis.Microlocal.Overlap.BaseFourierAction

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.AngularDyadicKernel (E)
open scoped ComplexConjugate FourierTransform InnerProduct Topology

theorem bounded_leftAction_integrand_integrable (p : E → E → ℂ)
    (hp : Measurable (uncurry p)) (B : ℝ) (hB : ∀ x ξ, ‖p x ξ‖ ≤ B)
    (f : SchwartzMap E ℂ) (x : E) :
    Integrable (fun ξ => baseFourierPhase ξ x * (p x ξ * (𝓕 (f : E → ℂ)) ξ)) := by
  let F := SchwartzMap.fourierTransformCLE ℂ f
  have hI : Integrable (fun ξ => B * ‖F ξ‖) := F.integrable.norm.const_mul B
  have hM : Measurable (fun ξ => baseFourierPhase ξ x * (p x ξ * F ξ)) :=
    (baseFourierPhase_continuous_apply continuous_id continuous_const).measurable.mul
      ((hp.comp (measurable_const.prodMk measurable_id)).mul F.continuous.measurable)
  refine hI.mono' hM.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, baseFourierPhase_norm, one_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right (hB x ξ) (norm_nonneg _)

theorem firstOrderAction_integrand_eq (p : E → E → ℂ) (f : E → ℂ) (x : E) :
    firstOrderAction p f x = ∫ ξ, baseFourierPhase ξ x * (p x ξ * (𝓕 f) ξ) := by
  rw [firstOrderAction, Real.fourierIntegralInv_eq']
  rfl

/-- The actual bounded left action can be tested by any Schwartz function. -/
theorem integrable_tested_bounded_leftAction (p : E → E → ℂ)
    (hp : Measurable (uncurry p)) (B : ℝ) (hB : ∀ x ξ, ‖p x ξ‖ ≤ B)
    (f v : SchwartzMap E ℂ) :
    Integrable (fun x => conj (v x) * firstOrderAction p f x) := by
  let F := SchwartzMap.fourierTransformCLE ℂ f
  let G (q : E × E) := baseFourierPhase q.2 q.1 * (p q.1 q.2 * F q.2)
  have hG : StronglyMeasurable G :=
    ((baseFourierPhase_continuous.measurable.comp measurable_swap).mul
      (hp.mul (F.continuous.measurable.comp measurable_snd))).stronglyMeasurable
  have hM : Measurable (firstOrderAction p f) := by
    rw [show firstOrderAction p (f : E → ℂ) = fun x => ∫ ξ, G (x,ξ)
      from funext (firstOrderAction_integrand_eq p (f : E → ℂ))]
    exact (hG.integral_prod_right' (ν := (volume : Measure E))).measurable
  have hBound (x : E) : ‖firstOrderAction p f x‖ ≤ B * ∫ ξ, ‖F ξ‖ := by
    rw [firstOrderAction_integrand_eq]
    have hI : Integrable (fun ξ => B * ‖F ξ‖) := F.integrable.norm.const_mul B
    have h := norm_integral_le_of_norm_le hI
      (Eventually.of_forall fun ξ => show ‖G (x,ξ)‖ ≤ B * ‖F ξ‖ by
        change ‖baseFourierPhase ξ x * (p x ξ * F ξ)‖ ≤ B * ‖F ξ‖
        rw [norm_mul, baseFourierPhase_norm, one_mul, norm_mul]
        exact mul_le_mul_of_nonneg_right (hB x ξ) (norm_nonneg _))
    simpa only [integral_const_mul] using h
  apply (v.integrable.norm.mul_const (B * ∫ ξ, ‖F ξ‖)).mono'
    ((Complex.continuous_conj.measurable.comp v.continuous.measurable).mul hM).aestronglyMeasurable
  filter_upwards with x
  change ‖conj (v x) * firstOrderAction p f x‖ ≤ ‖v x‖ * (B * ∫ ξ, ‖F ξ‖)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_left (hBound x) (norm_nonneg _)

/-- A bounded L² test against an error with a strongly null L² representative
converges to zero as an actual spatial integral. -/
theorem tendsto_tested_strongZero (v : ℕ → E → ℂ) (V : ℕ → ComplexL2 E)
    (hv : ∀ n, V n =ᵐ[volume] v n) (B : ℝ) (hB : ∀ n, ‖V n‖ ≤ B)
    (r : ℕ → E → ℂ) (R : ℕ → ComplexL2 E) (hr : ∀ n, R n =ᵐ[volume] r n)
    (hlim : Tendsto R atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, conj (v n x) * r n x) atTop (𝓝 0) := by
  have hPair (n : ℕ) : (∫ x, conj (v n x) * r n x) = inner ℂ (V n) (R n) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv n, hr n] with x hx hy
    simp only [RCLike.inner_apply', hx, hy]
  simp_rw [hPair]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hN : Tendsto (fun n => B * ‖R n‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hlim.norm.const_mul B
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hN
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hB n) (norm_nonneg _))

theorem integrable_testedL2_representatives (v r : E → ℂ) (V R : ComplexL2 E)
    (hv : V =ᵐ[volume] v) (hr : R =ᵐ[volume] r) :
    Integrable (fun x => conj (v x) * r x) := by
  refine (L2.integrable_inner V R).congr ?_
  filter_upwards [hv, hr] with x hx hy
  simp only [RCLike.inner_apply', hx, hy]

end Burnett.Microlocal.Overlap
