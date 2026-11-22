import Burnett.Analysis.GaugeProjection.MatrixProjectionRealization
import Burnett.Analysis.GaugeProjection.CoefficientCutoff

set_option autoImplicit false
set_option maxHeartbeats 2700000

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter
open Burnett.A02.FrequencySplit (E)
open Burnett.Fourier
open scoped ContDiff NNReal Topology

private def linearWeight (w : SchwartzMap E ℂ) (x : E) : ℝ := ‖x‖ * ‖w x‖

private theorem linearWeight_nonneg (w : SchwartzMap E ℂ) (x : E) : 0 ≤ linearWeight w x :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

private theorem continuous_linearWeight (w : SchwartzMap E ℂ) : Continuous (linearWeight w) :=
  continuous_norm.mul w.continuous.norm

private theorem memLp_linearWeight (w : SchwartzMap E ℂ) : MemLp (linearWeight w) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (continuous_linearWeight w).aestronglyMeasurable).2
  let U := SchwartzMap.seminorm ℝ 1 0 w
  have hi : Integrable (linearWeight w) := by
    simpa only [linearWeight, pow_one] using w.integrable_pow_mul volume 1
  have hb (x : E) : linearWeight w x ≤ U := by
    simpa only [linearWeight, pow_one] using w.norm_pow_mul_le_seminorm ℝ 1 x
  refine (hi.const_mul U).mono' ((continuous_linearWeight w).norm.pow 2).aestronglyMeasurable ?_
  filter_upwards with x
  change ‖‖linearWeight w x‖ ^ 2‖ ≤ U * linearWeight w x
  rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (linearWeight_nonneg w x), pow_two]
  exact mul_le_mul_of_nonneg_right (hb x) (linearWeight_nonneg w x)

private theorem normalizedCoefficient_product_memLp (f : E → ℂ) (L : ℝ≥0)
    (hL : LipschitzWith L f) (w : SchwartzMap E ℂ) :
    MemLp (fun x => (f x - f 0) * w x) 2 volume := by
  refine (memLp_linearWeight w).of_le_mul (c := (L : ℝ))
    ((hL.continuous.sub continuous_const).mul w.continuous).aestronglyMeasurable ?_
  filter_upwards with x
  rw [norm_mul, Real.norm_of_nonneg (linearWeight_nonneg w x), linearWeight, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (by simpa only [sub_zero] using hL.norm_sub_le x 0) (norm_nonneg _)

/-- Actual normalized coefficient multiplication by a globally Lipschitz
coefficient on a Schwartz input. The normalization subtracts a constant. -/
def projectionNormalizedCoefficientProductL2 (f : E → ℂ) (L : ℝ≥0)
    (hL : LipschitzWith L f) (w : SchwartzMap E ℂ) : ComplexL2 E :=
  (normalizedCoefficient_product_memLp f L hL w).toLp (fun x => (f x - f 0) * w x)

/-- Actual multiplication on a Schwartz input by a possibly linearly growing
coefficient, represented in the physical \(L^2\) space. -/
def projectionLipschitzCoefficientProductL2 (f : E → ℂ) (L : ℝ≥0)
    (hL : LipschitzWith L f) (w : SchwartzMap E ℂ) : ComplexL2 E :=
  projectionNormalizedCoefficientProductL2 f L hL w + f 0 • w.toLp 2 volume

theorem projectionLipschitzCoefficientProductL2_ae (f : E → ℂ) (L : ℝ≥0)
    (hL : LipschitzWith L f) (w : SchwartzMap E ℂ) :
    (projectionLipschitzCoefficientProductL2 f L hL w : E → ℂ) =ᵐ[volume] fun x => f x * w x := by
  let g := projectionNormalizedCoefficientProductL2 f L hL w
  let u := w.toLp 2 volume
  have hg := (normalizedCoefficient_product_memLp f L hL w).coeFn_toLp
  change (g + f 0 • u : ComplexL2 E) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_add g (f 0 • u), Lp.coeFn_smul (f 0) u, hg, w.coeFn_toLp 2 volume]
    with x ha hb hx hw
  change g x = (f x - f 0) * w x at hx
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha hb
  change u x = w x at hw
  rw [ha, hb, hx, hw]
  ring

/-- The actual compact spatial cutoffs give strong \(L^2\) convergence after
multiplication by any fixed Schwartz field. -/
theorem projectionCoefficientCutoff_product_tendsto
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (L : ℝ≥0) (hL : LipschitzWith L f) (w : SchwartzMap E ℂ) :
    Tendsto (fun n => (hodgeProduct (projectionCoefficientCutoff f hf n) w).toLp 2 volume)
      atTop (𝓝 (projectionNormalizedCoefficientProductL2 f L hL w)) := by
  let g := projectionNormalizedCoefficientProductL2 f L hL w
  let fn := projectionCoefficientCutoff f hf
  let u (n : ℕ) := (hodgeProduct (fn n) w).toLp 2 volume
  let error (n : ℕ) (x : E) := (fn n x - (f x - f 0)) * w x
  have hnrm (n : ℕ) : ‖u n - g‖ ^ 2 = ∫ x, ‖error n x‖ ^ 2 := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u n) g, (hodgeProduct (fn n) w).coeFn_toLp 2 volume,
      (normalizedCoefficient_product_memLp f L hL w).coeFn_toLp] with x hs hn hg
    change u n x = _ at hn
    change g x = _ at hg
    rw [hs, Pi.sub_apply, hn, hg, hodgeProduct_apply, ← sub_mul]
  have hc (n : ℕ) : Continuous (error n) :=
    ((fn n).continuous.sub (hL.continuous.sub continuous_const)).mul w.continuous
  have hb (n : ℕ) (x : E) : ‖error n x‖ ≤ (2 * (L : ℝ)) * linearWeight w x := by
    unfold error linearWeight
    rw [norm_mul]
    have hv : ‖f x - f 0‖ ≤ (L : ℝ) * ‖x‖ := by simpa only [sub_zero] using hL.norm_sub_le x 0
    calc
      _ ≤ (‖fn n x‖ + ‖f x - f 0‖) * ‖w x‖ :=
        mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ ((L : ℝ) * ‖x‖ + (L : ℝ) * ‖x‖) * ‖w x‖ :=
        mul_le_mul_of_nonneg_right
          (add_le_add ((projectionCoefficientCutoff_norm_le f hf n x).trans hv) hv) (norm_nonneg _)
      _ = _ := by ring
  have hi : Integrable (fun x => (2 * (L : ℝ)) ^ 2 * ‖linearWeight w x‖ ^ 2) :=
    ((memLp_two_iff_integrable_sq_norm (continuous_linearWeight w).aestronglyMeasurable).1
      (memLp_linearWeight w)).const_mul _
  have hlim : Tendsto (fun n => ∫ x, ‖error n x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have ht := tendsto_integral_of_dominated_convergence (μ := (volume : Measure E))
      (F := fun n x => ‖error n x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun x => (2 * (L : ℝ)) ^ 2 * ‖linearWeight w x‖ ^ 2)
      (fun n => ((hc n).norm.pow 2).aestronglyMeasurable) hi (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · simpa only [integral_zero] using ht
    · change ‖‖error n x‖ ^ 2‖ ≤ (2 * (L : ℝ)) ^ 2 * ‖linearWeight w x‖ ^ 2
      rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (linearWeight_nonneg w x), ← mul_pow]
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (by positivity) (linearWeight_nonneg w x))).2 (hb n x)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [projectionCoefficientCutoff_eventually_eq f hf x] with n hn
      simp only [error, fn, hn, sub_self, zero_mul, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have hp : Tendsto (fun n => ‖u n - g‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hnrm] using hlim
  have hs : Tendsto (fun n => ‖u n - g‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hp.sqrt
  exact tendsto_sub_nhds_zero_iff.mp ((tendsto_zero_iff_norm_tendsto_zero).2 hs)

end Burnett.P01
