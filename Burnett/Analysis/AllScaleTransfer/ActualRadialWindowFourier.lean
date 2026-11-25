import Burnett.Analysis.CubicEnergy.JointMultiplier.JointDyadicWindows
import Burnett.Analysis.AllScaleTransfer.RadianTrilinearChange

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.A05
open Burnett.Analysis.ShiftedFourierWindow

open MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier (radianTrilinearForm radianTrilinearWeight)
open scoped FourierTransform RealInnerProductSpace

private def phase (t : ℝ) : ℂ := Complex.exp ((↑(tau * t) : ℂ) * Complex.I)
private theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 := by simp [phase, Complex.norm_exp]

private theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private def shiftedProfile (a : SchwartzMap E ℂ) (t : ℝ) (q ξ : E) : ℂ :=
  phase (inner ℝ (t • ξ) q) * a (t • ξ)

/-- The two separated modulated Fourier windows and the actual third
unmodulated window, represented in manuscript radian frequencies. -/
def radianSeparatedWindowSymbol (a b d : SchwartzMap E ℂ) (t u v : ℝ)
    (q r : E) (p : Joint) : ℂ :=
  let ξ := tau⁻¹ • p.1
  let η := tau⁻¹ • p.2
  shiftedProfile a t q ξ * shiftedProfile b u r η * d (v • (-(ξ + η)))

private theorem radianForm_eq_rescaled (m : Joint → ℂ) (f g h : SchwartzMap E ℂ) :
    radianTrilinearForm m f g h =
      ∫ p : Joint, m (tau • p) * (𝓕 (f : E → ℂ) p.1 * 𝓕 (g : E → ℂ) p.2) *
        𝓕 (h : E → ℂ) (-(p.1+p.2)) := by
  letI := jointVolume_haar
  have dimE : Module.finrank ℝ E = 4 := finrank_euclideanSpace_fin
  have dimJoint : Module.finrank ℝ Joint = 8 := by rw [Module.finrank_prod, dimE]
  have changeFreq := Measure.integral_comp_smul_of_nonneg (volume : Measure Joint)
    (radianTrilinearWeight m f g h) tau (hR := (mul_pos (by norm_num) Real.pi_pos).le)
  rw [dimJoint] at changeFreq
  unfold radianTrilinearForm
  rw [← changeFreq]
  apply integral_congr_ae
  filter_upwards with p
  simp only [radianTrilinearWeight, radianWeight, Complex.ofReal_one, one_mul, Prod.smul_fst,
    Prod.smul_snd, ← smul_add, ← smul_neg, radianFourier_scaled, mul_assoc]

/-- The actual product of the three spatial windows is the normalized
trilinear frequency form with exactly the retained third frequency. -/
theorem shiftedWindowProduct_radianTrilinear
    (a b d f g h : SchwartzMap E ℂ) (t u v : ℝ) (hv : 0 < v) (q r : E) :
    (∫ x, shiftedWindowOperator a f t q x * shiftedWindowOperator b g u r x *
      shiftedWindowOperator d h v 0 x) =
      radianTrilinearForm (radianSeparatedWindowSymbol a b d t u v q r) f g h := by
  let H := windowTest d h v
  let A (ξ : E) := shiftedProfile a t q ξ * 𝓕 (f : E → ℂ) ξ
  let B (η : E) := shiftedProfile b u r η * 𝓕 (g : E → ℂ) η
  let U (p : Joint) := A p.1 * B p.2
  let O (x : E) (p : Joint) := phase (inner ℝ p.1 x + inner ℝ p.2 x)
  let V (x : E) (p : Joint) := U p * (O x p * H x)
  have absWindow (c : SchwartzMap E ℂ) (s : ℝ) (y : E) (z : E) :
      ‖shiftedProfile c s y z‖ ≤ SchwartzMap.seminorm ℝ 0 0 c := by
    rw [shiftedProfile, norm_mul, phase_norm, one_mul]
    exact c.norm_le_seminorm ℝ _
  have contWindow (c : SchwartzMap E ℂ) (s : ℝ) (y : E) : Continuous (shiftedProfile c s y) := by
    unfold shiftedProfile phase
    fun_prop
  have intA : Integrable A := (SchwartzMap.fourierTransformCLM ℂ f).integrable.bdd_mul'
    (contWindow a t q).aestronglyMeasurable (Filter.Eventually.of_forall (absWindow a t q))
  have intB : Integrable B := (SchwartzMap.fourierTransformCLM ℂ g).integrable.bdd_mul'
    (contWindow b u r).aestronglyMeasurable (Filter.Eventually.of_forall (absWindow b u r))
  have intU : Integrable U := by
    rw [Measure.volume_eq_prod E E]
    exact intA.mul_prod intB
  have contU : Continuous U :=
    (((contWindow a t q).mul (SchwartzMap.fourierTransformCLM ℂ f).continuous).comp continuous_fst).mul
      (((contWindow b u r).mul (SchwartzMap.fourierTransformCLM ℂ g).continuous).comp continuous_snd)
  have intV : Integrable (Function.uncurry V) ((volume : Measure E).prod volume) := by
    have contO : Continuous (fun z : E × Joint => O z.1 z.2) := by
      unfold O phase
      fun_prop
    refine (H.integrable.norm.mul_prod intU.norm).mono'
      (((contU.comp continuous_snd).mul (contO.mul (H.continuous.comp continuous_fst))).aestronglyMeasurable) ?_
    filter_upwards with z
    change ‖U z.2 * (O z.1 z.2 * H z.1)‖ ≤ ‖H z.1‖ * ‖U z.2‖
    simp only [O, norm_mul, phase_norm, one_mul]
    exact le_of_eq (mul_comm _ _)
  have third (x : E) : shiftedWindowOperator d h v 0 x = H x := by
    simpa only [H, neg_zero, zero_div, smul_zero, sub_zero] using
      (windowTest_translate d h v 0 hv x (0 : E)).symm
  have point (x : E) : shiftedWindowOperator a f t q x * shiftedWindowOperator b g u r x *
      shiftedWindowOperator d h v 0 x = ∫ p, V x p := by
    have first (c k : SchwartzMap E ℂ) (s : ℝ) (y : E) :
        shiftedWindowOperator c k s y x =
          ∫ ξ, phase (inner ℝ ξ x) * (shiftedProfile c s y ξ * 𝓕 (k : E → ℂ) ξ) := by
      apply integral_congr_ae
      filter_upwards with ξ
      change phase _ * phase _ * c _ * 𝓕 (k : E → ℂ) ξ =
        phase _ * (shiftedProfile c s y ξ * 𝓕 (k : E → ℂ) ξ)
      simp only [shiftedProfile]
      ring
    rw [first a f t q, first b g u r, third,
      ← integral_prod_mul (fun ξ => phase (inner ℝ ξ x) * A ξ) (fun η => phase (inner ℝ η x) * B η),
      ← integral_mul_const, ← Measure.volume_eq_prod E E]
    apply integral_congr_ae
    filter_upwards with p
    change ((phase (inner ℝ p.1 x) * A p.1) * (phase (inner ℝ p.2 x) * B p.2)) * H x = V x p
    simp only [V, U, O, phase_add]
    ring
  have phasePair (p : Joint) : (∫ x, O x p * H x) = 𝓕 (H : E → ℂ) (-(p.1+p.2)) := by
    rw [Real.fourierIntegral_eq']
    apply integral_congr_ae
    filter_upwards with x
    simp only [O, phase, inner_neg_right, inner_add_right, real_inner_comm x p.1,
      real_inner_comm x p.2, smul_eq_mul, neg_mul, mul_neg, neg_neg]
  have htau : tau ≠ 0 := (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).ne'
  simp_rw [point]
  rw [integral_integral_swap intV, radianForm_eq_rescaled]
  apply integral_congr_ae
  filter_upwards with p
  change (∫ x, U p * (O x p * H x)) = _
  rw [integral_const_mul, phasePair, windowTest_fourier]
  simp only [U, A, B, radianSeparatedWindowSymbol, Prod.smul_fst, Prod.smul_snd, smul_smul,
    inv_mul_cancel₀ htau, one_smul]
  ring

end Burnett.A05
