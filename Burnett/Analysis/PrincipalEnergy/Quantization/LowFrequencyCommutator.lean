import Burnett.Analysis.PrincipalEnergy.Quantization.LowFrequencyKernel
import Burnett.Analysis.PrincipalEnergy.Quantization.ConvolutionEnvelope

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Function Filter MeasureTheory Burnett.Microlocal.AngularDyadicKernel
open scoped FourierTransform

/-- The low-frequency action is the ordinary absolutely integrable
convolution with its actual inverse Fourier symbol at each base point. -/
theorem firstOrderLowAction_eq_kernel {a : E → E → ℂ} (ha : FrequencyOrderOne a)
    (f : E → ℂ) (hf : Integrable f) (x : E) :
    firstOrderLowAction a f x = ∫ y, firstOrderLowKernel a x (x-y) * f y :=
  inverseFourier_mul_fourier_eq_convolution _ _ (firstOrderLowSymbol_integrable ha x) hf x

def lowCoefficientCommutator (a : E → E → ℂ) (r f : E → ℂ) (x : E) : ℂ :=
  r x * firstOrderLowAction a f x - firstOrderLowAction a (fun y => r y*f y) x

def lowCoefficientKernel (a : E → E → ℂ) (r : E → ℂ) (x y : E) : ℂ :=
  (r x-r y) * firstOrderLowKernel a x (x-y)

private theorem lowKernel_continuous_at_base {a : E → E → ℂ}
    (ha : FrequencyOrderOne a) (hs : Continuous (uncurry a)) (x : E) :
    Continuous (fun y => firstOrderLowKernel a x (x-y)) := by
  let S (y : E) : E × E := (x,x-y)
  change Continuous (uncurry (firstOrderLowKernel a) ∘ S)
  have hS : Continuous S := continuous_const.prodMk (continuous_const.sub continuous_id)
  exact (firstOrderLowKernel_joint_continuous ha hs).comp hS

/-- Exact low-frequency coefficient commutator on bounded continuous
coefficients and actual complex Schwartz inputs. -/
theorem lowCoefficientCommutator_eq_kernel {a : E → E → ℂ}
    (ha : FrequencyOrderOne a) (hs : Continuous (uncurry a)) (r : E → ℂ)
    (hr : Continuous r) (U : ℝ) (hB : ∀ y, ‖r y‖ ≤ U)
    (f : SchwartzMap E ℂ) (x : E) :
    lowCoefficientCommutator a r f x = ∫ y, lowCoefficientKernel a r x y * f y := by
  obtain ⟨C,hC,_,hDom⟩ := exists_lowKernel_integrable_profile ha
  let k (y : E) := firstOrderLowKernel a x (x-y)
  have hkM : AEStronglyMeasurable k volume := (lowKernel_continuous_at_base ha hs x).aestronglyMeasurable
  have hkB (y : E) : ‖k y‖ ≤ C :=
    (hDom x (x-y)).trans (mul_le_of_le_one_right hC.le
      ((inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (le_add_of_nonneg_right (sq_nonneg _)))))
  have hRf : Integrable (fun y => r y*f y) := f.integrable.bdd_mul hr.aestronglyMeasurable ⟨U,hB⟩
  have hF := f.integrable.bdd_mul hkM ⟨C,hkB⟩
  have hFr := hRf.bdd_mul hkM ⟨C,hkB⟩
  unfold lowCoefficientCommutator
  rw [firstOrderLowAction_eq_kernel ha _ f.integrable,firstOrderLowAction_eq_kernel ha _ hRf]
  change r x * (∫ y, k y*f y) - (∫ y, k y*(r y*f y)) = _
  rw [← integral_const_mul,← integral_sub (hF.const_mul _) hFr]
  apply integral_congr_ae
  filter_upwards with y
  change r x*(k y*f y) - k y*(r y*f y) = (r x-r y)*k y*f y
  ring

/-- The bounded-frequency branch of the real problem already has the exact
L² estimate, using no derivative of the coefficient. -/
theorem exists_lowCoefficientCommutator_L2_bound {a : E → E → ℂ}
    (ha : FrequencyOrderOne a) (hs : Continuous (uncurry a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : E → ℂ), Continuous r → ∀ U : ℝ, 0 ≤ U →
      (∀ y, ‖r y‖ ≤ U) → ∀ f : SchwartzMap E ℂ,
        ∃ hL : MemLp (lowCoefficientCommutator a r f) 2 (volume : Measure E),
          ‖hL.toLp (lowCoefficientCommutator a r f)‖ ≤ C*U*‖f.toLp 2 volume‖ := by
  obtain ⟨C,hC,hEnv,hDom⟩ := exists_lowKernel_integrable_profile ha
  let d (z : E) := C*((1+‖z‖^2)^3)⁻¹
  have hd₀ (z : E) : 0 ≤ d z := by dsimp [d]; positivity
  have hdI : Integrable d := hEnv
  refine ⟨2*(∫ z,d z),mul_nonneg (by norm_num) (integral_nonneg hd₀),?_⟩
  intro r hr U hU hR f
  let K := lowCoefficientKernel a r
  let W (p : E × E) : E × E := (p.1,p.1-p.2)
  have hW : Continuous W := continuous_fst.prodMk (continuous_fst.sub continuous_snd)
  have hK : Continuous (uncurry K) := by
    change Continuous (fun p : E × E => (r p.1-r p.2) * (uncurry (firstOrderLowKernel a) ∘ W) p)
    exact (((hr.comp continuous_fst).sub (hr.comp continuous_snd))).mul
      ((firstOrderLowKernel_joint_continuous ha hs).comp hW)
  have hDominates (x y : E) : ‖K x y‖ ≤ (2*U)*d (x-y) := by
    change ‖(r x-r y)*firstOrderLowKernel a x (x-y)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul ((norm_sub_le _ _).trans (by linarith [hR x,hR y])) (hDom x (x-y))
      (norm_nonneg _) (by positivity)
  have wM : Measurable (fun z => (2*U)*d z) := by unfold d; fun_prop
  obtain ⟨hL,hBound⟩ := convolution_envelope_action_norm_le K hK.measurable _ wM
    (fun z => mul_nonneg (by positivity) (hd₀ z)) (hdI.const_mul _) hDominates f
    f.continuous.measurable f.integrable (f.memLp 2 volume)
  have hEq : lowCoefficientCommutator a r f = fun x => ∫ y, K x y*f y :=
    funext (lowCoefficientCommutator_eq_kernel ha hs r hr U hR f)
  rw [hEq]
  refine ⟨hL,hBound.trans_eq ?_⟩
  rw [integral_const_mul]
  change ((2*U)*(∫ z,d z))*‖f.toLp 2 volume‖ = _
  ring

end Burnett.Analysis.FirstOrderDyadic
