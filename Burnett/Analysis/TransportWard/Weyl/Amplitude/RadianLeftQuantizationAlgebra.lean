import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalOrderZeroLeft
import Burnett.Analysis.TransportWard.Weyl.Amplitude.RadianLeftFullSymbol

set_option autoImplicit false
set_option maxHeartbeats 4400000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff FourierTransform Topology

/-- The ordinary pointwise growth needed to form the genuine left Fourier
integral at each base point on a Schwartz input. -/
def RadianLeftSymbolGrowth (b : E → E → ℂ) : Prop :=
  ∀ x, Measurable (b x) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ, ‖b x ξ‖ ≤ C*(1+‖ξ‖)

private theorem radian_left_integrand_integrable (b : E → E → ℂ)
    (h : RadianLeftSymbolGrowth b) (u : SchwartzMap E ℂ) (x : E) :
    Integrable (fun ξ : E => patchFourierPhase ξ x * b x (tau • ξ) * 𝓕 (u : E → ℂ) ξ) volume := by
  obtain ⟨m,D,D0,g⟩ := h x
  let F := SchwartzMap.fourierTransformCLM ℂ u
  let J (ξ : E) := (1 + tau * ‖ξ‖) * ‖F ξ‖
  have τp : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have JI : Integrable J volume := by
    apply (F.integrable.norm.add ((F.integrable_pow_mul volume 1).const_mul tau)).congr
    filter_upwards with ξ
    change ‖F ξ‖ + tau * (‖ξ‖ ^ 1 * ‖F ξ‖) = J ξ
    rw [pow_one]
    dsimp only [J]
    ring
  let pair (ξ : E) : E × E := (ξ,x)
  have pc : Continuous (fun ξ : E => patchFourierPhase ξ x) := by
    change Continuous ((fun q : E × E => patchFourierPhase q.1 q.2) ∘ pair)
    exact patch_fourier_phase_continuous.comp (continuous_id.prodMk continuous_const)
  have bc : Measurable (fun ξ : E => b x (tau • ξ)) :=
    m.comp (continuous_const.smul continuous_id).measurable
  refine (JI.const_mul D).mono' ((pc.aestronglyMeasurable.mul bc.aestronglyMeasurable).mul
    F.continuous.aestronglyMeasurable) ?_
  filter_upwards with ξ
  change ‖patchFourierPhase ξ x * b x (tau • ξ) * F ξ‖ ≤ D * J ξ
  rw [norm_mul,norm_mul,patch_fourier_phase_norm,one_mul]
  have k := g (tau • ξ)
  rw [norm_smul,Real.norm_of_nonneg τp.le] at k
  exact (mul_le_mul_of_nonneg_right k (norm_nonneg _)).trans_eq (by dsimp only [J]; ring)

/-- Linearity is at the level of the actual radian integral, with
integrability justified for each symbol. -/
theorem radian_left_quantization_add_actual (a b : E → E → ℂ)
    (ha : RadianLeftSymbolGrowth a) (hb : RadianLeftSymbolGrowth b) (u : SchwartzMap E ℂ) :
    radianLeftQuantization (fun x ξ => a x ξ + b x ξ) u =
      radianLeftQuantization a u + radianLeftQuantization b u := by
  funext x
  simp only [radianLeftQuantization,Pi.add_apply]
  rw [← integral_add (radian_left_integrand_integrable a ha u x) (radian_left_integrand_integrable b hb u x)]
  exact integral_congr_ae (Eventually.of_forall fun ξ => by ring)

/-- Subtracting two actual left actions subtracts their complete symbols. -/
theorem radian_left_quantization_sub_actual (a b : E → E → ℂ)
    (ha : RadianLeftSymbolGrowth a) (hb : RadianLeftSymbolGrowth b) (u : SchwartzMap E ℂ) :
    radianLeftQuantization (fun x ξ => a x ξ - b x ξ) u =
      radianLeftQuantization a u - radianLeftQuantization b u := by
  funext x
  simp only [radianLeftQuantization,Pi.sub_apply]
  rw [← integral_sub (radian_left_integrand_integrable a ha u x) (radian_left_integrand_integrable b hb u x)]
  exact integral_congr_ae (Eventually.of_forall fun ξ => by ring)

/-- Left multiplication by the output cutoff is the actual operation
of multiplying the full left symbol in its base argument. -/
theorem radian_left_quantization_output_localization (b : E → E → ℂ)
    (χ : E → ℂ) (u : SchwartzMap E ℂ) (x : E) :
    radianLeftQuantization (fun y ξ => χ y * b y ξ) u x =
      χ x * radianLeftQuantization b u x := by
  unfold radianLeftQuantization
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun ξ => by ring)

end Burnett.A03
