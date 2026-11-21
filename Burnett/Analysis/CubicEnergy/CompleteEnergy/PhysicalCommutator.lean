import Burnett.Analysis.CubicEnergy.BilinearMultiplier.FourierConvention
import Burnett.Analysis.CubicEnergy.FourierIdentity
import Burnett.Analysis.Microlocal.AngularCommutator.FrequencyKernel

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory Set Metric Burnett.Microlocal.AngularCommutator
open scoped FourierTransform ContDiff

private theorem degreeOne_control (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ z, b (t • z)=t*b z) :
    Measurable b ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖b z‖ ≤ C*‖z‖ := by
  have hs : sphere (0:E) 1 ⊆ {x | x ≠ 0} := by
    intro x h
    have hx : ‖x‖=1 := by simpa only [mem_sphere,dist_zero_right] using h
    exact norm_ne_zero_iff.mp (hx.trans_ne one_ne_zero)
  obtain ⟨C,hC⟩ := (isCompact_sphere (0:E) 1).bddAbove_image (hb.continuousOn.norm.mono hs)
  refine ⟨measurable_of_continuousOn_compl_singleton 0 hb.continuousOn,max C 0,le_max_right _ _,?_⟩
  intro z
  by_cases hz : z=0
  · simp [hz,homogeneous_value_zero hh]
  let y : E := ‖z‖⁻¹ • z
  have hy : y ∈ sphere (0:E) 1 := by
    simpa only [mem_sphere,dist_zero_right,y] using norm_smul_inv_norm (𝕜 := ℝ) hz
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hzy : ‖z‖ • y = z := by simp [y,smul_smul,hzpos.ne']
  have h := hh ‖z‖ hzpos y
  rw [hzy] at h
  rw [h,norm_mul,norm_norm,mul_comm ‖z‖]
  exact mul_le_mul_of_nonneg_right ((hC (mem_image_of_mem _ hy)).trans (le_max_left _ _)) hzpos.le

/-- Positive homogeneity allows the genuine unbounded order-one symbol on the
Fourier transform of any Schwartz test, including at arbitrarily small frequencies. -/
theorem orderOne_spectrum_integrable (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ z, b (t • z)=t*b z) (v : SchwartzMap E ℂ) :
    Integrable (fun ξ => (b ξ : ℂ)*𝓕 (v : E → ℂ) ξ) := by
  obtain ⟨hm,C,hC,hbnd⟩ := degreeOne_control b hb hh
  let V := SchwartzMap.fourierTransformCLM ℂ v
  have hI : Integrable (fun ξ : E => ‖ξ‖ * ‖V ξ‖) := by simpa only [pow_one] using V.integrable_pow_mul volume 1
  apply (hI.const_mul C).mono' (((Complex.continuous_ofReal.measurable.comp hm).mul V.continuous.measurable).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro ξ
  change ‖(b ξ : ℂ)*V ξ‖ ≤ C*(‖ξ‖*‖V ξ‖)
  rw [norm_mul,Complex.norm_real,← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hbnd ξ) (norm_nonneg _)

/-- The Fourier representation of the physical commutator, with the symbol
acting on the full product in the first term and on the input in the second. -/
theorem orderOne_commutator_fourier (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ z, b (t • z)=t*b z) (f v : SchwartzMap E ℂ) (ζ : E) :
    (b ζ : ℂ) * 𝓕 (fun x => f x*v x) ζ -
      𝓕 (fun x => f x*orderOneAction b v x) ζ =
      ∫ ξ, ((b ζ : ℂ) - (b ξ : ℂ)) * (𝓕 (f : E → ℂ) (ζ-ξ)) * 𝓕 (v : E → ℂ) ξ := by
  let V := SchwartzMap.fourierTransformCLM ℂ v
  let F := SchwartzMap.fourierTransformCLM ℂ f
  have hinv : 𝓕⁻ (V : E → ℂ) = (v : E → ℂ) := v.continuous.fourier_inversion v.integrable V.integrable
  have h₁ : 𝓕 (fun x => f x*v x) ζ = ∫ ξ, F (ζ-ξ) * V ξ := by
    simpa only [hinv] using fourier_mul_inverse_eq_integral (f : E → ℂ) (V : E → ℂ) f.integrable V.integrable ζ
  have h₂ := fourier_mul_inverse_eq_integral (f : E → ℂ) (fun ξ => (b ξ : ℂ)*V ξ)
    f.integrable (orderOne_spectrum_integrable b hb hh v) ζ
  change 𝓕 (fun x => f x * orderOneAction b v x) ζ = ∫ ξ, F (ζ-ξ)*((b ξ : ℂ)*V ξ) at h₂
  have hmeas := (F.continuous.comp (continuous_const.sub continuous_id : Continuous (fun ξ : E => ζ-ξ))).aestronglyMeasurable (μ := (volume : Measure E))
  have hB : ∃ B : ℝ, ∀ ξ : E, ‖F (ζ-ξ)‖ ≤ B := ⟨_,fun ξ => F.norm_le_seminorm ℝ _⟩
  have hleft : Integrable (fun ξ => (b ζ : ℂ)*(F (ζ-ξ)*V ξ)) := (V.integrable.bdd_mul hmeas hB).const_mul _
  have hright : Integrable (fun ξ => F (ζ-ξ)*((b ξ : ℂ)*V ξ)) :=
    (orderOne_spectrum_integrable b hb hh v).bdd_mul hmeas hB
  rw [h₁,h₂,← integral_const_mul,← integral_sub hleft hright]
  apply integral_congr_ae
  filter_upwards with ξ
  change (b ζ : ℂ)*(F (ζ-ξ)*V ξ)-F (ζ-ξ)*((b ξ : ℂ)*V ξ) = ((b ζ : ℂ)-(b ξ : ℂ))*F (ζ-ξ)*V ξ
  ring

end Burnett.A02.FrequencySplit
