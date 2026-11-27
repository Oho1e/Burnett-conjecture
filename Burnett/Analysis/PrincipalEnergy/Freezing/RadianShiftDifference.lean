import Burnett.Analysis.PrincipalEnergy.Freezing.ModulatedAngularAction
import Burnett.Analysis.PrincipalEnergy.Freezing.PatchIntegralLpBound

set_option autoImplicit false
set_option maxHeartbeats 1750000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal FourierTransform Interval RealInnerProductSpace

theorem radian_action_fourier_integral (m : E → ℝ) (u : SchwartzMap E ℂ) (x : E) :
    radianAction m u x =
      ∫ ξ, patchFourierPhase ξ x * ((m (tau • ξ) : ℂ) * 𝓕 (u : E → ℂ) ξ) := by
  rw [← radianActionSpectrum_inverse, Real.fourierIntegralInv_eq']
  simp only [Burnett.Microlocal.Overlap.baseFourierPhase, radianActionSpectrum, tau, smul_eq_mul]

private theorem radian_kernel_phase_measurable {α : Type*} [MeasurableSpace α] :
    Measurable (fun z : (α × E) × E => patchFourierPhase z.2 z.1.2) := by
  let swapCoord : (α × E) × E → E × E := fun z => (z.2, z.1.2)
  let phase : E × E → ℂ := fun y => patchFourierPhase y.1 y.2
  change Measurable (phase ∘ swapCoord)
  have left : Measurable (Prod.fst : (α × E) × E → α × E) := measurable_fst
  have freq : Measurable (Prod.snd : (α × E) × E → E) := measurable_snd
  have space : Measurable (Prod.snd : α × E → E) := measurable_snd
  have phaseArgs : Measurable swapCoord := freq.prodMk (space.comp left)
  have phaseMeas : Measurable phase := patch_fourier_phase_continuous.measurable
  exact phaseMeas.comp phaseArgs

private theorem radian_kernel_symbol_measurable {α : Type*} [MeasurableSpace α]
    (m : α × E → ℝ) (hm : Measurable m) :
    Measurable (fun z : (α × E) × E => (m (z.1.1, tau • z.2) : ℂ)) := by
  have left : Measurable (Prod.fst : (α × E) × E → α × E) := measurable_fst
  have freq : Measurable (Prod.snd : (α × E) × E → E) := measurable_snd
  have param : Measurable (Prod.fst : α × E → α) := measurable_fst
  have scale : Measurable (fun ξ : E => tau • ξ) := (continuous_const.smul continuous_id).measurable
  have symbolArgs : Measurable (fun z : (α × E) × E => (z.1.1, tau • z.2)) :=
    (param.comp left).prodMk (scale.comp freq)
  exact Complex.continuous_ofReal.measurable.comp (hm.comp symbolArgs)

private theorem radian_kernel_measurable {α : Type*} [MeasurableSpace α]
    (m : α × E → ℝ) (hm : Measurable m) (F : E → ℂ) (hF : Measurable F) :
    Measurable (fun z : (α × E) × E =>
      patchFourierPhase z.2 z.1.2 * ((m (z.1.1, tau • z.2) : ℂ) * F z.2)) := by
  have freq : Measurable (Prod.snd : (α × E) × E → E) := measurable_snd
  exact radian_kernel_phase_measurable.mul ((radian_kernel_symbol_measurable m hm).mul (hF.comp freq))

theorem radian_action_varying_measurable {α : Type*} [MeasurableSpace α]
    (m : α × E → ℝ) (hm : Measurable m) (u : SchwartzMap E ℂ) :
    Measurable (fun z : α × E => radianAction (fun ξ : E => m (z.1, ξ)) u z.2) := by
  simp_rw [radian_action_fourier_integral]
  have hF : Measurable (𝓕 (u : E → ℂ)) :=
    (SchwartzMap.fourierTransformCLM ℂ u).continuous.measurable
  exact ((radian_kernel_measurable m hm _ hF).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure E))).measurable

theorem norm_radian_action_le_of_symbol_bound (m : E → ℝ) (M : ℝ)
    (bound : ∀ ξ, ‖m ξ‖ ≤ M) (u : SchwartzMap E ℂ) (x : E) :
    ‖radianAction m u x‖ ≤ M * ∫ ξ, ‖𝓕 (u : E → ℂ) ξ‖ := by
  let U := SchwartzMap.fourierTransformCLM ℂ u
  rw [radian_action_fourier_integral, ← integral_const_mul]
  apply norm_integral_le_of_norm_le (U.integrable.norm.const_mul M)
  filter_upwards with ξ
  simp only [norm_mul, patch_fourier_phase_norm, one_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (bound _) (norm_nonneg _)

/-- A global difference bound, including segments crossing the zero frequency. -/
theorem norm_symbol_shift_sub_le (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (D : ℝ) (hD : 0 ≤ D)
    (jet : ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ 1 b ξ‖ ≤ D)
    (v ξ : E) :
    ‖b (ξ + v) - b ξ‖ ≤ ‖v‖ * D := by
  rw [← angular_differential_integral_eq b hb hom]
  simpa using (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun t => angularDifferential b v (ξ + t • v)) (C := ‖v‖ * D)
    (fun t _ => angular_differential_bound b hb hom v D hD jet (ξ + t • v)))

private theorem radian_shift_difference_continuous (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (D : ℝ) (hD : 0 ≤ D)
    (jet : ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ 1 b ξ‖ ≤ D)
    (v : E) (u : SchwartzMap E ℂ) :
    Continuous (radianAction (fun ξ => b (ξ + v) - b ξ) u) := by
  let U := SchwartzMap.fourierTransformCLM ℂ u
  have mb := measurable_of_continuousOn_compl_singleton 0 hb.continuousOn
  have sm : Measurable (fun ξ : E => tau • ξ) := (continuous_const.smul continuous_id).measurable
  have hF : Integrable (radianActionSpectrum (fun ξ => b (ξ + v) - b ξ) u) := by
    apply (U.integrable.norm.const_mul (‖v‖ * D)).mono'
    · exact ((Complex.continuous_ofReal.measurable.comp
        ((mb.comp (sm.add_const v)).sub (mb.comp sm))).mul U.continuous.measurable).aestronglyMeasurable
    · filter_upwards with ξ
      change ‖(↑(b (tau • ξ + v) - b (tau • ξ)) : ℂ) * U ξ‖ ≤ (‖v‖ * D) * ‖U ξ‖
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (norm_symbol_shift_sub_le b hb hom D hD jet v _) (norm_nonneg _)
  rw [← radianActionSpectrum_inverse]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (continuous_fst.inner continuous_snd).neg hF

/-- The symbol segment identity passes to the actual Fourier integral. -/
theorem radian_shift_difference_integral (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (D : ℝ) (hD : 0 ≤ D)
    (jet : ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ 1 b ξ‖ ≤ D)
    (v : E) (u : SchwartzMap E ℂ) (x : E) :
    radianAction (fun ξ => b (ξ + v) - b ξ) u x =
      ∫ t in Ioc (0 : ℝ) 1, radianAction (fun ξ => angularDifferential b v (ξ + t • v)) u x := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  let U := SchwartzMap.fourierTransformCLM ℂ u
  let H : ℝ × E → ℂ := fun z =>
    patchFourierPhase z.2 x * ((angularDifferential b v (tau • z.2 + z.1 • v) : ℂ) * U z.2)
  have phaseArgs : Continuous (fun z : ℝ × E => (z.2, x)) := continuous_snd.prodMk continuous_const
  have phase : Measurable (fun z : ℝ × E => patchFourierPhase z.2 x) :=
    (patch_fourier_phase_continuous.comp phaseArgs).measurable
  have mA := measurable_of_continuousOn_compl_singleton 0
    (angular_differential_contDiffOn b hb v).continuousOn
  have hv : Continuous (fun z : ℝ × E => tau • z.2 + z.1 • v) :=
    (continuous_const.smul continuous_snd).add (continuous_fst.smul continuous_const)
  have hH : Measurable H := phase.mul ((Complex.continuous_ofReal.measurable.comp (mA.comp hv.measurable)).mul
    (U.continuous.measurable.comp measurable_snd))
  letI : IsFiniteMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
  have hi : Integrable H (μ.prod (volume : Measure E)) := by
    apply ((integrable_const (‖v‖ * D)).mul_prod U.integrable.norm).mono' hH.aestronglyMeasurable
    filter_upwards with z
    simp only [H, norm_mul, patch_fourier_phase_norm, one_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (angular_differential_bound b hb hom v D hD jet _) (norm_nonneg _)
  rw [radian_action_fourier_integral]
  calc
    _ = ∫ ξ, (∫ t, H (t, ξ) ∂μ) := by
      apply integral_congr_ae
      filter_upwards with ξ
      have seg := angular_differential_integral_eq b hb hom v (tau • ξ)
      rw [intervalIntegral.integral_of_le zero_le_one] at seg
      simp only [H, integral_const_mul, integral_mul_const]
      rw [integral_complex_ofReal, seg]
      rfl
    _ = ∫ t, (∫ ξ, H (t, ξ)) ∂μ := (integral_integral_swap (f := fun t ξ => H (t, ξ)) hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [radian_action_fourier_integral]
      rfl

/-- A finite translation in frequency gives a genuine order-zero multiplier
bound with the first power of the translation size. -/
theorem exists_radian_shift_difference_L3_bound :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 7 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ (v : E) (u : SchwartzMap E ℂ),
        let w := radianAction (fun ξ => b (ξ + v) - b ξ) u
        MemLp w (ENNReal.ofReal 3) volume ∧
          eLpNorm w (ENNReal.ofReal 3) volume ≤
            ENNReal.ofReal (K * (‖v‖ * D)) * eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume := by
  obtain ⟨K, hK, est⟩ := exists_translated_angular_action_L3_bound
  refine ⟨K, hK, ?_⟩
  intro b hb hom D hD jet v u w
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  let G : ℝ × E → ℂ := fun z => radianAction (fun ξ => angularDifferential b v (ξ + z.1 • v)) u z.2
  let J := ‖v‖ * D
  let U := eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume
  let V := ENNReal.ofReal K * U
  letI : IsFiniteMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
  have hJ : 0 ≤ J := mul_nonneg (norm_nonneg _) hD
  have hV : V < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (u.memLp _ volume).eLpNorm_lt_top
  have j1 := jet 1 (by decide)
  have meas : Measurable G := radian_action_varying_measurable _
    ((measurable_of_continuousOn_compl_singleton 0
      (angular_differential_contDiffOn b hb v).continuousOn).comp
      (measurable_snd.add (measurable_fst.smul measurable_const))) u
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have sectionBounds (t : ℝ) :
      MemLp (fun x => G (t, x)) (ENNReal.ofReal 3) volume ∧
        eLpNorm (fun x => G (t, x)) (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal J * V := by
    have shift : tau • ((t / tau) • v) = t • v := by
      rw [smul_smul, mul_div_cancel₀ _ hτ.ne']
    have e := est b hb hom D hD jet v ((t / tau) • v) u
    dsimp only at e
    rw [shift] at e
    simpa only [G, V, J, U, mul_assoc, ENNReal.ofReal_mul (mul_nonneg hK (norm_nonneg _)),
      ENNReal.ofReal_mul hK, mul_left_comm (ENNReal.ofReal K)] using e
  have bound := patch_integral_L3_bound μ G meas w
    (radian_shift_difference_continuous b hb hom D hD j1 v u)
    (radian_shift_difference_integral b hb hom D hD j1 v u)
    (fun _ => J) (integrable_const J) (fun _ => hJ) (∫ ξ, ‖𝓕 (u : E → ℂ) ξ‖)
    (fun t x => norm_radian_action_le_of_symbol_bound _ J
      (fun ξ => angular_differential_bound b hb hom v D hD j1 (ξ + t • v)) u x)
    V hV sectionBounds
  refine ⟨bound.1, bound.2.trans_eq ?_⟩
  have eq : (∫ _ : ℝ, J ∂μ) = J := by simp [μ]
  rw [eq, ENNReal.ofReal_mul hK]
  dsimp only [V, U]
  rw [← mul_assoc, mul_comm (ENNReal.ofReal J)]

end Burnett.A03
