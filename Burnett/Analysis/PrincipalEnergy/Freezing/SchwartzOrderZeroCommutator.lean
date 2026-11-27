import Burnett.Analysis.PrincipalEnergy.Freezing.RadianShiftDifference
import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianCommutator
import Burnett.Analysis.PrincipalEnergy.Freezing.RadianSkewDifferentiation
import Burnett.Analysis.PrincipalEnergy.Freezing.ProfileFourierMoment
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearIBP
import Mathlib.MeasureTheory.Group.Prod

set_option autoImplicit false
set_option maxHeartbeats 2100000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open Burnett.Microlocal.AngularCommutator (fourier_mul_inverse_eq_integral)
open scoped ContDiff ENNReal FourierTransform RealInnerProductSpace

private theorem shift_fourier_shear_preserving :
    MeasurePreserving (fun z : E × E => (z.1 - z.2, z.2))
      ((volume : Measure E).prod volume) ((volume : Measure E).prod volume) := by
  have eq : (fun z : E × E => (z.1 - z.2, z.2)) =
      Prod.swap ∘ (fun z : E × E => (z.2, -z.2 + z.1)) := by
    funext z
    exact Prod.ext (by change z.1 - z.2 = -z.2 + z.1; rw [sub_eq_add_neg, add_comm]) rfl
  rw [eq]
  exact Measure.measurePreserving_swap.comp (measurePreserving_prod_neg_add_swap (volume : Measure E) volume)

/-- The genuine commutator is a Fourier average of shifted symbol differences. -/
theorem radian_commutator_shift_integral (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (D : ℝ) (hD : 0 ≤ D)
    (jet : ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ 1 b ξ‖ ≤ D)
    (f u : SchwartzMap E ℂ) (x : E) :
    radianCommutator b f u x =
      ∫ η, (patchFourierPhase η x * 𝓕 (f : E → ℂ) η) *
        radianAction (fun ξ => b (ξ + tau • η) - b ξ) u x := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let U := SchwartzMap.fourierTransformCLM ℂ u
  let G (ξ : E) := patchFourierPhase ξ x
  let B (ξ : E) := b (tau • ξ)
  let H₁ (z : E × E) : ℂ := G (z.1 + z.2) * ((B (z.1 + z.2) : ℂ) * (F z.1 * U z.2))
  let H₂ (z : E × E) : ℂ := G (z.1 + z.2) * ((B z.2 : ℂ) * (F z.1 * U z.2))
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  let C := tau * D
  have hC : 0 ≤ C := mul_nonneg hτ.le hD
  have hB (ξ : E) : ‖B ξ‖ ≤ C * ‖ξ‖ := by
    have h := norm_symbol_shift_sub_le b hb hom D hD jet (tau • ξ) 0
    rw [zero_add, homogeneous_value_zero hom, sub_zero, norm_smul, Real.norm_of_nonneg hτ.le] at h
    exact h.trans_eq (by dsimp only [C]; ring)
  have measurableB : Measurable B := (measurable_of_continuousOn_compl_singleton 0 hb.continuousOn).comp
    (continuous_const.smul continuous_id).measurable
  let center : E → E × E := fun ξ => (ξ, x)
  have centerMeas : Measurable center := measurable_id.prodMk measurable_const
  have phaseMeas : Measurable (fun y : E × E => patchFourierPhase y.1 y.2) :=
    patch_fourier_phase_continuous.measurable
  have measurableG : Measurable G := by
    change Measurable ((fun y : E × E => patchFourierPhase y.1 y.2) ∘ center)
    exact phaseMeas.comp centerMeas
  have left : Measurable (Prod.fst : E × E → E) := measurable_fst
  have right : Measurable (Prod.snd : E × E → E) := measurable_snd
  have add : Measurable (fun z : E × E => z.1 + z.2) := left.add right
  have commonPhase : Measurable (fun z : E × E => G (z.1 + z.2)) := measurableG.comp add
  have commonProduct : Measurable (fun z : E × E => F z.1 * U z.2) :=
    (F.continuous.measurable.comp left).mul (U.continuous.measurable.comp right)
  have meas₁ : Measurable H₁ := commonPhase.mul ((Complex.continuous_ofReal.measurable.comp
    (measurableB.comp add)).mul commonProduct)
  have meas₂ : Measurable H₂ := commonPhase.mul ((Complex.continuous_ofReal.measurable.comp
    (measurableB.comp right)).mul commonProduct)
  have F₁ : Integrable (fun η : E => ‖η‖ * ‖F η‖) := by
    simpa only [pow_one] using F.integrable_pow_mul volume 1
  have U₁ : Integrable (fun ξ : E => ‖ξ‖ * ‖U ξ‖) := by
    simpa only [pow_one] using U.integrable_pow_mul volume 1
  have i₂ : Integrable H₂ ((volume : Measure E).prod volume) := by
    apply (F.integrable.norm.mul_prod (U₁.const_mul C)).mono' meas₂.aestronglyMeasurable
    filter_upwards with z
    simp only [H₂, G, norm_mul, patch_fourier_phase_norm, one_mul, Complex.norm_real]
    calc
      _ ≤ (C * ‖z.2‖) * (‖F z.1‖ * ‖U z.2‖) :=
        mul_le_mul_of_nonneg_right (hB _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  have i₁ : Integrable H₁ ((volume : Measure E).prod volume) := by
    apply (((F₁.const_mul C).mul_prod U.integrable.norm).add
      (F.integrable.norm.mul_prod (U₁.const_mul C))).mono' meas₁.aestronglyMeasurable
    filter_upwards with z
    simp only [H₁, G, norm_mul, patch_fourier_phase_norm, one_mul, Complex.norm_real]
    have hSum := (hB (z.1 + z.2)).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) hC)
    calc
      _ ≤ C * (‖z.1‖ + ‖z.2‖) * (‖F z.1‖ * ‖U z.2‖) :=
        mul_le_mul_of_nonneg_right hSum (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by simp only [Pi.add_apply]; ring
  have convolution (ζ : E) : 𝓕 (energyProduct f u : E → ℂ) ζ = ∫ ξ, F (ζ - ξ) * U ξ := by
    have inverse : 𝓕⁻ (U : E → ℂ) = (u : E → ℂ) :=
      u.continuous.fourier_inversion u.integrable U.integrable
    simpa only [inverse, energyProduct_apply] using
      fourier_mul_inverse_eq_integral (f : E → ℂ) (U : E → ℂ) f.integrable U.integrable ζ
  have first : radianAction b (energyProduct f u) x = ∫ η, ∫ ξ, H₁ (η, ξ) := by
    have iT := shift_fourier_shear_preserving.integrable_comp_of_integrable i₁
    rw [radian_action_fourier_integral]
    calc
      _ = ∫ ζ, ∫ ξ, H₁ (ζ - ξ, ξ) := by
        apply integral_congr_ae
        filter_upwards with ζ
        rw [convolution ζ, ← integral_const_mul, ← integral_const_mul]
        simp only [H₁, G, B, sub_add_cancel]
      _ = ∫ ξ, ∫ ζ, H₁ (ζ - ξ, ξ) :=
        integral_integral_swap (f := fun ζ ξ => H₁ (ζ - ξ, ξ)) iT
      _ = ∫ ξ, ∫ η, H₁ (η, ξ) := by
        apply integral_congr_ae
        filter_upwards with ξ
        simpa only [sub_eq_add_neg] using integral_add_right_eq_self (fun η => H₁ (η, ξ)) (-ξ)
      _ = _ := (integral_integral_swap (f := fun η ξ => H₁ (η, ξ)) i₁).symm
  have second : f x * radianAction b u x = ∫ η, ∫ ξ, H₂ (η, ξ) := by
    have fi : f x = ∫ η, G η * F η := by
      have inv := congrFun (f.continuous.fourier_inversion f.integrable F.integrable) x
      rw [Real.fourierIntegralInv_eq'] at inv
      simpa only [G, Burnett.Microlocal.Overlap.baseFourierPhase, tau, smul_eq_mul] using inv.symm
    rw [fi, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with η
    rw [radian_action_fourier_integral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ξ
    change (G η * F η) * (G ξ * ((B ξ : ℂ) * U ξ)) =
      G (η + ξ) * ((B ξ : ℂ) * (F η * U ξ))
    simp only [G, patch_fourier_phase_add]
    ring
  change radianAction b (energyProduct f u) x - f x * radianAction b u x = _
  rw [first, second, ← integral_integral_sub i₁ i₂]
  apply integral_congr_ae
  filter_upwards with η
  rw [radian_action_fourier_integral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [H₁, H₂, G, B, patch_fourier_phase_add, Complex.ofReal_sub, smul_add]
  change _ - _ = (patchFourierPhase η x * F η) * (patchFourierPhase ξ x *
    (((b (tau • ξ + tau • η) : ℂ) - (b (tau • ξ) : ℂ)) * U ξ))
  rw [add_comm (tau • η) (tau • ξ)]
  ring

/-- The first absolute Fourier moment of the spatial multiplier. -/
abbrev patchFourierFirstMoment (f : SchwartzMap E ℂ) : ℝ :=
  patchFourierMoment 1 f

theorem patch_fourier_first_moment_nonneg (f : SchwartzMap E ℂ) :
    0 ≤ patchFourierFirstMoment f :=
  integral_nonneg fun _ => mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)

/-- Actual order-zero L³ control, with an explicit Fourier moment of the
spatial profile and the first seven angular derivatives of the symbol. -/
theorem exists_radian_commutator_order_zero_L3_bound :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 7 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ f u : SchwartzMap E ℂ,
        MemLp (radianCommutator b f u) (ENNReal.ofReal 3) volume ∧
          eLpNorm (radianCommutator b f u) (ENNReal.ofReal 3) volume ≤
            ENNReal.ofReal (K * D * patchFourierFirstMoment f) *
              eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume := by
  obtain ⟨K, hK, est⟩ := exists_radian_shift_difference_L3_bound
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  refine ⟨tau * K, mul_nonneg hτ.le hK, ?_⟩
  intro b hb hom D hD jet f u
  let p := ENNReal.ofReal 3
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let V := ENNReal.ofReal K * eLpNorm (u : E → ℂ) p volume
  let w (η : E) := (tau * D) * (‖η‖ * ‖F η‖)
  let R (η : E) := radianAction (fun ξ => b (ξ + tau • η) - b ξ) u
  let G (z : E × E) : ℂ := (patchFourierPhase z.1 z.2 * F z.1) * R z.1 z.2
  let A := radianCommutator b f u
  have j1 := jet 1 (by decide)
  have w0 (η : E) : 0 ≤ w η := by dsimp only [w]; positivity
  have hw : Integrable w := by
    simpa only [w, pow_one] using (F.integrable_pow_mul volume 1).const_mul (tau * D)
  have hV : V < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (u.memLp p volume).eLpNorm_lt_top
  have mb := measurable_of_continuousOn_compl_singleton 0 hb.continuousOn
  have hM : Measurable (fun z : E × E => b (z.2 + tau • z.1) - b z.2) :=
    (mb.comp (measurable_snd.add (measurable_const.smul measurable_fst))).sub (mb.comp measurable_snd)
  have hG : Measurable G := (patch_fourier_phase_continuous.measurable.mul
    (F.continuous.measurable.comp measurable_fst)).mul (radian_action_varying_measurable _ hM u)
  have cont : Continuous A := by
    unfold A radianCommutator
    change Continuous (fun x => radianAction b (energyProduct f u) x - f x * radianAction b u x)
    have hAct (v : SchwartzMap E ℂ) : Continuous (radianAction b v) :=
      (show Differentiable ℝ (radianAction b v) from fun x =>
        (radian_action_coordinate_derivative b hb hom v x).1).continuous
    exact (hAct _).sub (f.continuous.mul (hAct _))
  have wt (η : E) : w η = ‖F η‖ * (‖tau • η‖ * D) := by
    simp only [w, norm_smul, Real.norm_of_nonneg hτ.le]
    ring
  have major (η x : E) : ‖G (η,x)‖ ≤ w η * (∫ ξ, ‖𝓕 (u : E → ℂ) ξ‖) := by
    dsimp only [G]
    rw [norm_mul, norm_mul, patch_fourier_phase_norm, one_mul, wt, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_radian_action_le_of_symbol_bound _ _
      (fun ξ => norm_symbol_shift_sub_le b hb hom D hD j1 (tau • η) ξ) u x) (norm_nonneg _)
  have sectionBound (η : E) :
      MemLp (fun x => G (η,x)) p volume ∧ eLpNorm (fun x => G (η,x)) p volume ≤ ENNReal.ofReal (w η) * V := by
    have sh := est b hb hom D hD jet (tau • η) u
    have hm := (hG.comp (measurable_const.prodMk measurable_id : Measurable (fun x : E => (η,x)))).aestronglyMeasurable
      (μ := (volume : Measure E))
    have hNorm (x : E) : ‖G (η,x)‖ = ‖F η • R η x‖ := by
      simp only [G, norm_mul, patch_fourier_phase_norm, one_mul, norm_smul]
    refine ⟨(sh.1.const_smul (F η)).congr_norm hm (Eventually.of_forall fun x => (hNorm x).symm), ?_⟩
    rw [eLpNorm_congr_norm_ae (Eventually.of_forall hNorm)]
    change eLpNorm (F η • R η) p volume ≤ _
    rw [eLpNorm_const_smul]
    refine (mul_le_mul_left' sh.2 _).trans_eq ?_
    rw [wt, ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul hK]
    simp only [V, ← ofReal_norm_eq_enorm, mul_assoc, mul_left_comm]
    rfl
  have out := patch_integral_L3_bound volume G hG A cont
    (radian_commutator_shift_integral b hb hom D hD j1 f u) w hw w0
    (∫ ξ, ‖𝓕 (u : E → ℂ) ξ‖) major V hV sectionBound
  refine ⟨out.1, out.2.trans_eq ?_⟩
  have iw : (∫ η, w η) = (tau * D) * patchFourierFirstMoment f := by
    simp only [w, patchFourierFirstMoment, patchFourierMoment, pow_one, integral_const_mul]
    rfl
  rw [iw]
  dsimp only [V]
  rw [← mul_assoc, ← ENNReal.ofReal_mul
    (mul_nonneg (mul_nonneg hτ.le hD) (patch_fourier_first_moment_nonneg f))]
  congr 2
  ring

end Burnett.A03
