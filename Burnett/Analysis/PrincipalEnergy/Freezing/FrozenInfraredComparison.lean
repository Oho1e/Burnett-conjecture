import Burnett.Analysis.PrincipalEnergy.Freezing.FixedTestOrderZeroAlgebra
import Burnett.Analysis.PrincipalEnergy.Freezing.FixedInfraredWeyl

set_option autoImplicit false
set_option maxHeartbeats 2700000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal ContDiff FourierTransform RealInnerProductSpace

/-- Any bounded real radian multiplier has the usual exact output jet,
even when its fixed low-frequency profile is nonsmooth at the origin. -/
theorem bounded_radian_multiplier_coordinate (b : E → ℝ) (bM : Measurable b)
    (C : ℝ) (bound : ∀ ξ, ‖b ξ‖ ≤ C) (u : SchwartzMap E ℂ) (x : E) :
    DifferentiableAt ℝ (radianAction b u) x ∧
      ∀ j : Index, actualCoordinateJet (radianAction b u) j x = radianAction b (energyPartial j u) x := by
  let U := SchwartzMap.fourierTransformCLM ℂ u
  let F := radianActionSpectrum b u
  let L := VectorFourier.fourierSMulRight (innerSL ℝ) F
  let Neg : E →L[ℝ] E := -ContinuousLinearMap.id ℝ E
  have fm : Measurable F := by
    change Measurable (fun ξ : E => (b (tau • ξ) : ℂ) * U ξ)
    exact (Complex.continuous_ofReal.measurable.comp
      (bM.comp (continuous_const.smul continuous_id).measurable)).mul U.continuous.measurable
  have fb (ξ : E) : ‖F ξ‖ ≤ C * ‖U ξ‖ := by
    change ‖(b (tau • ξ) : ℂ) * U ξ‖ ≤ _
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (bound _) (norm_nonneg _)
  have hF : Integrable F := (U.integrable.norm.const_mul C).mono' fm.aestronglyMeasurable
    (Eventually.of_forall fb)
  have hM : Integrable (fun ξ => ‖ξ‖ * ‖F ξ‖) := by
    apply ((U.integrable_pow_mul volume 1).const_mul C).mono'
      (continuous_norm.measurable.mul fm.norm).aestronglyMeasurable
    filter_upwards with ξ
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)), pow_one]
    exact (mul_le_mul_of_nonneg_left (fb ξ) (norm_nonneg _)).trans_eq (by ring)
  have hL : Integrable L := by
    apply (hM.const_mul (2 * Real.pi * ‖(innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)‖)).mono'
      hF.aestronglyMeasurable.fourierSMulRight
    filter_upwards with ξ
    simpa only [L, mul_assoc] using VectorFourier.norm_fourierSMulRight_le (innerSL ℝ) F ξ
  have inverse : radianAction b u = (𝓕 F) ∘ Neg :=
    (radianActionSpectrum_inverse b u).symm.trans
      (funext fun y => Real.fourierIntegralInv_eq_fourierIntegral_neg F y)
  have hD : HasFDerivAt (radianAction b u) ((𝓕 L (Neg x)).comp Neg) x := by
    rw [inverse]
    exact (Real.hasFDerivAt_fourierIntegral hF hM (Neg x)).comp x Neg.hasFDerivAt
  refine ⟨hD.differentiableAt, fun j => ?_⟩
  unfold actualCoordinateJet
  rw [hD.fderiv]
  change 𝓕 L (-x) (-(EuclideanSpace.single j 1)) =
    radianAction b (energyPartial j u) x
  rw [Real.fourierIntegral_continuousLinearMap_apply hL,
    ← radianActionSpectrum_inverse, Real.fourierIntegralInv_eq_fourierIntegral_neg]
  congr 1
  funext ξ
  have hcoord : (innerSL ℝ) ξ (-(EuclideanSpace.single j 1)) = -ξ j := by
    change inner ℝ ξ (-(EuclideanSpace.single j 1)) = -ξ j
    simp [EuclideanSpace.inner_single_right]
  simp only [L, F, VectorFourier.fourierSMulRight_apply, hcoord, Complex.real_smul,
    smul_eq_mul, radianActionSpectrum, energyPartial_fourier, tau]
  push_cast
  ring

private theorem radian_multiplier_jet_bound_from_value (b : E → ℝ) (bM : Measurable b)
    (C : ℝ) (size : ∀ ξ, ‖b ξ‖ ≤ C) (A : ℝ≥0∞)
    (value : ∀ u : SchwartzMap E ℂ,
      MemLp (radianAction b u) (ENNReal.ofReal 3) volume ∧
      eLpNorm (radianAction b u) (ENNReal.ofReal 3) volume ≤ A * eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume) :
    SchwartzOrderZeroJetBound (radianAction b) A 0 := by
  intro u
  have h (x : E) := bounded_radian_multiplier_coordinate b bM C size u x
  refine ⟨(value u).1,(value u).2,fun x => (h x).1,?_⟩
  intro j d
  have eq : d = radianAction b (energyPartial j u) := funext fun x => (h x).2 j
  rw [eq, zero_mul, add_zero]
  exact value _

/-- The fixed infrared correction of the actual frozen multiplier, with
a constant uniform over a sphere-jet bounded family of frozen profiles. -/
theorem exists_frozen_fixed_infrared_difference_W13
    (cut add : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ) (D : ℝ) (D0 : 0 ≤ D) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧
      ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} →
        (∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) →
        (∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
          SchwartzOrderZeroJetBound (fun u => radianAction (fixedInfraredSymbol cut add b) u -
            radianAction b u) K 0 := by
  obtain ⟨K,Kfin,low⟩ := fixed_infrared_sphere_bound cut hcut 3 (by norm_num)
  obtain ⟨L,Lfin,more⟩ := fixedRadianProfile_Lp add hadd 3 (by norm_num)
  refine ⟨L+K*ENNReal.ofReal D, ENNReal.add_lt_top.mpr ⟨Lfin,ENNReal.mul_lt_top Kfin ENNReal.ofReal_lt_top⟩,?_⟩
  intro b hb hom jet
  let bcut (ξ : E) := fixedRadianProfile cut ξ * b ξ
  let r := fixedRadianProfile add
  have τp : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have mb := measurable_of_continuousOn_compl_singleton 0 hb.continuousOn
  have bb (ξ : E) : ‖b ξ‖ ≤ ‖ξ‖ * D := by
    have h := norm_symbol_shift_sub_le b hb hom D D0 (jet 1 (by decide)) ξ 0
    simpa only [zero_add, homogeneous_value_zero hom, sub_zero] using h
  have cutBound (ξ : E) : ‖bcut ξ‖ ≤ (tau * SchwartzMap.seminorm ℝ 1 0 cut) * D := by
    let ζ := tau⁻¹ • ξ
    have scale : ‖ξ‖ = tau * ‖ζ‖ := by
      dsimp only [ζ]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr τp.le), ← mul_assoc, mul_inv_cancel₀ τp.ne', one_mul]
    have h := SchwartzMap.norm_pow_mul_le_seminorm ℝ cut 1 ζ
    rw [pow_one] at h
    change ‖fixedRadianProfile cut ξ * b ξ‖ ≤ _
    rw [norm_mul]
    have weight : ‖fixedRadianProfile cut ξ‖ * ‖ξ‖ ≤ tau * SchwartzMap.seminorm ℝ 1 0 cut := by
      change ‖(cut ζ).re‖ * ‖ξ‖ ≤ _
      rw [← Complex.norm_real, hcut, scale]
      nlinarith only [mul_le_mul_of_nonneg_left h τp.le]
    exact (mul_le_mul_of_nonneg_left (bb ξ) (norm_nonneg _)).trans
      (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right weight D0)
  have Bcut := radian_multiplier_jet_bound_from_value bcut ((fixed_radian_profile_measurable cut).mul mb)
    _ cutBound (K*ENNReal.ofReal D) (low b hb hom D D0 jet)
  have Badd := radian_multiplier_jet_bound_from_value r (fixed_radian_profile_measurable add)
    _ (fixed_radian_profile_norm_bound add hadd) L more
  have rest := schwartz_order_zero_jet_bound_sub (radianAction r) (radianAction bcut) L 0
    (K*ENNReal.ofReal D) 0 Badd Bcut
  rw [add_zero] at rest
  have eq : (fun u => radianAction (fixedInfraredSymbol cut add b) u - radianAction b u) =
      (fun u => radianAction r u - radianAction bcut u) := by
    funext u x
    have same := congrFun (fixedInfraredSymbol_action cut add hcut hadd b hb hom u) x
    simp only [Pi.sub_apply, Pi.add_apply] at same
    change radianAction (fixedInfraredSymbol cut add b) u x - radianAction b u x =
      radianAction r u x - radianAction bcut u x
    rw [same]
    ring
  rw [eq]
  exact rest

end Burnett.A03
