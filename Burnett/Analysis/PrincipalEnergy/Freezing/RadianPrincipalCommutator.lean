import Burnett.Analysis.PrincipalEnergy.Freezing.FixedTestOrderZeroAlgebra
import Burnett.Analysis.PrincipalEnergy.Freezing.FourierOrderZeroModeBounds
import Burnett.Analysis.PrincipalEnergy.Freezing.SchwartzOrderZeroCommutator

set_option autoImplicit false
set_option maxHeartbeats 3700000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal ContDiff FourierTransform

private def commutatorFourierShift (b : E → ℝ) (z : E × E) : ℝ :=
  b (z.2 + tau • z.1) - b z.2

private theorem commutator_fourier_average_eq (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (D : ℝ) (D0 : 0 ≤ D) (jet : ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ 1 b ξ‖ ≤ D) :
    let m := commutatorFourierShift b
    Measurable m ∧ RadianAverageGrowth m ∧
      ∀ (f u : SchwartzMap E ℂ), radianCommutator b f u = radianFourierAverage m f u := by
  intro m
  have τ0 : 0 ≤ tau := by unfold tau; positivity
  have bm := measurable_of_continuousOn_compl_singleton 0 hb.continuousOn
  have mm : Measurable m :=
    (bm.comp (measurable_snd.add (measurable_const.smul measurable_fst))).sub (bm.comp measurable_snd)
  have p (η ξ : E) : ‖m (η, ξ)‖ ≤ (tau * D) * ‖η‖ := by
    have h := norm_symbol_shift_sub_le b hb hom D D0 jet (tau • η) ξ
    rw [norm_smul, Real.norm_of_nonneg τ0] at h
    exact h.trans_eq (by ring)
  have C0 : 0 ≤ tau * D := mul_nonneg τ0 D0
  have mg : RadianAverageGrowth m := by
    refine ⟨tau * D,C0,fun η ξ => (p η _).trans ?_⟩
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) C0).trans
      (le_mul_of_one_le_right (mul_nonneg C0 (by positivity)) (le_add_of_nonneg_right (norm_nonneg _)))
  refine ⟨mm,mg,fun f u => funext fun x => ?_⟩
  rw [radian_fourier_average_eq_integral m mm mg, radian_commutator_shift_integral b hb hom D D0 jet]
  rfl

private theorem commutator_pointwise_le (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (D : ℝ) (D0 : 0 ≤ D) (jet : ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ 1 b ξ‖ ≤ D)
    (f u : SchwartzMap E ℂ) (x : E) :
    ‖radianCommutator b f u x‖ ≤ tau * D * patchFourierMoment 1 f * patchFourierMoment 0 u := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let W (η : E) := ‖η‖ * ‖F η‖
  let C := tau * D * patchFourierMoment 0 u
  have τ0 : 0 ≤ tau := by unfold tau; positivity
  have WI : Integrable W volume := by simpa only [W, pow_one] using F.integrable_pow_mul volume 1
  have eq : tau * D * patchFourierMoment 1 f * patchFourierMoment 0 u = ∫ η : E, C * W η := by
    rw [integral_const_mul]
    simp only [C, patchFourierMoment, pow_one, W, F, SchwartzMap.fourierTransformCLM_apply]
    ring
  rw [radian_commutator_shift_integral b hb hom D D0 jet, eq]
  apply norm_integral_le_of_norm_le (WI.const_mul C)
  filter_upwards with η
  simp only [norm_mul, patch_fourier_phase_norm, one_mul]
  have bnd (ξ : E) : ‖b (ξ + tau • η) - b ξ‖ ≤ tau * ‖η‖ * D := by
    simpa only [norm_smul, Real.norm_of_nonneg τ0] using norm_symbol_shift_sub_le b hb hom D D0 jet (tau • η) ξ
  let m (ξ : E) := b (ξ + tau • η) - b ξ
  have h := norm_radian_action_le_of_symbol_bound m _ bnd u x
  calc
    _ ≤ ‖F η‖ * (tau * ‖η‖ * D * ∫ ξ, ‖𝓕 (u : E → ℂ) ξ‖) :=
      mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = _ := by simp only [C, W, patchFourierMoment, pow_zero, one_mul]; ring

/-- The genuine commutator with a cutoff of a homogeneous multiplier,
including the exact continuous first jet required for a space Fourier sum. -/
theorem radian_commutator_pointwise_and_coordinate (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (D : ℝ) (D0 : 0 ≤ D) (jet : ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ 1 b ξ‖ ≤ D)
    (f u : SchwartzMap E ℂ) :
    (∀ x, ‖radianCommutator b f u x‖ ≤ tau * D * patchFourierMoment 1 f * patchFourierMoment 0 u) ∧
      Differentiable ℝ (radianCommutator b f u) ∧
      ∀ j : Index, let d := actualCoordinateJet (radianCommutator b f u) j
        Continuous d ∧ d = radianCommutator b (energyPartial j f) u + radianCommutator b f (energyPartial j u) := by
  obtain ⟨mm,mg,eq⟩ := commutator_fourier_average_eq b hb hom D D0 jet
  let m := commutatorFourierShift b
  have diff (s v : SchwartzMap E ℂ) : Differentiable ℝ (radianCommutator b s v) := by
    rw [eq]
    exact fun x => (radian_fourier_average_coordinate m mm mg s v 0 x).1
  refine ⟨commutator_pointwise_le b hb hom D D0 jet f u,diff f u,?_⟩
  intro j d
  have same : d = radianCommutator b (energyPartial j f) u + radianCommutator b f (energyPartial j u) := by
    change actualCoordinateJet (radianCommutator b f u) j = _
    simp only [eq]
    exact funext fun x => (radian_fourier_average_coordinate m mm mg f u j x).2
  exact ⟨same.symm ▸ (diff _ _).continuous.add (diff _ _).continuous, same⟩

/-- The fixed-cutoff actual commutator has both value and first-jet
estimates, using one and two Fourier moments of the fixed cutoff. -/
theorem exists_radian_commutator_order_zero_W13 :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} →
        (∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) →
        ∀ D : ℝ, 0 ≤ D →
        (∀ n : ℕ, n ≤ 7 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
        ∀ f : SchwartzMap E ℂ,
          SchwartzOrderZeroJetBound (radianCommutator b f)
            (ENNReal.ofReal (K * D * patchFourierMoment 1 f))
            (ENNReal.ofReal (K * D * tau * patchFourierMoment 2 f)) := by
  obtain ⟨K,K0,old⟩ := exists_radian_commutator_order_zero_L3_bound
  refine ⟨K,K0,?_⟩
  intro b hb hom D D0 jet f u
  let p := ENNReal.ofReal 3
  have h := radian_commutator_pointwise_and_coordinate b hb hom D D0 (jet 1 (by decide)) f u
  have e (g v : SchwartzMap E ℂ) := old b hb hom D D0 jet g v
  refine ⟨(e f u).1,(e f u).2,h.2.1,?_⟩
  intro j d
  have eq : d = radianCommutator b (energyPartial j f) u + radianCommutator b f (energyPartial j u) := (h.2.2 j).2
  rw [eq]
  have a := e (energyPartial j f) u
  have b' := e f (energyPartial j u)
  have grow : K * D * patchFourierMoment 1 (energyPartial j f) ≤ K * D * tau * patchFourierMoment 2 f := by
    rw [mul_assoc (K * D)]
    exact mul_le_mul_of_nonneg_left (patch_fourier_moment_partial 1 j f) (mul_nonneg K0 D0)
  refine ⟨a.1.add b'.1,(eLpNorm_add_le a.1.1 b'.1.1 (by norm_num [p])).trans ?_⟩
  rw [add_comm]
  exact add_le_add b'.2 (a.2.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal grow) _))

end Burnett.A03
