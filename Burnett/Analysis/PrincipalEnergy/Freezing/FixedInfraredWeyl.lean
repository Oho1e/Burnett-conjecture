import Burnett.Analysis.PrincipalEnergy.Freezing.WeylPhysicalKernel
import Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedInfraredStructure
import Burnett.Analysis.PrincipalEnergy.Freezing.ModeFourierMoment

set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ContDiff ENNReal FourierTransform Topology

/-- A bounded frequency multiplier with an established L³ bound gives a
separated order-zero quantization, uniformly in the slant parameter. -/
theorem separated_radian_order_zero_W13 (m : E → ℝ) (hm : Measurable m)
    (A : ℝ) (A0 : 0 ≤ A) (sup : ∀ ξ, ‖m ξ‖ ≤ A)
    (LpBound : ∀ u : SchwartzMap E ℂ, MemLp (radianAction m u) (ENNReal.ofReal 3) volume ∧
      eLpNorm (radianAction m u) (ENNReal.ofReal 3) volume ≤
        ENNReal.ofReal A * eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume)
    (σ : ℝ) (f u : SchwartzMap E ℂ) :
    let p := ENNReal.ofReal 3
    let W := separatedRadianQuantization σ m f u
    MemLp W p volume ∧
      eLpNorm W p volume ≤ ENNReal.ofReal (A * patchFourierMoment 0 f) * eLpNorm (u : E → ℂ) p volume ∧
      Differentiable ℝ W ∧
      ∀ j : Index, let d (x : E) := fderiv ℝ W x (EuclideanSpace.single j 1)
        MemLp d p volume ∧ eLpNorm d p volume ≤
          ENNReal.ofReal (A * patchFourierMoment 0 f) * eLpNorm (energyPartial j u : E → ℂ) p volume +
          ENNReal.ofReal (A * tau * patchFourierMoment 1 f) * eLpNorm (u : E → ℂ) p volume := by
  intro p W
  let mσ := slantedRadianSymbol σ m
  have meas : Measurable mσ := slanted_radian_symbol_measurable σ m hm
  have grow : RadianAverageGrowth mσ := slanted_radian_symbol_growth σ m A A0 fun ξ =>
    (sup ξ).trans (le_mul_of_one_le_right A0 (le_add_of_nonneg_right (norm_nonneg _)))
  have value (g v : SchwartzMap E ℂ) :
      MemLp (radianFourierAverage mσ g v) p volume ∧
        eLpNorm (radianFourierAverage mσ g v) p volume ≤
          ENNReal.ofReal (A * patchFourierMoment 0 g) * eLpNorm (v : E → ℂ) p volume := by
    let F := SchwartzMap.fourierTransformCLM ℂ g
    have int : Integrable (fun η => A * ‖𝓕 (g : E → ℂ) η‖) := F.integrable.norm.const_mul A
    have vFin := (v.memLp p volume).eLpNorm_lt_top
    have est (η : E) := radian_shift_preserves_L3_bound m (ENNReal.ofReal A) LpBound (σ • η) v
    simpa only [patchFourierMoment, pow_zero, one_mul, integral_const_mul] using
      radian_fourier_average_L3_bound mσ meas grow g v (fun _ => A) (fun _ => A0)
        (fun _ _ => sup _) int _ vFin est
  refine ⟨(value f u).1, (value f u).2, ?_, ?_⟩
  · exact fun x => (radian_fourier_average_coordinate mσ meas grow f u 0 x).1
  · intro j d
    have eq : d = radianFourierAverage mσ (energyPartial j f) u + radianFourierAverage mσ f (energyPartial j u) :=
      funext fun x => (radian_fourier_average_coordinate mσ meas grow f u j x).2
    rw [eq]
    have first := value (energyPartial j f) u
    have second := value f (energyPartial j u)
    have mass := patch_fourier_moment_partial 0 j f
    have coeff := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left mass A0)
    rw [← mul_assoc] at coeff
    refine ⟨first.1.add second.1, (eLpNorm_add_le first.1.1 second.1.1 (by norm_num [p])).trans ?_⟩
    exact (add_le_add (first.2.trans (mul_le_mul_right' coeff _)) second.2).trans_eq (add_comm _ _)

private theorem radian_action_bounded_sub (a b : E → ℝ) (ha : Measurable a) (hb : Measurable b)
    (A B : ℝ) (supA : ∀ ξ, ‖a ξ‖ ≤ A) (supB : ∀ ξ, ‖b ξ‖ ≤ B) (u : SchwartzMap E ℂ) :
    radianAction (fun ξ => a ξ - b ξ) u = radianAction a u - radianAction b u := by
  let U := SchwartzMap.fourierTransformCLM ℂ u
  funext x
  have pM : Measurable (fun ξ : E => patchFourierPhase ξ x) := by
    let args : E → E × E := fun ξ => (ξ, x)
    have argsC : Continuous args := continuous_id.prodMk continuous_const
    exact (patch_fourier_phase_continuous.comp argsC).measurable
  have sm : Measurable (fun ξ : E => tau • ξ) := (continuous_const.smul continuous_id).measurable
  have int (m : E → ℝ) (hm : Measurable m) (M : ℝ) (sup : ∀ ξ, ‖m ξ‖ ≤ M) :
      Integrable (fun ξ => patchFourierPhase ξ x * ((m (tau • ξ) : ℂ) * U ξ)) := by
    refine (U.integrable.norm.const_mul M).mono'
      (pM.mul ((Complex.continuous_ofReal.measurable.comp (hm.comp sm)).mul U.continuous.measurable)).aestronglyMeasurable ?_
    filter_upwards with ξ
    simp only [norm_mul, patch_fourier_phase_norm, one_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (sup _) (norm_nonneg _)
  simp only [Pi.sub_apply, radian_action_fourier_integral]
  change (∫ ξ, patchFourierPhase ξ x * (((a (tau • ξ) - b (tau • ξ) : ℝ) : ℂ) * U ξ)) =
    (∫ ξ, patchFourierPhase ξ x * ((a (tau • ξ) : ℂ) * U ξ)) -
      ∫ ξ, patchFourierPhase ξ x * ((b (tau • ξ) : ℂ) * U ξ)
  rw [← integral_sub (int a ha A supA) (int b hb B supB)]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [Complex.ofReal_sub]
  ring

/-- The fixed infrared difference is the literal difference of the
regularized and homogeneous quantizations. Its constant is determined by
the fixed profiles, separately from the angular jet bound of the mode. -/
theorem exists_fixed_infrared_quantization_difference_W13 (cut add : SchwartzMap E ℂ)
    (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ) (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ)
    (plateau : ∀ᶠ ζ in 𝓝 (0 : E), fixedRadianProfile cut ζ = 1) :
    ∃ Kc Ka : ℝ, 0 ≤ Kc ∧ 0 ≤ Ka ∧
      ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ (σ : ℝ) (f u : SchwartzMap E ℂ),
        let p := ENNReal.ofReal 3
        let A := Kc * D + Ka
        let W := separatedRadianQuantization σ (fixedInfraredSymbol cut add b) f u -
          separatedRadianQuantization σ b f u
        MemLp W p volume ∧
          eLpNorm W p volume ≤ ENNReal.ofReal (A * patchFourierMoment 0 f) * eLpNorm (u : E → ℂ) p volume ∧
          Differentiable ℝ W ∧
          ∀ j : Index, let d (x : E) := fderiv ℝ W x (EuclideanSpace.single j 1)
            MemLp d p volume ∧ eLpNorm d p volume ≤
              ENNReal.ofReal (A * patchFourierMoment 0 f) * eLpNorm (energyPartial j u : E → ℂ) p volume +
              ENNReal.ofReal (A * tau * patchFourierMoment 1 f) * eLpNorm (u : E → ℂ) p volume := by
  obtain ⟨K, Kfin, lower⟩ := fixed_infrared_sphere_bound cut hcut 3 (by norm_num)
  obtain ⟨L, Lfin, extra⟩ := fixedRadianProfile_Lp add hadd 3 (by norm_num)
  have τp : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  let CA := SchwartzMap.seminorm ℝ 0 0 add
  let BC := tau * SchwartzMap.seminorm ℝ 1 0 cut
  let Kc := max BC K.toReal
  let Ka := max CA L.toReal
  have Kc0 : 0 ≤ Kc := ENNReal.toReal_nonneg.trans (le_max_right _ _)
  have Ka0 : 0 ≤ Ka := ENNReal.toReal_nonneg.trans (le_max_right _ _)
  refine ⟨Kc, Ka, Kc0, Ka0, ?_⟩
  intro b hb hom D D0 jet σ f u p A W
  let r := fixedRadianProfile add
  let c (ξ : E) := fixedRadianProfile cut ξ * b ξ
  let m (ξ : E) := r ξ - c ξ
  let reg := fixedInfraredSymbol cut add b
  have A0 : 0 ≤ A := add_nonneg (mul_nonneg Kc0 D0) Ka0
  have bc (ξ : E) : ‖b ξ‖ ≤ ‖ξ‖ * D := by
    have e := norm_symbol_shift_sub_le b hb hom D D0 (jet 1 (by decide)) ξ 0
    simpa only [zero_add, homogeneous_value_zero hom, sub_zero] using e
  have rM : Measurable r := fixed_radian_profile_measurable add
  have bM := measurable_of_continuousOn_compl_singleton 0 hb.continuousOn
  have cM : Measurable c := (fixed_radian_profile_measurable cut).mul bM
  have cSup (ξ : E) : ‖c ξ‖ ≤ Kc * D := by
    let ζ := tau⁻¹ • ξ
    have scale : ‖ξ‖ = tau * ‖ζ‖ := by
      dsimp only [ζ]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr τp.le), ← mul_assoc, mul_inv_cancel₀ τp.ne', one_mul]
    have weight : ‖fixedRadianProfile cut ξ‖ * ‖ξ‖ ≤ BC := by
      change ‖(cut ζ).re‖ * ‖ξ‖ ≤ BC
      rw [← Complex.norm_real, hcut, scale]
      have e := SchwartzMap.norm_pow_mul_le_seminorm ℝ cut 1 ζ
      rw [pow_one] at e
      exact (by dsimp only [BC]; nlinarith only [mul_le_mul_of_nonneg_left e τp.le] :
        ‖cut ζ‖ * (tau * ‖ζ‖) ≤ BC)
    dsimp only [c]
    rw [norm_mul]
    calc
      _ ≤ ‖fixedRadianProfile cut ξ‖ * (‖ξ‖ * D) := mul_le_mul_of_nonneg_left (bc ξ) (norm_nonneg _)
      _ ≤ BC * D := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right weight D0
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) D0
  have rSup (ξ : E) : ‖r ξ‖ ≤ Ka := (fixed_radian_profile_norm_bound add hadd ξ).trans (le_max_left _ _)
  have mSup (ξ : E) : ‖m ξ‖ ≤ A := (norm_sub_le _ _).trans
    ((add_le_add (rSup ξ) (cSup ξ)).trans_eq (add_comm _ _))
  have sec (v : SchwartzMap E ℂ) :
      MemLp (radianAction m v) p volume ∧ eLpNorm (radianAction m v) p volume ≤
        ENNReal.ofReal A * eLpNorm (v : E → ℂ) p volume := by
    have sub := radian_action_bounded_sub r c rM cM Ka (Kc * D) rSup cSup v
    change radianAction m v = _ at sub
    rw [sub]
    have ha := extra v
    have hc := lower b hb hom D D0 jet v
    refine ⟨ha.1.sub hc.1, (eLpNorm_sub_le ha.1.1 hc.1.1 (by norm_num [p])).trans ?_⟩
    have lBound : L ≤ ENNReal.ofReal Ka := by
      rw [← ENNReal.ofReal_toReal Lfin.ne]
      exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
    have kBound : K ≤ ENNReal.ofReal Kc := by
      rw [← ENNReal.ofReal_toReal Kfin.ne]
      exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
    calc
      _ ≤ (ENNReal.ofReal Ka * eLpNorm (v : E → ℂ) p volume) +
          ((ENNReal.ofReal Kc * ENNReal.ofReal D) * eLpNorm (v : E → ℂ) p volume) :=
        add_le_add (ha.2.trans (mul_le_mul_right' lBound _))
          (hc.2.trans (mul_le_mul_right' (mul_le_mul_right' kBound _) _))
      _ = _ := by
        dsimp only [A]
        rw [ENNReal.ofReal_add (mul_nonneg Kc0 D0) Ka0, ENNReal.ofReal_mul Kc0, add_mul, add_comm]
  have diff (ξ : E) : reg ξ - b ξ = m ξ := by dsimp only [reg, fixedInfraredSymbol, m, r, c]; ring
  have regM : Measurable reg := (fixedInfraredSymbol_smooth cut add b hb plateau).continuous.measurable
  have regBase (ξ : E) : reg ξ = b ξ + m ξ := by linarith only [diff ξ]
  have regBound (ξ : E) : ‖reg ξ‖ ≤ (D + A) * (1 + ‖ξ‖) := by
    rw [regBase]
    exact (norm_add_le _ _).trans ((add_le_add (bc ξ) (mSup ξ)).trans (by
      nlinarith only [D0, A0, mul_nonneg A0 (norm_nonneg ξ)]))
  have bBound (ξ : E) : ‖b ξ‖ ≤ D * (1 + ‖ξ‖) := (bc ξ).trans (by nlinarith only [D0])
  have eq : W = separatedRadianQuantization σ m f u := by
    change radianFourierAverage (slantedRadianSymbol σ reg) f u -
      radianFourierAverage (slantedRadianSymbol σ b) f u = _
    rw [← radian_fourier_average_sub _ _ (slanted_radian_symbol_measurable σ reg regM)
      (slanted_radian_symbol_measurable σ b bM) (slanted_radian_symbol_growth σ reg (D + A) (add_nonneg D0 A0) regBound)
      (slanted_radian_symbol_growth σ b D D0 bBound)]
    congr 1
    exact funext fun z => diff (z.2 + tau • (σ • z.1))
  rw [eq]
  exact separated_radian_order_zero_W13 m (rM.sub cM) A A0 mSup sec σ f u

end Burnett.A03
