import Burnett.Analysis.CubicEnergy.HighSlotCommutator.ComparableWeightedLowWindows
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.ComparableHighWindowSquare

set_option autoImplicit false
set_option maxHeartbeats 4400000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit Burnett.Analysis.CenteredMaximal
open MeasureTheory Finset Metric
open scoped ENNReal NNReal BigOperators

def normalizedRealCoefficientAmplitude (profile D : SchwartzMap E ℂ)
    (t : ℝ) (j : ℕ) (x : E) : ℝ≥0∞ :=
  ‖(dyadicScale t j)⁻¹*(windowTest profile D (dyadicScale t j) x).re‖ₑ

private theorem actualAmplitude_sq (profile D : SchwartzMap E ℂ) (t : ℝ) (j : ℕ) (x : E) :
    (normalizedRealCoefficientAmplitude profile D t j x)^2 = normalizedRealCoefficientSquare profile D t j x := by
  unfold normalizedRealCoefficientAmplitude normalizedRealCoefficientSquare
  rw [Real.enorm_eq_ofReal_abs,← ENNReal.ofReal_pow (abs_nonneg _),sq_abs]

private theorem amplitude_measurable (profile D : SchwartzMap E ℂ) (t : ℝ) (j : ℕ) :
    Measurable (normalizedRealCoefficientAmplitude profile D t j) := by
  have h : Continuous (fun x : E => (dyadicScale t j)⁻¹*(windowTest profile D (dyadicScale t j) x).re) :=
    continuous_const.mul (Complex.continuous_re.comp (windowTest profile D (dyadicScale t j)).continuous)
  exact h.enorm.measurable

private theorem window_enorm_measurable (a f : SchwartzMap E ℂ) (u t : ℝ) (j : ℕ) (Y : E) :
    Measurable (fun x => ‖shiftedTest a f u t j Y x‖ₑ) := by
  have cont : Continuous (fun x => shiftedTest a f u t j Y x) := by unfold shiftedTest; fun_prop
  exact cont.enorm.measurable

private theorem sq_half (z : ℝ≥0∞) : (z^2)^((1:ℝ)/2) = z := by
  rw [← ENNReal.rpow_natCast_mul]
  norm_num

private theorem half_sq (z : ℝ≥0∞) : (z^((1:ℝ)/2))^2 = z := by
  rw [← ENNReal.rpow_mul_natCast]
  norm_num

private theorem quartic_half (z : ℝ≥0∞) : (z^4)^((1:ℝ)/2) = z^2 := by
  rw [← ENNReal.rpow_natCast_mul]
  norm_num [ENNReal.rpow_two]

/-- When the output stays annular, the absolute paired product of the
normalized coefficient and the actual three windows sums uniformly. -/
theorem exists_comparableCoefficient_low_low_high_sum (profile a b e : SchwartzMap E ℂ)
    (hc : HasCompactSupport (profile : E → ℂ)) (he : HasCompactSupport (e : E → ℂ))
    (hprofile : ∀ z, profile z≠0 → 1/2<‖z‖ ∧ ‖z‖<2)
    (heAnn : ∀ z, e z≠0 → 1/2<‖z‖ ∧ ‖z‖<2) :
    ∃ C : ℝ≥0∞, C<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {t T : ℝ}, 0<t → ∀ (J : Finset ℕ), (∀ j ∈ J, dyadicScale t j≤T) →
      ∀ (f g h : SchwartzMap E ℂ) {u v w : ℝ}, 0<u → 0<v → 0<w → ∀ Y Z Q : E,
      (∑ j ∈ J, ∫⁻ x : E, normalizedRealCoefficientAmplitude profile D t j x *
        (‖shiftedTest a f u t j Y x‖ₑ*‖shiftedTest b g v t j Z x‖ₑ*‖shiftedTest e h w t j Q x‖ₑ)) ≤
        C*(L : ℝ≥0∞)*coefficientWindowShiftCost u Y*coefficientWindowShiftCost v Z*
          ENNReal.ofReal (1+‖(-w⁻¹) • Q‖)*triLpMass f g h 4 4 2 := by
  obtain ⟨C,hC,B⟩ := exists_realAnnularCoefficient_two_low_square_bound profile a b hc hprofile
  obtain ⟨H,_,hH,_,HS⟩ := exists_comparableHighWindowEnergy_moments e he heAnn
  refine ⟨C^((1:ℝ)/2)*H,ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC.ne) hH,?_⟩
  intro D L hD t T ht J hJ f g h u v w hu hv hw Y Z Q
  let U j (x : E) := normalizedRealCoefficientAmplitude profile D t j x *
    (‖shiftedTest a f u t j Y x‖ₑ*‖shiftedTest b g v t j Z x‖ₑ)
  let V j (x : E) := ‖shiftedTest e h w t j Q x‖ₑ
  have hU (j : ℕ) : Measurable (U j) := (amplitude_measurable profile D t j).mul
    ((window_enorm_measurable a f u t j Y).mul (window_enorm_measurable b g v t j Z))
  have hV (j : ℕ) : Measurable (V j) := window_enorm_measurable e h w t j Q
  have hnear : (∑ j ∈ J, ∫⁻ x : E, U j x^2) ≤
      C*(L : ℝ≥0∞)^2*(coefficientWindowShiftCost u Y)^2*(coefficientWindowShiftCost v Z)^2*
        eLpNorm (f : E → ℂ) 4 volume^2*eLpNorm (g : E → ℂ) 4 volume^2 := by
    simpa only [U,mul_pow,actualAmplitude_sq] using B D L hD ht J hJ f g hu hv Y Z
  have hfar : (∑ j ∈ J, ∫⁻ x : E, V j x^2) ≤
      (H*ENNReal.ofReal (1+‖(-w⁻¹) • Q‖)*eLpNorm (h : E → ℂ) 2 volume)^2 := by
    rw [← lintegral_finset_sum _ (fun j _ => (hV j).pow_const (2:ℕ))]
    exact (HS h hw ht J Q).1
  calc
    _ = ∑ j ∈ J, ∫⁻ x : E, U j x*V j x := by simp only [U,V,mul_assoc]
    _ ≤ _ := (comparable_finite_Cauchy J U V hU hV).trans
      ((mul_le_mul' (ENNReal.rpow_le_rpow hnear (by norm_num)) (ENNReal.rpow_le_rpow hfar (by norm_num))).trans_eq
        (by
          simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ)≤1/2),sq_half,triLpMass,
            ENNReal.ofReal_ofNat]
          ring))

private theorem exists_low_high_window_sq (a b : SchwartzMap E ℂ)
    (hb : HasCompactSupport (b : E → ℂ))
    (hAnn : ∀ z, b z≠0 → 1/2<‖z‖ ∧ ‖z‖<2) :
    ∃ C : ℝ≥0∞, C<⊤ ∧ ∀ (f g : SchwartzMap E ℂ) {u v t : ℝ}, 0<u → 0<v → 0<t →
      ∀ (J : Finset ℕ) (Y Z : E),
      (∑ j ∈ J, ∫⁻ x : E, (‖shiftedTest a f u t j Y x‖ₑ*‖shiftedTest b g v t j Z x‖ₑ)^2) ≤
        C*(coefficientWindowShiftCost u Y)^2*(ENNReal.ofReal (1+‖(-v⁻¹) • Z‖))^2*
          eLpNorm (f : E → ℂ) 4 volume^2*eLpNorm (g : E → ℂ) 4 volume^2 := by
  obtain ⟨K,hK,MB⟩ := exists_windowTest_ball_maximal_bound a
  obtain ⟨_,H₄,_,hH₄,B⟩ := exists_comparableHighWindowEnergy_moments b hb hAnn
  let M₄ := (maximalConstant 4)^((1:ℝ)/2)
  have hM₄ : M₄ < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) (maximalConstant_finite 4).ne
  refine ⟨K^2*M₄*H₄^2,ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top hK) hM₄)
    (ENNReal.pow_lt_top hH₄),?_⟩
  intro f g u v t hu hv ht J Y Z
  let F j (x : E) := ‖shiftedTest a f u t j Y x‖ₑ
  let G j (x : E) := ‖shiftedTest b g v t j Z x‖ₑ
  let W := K*coefficientWindowShiftCost u Y
  let U (x : E) := coefficientCenteredMax f x
  let V := comparableHighWindowEnergy b g v t J Z
  have hU : Measurable U := centeredMax_measurable _
  have hV : Measurable V := measurable_sum _ fun j _ => (window_enorm_measurable b g v t j Z).pow_const _
  have control (j : ℕ) (x : E) : F j x ≤ W*U x := MB f hu
    (show 0<dyadicScale t j by unfold dyadicScale; positivity) Y x x
    (mem_ball_self (by unfold dyadicScale; positivity))
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure E) Real.HolderConjugate.two_two
    (hU.pow_const (2:ℕ)).aemeasurable hV.aemeasurable
  simp only [Pi.mul_apply,ENNReal.rpow_two,← pow_mul,show (2:ℕ)*2=4 by decide] at hHolder
  have hUL : (∫⁻ x, U x^4)^((1:ℝ)/2) ≤ M₄ * eLpNorm (f : E → ℂ) 4 volume^2 := by
    have hh := ENNReal.rpow_le_rpow (coefficientCenteredMax_fourth_moment f) (by norm_num : (0:ℝ)≤1/2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),quartic_half] at hh
    exact hh
  have hVL : (∫⁻ x, V x^2)^((1:ℝ)/2) ≤
      (H₄*ENNReal.ofReal (1+‖(-v⁻¹) • Z‖)*eLpNorm (g : E → ℂ) 4 volume)^2 := by
    have hh := ENNReal.rpow_le_rpow (B g hv ht J Z).2 (by norm_num : (0:ℝ)≤1/2)
    rwa [quartic_half] at hh
  calc
    _ = ∫⁻ x : E, ∑ j ∈ J, (F j x*G j x)^2 := by
      rw [lintegral_finset_sum _ (fun j _ => ((window_enorm_measurable a f u t j Y).mul
        (window_enorm_measurable b g v t j Z)).pow_const (2:ℕ))]
    _ ≤ ∫⁻ x : E, W^2*(U x^2*V x) := by
      refine lintegral_mono fun x => ?_
      have point (j : ℕ) : (F j x*G j x)^2 ≤ W^2*(U x^2*G j x^2) := by
        exact (pow_le_pow_left' (mul_le_mul_right' (control j x) _) 2).trans_eq (by simp only [mul_pow]; ring)
      unfold V comparableHighWindowEnergy
      rw [mul_sum,mul_sum]
      exact sum_le_sum fun j _ => point j
    _ = W^2*(∫⁻ x : E, U x^2*V x) :=
      lintegral_const_mul' _ _ (ENNReal.pow_ne_top (ENNReal.mul_ne_top hK.ne ENNReal.ofReal_ne_top))
    _ ≤ W^2*((∫⁻ x : E, U x^4)^((1:ℝ)/2)*(∫⁻ x : E, V x^2)^((1:ℝ)/2)) :=
      mul_le_mul_left' hHolder _
    _ ≤ _ := (mul_le_mul_left' (mul_le_mul' hUL hVL) _).trans_eq (by
      simp only [W,mul_pow]
      ring)

/-- When the high input stays annular, the coefficient is paired with the
single low (L^2) output test. The remaining two operands have exponents
(4,4), giving the same trilinear mass as the other placement. -/
theorem exists_comparableCoefficient_low_high_low_sum (profile a b e : SchwartzMap E ℂ)
    (hc : HasCompactSupport (profile : E → ℂ)) (hb : HasCompactSupport (b : E → ℂ))
    (hprofile : ∀ z, profile z≠0 → 1/2<‖z‖ ∧ ‖z‖<2)
    (hbAnn : ∀ z, b z≠0 → 1/2<‖z‖ ∧ ‖z‖<2) :
    ∃ C : ℝ≥0∞, C<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {t T : ℝ}, 0<t → ∀ (J : Finset ℕ), (∀ j ∈ J, dyadicScale t j≤T) →
      ∀ (f g h : SchwartzMap E ℂ) {u v w : ℝ}, 0<u → 0<v → 0<w → ∀ Y Z Q : E,
      (∑ j ∈ J, ∫⁻ x : E, normalizedRealCoefficientAmplitude profile D t j x *
        (‖shiftedTest a f u t j Y x‖ₑ*‖shiftedTest b g v t j Z x‖ₑ*‖shiftedTest e h w t j Q x‖ₑ)) ≤
        C*(L : ℝ≥0∞)*coefficientWindowShiftCost u Y*ENNReal.ofReal (1+‖(-v⁻¹) • Z‖)*
          coefficientWindowShiftCost w Q*triLpMass f g h 4 4 2 := by
  obtain ⟨C,hC,A⟩ := exists_realAnnularCoefficient_one_low_square_bound profile e hc hprofile
  obtain ⟨H,hH,B⟩ := exists_low_high_window_sq a b hb hbAnn
  refine ⟨C^((1:ℝ)/2)*H^((1:ℝ)/2),ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC.ne)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hH.ne),?_⟩
  intro D L hD t T ht J hJ f g h u v w hu hv hw Y Z Q
  let U j (x : E) := normalizedRealCoefficientAmplitude profile D t j x * ‖shiftedTest e h w t j Q x‖ₑ
  let V j (x : E) := ‖shiftedTest a f u t j Y x‖ₑ * ‖shiftedTest b g v t j Z x‖ₑ
  have hU (j : ℕ) : Measurable (U j) :=
    (amplitude_measurable profile D t j).mul (window_enorm_measurable e h w t j Q)
  have hV (j : ℕ) : Measurable (V j) :=
    (window_enorm_measurable a f u t j Y).mul (window_enorm_measurable b g v t j Z)
  have hnear : (∑ j ∈ J, ∫⁻ x : E, U j x^2) ≤
      C*(L : ℝ≥0∞)^2*(coefficientWindowShiftCost w Q)^2*eLpNorm (h : E → ℂ) 2 volume^2 := by
    simpa only [U,mul_pow,actualAmplitude_sq] using A D L hD ht J hJ h hw Q
  have hfar : (∑ j ∈ J, ∫⁻ x : E, V j x^2) ≤
      H*(coefficientWindowShiftCost u Y)^2*(ENNReal.ofReal (1+‖(-v⁻¹) • Z‖))^2*
        eLpNorm (f : E → ℂ) 4 volume^2*eLpNorm (g : E → ℂ) 4 volume^2 :=
    B f g hu hv ht J Y Z
  calc
    _ = ∑ j ∈ J, ∫⁻ x : E, U j x*V j x := by
      refine sum_congr rfl fun j _ => lintegral_congr fun x => ?_
      unfold U V
      ring
    _ ≤ _ := (comparable_finite_Cauchy J U V hU hV).trans
      ((mul_le_mul' (ENNReal.rpow_le_rpow hnear (by norm_num)) (ENNReal.rpow_le_rpow hfar (by norm_num))).trans_eq
        (by
          simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ)≤1/2),sq_half,triLpMass,
            ENNReal.ofReal_ofNat]
          ring))

end Burnett.A06
