import Burnett.Analysis.CubicEnergy.HighSlotCommutator.ComparableRealCoefficientEmbedding
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.ComparableLocalWindowMajorant

set_option autoImplicit false
set_option maxHeartbeats 3800000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open Burnett.Analysis.CenteredMaximal
open MeasureTheory Metric Finset
open scoped ENNReal NNReal BigOperators

def coefficientWindowShiftCost (u : ℝ) (Y : E) : ℝ≥0∞ :=
  ENNReal.ofReal ((1+u⁻¹*(‖Y‖+1))^5)

def normalizedRealCoefficientSquare (profile D : SchwartzMap E ℂ) (t : ℝ) (j : ℕ) (x : E) : ℝ≥0∞ :=
  ENNReal.ofReal (((dyadicScale t j)⁻¹*(windowTest profile D (dyadicScale t j) x).re)^2)

def coefficientCenteredMax (f : SchwartzMap E ℂ) (x : E) : ℝ≥0∞ :=
  centeredMax (fun y => ‖f y‖ₑ) x

private abbrev centeredSchwartz := coefficientCenteredMax

private theorem centeredSchwartz_measurable (f : SchwartzMap E ℂ) : Measurable (centeredSchwartz f) :=
  centeredMax_measurable _

private theorem centeredSchwartz_finite (f : SchwartzMap E ℂ) (x : E) :
    centeredSchwartz f x ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (centeredMax_le_const _
    (ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 f)) (fun y => ?_) x)
  rw [← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal (SchwartzMap.norm_le_seminorm ℝ f y)

private theorem localWindow_real_bound {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (f : SchwartzMap E ℂ) (x : E) {z : ℂ} (h : ‖z‖ₑ ≤ B*centeredSchwartz f x) :
    ‖z‖ ≤ (B*centeredSchwartz f x).toReal := by
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hB (centeredSchwartz_finite f x)) h
  simpa only [← ofReal_norm_eq_enorm,ENNReal.toReal_ofReal (norm_nonneg _)] using h

private theorem integral_sq_maximal (f : SchwartzMap E ℂ) :
    (∫⁻ x : E, centeredSchwartz f x^2) ≤ maximalConstant 2 * eLpNorm (f : E → ℂ) 2 volume^2 := by
  have h : eLpNorm (centeredSchwartz f) 2 volume ≤
      maximalConstant 2 ^ ((1:ℝ)/2) * eLpNorm (f : E → ℂ) 2 volume := by
    simpa only [centeredSchwartz,coefficientCenteredMax,ENNReal.ofReal_ofNat] using
      centeredMax_complex_Lp (f : E → ℂ) f.continuous.measurable 2 (by norm_num)
  have h2 := pow_le_pow_left' h 2
  have ep : eLpNorm (centeredSchwartz f) 2 volume ^ (2:ℕ) =
      ∫⁻ x : E, centeredSchwartz f x^2 := by
    simpa using eLpNorm_nnreal_pow_eq_lintegral (μ := (volume : Measure E))
      (f := centeredSchwartz f) (p := 2) (by norm_num)
  rw [ep,mul_pow,← ENNReal.rpow_mul_natCast] at h2
  norm_num at h2
  exact h2

/-- The comparable-coefficient square bound with a single actual low-pass
L² operand. This is the weighted factor when the high input remains annular. -/
theorem exists_realAnnularCoefficient_one_low_square_bound (profile a : SchwartzMap E ℂ)
    (hc : HasCompactSupport (profile : E → ℂ))
    (hAnn : ∀ z, profile z ≠ 0 → 1/2 < ‖z‖ ∧ ‖z‖ < 2) :
    ∃ C : ℝ≥0∞, C<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {t T : ℝ}, 0<t → ∀ (J : Finset ℕ), (∀ j ∈ J, dyadicScale t j≤T) →
      ∀ (f : SchwartzMap E ℂ) {u : ℝ}, 0<u → ∀ Y : E,
      (∑ j ∈ J, ∫⁻ x : E, normalizedRealCoefficientSquare profile D t j x *
        ‖shiftedTest a f u t j Y x‖ₑ^2) ≤
        C*(L : ℝ≥0∞)^2*(coefficientWindowShiftCost u Y)^2*eLpNorm (f : E → ℂ) 2 volume^2 := by
  obtain ⟨C,hC,embed⟩ := exists_realAnnularCoefficient_embedded_square_bound profile hc hAnn
  obtain ⟨K,hK,maxBound⟩ := exists_windowTest_ball_maximal_bound a
  have hKsq : K^2 < ⊤ := ENNReal.pow_lt_top hK
  refine ⟨C*K^2*maximalConstant 2,ENNReal.mul_lt_top (ENNReal.mul_lt_top hC hKsq)
    (maximalConstant_finite 2),?_⟩
  intro D L hD t T ht J hJ f u hu Y
  let H := K*coefficientWindowShiftCost u Y
  let G j (x : E) := ‖shiftedTest a f u t j Y x‖
  let M (x : E) := (H*centeredSchwartz f x).toReal
  have hf : H ≠ ⊤ := ENNReal.mul_ne_top hK.ne ENNReal.ofReal_ne_top
  have hG (j : ℕ) : Measurable (G j) := by
    dsimp only [G,shiftedTest]
    fun_prop
  have hM : Measurable M := (measurable_const.mul (centeredSchwartz_measurable f)).ennreal_toReal
  have hdom (j : ℕ) (_hj : j∈J) (x y : E) (hy : y∈ball x (dyadicScale t j)) :
      G j x ≤ M y := by
    have hs : 0<dyadicScale t j := by unfold dyadicScale; positivity
    exact localWindow_real_bound hf f y (maxBound f hu hs Y x y hy)
  have est := embed D L hD ht J hJ G M hG (fun _ _ => norm_nonneg _) hM
    (fun _ => ENNReal.toReal_nonneg) hdom
  have hWeight (x : E) : ENNReal.ofReal ((M x)^2) = H^2*centeredSchwartz f x^2 := by
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg]
    rw [ENNReal.ofReal_toReal (ENNReal.mul_ne_top hf (centeredSchwartz_finite f x)),mul_pow]
  simp only [G,ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm_eq_enorm] at est
  calc
    _ ≤ C*(L : ℝ≥0∞)^2 * ∫⁻ x : E, ENNReal.ofReal ((M x)^2) := est
    _ = C*(L : ℝ≥0∞)^2*(H^2*(∫⁻ x : E, centeredSchwartz f x^2)) := by
      simp_rw [hWeight]
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top hf)]
    _ ≤ _ := (mul_le_mul_left' (mul_le_mul_left' (integral_sq_maximal f) _) _).trans_eq (by
      simp only [H,mul_pow]
      ring)

theorem coefficientCenteredMax_fourth_moment (f : SchwartzMap E ℂ) :
    (∫⁻ x : E, coefficientCenteredMax f x^4) ≤ maximalConstant 4 * eLpNorm (f : E → ℂ) 4 volume^4 := by
  have h : eLpNorm (centeredSchwartz f) 4 volume ≤
      maximalConstant 4 ^ ((1:ℝ)/4) * eLpNorm (f : E → ℂ) 4 volume := by
    simpa only [centeredSchwartz,coefficientCenteredMax,ENNReal.ofReal_ofNat] using
      centeredMax_complex_Lp (f : E → ℂ) f.continuous.measurable 4 (by norm_num)
  have h4 := pow_le_pow_left' h 4
  have ep : eLpNorm (centeredSchwartz f) 4 volume ^ (4:ℕ) =
      ∫⁻ x : E, centeredSchwartz f x^4 := by
    simpa using eLpNorm_nnreal_pow_eq_lintegral (μ := (volume : Measure E))
      (f := centeredSchwartz f) (p := 4) (by norm_num)
  rw [ep,mul_pow,← ENNReal.rpow_mul_natCast] at h4
  norm_num at h4
  exact h4

private theorem integral_sq_maximal_product (f g : SchwartzMap E ℂ) :
    (∫⁻ x : E, centeredSchwartz f x^2*centeredSchwartz g x^2) ≤
      maximalConstant 4 * eLpNorm (f : E → ℂ) 4 volume^2 * eLpNorm (g : E → ℂ) 4 volume^2 := by
  have hold := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure E) Real.HolderConjugate.two_two
    ((centeredSchwartz_measurable f).pow_const (2:ℕ)).aemeasurable
    ((centeredSchwartz_measurable g).pow_const (2:ℕ)).aemeasurable
  simp only [Pi.mul_apply,ENNReal.rpow_two,← pow_mul,show (2:ℕ)*2=4 by norm_num] at hold
  have step (D : SchwartzMap E ℂ) :
      (∫⁻ x : E, centeredSchwartz D x^4)^((1:ℝ)/2) ≤
        (maximalConstant 4)^((1:ℝ)/2)*eLpNorm (D : E → ℂ) 4 volume^2 := by
    have h := ENNReal.rpow_le_rpow (coefficientCenteredMax_fourth_moment D) (by norm_num : (0:ℝ)≤1/2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),← ENNReal.rpow_natCast_mul] at h
    norm_num at h
    simpa only [ENNReal.rpow_two] using h
  refine hold.trans ((mul_le_mul' (step f) (step g)).trans_eq ?_)
  calc
    _ = ((maximalConstant 4)^((1:ℝ)/2)*(maximalConstant 4)^((1:ℝ)/2)) *
        eLpNorm (f : E → ℂ) 4 volume^2 * eLpNorm (g : E → ℂ) 4 volume^2 := by ring
    _ = _ := by
      have eq : (maximalConstant 4)^((1:ℝ)/2)*(maximalConstant 4)^((1:ℝ)/2) = maximalConstant 4 := by
        rw [← ENNReal.rpow_add_of_nonneg ((1:ℝ)/2) ((1:ℝ)/2) (by norm_num) (by norm_num),
          show (1:ℝ)/2+1/2 = 1 by norm_num, ENNReal.rpow_one]
      rw [eq]

/-- The comparable-coefficient square bound with two actual low-pass L⁴
operands. This is the weighted factor when the output test remains annular. -/
theorem exists_realAnnularCoefficient_two_low_square_bound (profile a b : SchwartzMap E ℂ)
    (hc : HasCompactSupport (profile : E → ℂ))
    (hAnn : ∀ z, profile z ≠ 0 → 1/2 < ‖z‖ ∧ ‖z‖ < 2) :
    ∃ C : ℝ≥0∞, C<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {t T : ℝ}, 0<t → ∀ (J : Finset ℕ), (∀ j ∈ J, dyadicScale t j≤T) →
      ∀ (f g : SchwartzMap E ℂ) {u v : ℝ}, 0<u → 0<v → ∀ Y Z : E,
      (∑ j ∈ J, ∫⁻ x : E, normalizedRealCoefficientSquare profile D t j x *
        (‖shiftedTest a f u t j Y x‖ₑ^2*‖shiftedTest b g v t j Z x‖ₑ^2)) ≤
        C*(L : ℝ≥0∞)^2*(coefficientWindowShiftCost u Y)^2*(coefficientWindowShiftCost v Z)^2*
          eLpNorm (f : E → ℂ) 4 volume^2*eLpNorm (g : E → ℂ) 4 volume^2 := by
  obtain ⟨C,hC,embed⟩ := exists_realAnnularCoefficient_embedded_square_bound profile hc hAnn
  obtain ⟨K,hK,maxBoundA⟩ := exists_windowTest_ball_maximal_bound a
  obtain ⟨N,hN,maxBoundB⟩ := exists_windowTest_ball_maximal_bound b
  refine ⟨C*K^2*N^2*maximalConstant 4,ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC (ENNReal.pow_lt_top hK)) (ENNReal.pow_lt_top hN))
    (maximalConstant_finite 4),?_⟩
  intro D L hD t T ht J hJ f g u v hu hv Y Z
  let H := K*coefficientWindowShiftCost u Y
  let I := N*coefficientWindowShiftCost v Z
  let G j (x : E) := ‖shiftedTest a f u t j Y x‖*‖shiftedTest b g v t j Z x‖
  let M (x : E) := (H*centeredSchwartz f x*(I*centeredSchwartz g x)).toReal
  have hf : H ≠ ⊤ := ENNReal.mul_ne_top hK.ne ENNReal.ofReal_ne_top
  have hg : I ≠ ⊤ := ENNReal.mul_ne_top hN.ne ENNReal.ofReal_ne_top
  have hG (j : ℕ) : Measurable (G j) := by
    dsimp only [G,shiftedTest]
    fun_prop
  have hM : Measurable M := ((measurable_const.mul (centeredSchwartz_measurable f)).mul
    (measurable_const.mul (centeredSchwartz_measurable g))).ennreal_toReal
  have hdom (j : ℕ) (_hj : j∈J) (x y : E) (hy : y∈ball x (dyadicScale t j)) :
      G j x ≤ M y := by
    have hs : 0<dyadicScale t j := by unfold dyadicScale; positivity
    change _ ≤ (H*centeredSchwartz f y*(I*centeredSchwartz g y)).toReal
    rw [ENNReal.toReal_mul]
    exact mul_le_mul (localWindow_real_bound hf f y (maxBoundA f hu hs Y x y hy))
      (localWindow_real_bound hg g y (maxBoundB g hv hs Z x y hy))
      (norm_nonneg _) ENNReal.toReal_nonneg
  have est := embed D L hD ht J hJ G M hG (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    hM (fun _ => ENNReal.toReal_nonneg) hdom
  have hWeight (x : E) : ENNReal.ofReal ((M x)^2) =
      (H^2*I^2)*(centeredSchwartz f x^2*centeredSchwartz g x^2) := by
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hf (centeredSchwartz_finite f x))
      (ENNReal.mul_ne_top hg (centeredSchwartz_finite g x)))]
    simp only [mul_pow]
    ring
  have weightG (j : ℕ) (x : E) : ENNReal.ofReal ((G j x)^2) =
      ‖shiftedTest a f u t j Y x‖ₑ^2*‖shiftedTest b g v t j Z x‖ₑ^2 := by
    simp only [G,mul_pow,ENNReal.ofReal_mul (sq_nonneg _),ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm]
  simp_rw [weightG] at est
  calc
    _ ≤ C*(L : ℝ≥0∞)^2 * ∫⁻ x : E, ENNReal.ofReal ((M x)^2) := est
    _ = C*(L : ℝ≥0∞)^2*(H^2*I^2*(∫⁻ x : E, centeredSchwartz f x^2*centeredSchwartz g x^2)) := by
      simp_rw [hWeight]
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.pow_ne_top hf) (ENNReal.pow_ne_top hg))]
    _ ≤ _ := (mul_le_mul_left' (mul_le_mul_left' (integral_sq_maximal_product f g) _) _).trans_eq (by
      simp only [H,I,mul_pow]
      ring)

end Burnett.A06
