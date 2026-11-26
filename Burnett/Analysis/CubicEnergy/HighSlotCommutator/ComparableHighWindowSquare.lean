import Burnett.Analysis.CubicEnergy.JointMultiplier.JointDyadicWindows

set_option autoImplicit false
set_option maxHeartbeats 3700000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Finset
open scoped ENNReal BigOperators

def comparableHighWindowEnergy (a f : SchwartzMap E ℂ) (u t : ℝ)
    (J : Finset ℕ) (Y x : E) : ℝ≥0∞ := ∑ j ∈ J, ‖shiftedTest a f u t j Y x‖ₑ^2

private def highWindowRoot (a f : SchwartzMap E ℂ) (u t : ℝ) (J : Finset ℕ) (Y x : E) : ℝ :=
  Real.sqrt (∑ j ∈ J, ‖shiftedTest a f u t j Y x‖^2)

private theorem highWindowRoot_sq (a f : SchwartzMap E ℂ) (u t : ℝ)
    (J : Finset ℕ) (Y x : E) :
    ‖highWindowRoot a f u t J Y x‖ₑ^2 = comparableHighWindowEnergy a f u t J Y x := by
  unfold highWindowRoot comparableHighWindowEnergy
  rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _),← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  simp only [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm_eq_enorm]

private theorem highWindowRoot_eq_annularSquare (a f : SchwartzMap E ℂ) {u t : ℝ}
    (hu : 0<u) (ht : 0<t) (J : Finset ℕ) (Y x : E) :
    highWindowRoot a f u t J Y x =
      annularSquare (J.orderEmbOfFin rfl).toEmbedding a (u*t) ((-u⁻¹) • Y) f x := by
  let e : Fin J.card ↪ ℕ := (J.orderEmbOfFin rfl).toEmbedding
  rw [annular_square_fourier e a f (u*t) (mul_pos hu ht),highWindowRoot]
  have hm : Finset.univ.map e = J := J.map_orderEmbOfFin_univ rfl
  congr 1
  calc
    _ = ∑ j ∈ Finset.univ.map e, ‖shiftedTest a f u t j Y x‖^2 := by rw [hm]
    _ = _ := by rw [sum_map]; simp only [shiftedTest_fourier a f u t hu ht]

/-- The annulus that survives coefficient insertion has the actual (L^2)
and (L^4) square moments, with the correct relative shift factor. -/
theorem exists_comparableHighWindowEnergy_moments (a : SchwartzMap E ℂ)
    (ha : HasCompactSupport (a : E → ℂ))
    (hAnn : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) :
    ∃ C₂ C₄ : ℝ≥0∞, C₂<⊤ ∧ C₄<⊤ ∧ ∀ (f : SchwartzMap E ℂ) {u t : ℝ}, 0<u → 0<t →
      ∀ (J : Finset ℕ) (Y : E),
        (∫⁻ x : E, comparableHighWindowEnergy a f u t J Y x) ≤
          (C₂*ENNReal.ofReal (1+‖(-u⁻¹) • Y‖)*eLpNorm (f : E → ℂ) 2 volume)^2 ∧
        (∫⁻ x : E, comparableHighWindowEnergy a f u t J Y x^2) ≤
          (C₄*ENNReal.ofReal (1+‖(-u⁻¹) • Y‖)*eLpNorm (f : E → ℂ) 4 volume)^4 := by
  obtain ⟨C₂,h₂,bd₂⟩ := annular_square_all_Lp a ha hAnn 2 (by norm_num)
  obtain ⟨C₄,h₄,bd₄⟩ := annular_square_all_Lp a ha hAnn 4 (by norm_num)
  refine ⟨C₂,C₄,h₂,h₄,?_⟩
  intro f u t hu ht J Y
  let e : Fin J.card ↪ ℕ := (J.orderEmbOfFin rfl).toEmbedding
  have eq : highWindowRoot a f u t J Y = annularSquare e a (u*t) ((-u⁻¹) • Y) f :=
    funext (highWindowRoot_eq_annularSquare a f hu ht J Y)
  have b₂ := bd₂ (u*t) (mul_pos hu ht) ((-u⁻¹) • Y) J.card e f (f.memLp _)
  have b₄ := bd₄ (u*t) (mul_pos hu ht) ((-u⁻¹) • Y) J.card e f (f.memLp _)
  simp only [← eq,ENNReal.ofReal_ofNat] at b₂ b₄
  have ep₂ : eLpNorm (highWindowRoot a f u t J Y) 2 volume ^ (2:ℕ) =
      ∫⁻ x : E, ‖highWindowRoot a f u t J Y x‖ₑ^2 := by
    simpa using eLpNorm_nnreal_pow_eq_lintegral (μ := (volume : Measure E))
      (f := highWindowRoot a f u t J Y) (p := 2) (by norm_num)
  have ep₄ : eLpNorm (highWindowRoot a f u t J Y) 4 volume ^ (4:ℕ) =
      ∫⁻ x : E, ‖highWindowRoot a f u t J Y x‖ₑ^4 := by
    simpa using eLpNorm_nnreal_pow_eq_lintegral (μ := (volume : Measure E))
      (f := highWindowRoot a f u t J Y) (p := 4) (by norm_num)
  constructor
  · have b := pow_le_pow_left' b₂ 2
    simpa only [ep₂,highWindowRoot_sq] using b
  · have b := pow_le_pow_left' b₄ 4
    rw [ep₄] at b
    have eq4 (x : E) : ‖highWindowRoot a f u t J Y x‖ₑ^4 =
        comparableHighWindowEnergy a f u t J Y x^2 := by
      have h := pow_mul ‖highWindowRoot a f u t J Y x‖ₑ 2 2
      simpa only [highWindowRoot_sq,show (2:ℕ)*2=4 by decide] using h
    simpa only [eq4] using b

/-- Cauchy–Schwarz in space and over the finite common dyadic index set. -/
theorem comparable_finite_Cauchy (J : Finset ℕ) (U V : ℕ → E → ℝ≥0∞)
    (hU : ∀ j, Measurable (U j)) (hV : ∀ j, Measurable (V j)) :
    (∑ j ∈ J, ∫⁻ x : E, U j x*V j x) ≤
      (∑ j ∈ J, ∫⁻ x : E, U j x^2)^((1:ℝ)/2) *
      (∑ j ∈ J, ∫⁻ x : E, V j x^2)^((1:ℝ)/2) := by
  let a j := (∫⁻ x : E, U j x^2)^((1:ℝ)/2)
  let b j := (∫⁻ x : E, V j x^2)^((1:ℝ)/2)
  let μ := (Measure.count : Measure ℕ).restrict (J : Set ℕ)
  have eq (F : ℕ → ℝ≥0∞) : (∫⁻ j, F j ∂μ) = ∑ j ∈ J, F j := by
    simp only [μ,lintegral_finset,Measure.count_singleton,mul_one]
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (measurable_of_countable a).aemeasurable (measurable_of_countable b).aemeasurable
  simp only [eq,Pi.mul_apply,ENNReal.rpow_two] at H
  have hpow (z : ℝ≥0∞) : (z^((1:ℝ)/2))^2 = z := by
    rw [← ENNReal.rpow_mul_natCast]
    norm_num
  simp only [a,b,hpow] at H
  refine (sum_le_sum fun j _ => ?_).trans H
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure E) Real.HolderConjugate.two_two
    (hU j).aemeasurable (hV j).aemeasurable
  simpa only [a,b,Pi.mul_apply,ENNReal.rpow_two] using h

end Burnett.A06
