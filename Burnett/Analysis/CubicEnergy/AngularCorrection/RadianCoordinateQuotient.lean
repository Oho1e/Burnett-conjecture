import Burnett.Analysis.CubicEnergy.HighSlotCommutator.RadianHighDerivativeCommutator

set_option autoImplicit false
set_option maxHeartbeats 2600000

noncomputable section

namespace Burnett.A07

open MeasureTheory
open Burnett.A02.FrequencySplit (E Joint radianFourier tau)
open Burnett.A06
open scoped BigOperators ComplexConjugate

/-- The high-coordinate component of the first-order symbol divided by the
squared high radius. The definition is total on the high axis. -/
def coordinateQuotient (b : Joint → ℂ) (j : Fin 4) (x : Joint) : ℂ :=
  ((x.2 j / ‖x.2‖ ^ 2 : ℝ) : ℂ) * b x

theorem coordinateQuotient_measurable
    {b : Joint → ℂ} (hb : Measurable b) (j : Fin 4) :
    Measurable (coordinateQuotient b j) := by
  refine (Complex.continuous_ofReal.measurable.comp ?_).mul hb
  exact (show Measurable (fun p : Joint => p.2 j) by fun_prop).div
    ((continuous_snd.norm.pow 2).measurable)

theorem coordinateQuotient_orderOne_bound
    (b : Joint → ℂ) {B r : ℝ} (hB : 0 ≤ B) (hr : 0 < r)
    (bound : ∀ x : Joint, ‖b x‖ ≤ B * (1 + ‖x.1‖ + ‖x.2‖))
    (hIR : ∀ x : Joint, ‖x.2‖ ≤ r → b x = 0) (j : Fin 4) (x : Joint) :
    ‖coordinateQuotient b j x‖ ≤ (B / r) * (1 + ‖x.1‖ + ‖x.2‖) := by
  by_cases hz : ‖x.2‖ ≤ r
  · rw [coordinateQuotient, hIR _ hz, mul_zero, norm_zero]
    positivity
  have hh : r < ‖x.2‖ := lt_of_not_ge hz
  have hpos : 0 < ‖x.2‖ := hr.trans hh
  have hcoord := PiLp.norm_apply_le x.2 j
  have hmul : ‖x.2 j‖ * r ≤ ‖x.2‖ ^ 2 := by
    calc
      _ ≤ ‖x.2‖ * r := mul_le_mul_of_nonneg_right hcoord hr.le
      _ ≤ ‖x.2‖ ^ 2 := by
        simpa only [pow_two] using mul_le_mul_of_nonneg_left hh.le hpos.le
  have hrat : ‖x.2 j‖ / ‖x.2‖ ^ 2 ≤ r⁻¹ := by
    calc
      _ ≤ (‖x.2‖ ^ 2 / r) / ‖x.2‖ ^ 2 :=
        div_le_div_of_nonneg_right ((le_div_iff₀ hr).mpr hmul) (by positivity)
      _ = _ := by field_simp [hpos.ne', hr.ne']
  rw [coordinateQuotient, norm_mul, Complex.norm_real, norm_div,
    Real.norm_of_nonneg (sq_nonneg ‖x.2‖)]
  calc
    _ ≤ r⁻¹ * (B * (1 + ‖x.1‖ + ‖x.2‖)) :=
      mul_le_mul hrat (bound x) (norm_nonneg _) (inv_nonneg.mpr hr.le)
    _ = _ := by ring

private theorem sum_coordinateSquares (v : E) :
    ∑ j : Fin 4, (v j) ^ 2 = ‖v‖ ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq v).symm

theorem coordinateQuotient_sum_frequency
    (b : Joint → ℂ) (haxis : ∀ x : Joint, x.2 = 0 → b x = 0) (x : Joint) :
    (∑ j : Fin 4, (-Complex.I) * coordinateQuotient b j x * (Complex.I * (x.2 j : ℂ))) =
      b x := by
  by_cases hz : x.2 = 0
  · simp [coordinateQuotient, haxis x hz]
  have hs : ‖x.2‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  have hR : (∑ j : Fin 4, (x.2 j) ^ 2 / ‖x.2‖ ^ 2) = 1 := by
    rw [← Finset.sum_div, sum_coordinateSquares, div_self hs]
  have hC : (∑ j : Fin 4, (((x.2 j) ^ 2 / ‖x.2‖ ^ 2 : ℝ) : ℂ)) = 1 := by
    simpa only [Complex.ofReal_sum, Complex.ofReal_one] using congrArg Complex.ofReal hR
  have hI : (-Complex.I) * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  calc
    _ = ∑ j : Fin 4, (((x.2 j) ^ 2 / ‖x.2‖ ^ 2 : ℝ) : ℂ) * b x := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = ((-Complex.I) * Complex.I) * ((((x.2 j) ^ 2 / ‖x.2‖ ^ 2 : ℝ) : ℂ) * b x) := by
          simp only [coordinateQuotient, Complex.ofReal_div, Complex.ofReal_pow]
          ring
        _ = _ := by rw [hI, one_mul]
    _ = _ := by rw [← Finset.sum_mul, hC, one_mul]

private theorem radianHighPairWeight_eq_sum_coordinateDerivative
    (b : Joint → ℂ) (haxis : ∀ x : Joint, x.2 = 0 → b x = 0)
    (f u w : SchwartzMap E ℂ) (x : Joint) :
    radianHighPairWeight b f u w x =
      ∑ j : Fin 4, (-Complex.I) *
        radianHighPairWeight (coordinateQuotient b j) f (coordinateDerivative j u) w x := by
  calc
    _ = (∑ j : Fin 4, (-Complex.I) * coordinateQuotient b j x * (Complex.I * (x.2 j : ℂ))) *
        radianFourier f x.1 * radianFourier u x.2 * conj (radianFourier w (x.2+x.1)) := by
      rw [coordinateQuotient_sum_frequency b haxis]
      rfl
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [radianHighPairWeight, radianFourier_coordinateDerivative]
      ring

/-- Exact tested reconstruction of the order-one action from its four
coordinate quotients, with a derivative falling on the original high field. -/
theorem radianHighPair_eq_sum_coordinateDerivative
    (b : Joint → ℂ) (hb : Measurable b) {B r : ℝ} (hB : 0 ≤ B) (hr : 0 < r)
    (bound : ∀ x : Joint, ‖b x‖ ≤ B * (1 + ‖x.1‖ + ‖x.2‖))
    (hIR : ∀ x : Joint, ‖x.2‖ ≤ r → b x = 0)
    (f u w : SchwartzMap E ℂ) :
    radianHighPair b f u w =
      ∑ j : Fin 4, (-Complex.I) *
        radianHighPair (coordinateQuotient b j) f (coordinateDerivative j u) w := by
  have haxis (x : Joint) (hz : x.2 = 0) : b x = 0 :=
    hIR x (by simpa only [hz, norm_zero] using hr.le)
  let W (j : Fin 4) (x : Joint) :=
    (-Complex.I) * radianHighPairWeight (coordinateQuotient b j) f (coordinateDerivative j u) w x
  have hI (j : Fin 4) : Integrable (W j) :=
    (integrable_radianHighPairWeight_of_orderOne (coordinateQuotient b j)
      (coordinateQuotient_measurable hb j) (B / r) (div_nonneg hB hr.le)
      (coordinateQuotient_orderOne_bound b hB hr bound hIR j) f (coordinateDerivative j u)
      w).const_mul _
  have eq : radianHighPairWeight b f u w = fun x => ∑ j : Fin 4, W j x :=
    funext (radianHighPairWeight_eq_sum_coordinateDerivative b haxis f u w)
  unfold radianHighPair
  rw [eq, integral_finset_sum Finset.univ (fun j _ => hI j), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (∫ x, W j x) = (-Complex.I) *
    ∫ x, radianHighPairWeight (coordinateQuotient b j) f (coordinateDerivative j u) w x from
      integral_const_mul _ _]
  simp only [Complex.real_smul]
  ring

theorem regularizedLowCartesianSymbol_eq_zero_on_highGap
    (η χ : ℝ → ℝ) (c : Joint → ℂ) {r : ℝ} (hη : ∀ s ≤ r, η s = 0)
    (x : Joint) (hx : ‖x.2‖ ≤ r) :
    regularizedLowCartesianSymbol η χ c x = 0 := by
  simp [regularizedLowCartesianSymbol, hη _ hx]

theorem highAdjoint_regularizedLowCartesianSymbol_eq_zero_on_highGap
    (η χ : ℝ → ℝ) (c : Joint → ℂ) {r ρ : ℝ}
    (hη : ∀ s ≤ r, η s = 0) (hρ : 0 ≤ ρ) (hsmall : ρ < 1)
    (hχ : ∀ s ≥ ρ ^ 2, χ s = 0)
    (x : Joint) (hx : ‖x.2‖ ≤ (1 - ρ) * r) :
    highAdjointSymbol (regularizedLowCartesianSymbol η χ c) x = 0 := by
  by_contra hn
  obtain ⟨_, _, _, _, _, hgap⟩ :=
    regularizedLowCartesianSymbol_highAdjointSupport η χ c hρ hsmall hχ hη x hn
  exact (not_lt_of_ge hx) hgap

/-- The original fixed infrared cutoff stays on the high input in the
coordinate quotients of the forward symbol. -/
theorem coordinateQuotient_regularizedLowCartesianSymbol
    (η χ : ℝ → ℝ) (c : Joint → ℂ) (j : Fin 4) (x : Joint) :
    coordinateQuotient (regularizedLowCartesianSymbol η χ c) j x =
      η ‖x.2‖ • coordinateQuotient (lowCartesianSymbol χ c) j x := by
  simp only [coordinateQuotient, regularizedLowCartesianSymbol, Complex.real_smul]
  ring

/-- In the true high adjoint the same infrared cutoff acts on the high output. -/
theorem coordinateQuotient_highAdjoint_regularizedLowCartesianSymbol
    (η χ : ℝ → ℝ) (c : Joint → ℂ) (j : Fin 4) (x : Joint) :
    coordinateQuotient (highAdjointSymbol (regularizedLowCartesianSymbol η χ c)) j x =
      η ‖x.2 + x.1‖ • coordinateQuotient (highAdjointSymbol (lowCartesianSymbol χ c)) j x := by
  simp only [coordinateQuotient, highAdjointSymbol, regularizedLowCartesianSymbol,
    Complex.real_smul, map_mul, Complex.conj_ofReal]
  change _ * ((η ‖x.2 + x.1‖ : ℂ) * _) = _
  ring

end Burnett.A07
