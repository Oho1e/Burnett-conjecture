import Burnett.Analysis.FrozenTransport.GaugeCorrection.NormalizedLowGaugePotential

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 4400000

noncomputable section

namespace Burnett.V08

open Matrix Burnett.P01
open Burnett.A02.FrequencySplit (E)
open scoped BigOperators ContDiff Matrix ComplexConjugate

open private complexFrequency from Burnett.Analysis.GaugeProjection.GaugeProjectionFourier

theorem normalizedGaugePotential_apply (lowDir : E) (G : ComplexComponents) (i : Fin 4) :
    normalizedGaugePotential lowDir G i =
      (∑ b : Fin 4, G i b * (lowDir b : ℂ)) -
        (∑ a : Fin 4, (lowDir a : ℂ) * (∑ b : Fin 4, G a b * (lowDir b : ℂ))) / 2 * (lowDir i : ℂ) := by
  rfl

/-- The coefficient of every low tensor entry extends as a smooth
function of the independent ambient direction, including the origin. -/
theorem normalizedGaugePotential_contDiff (G : ComplexComponents) (i : Fin 4) :
    ContDiff ℝ ∞ (fun lowDir => normalizedGaugePotential lowDir G i) := by
  have hCoordinate (a : Fin 4) : ContDiff ℝ ∞ (fun lowDir : E => (lowDir a : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) a).contDiff
  have hRow (a : Fin 4) : ContDiff ℝ ∞ (fun lowDir : E => ∑ b : Fin 4, G a b * (lowDir b : ℂ)) := by
    exact ContDiff.sum fun b _ => contDiff_const.mul (hCoordinate b)
  have hCenter : ContDiff ℝ ∞ (fun lowDir : E =>
      ∑ a : Fin 4, (lowDir a : ℂ) * (∑ b : Fin 4, G a b * (lowDir b : ℂ))) :=
    ContDiff.sum fun a _ => (hCoordinate a).mul (hRow a)
  simp only [normalizedGaugePotential_apply]
  simpa only [div_eq_mul_inv] using
    (hRow i).sub ((hCenter.mul (contDiff_const (c := (2 : ℂ)⁻¹))).mul (hCoordinate i))

private theorem normalizedGaugePotential_neg_direction (lowDir : E) (G : ComplexComponents) (i : Fin 4) :
    normalizedGaugePotential (-lowDir) G i = -normalizedGaugePotential lowDir G i := by
  have hRow (a : Fin 4) :
      (∑ b : Fin 4, G a b * ((-lowDir) b : ℂ)) = -(∑ b : Fin 4, G a b * (lowDir b : ℂ)) := by
    simp only [PiLp.neg_apply, Complex.ofReal_neg, mul_neg, Finset.sum_neg_distrib]
  have hCenter :
      (∑ a : Fin 4, ((-lowDir) a : ℂ) * (∑ b : Fin 4, G a b * ((-lowDir) b : ℂ))) =
        ∑ a : Fin 4, (lowDir a : ℂ) * (∑ b : Fin 4, G a b * (lowDir b : ℂ)) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [hRow a]
    simp only [PiLp.neg_apply, Complex.ofReal_neg, neg_mul_neg]
  rw [normalizedGaugePotential_apply, normalizedGaugePotential_apply, hRow i, hCenter]
  simp only [PiLp.neg_apply, Complex.ofReal_neg]
  ring

private theorem normalizedGaugePotential_conj (lowDir : E) (G : ComplexComponents) (i : Fin 4) :
    normalizedGaugePotential lowDir (fun a b => conj (G a b)) i =
      conj (normalizedGaugePotential lowDir G i) := by
  simp only [normalizedGaugePotential_apply, map_sub, map_sum, map_mul,
    Complex.conj_ofReal, map_div₀, map_ofNat]

/-- The reflection of the normalized gauge vector on a real low field.
It supplies the minus sign paired with oddness of the cyclic test. -/
theorem normalizedGaugePotential_reflection (lowDir : E) (G : ComplexComponents) (i : Fin 4) :
    normalizedGaugePotential (-lowDir) (fun a b => conj (G a b)) i =
      -conj (normalizedGaugePotential lowDir G i) := by
  rw [normalizedGaugePotential_neg_direction, normalizedGaugePotential_conj]

/-- The fixed polynomial recovers the same representative from a
pure-gauge input on the unit sphere. -/
theorem normalizedGaugePotential_amplitude (lowDir : E) (hlowDir : ‖lowDir‖ = 1) (v : ComplexCovector) :
    normalizedGaugePotential lowDir (normalizedGaugeAmplitude lowDir v) = v := by
  let w := complexFrequency lowDir
  have hReal : (∑ a : Fin 4, lowDir a * lowDir a) = 1 := by
    have h := EuclideanSpace.norm_sq_eq lowDir
    rw [hlowDir, one_pow] at h
    calc
      _ = ∑ a : Fin 4, lowDir a ^ 2 := by simp only [pow_two]
      _ = 1 := by simpa only [Real.norm_eq_abs, sq_abs] using h.symm
  have hw : w ⬝ᵥ w = 1 := by
    simpa only [dotProduct, w, complexFrequency, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_one]
      using congrArg Complex.ofReal hReal
  have hImage : (vecMulVec w v + vecMulVec v w) *ᵥ w = (v ⬝ᵥ w) • w + v := by
    simp only [add_mulVec, vecMulVec_mulVec, op_smul_eq_smul, hw, one_smul]
  change (vecMulVec w v + vecMulVec v w) *ᵥ w -
    ((w ⬝ᵥ ((vecMulVec w v + vecMulVec v w) *ᵥ w)) / 2) • w = v
  rw [hImage]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hw, mul_one, dotProduct_comm w v]
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Burnett.V08
