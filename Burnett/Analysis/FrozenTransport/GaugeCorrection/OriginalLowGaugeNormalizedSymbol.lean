import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalLowGaugeCorrection

set_option autoImplicit false
set_option maxRecDepth 4300
set_option maxHeartbeats 5800000

noncomputable section

namespace Burnett.V08

open Matrix Burnett.P01
open Burnett.A02.FrequencySplit (E)
open scoped BigOperators ContDiff Matrix

/-- The coefficient left after the high frequency is factored out of
the low-gauge correction, in independent low-angle and ratio variables. -/
def lowGaugeNormalizedHighDifference (m : Fin 4 → Fin 4 → ℝ) (G : ComplexComponents)
    (lowDir z highDir : E) : ℂ :=
  lowGaugeHighDifference m (normalizedGaugePotential lowDir G) z highDir

/-- The exact gauge correction is the high magnitude times the profile
whose low test factor and gauge potential have regular unit-direction formulas. -/
theorem originalLowGaugeCorrection_eq_highMagnitude_profile
    (h : ProjectionSchwartzMatrix) (m : Fin 4 → Fin 4 → ℝ) (w : ℝ)
    (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (hHom : ∀ (s : ℝ), 0 < s → ∀ ξ, a (s • ξ) = s * a ξ)
    (C : Matrix TensorSlot TensorSlot ℝ) (S : E → Matrix TensorSlot TensorSlot ℝ)
    (hS : ∀ (s : ℝ), 0 < s → ∀ ξ, S (s • ξ) = S ξ)
    (lowDir ratio highDir : E) (pSize qSize : ℝ) (hp : 0 < pSize) (hq : 0 < qSize)
    (hLow : ‖lowDir‖ = 1) (hHigh : ‖highDir‖ = 1) (hRatio : ‖ratio‖ < 1/2)
    (hScale : ratio = (pSize / qSize) • lowDir) (i j : TensorSlot) :
    let p := pSize • lowDir
    let q := qSize • highDir
    lowGaugeCorrectionCoefficient m w a (originalLowGaugePotential h) C S p q i j =
      (qSize : ℂ) * ((w / 3 * cyclicLowNormalizedPhase a lowDir ratio highDir : ℝ) : ℂ) *
        lowGaugeNormalizedHighDifference m (originalGaugeSpectrum h p) lowDir ratio highDir *
        (lowGaugeHighMatrix C S ratio highDir i j : ℂ) := by
  dsimp only
  let p := pSize • lowDir
  let q := qSize • highDir
  have hLen : ‖p‖ = pSize := by
    change ‖pSize • lowDir‖ = pSize
    rw [norm_smul, Real.norm_of_nonneg hp.le, hLow, mul_one]
  have hUnit : pSize⁻¹ • p = lowDir := by
    change pSize⁻¹ • (pSize • lowDir) = _
    rw [smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
  have hAngle :
      signedCyclicPhase a p q = pSize * cyclicLowNormalizedPhase a lowDir ratio highDir := by
    have h := (div_eq_iff hp.ne').mp
      (signedCyclicPhase_div_eq_lowNormalized a ha hOdd hHom lowDir ratio highDir
        pSize qSize hp hq hHigh hRatio hScale)
    exact h.trans (mul_comm _ _)
  have hScaleProduct : qSize * (pSize / qSize) = pSize := by field_simp
  have hSum : p + q = qSize • (ratio + highDir) := by
    change pSize • lowDir + qSize • highDir = _
    rw [hScale, smul_add, smul_smul, hScaleProduct]
  have hOut : lowGaugeHighMatrix C S p q = lowGaugeHighMatrix C S ratio highDir := by
    simp only [lowGaugeHighMatrix, hSum, q, hS qSize hq]
  have hDiff : q + (p + q) = qSize • (highDir + (ratio + highDir)) := by
    rw [hSum]
    exact (smul_add qSize highDir (ratio + highDir)).symm
  have hContract :
      lowGaugeHighDifference m (originalLowGaugePotential h p) p q =
        ((qSize / pSize : ℝ) : ℂ) *
          lowGaugeNormalizedHighDifference m (originalGaugeSpectrum h p) lowDir ratio highDir := by
    unfold lowGaugeNormalizedHighDifference lowGaugeHighDifference
    rw [hDiff]
    simp only [originalLowGaugePotential, hLen, hUnit, PiLp.smul_apply, smul_eq_mul,
      Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_inv]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold lowGaugeCorrectionCoefficient
  rw [hAngle, hContract, hOut]
  have hpc : (pSize : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [Complex.ofReal_mul, Complex.ofReal_div]
  field_simp
  ring

end Burnett.V08
