import Burnett.Analysis.FrozenTransport.GaugeCorrection.LowGaugeCorrectionSymbol
import Burnett.Analysis.FrozenTransport.GaugeCorrection.NormalizedGaugePotentialJets

set_option autoImplicit false
set_option maxRecDepth 4400
set_option maxHeartbeats 5600000

noncomputable section

namespace Burnett.V08

open Matrix MeasureTheory Burnett.P01
open Burnett.A02.FrequencySplit (E radianFourier)
open scoped BigOperators Matrix ComplexConjugate RealInnerProductSpace

open private complexFrequency from Burnett.Analysis.GaugeProjection.GaugeProjectionFourier

private theorem radianFourier_real_reflection (f : E → ℂ) (hReal : ∀ x, conj (f x) = f x) (ξ : E) :
    radianFourier f (-ξ) = conj (radianFourier f ξ) := by
  rw [radianFourier, radianFourier, ← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change Complex.exp (-(inner ℝ x (-ξ) : ℂ) * Complex.I) * f x =
      conj (Complex.exp (-(inner ℝ x ξ : ℂ) * Complex.I) * f x)
    rw [inner_neg_right, Complex.ofReal_neg, neg_neg, map_mul, hReal,
      ← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, neg_mul_neg]

/-- The Fourier amplitude of the actual complementary gauge field. -/
def originalGaugeSpectrum (z : ProjectionSchwartzMatrix) (ξ : E) : ComplexComponents :=
  fun i j => radianFourier (Burnett.C03.projectedGaugeComplement z i j) ξ

theorem originalGaugeSpectrum_reflection (z : ProjectionSchwartzMatrix)
    (hReal : ∀ i j x, conj (z i j x) = z i j x) (ξ : E) :
    originalGaugeSpectrum z (-ξ) = fun a b => conj (originalGaugeSpectrum z ξ a b) := by
  ext i j
  change radianFourier (Burnett.C03.projectedGaugeComplement z i j) (-ξ) =
    conj (radianFourier (Burnett.C03.projectedGaugeComplement z i j) ξ)
  rw [Burnett.C03.projectedGaugeComplement_radianFourier,
    Burnett.C03.projectedGaugeComplement_radianFourier]
  simp only [norm_neg, radianFourier_real_reflection _ (hReal _ _), gaugeProjectionSymbol_even,
    map_mul, map_sub, map_sum, Complex.conj_ofReal]

/-- The gauge vector in the original frequency variables.
The division is by the low magnitude, independently of the wave phase. -/
def originalLowGaugePotential (z : ProjectionSchwartzMatrix) (ξ : E) : ComplexCovector :=
  fun i => (‖ξ‖⁻¹ : ℝ) *
    normalizedGaugePotential (‖ξ‖⁻¹ • ξ) (originalGaugeSpectrum z ξ) i

theorem originalLowGaugePotential_reflection (z : ProjectionSchwartzMatrix)
    (hReal : ∀ i j x, conj (z i j x) = z i j x) (ξ : E) (i : Fin 4) :
    originalLowGaugePotential z (-ξ) i = -conj (originalLowGaugePotential z ξ i) := by
  simp only [originalLowGaugePotential, norm_neg, smul_neg, originalGaugeSpectrum_reflection z hReal,
    normalizedGaugePotential_reflection, map_mul, Complex.conj_ofReal, mul_neg]

private theorem normalizedGaugeAmplitude_smul (ξ : E) (c : ℂ) (v : ComplexCovector) :
    normalizedGaugeAmplitude ξ (c • v) = c • normalizedGaugeAmplitude ξ v := by
  simp only [normalizedGaugeAmplitude, vecMulVec_smul, smul_vecMulVec, smul_add]

/-- The actual gauge spectrum is the pure-gauge tensor of this same
original low vector, for every nonzero frequency. -/
theorem originalGaugeSpectrum_eq_amplitude
    (z : ProjectionSchwartzMatrix) (hSym : ∀ i j, z i j = z j i) (ξ : E) (hξ : ξ ≠ 0) :
    originalGaugeSpectrum z ξ = normalizedGaugeAmplitude ξ (originalLowGaugePotential z ξ) := by
  let lowDir := ‖ξ‖⁻¹ • ξ
  let H : ComplexComponents := fun a b => radianFourier (z a b) ξ
  let v := (gaugeProjectionInfrared ‖ξ‖ : ℂ) • normalizedGaugePotential lowDir H
  have hDir : ‖lowDir‖ = 1 := by
    change ‖‖ξ‖⁻¹ • ξ‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)]
  have hG : originalGaugeSpectrum z ξ = normalizedGaugeAmplitude lowDir v := by
    rw [normalizedGaugeAmplitude_smul]
    ext i j
    exact Burnett.V08.projectedGaugeComplement_eq_normalizedGauge z hSym ξ hξ i j
  have hPotential : normalizedGaugePotential lowDir (originalGaugeSpectrum z ξ) = v := by
    rw [hG, normalizedGaugePotential_amplitude lowDir hDir v]
  rw [hG]
  ext i j
  have hi := congrFun hPotential i
  have hj := congrFun hPotential j
  change _ =
    (ξ i : ℂ) * ((‖ξ‖⁻¹ : ℝ) * normalizedGaugePotential lowDir (originalGaugeSpectrum z ξ) j) +
      ((‖ξ‖⁻¹ : ℝ) * normalizedGaugePotential lowDir (originalGaugeSpectrum z ξ) i) * (ξ j : ℂ)
  rw [hi, hj]
  simp only [normalizedGaugeAmplitude, Matrix.add_apply, vecMulVec_apply, complexFrequency, lowDir,
    PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

/-- The actual original gauge low field supplies the Hermitian correction
when the original localized fluctuation is real. -/
theorem lowGaugeCorrectionCoefficient_original_hermitian
    (z : ProjectionSchwartzMatrix) (hReal : ∀ i j x, conj (z i j x) = z i j x)
    (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ)
    (C : Matrix TensorSlot TensorSlot ℝ) (hC : Cᵀ = C)
    (S : E → Matrix TensorSlot TensorSlot ℝ)
    (ha : ∀ ξ, a (-ξ) = -a ξ) (p q : E) (i j : TensorSlot) :
    lowGaugeCorrectionCoefficient m w a (originalLowGaugePotential z) C S (-p) (p + q) j i =
      conj (lowGaugeCorrectionCoefficient m w a (originalLowGaugePotential z) C S p q i j) :=
  lowGaugeCorrectionCoefficient_hermitian m w a (originalLowGaugePotential z) C hC S ha
    (originalLowGaugePotential_reflection z hReal) p q i j

end Burnett.V08
