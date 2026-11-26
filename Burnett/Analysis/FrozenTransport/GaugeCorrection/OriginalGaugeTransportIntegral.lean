import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeEntryExpansion
import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalMixedWeakEnergy

set_option autoImplicit false
set_option maxHeartbeats 3100000
set_option maxRecDepth 4500

noncomputable section

namespace Burnett.V08

open Matrix MeasureTheory Burnett.P01 Burnett.A06 Burnett.A07 Burnett.A08
open Burnett.A02.FrequencySplit (E Joint radianFourier tau)
open scoped Matrix ComplexConjugate BigOperators ENNReal

/-- Absolute integrability uses the actual finite entry symbols at the two Schwartz high slots. -/
theorem originalGaugeRadianPair_eq_integral (θ hi ho : ℝ → ℝ) (κ : ℝ)
    (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ) (C : Matrix TensorSlot TensorSlot ℝ)
    (S : GaugeScreen) (z : ProjectionSchwartzMatrix) (i j : TensorSlot)
    (B : ℝ) (hB : 0 ≤ B)
    (hMeas : ∀ k, Measurable (gaugeRawEntry θ hi ho κ m w a C S k i j))
    (hOrder : ∀ k (x : Joint), ‖gaugeRawEntry θ hi ho κ m w a C S k i j x‖ ≤ B*(1+‖x.1‖+‖x.2‖))
    (u v : SchwartzMap E ℂ) :
    let K (x : Joint) := (gaugeTriadCutoff θ hi ho κ x.1 x.2 : ℂ) *
      lowGaugeCorrectionCoefficient m w a (originalLowGaugePotential z) C S x.1 x.2 i j *
      radianFourier u x.2 * conj (radianFourier v (x.2+x.1))
    Integrable K ∧ originalGaugeRadianPair θ hi ho κ m w a C S z i j u v = (tau^8)⁻¹ • ∫ x, K x := by
  intro K
  let term (k : TensorSlot) := radianHighPairWeight (gaugeRawEntry θ hi ho κ m w a C S k i j)
    (Burnett.C03.projectedGaugeComplement z k.1 k.2) u v
  have hInt (k : TensorSlot) : Integrable (term k) :=
    integrable_radianHighPairWeight_of_orderOne _ (hMeas k) B hB (hOrder k) _ u v
  have hSum : (fun x => ∑ k : TensorSlot, term k x) = K := by
    funext x
    simp only [term, radianHighPairWeight, ← Finset.sum_mul, sum_gaugeRawEntry_spectrum, K]
  refine ⟨hSum ▸ integrable_finset_sum _ (fun k _ => hInt k), ?_⟩
  unfold originalGaugeRadianPair radianHighPair
  rw [← Finset.smul_sum]
  congr 1
  rw [← hSum, integral_finset_sum _ (fun k _ => hInt k)]

/-- The difference of the two original high-slot pairings is the absolutely
integrable transport numerator, including at equality of the two wave phases. -/
theorem originalGaugeRadianPair_eq_transportIntegral
    (θ hi ho : ℝ → ℝ) (κ : ℝ) (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ)
    (C : Matrix TensorSlot TensorSlot ℝ) (S : GaugeScreen) (z : ProjectionSchwartzMatrix) (i j : TensorSlot)
    (B : ℝ) (hB : 0 ≤ B)
    (hMeas : ∀ k, Measurable (gaugeRawEntry θ hi ho κ m w a C S k i j))
    (hOrder : ∀ k (x : Joint), ‖gaugeRawEntry θ hi ho κ m w a C S k i j x‖ ≤ B*(1+‖x.1‖+‖x.2‖))
    (u v : SchwartzMap E ℂ) :
    let N (x : Joint) := (gaugeTriadCutoff θ hi ho κ x.1 x.2 : ℂ) *
      lowGaugeTransportCoefficient m w a (originalLowGaugePotential z) C S x.1 x.2 i j *
      radianFourier u x.2 * conj (radianFourier v (x.2+x.1))
    Integrable N ∧ Complex.I * (originalGaugeRadianPair θ hi ho κ m w a C S z i j u (constantWave m v) -
      originalGaugeRadianPair θ hi ho κ m w a C S z i j (constantWave m u) v) = (tau^8)⁻¹ • ∫ x, N x := by
  intro N
  let K (f h : SchwartzMap E ℂ) (x : Joint) := (gaugeTriadCutoff θ hi ho κ x.1 x.2 : ℂ) *
    lowGaugeCorrectionCoefficient m w a (originalLowGaugePotential z) C S x.1 x.2 i j *
    radianFourier f x.2 * conj (radianFourier h (x.2+x.1))
  have one := originalGaugeRadianPair_eq_integral θ hi ho κ m w a C S z i j B hB hMeas hOrder u (constantWave m v)
  have two := originalGaugeRadianPair_eq_integral θ hi ho κ m w a C S z i j B hB hMeas hOrder (constantWave m u) v
  let out := K u (constantWave m v)
  let inp := K (constantWave m u) v
  have hId : (fun x : Joint => Complex.I * (out x - inp x)) = N := by
    funext x
    simp only [out, inp, K, N, radianFourier_constantWave, map_mul, Complex.conj_ofReal,
      lowGaugeTransportCoefficient_eq_commutator, Complex.ofReal_sub]
    rw [show waveQuadratic m (x.2+x.1) = frozenWavePhase m (x.1+x.2) by rw [add_comm x.2 x.1]; rfl]
    change _ = _ * (Complex.I * ((frozenWavePhase m (x.1 + x.2) : ℂ) - (waveQuadratic m x.2 : ℂ)) * _) * _ * _
    ring
  have hOut : Integrable out := one.1
  have hInp : Integrable inp := two.1
  refine ⟨hId ▸ (hOut.sub hInp).const_mul Complex.I, ?_⟩
  rw [one.2, two.2, ← hId, integral_const_mul,
    integral_sub hOut hInp, ← smul_sub]
  change Complex.I * (((tau^8)⁻¹ : ℝ) • ((∫ x, out x) - ∫ x, inp x)) = _
  simp only [Algebra.smul_def, Complex.coe_algebraMap]
  ring

/-- A forward L² representative of this raw matrix entry has the same weak
commutator with the frozen wave operator. -/
theorem weakConstantWaveCommutatorPair_eq_originalGauge_transport
    (θ hi ho : ℝ → ℝ) (κ : ℝ) (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ)
    (C : Matrix TensorSlot TensorSlot ℝ) (S : GaugeScreen) (z : ProjectionSchwartzMatrix) (i j : TensorSlot)
    (B : ℝ) (hB : 0 ≤ B)
    (hMeas : ∀ k, Measurable (gaugeRawEntry θ hi ho κ m w a C S k i j))
    (hOrder : ∀ k (x : Joint), ‖gaugeRawEntry θ hi ho κ m w a C S k i j x‖ ≤ B*(1+‖x.1‖+‖x.2‖))
    (T : SchwartzMap E ℂ → FirstOrderLp 2)
    (hT : ∀ (u v : SchwartzMap E ℂ), inner ℂ (v.toLp 2 volume) (T u) =
      originalGaugeRadianPair θ hi ho κ m w a C S z i j u v) (u v : SchwartzMap E ℂ) :
    let N (x : Joint) := (gaugeTriadCutoff θ hi ho κ x.1 x.2 : ℂ) *
      lowGaugeTransportCoefficient m w a (originalLowGaugePotential z) C S x.1 x.2 i j *
      radianFourier u x.2 * conj (radianFourier v (x.2+x.1))
    Integrable N ∧ Complex.I * weakConstantWaveCommutatorPair m T u v = (tau^8)⁻¹ • ∫ x, N x := by
  simpa only [weakConstantWaveCommutatorPair, hT] using
    originalGaugeRadianPair_eq_transportIntegral θ hi ho κ m w a C S z i j B hB hMeas hOrder u v

end Burnett.V08
