import Burnett.Analysis.FrozenTransport.GaugeCorrection.CyclicLowPhaseExtension
import Burnett.Analysis.FrozenTransport.GaugeCorrection.NormalizedLowGaugePotential

set_option autoImplicit false
set_option maxRecDepth 3800
set_option maxHeartbeats 4900000

noncomputable section

namespace Burnett.V08

open Matrix Burnett.P01
open Burnett.A02.FrequencySplit (E)
open scoped BigOperators Matrix ComplexConjugate

abbrev TensorSlot := Fin 4 × Fin 4

/-- The high-index matrix pairs the output screen with the input
screen through the real frozen tensor contraction. -/
def lowGaugeHighMatrix (C : Matrix TensorSlot TensorSlot ℝ)
    (S : E → Matrix TensorSlot TensorSlot ℝ) (p q : E) : Matrix TensorSlot TensorSlot ℝ :=
  (S (p + q))ᵀ * C * S q

/-- The raised low vector contracted with the symmetric high covector
difference `q-r=q+(p+q)`. -/
def lowGaugeHighDifference (m : Fin 4 → Fin 4 → ℝ) (v : ComplexCovector) (p q : E) : ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4, (m i j : ℂ) * v j * ((q + (p + q)) i : ℂ)

/-- The paper's symmetric low-gauge correction coefficient, before
application of the fixed low/high cutoffs. -/
def lowGaugeCorrectionCoefficient (m : Fin 4 → Fin 4 → ℝ) (w : ℝ)
    (a : E → ℝ) (v : E → ComplexCovector) (C : Matrix TensorSlot TensorSlot ℝ)
    (S : E → Matrix TensorSlot TensorSlot ℝ) (p q : E) (i j : TensorSlot) : ℂ :=
  ((w / 3 * signedCyclicPhase a p q : ℝ) : ℂ) * lowGaugeHighDifference m (v p) p q *
    (lowGaugeHighMatrix C S p q i j : ℂ)

theorem signedCyclicPhase_highAdjoint (a : E → ℝ) (ha : ∀ ξ, a (-ξ) = -a ξ) (p q : E) :
    signedCyclicPhase a (-p) (p + q) = -signedCyclicPhase a p q := by
  unfold signedCyclicPhase
  rw [show -p + (p + q) = q by abel, ha p, ha q, ha (p + q)]
  ring

theorem lowGaugeHighMatrix_highAdjoint (C : Matrix TensorSlot TensorSlot ℝ)
    (hC : Cᵀ = C) (S : E → Matrix TensorSlot TensorSlot ℝ) (p q : E) :
    lowGaugeHighMatrix C S (-p) (p + q) = (lowGaugeHighMatrix C S p q)ᵀ := by
  simp only [lowGaugeHighMatrix, neg_add_cancel_left, transpose_mul, transpose_transpose, hC]
  rw [Matrix.mul_assoc]

private theorem lowGaugeHighDifference_highAdjoint
    (m : Fin 4 → Fin 4 → ℝ) (v : E → ComplexCovector)
    (hv : ∀ p i, v (-p) i = -conj (v p i)) (p q : E) :
    lowGaugeHighDifference m (v (-p)) (-p) (p + q) =
      -conj (lowGaugeHighDifference m (v p) p q) := by
  have hFreq : (p + q) + (-p + (p + q)) = q + (p + q) := by abel
  simp only [lowGaugeHighDifference, hFreq, hv, map_sum, map_mul, Complex.conj_ofReal]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The two signed factors from the odd test and the real gauge field
cancel under high adjunction. The output screen is transposed exactly once. -/
theorem lowGaugeCorrectionCoefficient_hermitian
    (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ) (v : E → ComplexCovector)
    (C : Matrix TensorSlot TensorSlot ℝ) (hC : Cᵀ = C)
    (S : E → Matrix TensorSlot TensorSlot ℝ)
    (ha : ∀ ξ, a (-ξ) = -a ξ) (hv : ∀ p i, v (-p) i = -conj (v p i))
    (p q : E) (i j : TensorSlot) :
    lowGaugeCorrectionCoefficient m w a v C S (-p) (p + q) j i =
      conj (lowGaugeCorrectionCoefficient m w a v C S p q i j) := by
  simp only [lowGaugeCorrectionCoefficient, signedCyclicPhase_highAdjoint a ha,
    lowGaugeHighDifference_highAdjoint m v hv, lowGaugeHighMatrix_highAdjoint C hC,
    Matrix.transpose_apply, map_mul, Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

/-- The real phase of the original constant scalar divergence operator. -/
def frozenWavePhase (m : Fin 4 → Fin 4 → ℝ) (p : E) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, m i j * p i * p j

/-- The transport summand of the actual one-low-gauge coefficient. -/
def lowGaugeTransportCoefficient (m : Fin 4 → Fin 4 → ℝ) (w : ℝ)
    (a : E → ℝ) (v : E → ComplexCovector) (C : Matrix TensorSlot TensorSlot ℝ)
    (S : E → Matrix TensorSlot TensorSlot ℝ) (p q : E) (i j : TensorSlot) : ℂ :=
  Complex.I * ((w / 3 : ℝ) : ℂ) * (signedCyclicPhase a p q : ℂ) *
    ((frozenWavePhase m (p + q) - frozenWavePhase m q : ℝ) : ℂ) *
    lowGaugeHighDifference m (v p) p q * (lowGaugeHighMatrix C S p q i j : ℂ)

/-- The commutator symbol identity also holds at coincident high phases.
It uses multiplication by the actual phase difference. -/
theorem lowGaugeTransportCoefficient_eq_commutator
    (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ) (v : E → ComplexCovector)
    (C : Matrix TensorSlot TensorSlot ℝ) (S : E → Matrix TensorSlot TensorSlot ℝ)
    (p q : E) (i j : TensorSlot) :
    lowGaugeTransportCoefficient m w a v C S p q i j =
      Complex.I * ((frozenWavePhase m (p + q) - frozenWavePhase m q : ℝ) : ℂ) *
        lowGaugeCorrectionCoefficient m w a v C S p q i j := by
  simp only [lowGaugeTransportCoefficient, lowGaugeCorrectionCoefficient, Complex.ofReal_mul]
  ring

end Burnett.V08
