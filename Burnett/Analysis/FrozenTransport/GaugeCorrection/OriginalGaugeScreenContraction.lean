import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeRadianPair
import Burnett.Analysis.TransportPatches.ActualThinScreenCombination
import Burnett.Analysis.FrozenScreen.Phase

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4500

noncomputable section

namespace Burnett.V08

open Matrix Burnett.P01 Burnett.RicciSymbol Burnett.V06 Burnett.C02
open Burnett.A02.FrequencySplit (E radianFourier)
open Burnett.Analysis.TransportWardSymbol (inverseMatrix metricDensity)
open scoped Matrix ComplexConjugate BigOperators

/-- A nested regularizer for both high slots, identically one on the support of
the actual high-pass profile of the original projector. -/
def gaugeCorrectionInfrared (s : ℝ) : ℝ := gaugeProjectionInfrared (2*s)

theorem gaugeCorrectionInfrared_acts_identically_on_high (s : ℝ) :
    gaugeCorrectionInfrared s * gaugeProjectionInfrared s = gaugeProjectionInfrared s := by
  by_cases h : s ≤ 1
  · simp [gaugeProjectionInfrared_zero h]
  · simp [gaugeCorrectionInfrared, gaugeProjectionInfrared_one (show 2 ≤ 2*s by linarith)]

theorem gaugeCorrectionInfrared_preserves_original_fourier (z : ProjectionSchwartzMatrix)
    (i j : Fin 4) (p : E) :
    (gaugeCorrectionInfrared ‖p‖ : ℂ) * radianFourier (projectionFullSchwartz z i j) p =
      radianFourier (projectionFullSchwartz z i j) p ∧
    (gaugeCorrectionInfrared ‖p‖ : ℂ) * originalGaugeSpectrum z p i j = originalGaugeSpectrum z p i j := by
  have h : (gaugeCorrectionInfrared ‖p‖ : ℂ) * (gaugeProjectionInfrared ‖p‖ : ℂ) =
      (gaugeProjectionInfrared ‖p‖ : ℂ) := by exact_mod_cast gaugeCorrectionInfrared_acts_identically_on_high ‖p‖
  constructor
  · rw [projectionFullSchwartz_radianFourier]
    simp only [regularizedComplexGaugeProjection, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h]
  · simp only [originalGaugeSpectrum, Burnett.C03.projectedGaugeComplement_radianFourier, ← mul_assoc, h]

/-- Matrix of the frozen quarter trace-reversal map on ordered covariant tensor entries. -/
def gaugeFrozenContraction (m : ScreenMatrix) (i j : TensorSlot) : ℝ :=
  (m i.1 j.1 * m i.2 j.2 - m i.1 i.2 * m j.1 j.2 / 2) / 4

theorem gaugeFrozenContraction_action (m : ScreenMatrix) (J : ComplexTensor2) (i : TensorSlot) :
    (∑ j : TensorSlot, (gaugeFrozenContraction m i j : ℂ) * J j.1 j.2) =
      Burnett.V06.physicalCoefficient m J i.1 i.2 := by
  simp only [Burnett.V06.physicalCoefficient, raiseBoth, complexRaiseSecond, complexMetricTrace,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  simp only [gaugeFrozenContraction, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

theorem gaugeFrozenContraction_symmetric (m : ScreenMatrix) (hm : mᵀ = m) :
    (gaugeFrozenContraction m : Matrix TensorSlot TensorSlot ℝ)ᵀ = gaugeFrozenContraction m := by
  have sym (a b : Fin 4) : m b a = m a b := congrFun (congrFun hm a) b
  ext i j
  change (m j.1 i.1 * m j.2 i.2 - m j.1 j.2 * m i.1 i.2 / 2) / 4 = _
  rw [sym i.1 j.1, sym i.2 j.2]
  unfold gaugeFrozenContraction
  ring

/-- The literal low-gauge form on the two original projected physical high fields.
Both screens use the same inverse of the frozen metric and each appears once. -/
def originalScreenGaugeMatrixPair (θ : ℝ → ℝ) (κ : ℝ) (g : ScreenMatrix) (a : E → ℝ)
    (i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η)
    (inner outer : ℝ) (z u v : ProjectionSchwartzMatrix) : ℂ :=
  let m := inverseMatrix g
  let S := (thinScreenAngular m i o hm hη inner outer).matrix
  ∑ k : TensorSlot, ∑ l : TensorSlot,
    originalGaugeRadianPair θ gaugeCorrectionInfrared gaugeCorrectionInfrared κ m (metricDensity g) a
      (gaugeFrozenContraction m) S z k l (projectionFullSchwartz u l.1 l.2) (projectionFullSchwartz v k.1 k.2)

theorem originalScreenGaugeMatrixPair_adjoint (θ : ℝ → ℝ) (κ : ℝ) (g : ScreenMatrix)
    (hg : gᵀ = g) (a : E → ℝ) (ha : ∀ ξ, a (-ξ) = -a ξ)
    (i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η)
    (inner outer : ℝ) (z u v : ProjectionSchwartzMatrix) (hReal : ∀ k l x, conj (z k l x) = z k l x) :
    originalScreenGaugeMatrixPair θ κ g a i o hm hη inner outer z v u =
      conj (originalScreenGaugeMatrixPair θ κ g a i o hm hη inner outer z u v) := by
  have hSym : (inverseMatrix g : ScreenMatrix)ᵀ = inverseMatrix g := by
    change g⁻¹ᵀ = g⁻¹
    rw [Matrix.transpose_nonsing_inv, hg]
  simp only [originalScreenGaugeMatrixPair, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  exact originalGaugeRadianPair_adjoint θ gaugeCorrectionInfrared gaugeCorrectionInfrared κ (inverseMatrix g)
    (metricDensity g) a ha (gaugeFrozenContraction _) (gaugeFrozenContraction_symmetric _ hSym) _ z hReal k l _ _

end Burnett.V08
