import Burnett.Analysis.TransportWard.Weyl.RightSchwartzSymbol
import Burnett.Analysis.FrozenTransport.V03SegmentTaylor

/-! Exact scalar input-side coefficient commutator and its first Taylor
term in the actual Fourier frequency. -/

set_option autoImplicit false
set_option maxHeartbeats 6900000
set_option maxRecDepth 4800

noncomputable section

namespace Burnett.V03

open Function MeasureTheory Filter Set Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic Burnett.Analysis.CarlesonEmbedding
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped FourierTransform ContDiff BigOperators Interval

theorem integrable_coefficientFourierFactor_mul (c : SchwartzMap E ℂ) (x : E)
    {f : E → ℂ} (hf : Continuous f) (n : ℕ) {C : ℝ}
    (hC : ∀ η, ‖f η‖ ≤ C * (1 + ‖η‖)^n) :
    Integrable (fun η => coefficientFourierFactor c x η * f η) (volume : Measure E) := by
  let F := SchwartzMap.fourierTransformCLM ℂ c
  have hQ : Continuous (fun η => coefficientFourierFactor c x η * f η) :=
    (coefficientFourierFactor_continuous c x).mul hf
  refine ((integrable_schwartz_weighted F n).const_mul C).mono' hQ.aestronglyMeasurable ?_
  filter_upwards with η
  simp only [coefficientFourierFactor, norm_mul, patch_fourier_phase_norm, one_mul]
  have h := mul_le_mul_of_nonneg_left (hC η) (norm_nonneg ((𝓕 (c : E → ℂ)) η))
  refine h.trans_eq ?_
  simp only [F, SchwartzMap.fourierTransformCLM_apply]
  ring

/-- The exact left symbol of `i[B,c]`, where `[B,c]u=B(cu)-cBu`. -/
def coefficientCommutatorSymbol (a : E → E → ℂ) (c : SchwartzMap E ℂ) (x ξ : E) : ℂ :=
  Complex.I * (rightSchwartzSymbol a c x ξ - c x * a x ξ)

theorem firstOrderAction_coefficientCommutatorSymbol {a : E → E → ℂ} (ha : FrequencyOrderOne a)
    (c u : SchwartzMap E ℂ) (x : E) :
    firstOrderAction (coefficientCommutatorSymbol a c) u x =
      Complex.I * (firstOrderAction a (scalarSchwartzProduct c u) x - c x * firstOrderAction a u x) := by
  obtain ⟨hEq, hRight⟩ := firstOrderAction_rightSchwartzSymbol ha c u x
  obtain ⟨C,_,hC⟩ := ha.order 0
  have hA : Integrable (leftActionIntegrand a u x) volume :=
    leftActionIntegrand_integrable_of_growth u x (ha.smooth x).continuous 1
      (fun ξ => by simpa only [pow_zero,pow_one,mul_one,norm_iteratedFDeriv_zero] using hC x ξ)
  have hSymbol : leftActionIntegrand (coefficientCommutatorSymbol a c) u x =
      fun ξ => Complex.I * (leftActionIntegrand (rightSchwartzSymbol a c) u x ξ -
        c x * leftActionIntegrand a u x ξ) := by
    funext ξ
    simp only [leftActionIntegrand, coefficientCommutatorSymbol]
    ring
  rw [firstOrderAction_eq_leftActionIntegrand, hSymbol, integral_const_mul,
    integral_sub hRight (hA.const_mul _), integral_const_mul,
    ← firstOrderAction_eq_leftActionIntegrand, ← firstOrderAction_eq_leftActionIntegrand, hEq]

/-- The true Taylor remainder in the right composition, including the
factor (i) already present in the energy commutator. -/
def coefficientCommutatorRemainder (a : E → E → ℂ) (c : SchwartzMap E ℂ) (x ξ : E) : ℂ :=
  Complex.I * (∫ η, coefficientFourierFactor c x η * linearTaylorRemainder (a x) ξ η)

/-- The coefficient derivative and the Fourier-symbol derivative in cycles
are paired with precisely one inverse radian conversion. -/
def coefficientCommutatorLeading (a : E → E → ℂ) (c : SchwartzMap E ℂ) (x ξ : E) : ℂ :=
  ∑ k : Fin 4, (tau : ℂ)⁻¹ * (frozenSchwartzCoordinatePartial k c) x *
    fderiv ℝ (a x) ξ (coordinateDirection k)

private theorem coefficientFourier_linearMoment (c : SchwartzMap E ℂ) (x : E) (L : E →L[ℝ] ℂ) :
    Complex.I * (∫ η, coefficientFourierFactor c x η * L η) =
      ∑ k : Fin 4, (tau : ℂ)⁻¹ * (frozenSchwartzCoordinatePartial k c) x * L (coordinateDirection k) := by
  have apply_basis (η : E) : L η = ∑ k : Fin 4, (η k : ℂ) * L (coordinateDirection k) := by
    have h := ((EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr η).symm
    calc
      _ = L (∑ k, (EuclideanSpace.basisFun (Fin 4) ℝ).repr η k •
          EuclideanSpace.basisFun (Fin 4) ℝ k) := congrArg L h
      _ = _ := by
        simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
          map_sum, map_smul, Complex.real_smul, coordinateDirection]
  have hK (k : Fin 4) : Integrable
      (fun η : E => coefficientFourierFactor c x η * (η k : ℂ)) volume := by
    apply integrable_coefficientFourierFactor_mul c x (Complex.continuous_ofReal.comp (EuclideanSpace.proj k).continuous) 1 (C := 1)
    intro η
    change ‖(η k : ℂ)‖ ≤ 1 * (1 + ‖η‖)^1
    simp only [Complex.norm_real, pow_one, one_mul]
    exact (PiLp.norm_apply_le η k).trans (le_add_of_nonneg_left zero_le_one)
  have hInt (k : Fin 4) : Integrable
      (fun η : E => (coefficientFourierFactor c x η * (η k : ℂ)) * L (coordinateDirection k)) volume :=
    (hK k).mul_const _
  calc
    _ = Complex.I * (∫ η, ∑ k : Fin 4,
        (coefficientFourierFactor c x η * (η k : ℂ)) * L (coordinateDirection k)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with η
      rw [apply_basis η, Finset.mul_sum]
      simp only [mul_assoc]
    _ = _ := by
      rw [integral_finset_sum _ (fun k _ => hInt k), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [integral_mul_const, ← mul_assoc, coefficientFourier_firstMoment]

theorem coefficientCommutatorSymbol_eq_leading_add_remainder {a : E → E → ℂ}
    (ha : FrequencyOrderOne a) (c : SchwartzMap E ℂ) (x ξ : E) :
    coefficientCommutatorSymbol a c x ξ =
      coefficientCommutatorLeading a c x ξ + coefficientCommutatorRemainder a c x ξ := by
  let K (η : E) := coefficientFourierFactor c x η
  let L := fderiv ℝ (a x) ξ
  let T (η : E) := linearTaylorRemainder (a x) ξ η
  obtain ⟨C,hC,hBound⟩ := ha.order 0
  have hShift : Integrable (fun η => K η * a x (ξ+η)) volume := by
    refine integrable_coefficientFourierFactor_mul c x ((ha.smooth x).continuous.comp
      (continuous_const.add continuous_id)) 1 (C := C*(1+‖ξ‖)) (fun η => ?_)
    have hb : ‖a x (ξ+η)‖ ≤ C*(1+‖ξ+η‖) := by
      simpa only [pow_zero,mul_one,norm_iteratedFDeriv_zero] using hBound x (ξ+η)
    have hAdd : 1+‖ξ+η‖ ≤ (1+‖ξ‖)*(1+‖η‖) := by
      nlinarith only [norm_add_le ξ η, mul_nonneg (norm_nonneg ξ) (norm_nonneg η)]
    simpa only [pow_one, mul_assoc] using hb.trans (mul_le_mul_of_nonneg_left hAdd hC)
  have hA : Integrable (fun η => K η * a x ξ) volume :=
    integrable_coefficientFourierFactor_mul c x continuous_const 0 (C := ‖a x ξ‖)
      (fun η => by simp only [pow_zero,mul_one,le_refl])
  have hL : Integrable (fun η => K η * L η) volume :=
    integrable_coefficientFourierFactor_mul c x L.continuous 1 (C := ‖L‖) fun η =>
      (L.le_opNorm η).trans (by simpa only [pow_one] using
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one : ‖η‖ ≤ 1+‖η‖) (norm_nonneg L))
  have hT : Integrable (fun η => K η * T η) volume :=
    ((hShift.sub hA).sub hL).congr (Eventually.of_forall fun η => by
      change (K η * a x (ξ+η) - K η * a x ξ) - K η * L η = K η * T η
      simp only [T, L, linearTaylorRemainder]
      ring)
  have hDecompose : (∫ η, K η * a x (ξ+η)) =
      (∫ η, K η * a x ξ) + (∫ η, K η * L η) + (∫ η, K η * T η) := by
    have hAL : Integrable (fun η => K η * a x ξ + K η * L η) volume := hA.add hL
    rw [← integral_add hA hL, ← integral_add hAL hT]
    apply integral_congr_ae
    filter_upwards with η
    change K η * a x (ξ+η) = K η * a x ξ + K η * L η + K η * T η
    simp only [T,L,linearTaylorRemainder]
    ring
  change Complex.I * ((∫ η, K η * a x (ξ+η)) - c x * a x ξ) =
    coefficientCommutatorLeading a c x ξ + Complex.I * (∫ η, K η * T η)
  rw [hDecompose, integral_mul_const,
    show (∫ η, K η) = c x from coefficientFourier_zeroMoment c x]
  have hLin : Complex.I * (∫ η, K η * L η) = coefficientCommutatorLeading a c x ξ :=
    coefficientFourier_linearMoment c x L
  rw [← hLin]
  ring

theorem coefficientCommutatorRemainder_eq_segment {a : E → E → ℂ} (ha : FrequencyOrderOne a)
    (c : SchwartzMap E ℂ) (x ξ : E) :
    coefficientCommutatorRemainder a c x ξ = Complex.I * (∫ η,
      coefficientFourierFactor c x η *
        (∫ t in (0 : ℝ)..1, (1-t) • secondFDeriv (a x) (ξ+t • η) η η)) := by
  simp only [coefficientCommutatorRemainder]
  congr 1
  apply integral_congr_ae
  filter_upwards with η
  exact congrArg (fun z => coefficientFourierFactor c x η * z)
    (linearTaylorRemainder_eq_integral (a x) isOpen_univ (ha.smooth x).contDiffOn ξ η
      (fun t _ => mem_univ (fieldSegment ξ η t)))

end Burnett.V03
