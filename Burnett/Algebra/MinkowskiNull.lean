import Burnett.Algebra.HermitianScreen
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Burnett.RicciSymbol.MinkowskiNull

open scoped BigOperators
open NullScreen

theorem symbolNorm_eq_coordinates (ξ : Covector) :
    symbolNorm minkowskiInverse ξ =
      -(ξ 0)^2 + (ξ 1)^2 + (ξ 2)^2 + (ξ 3)^2 := by
  simp [symbolNorm, minkowskiInverse, Fin.sum_univ_succ, Fin.isValue, pow_two, add_assoc]

/-- Every nonzero Minkowski-null covector has a nonzero temporal component. -/
theorem temporal_component_ne_zero (ξ : Covector) (hξ : ξ ≠ 0)
    (hs : symbolNorm minkowskiInverse ξ = 0) : ξ 0 ≠ 0 := by
  rw [symbolNorm_eq_coordinates] at hs
  intro h0
  rw [h0] at hs
  norm_num at hs
  have h1sq : ξ 1 * ξ 1 = 0 := by
    nlinarith [sq_nonneg (ξ 1), sq_nonneg (ξ 2), sq_nonneg (ξ 3)]
  have h2sq : ξ 2 * ξ 2 = 0 := by
    nlinarith [sq_nonneg (ξ 1), sq_nonneg (ξ 2), sq_nonneg (ξ 3)]
  have h3sq : ξ 3 * ξ 3 = 0 := by
    nlinarith [sq_nonneg (ξ 1), sq_nonneg (ξ 2), sq_nonneg (ξ 3)]
  have h1 : ξ 1 = 0 := (mul_eq_zero.mp h1sq).elim id id
  have h2 : ξ 2 = 0 := (mul_eq_zero.mp h2sq).elim id id
  have h3 : ξ 3 = 0 := (mul_eq_zero.mp h3sq).elim id id
  apply hξ
  funext a
  fin_cases a <;> simp [h0, h1, h2, h3, Fin.isValue]

/-- A concrete gauge vector that removes all temporal components. -/
def temporalGaugeVector (ξ : Covector) (k : Tensor2) : Covector := fun b =>
  (k 0 b - ξ b * k 0 0 / (2 * ξ 0)) / ξ 0

/-- Subtracting the pure gauge tensor without a choice of null-frame rotation. -/
def gaugeFixedRep (ξ : Covector) (k : Tensor2) : Tensor2 :=
  k + pureGauge ξ (-temporalGaugeVector ξ k)

theorem gaugeFixedRep_temporal_row (ξ : Covector) (k : Tensor2) (h0 : ξ 0 ≠ 0) :
    ∀ b, gaugeFixedRep ξ k 0 b = 0 := by
  intro b
  simp only [gaugeFixedRep, Pi.add_apply, pureGauge, Pi.neg_apply, temporalGaugeVector]
  field_simp [h0]
  ring

theorem gaugeFixedRep_symmetric (ξ : Covector) (k : Tensor2)
    (hkSymm : IsSymmetricTensor k) : IsSymmetricTensor (gaugeFixedRep ξ k) := by
  intro a b
  simp only [gaugeFixedRep, Pi.add_apply, pureGauge, Pi.neg_apply]
  rw [hkSymm a b]
  ring

theorem gaugeFixedRep_kernel (ξ : Covector) (k : Tensor2)
    (hk : ∀ a b, ricciSymbol minkowskiInverse ξ k a b = 0) :
    ∀ a b, ricciSymbol minkowskiInverse ξ (gaugeFixedRep ξ k) a b = 0 := by
  intro a b
  rw [gaugeFixedRep, ricciSymbol_add, hk a b,
    ricciSymbol_pureGauge_eq_zero minkowskiInverse ξ (-temporalGaugeVector ξ k)
      minkowskiInverse_symmetric a b, zero_add]

theorem gaugeFixedRep_trace_zero (ξ : Covector) (k : Tensor2)
    (hkSymm : IsSymmetricTensor k) (hξ : ξ ≠ 0)
    (hs : symbolNorm minkowskiInverse ξ = 0)
    (hk : ∀ a b, ricciSymbol minkowskiInverse ξ k a b = 0) :
    metricTrace minkowskiInverse (gaugeFixedRep ξ k) = 0 := by
  have h0 := temporal_component_ne_zero ξ hξ hs
  have hrow := gaugeFixedRep_temporal_row ξ k h0
  have hsymm := gaugeFixedRep_symmetric ξ k hkSymm
  have hcol (a : Index) : gaugeFixedRep ξ k a 0 = 0 := by
    rw [hsymm a 0, hrow a]
  have hq := (null_kernel_iff_contracted minkowskiInverse ξ (gaugeFixedRep ξ k)
    hξ hs).mp (gaugeFixedRep_kernel ξ k hk)
  have hcontract : contracted minkowskiInverse ξ (gaugeFixedRep ξ k) 0 = 0 := by
    unfold contracted
    apply Finset.sum_eq_zero
    intro a ha
    rw [hcol a, mul_zero]
  have hq0 := hq 0
  rw [hcontract] at hq0
  have hmul : metricTrace minkowskiInverse (gaugeFixedRep ξ k) * ξ 0 = 0 := by
    linarith
  exact (mul_eq_zero.mp hmul).resolve_right h0

/-- This is the actual original pairing, not a positivity-defined surrogate. -/
theorem gaugeFixedRep_physicalPairing (ξ : Covector) (k : Tensor2)
    (hkSymm : IsSymmetricTensor k) (hξ : ξ ≠ 0)
    (hs : symbolNorm minkowskiInverse ξ = 0)
    (hk : ∀ a b, ricciSymbol minkowskiInverse ξ k a b = 0) :
    physicalPairing minkowskiInverse (gaugeFixedRep ξ k) (gaugeFixedRep ξ k) =
      physicalPairing minkowskiInverse k k :=
  physicalPairing_add_pureGauge_both minkowskiInverse ξ k k
    (-temporalGaugeVector ξ k) (-temporalGaugeVector ξ k)
    minkowskiInverse_symmetric hkSymm hkSymm hξ hs hk hk

theorem physicalPairing_eq_sum_squares_of_temporal_zero (k : Tensor2)
    (hkSymm : IsSymmetricTensor k) (hrow : ∀ b, k 0 b = 0)
    (htrace : metricTrace minkowskiInverse k = 0) :
    physicalPairing minkowskiInverse k k = ∑ a, ∑ b, (k a b)^2 := by
  have hcol (a : Index) : k a 0 = 0 := by rw [hkSymm a 0, hrow a]
  simp [physicalPairing, htrace, tensorPairing, minkowskiInverse,
    Fin.sum_univ_succ, Fin.isValue, hrow, hcol, pow_two]

/-- Positivity for every nonzero null direction in the fixed Minkowski metric,
using an explicit temporal gauge instead of assuming a screen decomposition. -/
theorem physicalPairing_eq_gaugeFixed_sum_squares (ξ : Covector) (k : Tensor2)
    (hkSymm : IsSymmetricTensor k) (hξ : ξ ≠ 0)
    (hs : symbolNorm minkowskiInverse ξ = 0)
    (hk : ∀ a b, ricciSymbol minkowskiInverse ξ k a b = 0) :
    physicalPairing minkowskiInverse k k =
      ∑ a, ∑ b, (gaugeFixedRep ξ k a b)^2 := by
  calc
    physicalPairing minkowskiInverse k k =
        physicalPairing minkowskiInverse (gaugeFixedRep ξ k) (gaugeFixedRep ξ k) :=
      (gaugeFixedRep_physicalPairing ξ k hkSymm hξ hs hk).symm
    _ = _ := physicalPairing_eq_sum_squares_of_temporal_zero _
      (gaugeFixedRep_symmetric ξ k hkSymm)
      (gaugeFixedRep_temporal_row ξ k (temporal_component_ne_zero ξ hξ hs))
      (gaugeFixedRep_trace_zero ξ k hkSymm hξ hs hk)

theorem physicalPairing_self_nonneg (ξ : Covector) (k : Tensor2)
    (hkSymm : IsSymmetricTensor k) (hξ : ξ ≠ 0)
    (hs : symbolNorm minkowskiInverse ξ = 0)
    (hk : ∀ a b, ricciSymbol minkowskiInverse ξ k a b = 0) :
    0 ≤ physicalPairing minkowskiInverse k k := by
  rw [physicalPairing_eq_gaugeFixed_sum_squares ξ k hkSymm hξ hs hk]
  exact Finset.sum_nonneg fun a ha => Finset.sum_nonneg fun b hb => sq_nonneg _

theorem physicalPairing_self_eq_zero_iff_pureGauge (ξ : Covector) (k : Tensor2)
    (hkSymm : IsSymmetricTensor k) (hξ : ξ ≠ 0)
    (hs : symbolNorm minkowskiInverse ξ = 0)
    (hk : ∀ a b, ricciSymbol minkowskiInverse ξ k a b = 0) :
    physicalPairing minkowskiInverse k k = 0 ↔ ∃ v : Covector, k = pureGauge ξ v := by
  constructor
  · intro hz
    rw [physicalPairing_eq_gaugeFixed_sum_squares ξ k hkSymm hξ hs hk] at hz
    have hrows : ∀ a ∈ (Finset.univ : Finset Index),
        (∑ b, (gaugeFixedRep ξ k a b)^2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun a ha =>
        Finset.sum_nonneg fun b hb => sq_nonneg (gaugeFixedRep ξ k a b))).mp hz
    have hrep : gaugeFixedRep ξ k = 0 := by
      funext a b
      have hab : (gaugeFixedRep ξ k a b)^2 = 0 :=
        ((Finset.sum_eq_zero_iff_of_nonneg (fun b hb =>
          sq_nonneg (gaugeFixedRep ξ k a b))).mp (hrows a (Finset.mem_univ a)))
          b (Finset.mem_univ b)
      exact sq_eq_zero_iff.mp hab
    refine ⟨temporalGaugeVector ξ k, ?_⟩
    funext a b
    have hab := congrFun (congrFun hrep a) b
    simp only [gaugeFixedRep, Pi.add_apply, pureGauge, Pi.neg_apply,
      Pi.zero_apply, mul_neg, neg_mul] at hab
    simp only [pureGauge]
    linarith
  · rintro ⟨v, hv⟩
    calc
      physicalPairing minkowskiInverse k k =
          physicalPairing minkowskiInverse k (pureGauge ξ v) := by rw [← hv]
      _ = 0 := physicalPairing_pureGauge_eq_zero_of_null_kernel
        minkowskiInverse ξ k v minkowskiInverse_symmetric hkSymm hξ hs hk

end Burnett.RicciSymbol.MinkowskiNull
