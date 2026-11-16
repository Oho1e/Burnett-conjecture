import Burnett.Algebra.NullKernel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Burnett.RicciSymbol.NullScreen

open scoped BigOperators

/-- The inverse Minkowski metric in the signature used in the paper. -/
def minkowskiInverse : Tensor2 :=
  fun a b => if a = b then (if a = 0 then -1 else 1) else 0

/-- A fixed nonzero null covector. This module is a coordinate-normal-form
calculation; existence of such a frame for arbitrary Lorentz data is separate. -/
def nullCovector : Covector :=
  fun a => if a = 0 then -1 else if a = 1 then 1 else 0

theorem minkowskiInverse_symmetric : IsSymmetricTensor minkowskiInverse := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [minkowskiInverse, Fin.isValue]

theorem nullCovector_ne_zero : nullCovector ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [nullCovector] at h0

theorem nullCovector_symbolNorm : symbolNorm minkowskiInverse nullCovector = 0 := by
  simp [symbolNorm, minkowskiInverse, nullCovector, Fin.sum_univ_succ, Fin.isValue]

/-- Explicit component constraints derived from the original Ricci symbol.
The last identity is the trace-free screen constraint. -/
theorem kernel_constraints (k : Tensor2) (hkSymm : IsSymmetricTensor k)
    (hk : ∀ a b, ricciSymbol minkowskiInverse nullCovector k a b = 0) :
    k 0 0 + 2 * k 0 1 + k 1 1 = 0 ∧
    k 0 2 + k 1 2 = 0 ∧ k 0 3 + k 1 3 = 0 ∧ k 2 2 + k 3 3 = 0 := by
  have hq := (null_kernel_iff_contracted minkowskiInverse nullCovector k
    nullCovector_ne_zero nullCovector_symbolNorm).mp hk
  have h0 := hq 0
  have h1 := hq 1
  have h2 := hq 2
  have h3 := hq 3
  simp [contracted, raiseCovector, metricTrace, minkowskiInverse,
    nullCovector, Fin.sum_univ_succ, Fin.isValue] at h0 h1 h2 h3
  rw [hkSymm 1 0] at h0
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The two independent components of a trace-free symmetric screen tensor. -/
def screenTensor (a b : ℝ) : Tensor2 := fun i j =>
  if i = 2 ∧ j = 2 then a else
  if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then b else
  if i = 3 ∧ j = 3 then -a else 0

theorem screenTensor_symmetric (a b : ℝ) : IsSymmetricTensor (screenTensor a b) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [screenTensor, Fin.isValue]

/-- Every pair of real screen coordinates gives an actual kernel amplitude. -/
theorem screenTensor_kernel (a b : ℝ) :
    ∀ i j, ricciSymbol minkowskiInverse nullCovector (screenTensor a b) i j = 0 := by
  apply (null_kernel_iff_contracted minkowskiInverse nullCovector (screenTensor a b)
    nullCovector_ne_zero nullCovector_symbolNorm).mpr
  intro i
  fin_cases i <;>
    simp [metricTrace, contracted, raiseCovector,
      minkowskiInverse, nullCovector, screenTensor, Fin.sum_univ_succ, Fin.isValue]

/-- A gauge covector chosen from the longitudinal components of the amplitude. -/
def gaugeVector (k : Tensor2) : Covector := fun i =>
  if i = 0 then -k 0 0 / 2 else
  if i = 1 then k 1 1 / 2 else
  if i = 2 then -k 0 2 else -k 0 3

/-- Every symmetric kernel amplitude is the sum of an explicitly constructed
pure gauge tensor and its trace-free screen part. -/
theorem kernel_decomposition (k : Tensor2) (hkSymm : IsSymmetricTensor k)
    (hk : ∀ a b, ricciSymbol minkowskiInverse nullCovector k a b = 0) :
    k = pureGauge nullCovector (gaugeVector k) + screenTensor (k 2 2) (k 2 3) := by
  obtain ⟨h01, h02, h03, htr⟩ := kernel_constraints k hkSymm hk
  have h10 := hkSymm 1 0
  have h20 := hkSymm 2 0
  have h30 := hkSymm 3 0
  have h21 := hkSymm 2 1
  have h31 := hkSymm 3 1
  have h32 := hkSymm 3 2
  funext a b
  fin_cases a <;> fin_cases b <;>
    simp [pureGauge, nullCovector, gaugeVector, screenTensor, Pi.add_apply, Fin.isValue] <;>
    linarith

/-- In these fixed null coordinates, the original ordered-pair contraction
reduces to the ordinary Euclidean pairing of the two screen components. -/
theorem physicalPairing_eq_screen (k l : Tensor2)
    (hkSymm : IsSymmetricTensor k) (hlSymm : IsSymmetricTensor l)
    (hk : ∀ a b, ricciSymbol minkowskiInverse nullCovector k a b = 0)
    (hl : ∀ a b, ricciSymbol minkowskiInverse nullCovector l a b = 0) :
    physicalPairing minkowskiInverse k l =
      2 * (k 2 2 * l 2 2 + k 2 3 * l 2 3) := by
  obtain ⟨hk01, hk02, hk03, hktr⟩ := kernel_constraints k hkSymm hk
  obtain ⟨hl01, hl02, hl03, hltr⟩ := kernel_constraints l hlSymm hl
  have hk11 : k 1 1 = -k 0 0 - 2 * k 0 1 := by linarith
  have hk12 : k 1 2 = -k 0 2 := by linarith
  have hk13 : k 1 3 = -k 0 3 := by linarith
  have hk33 : k 3 3 = -k 2 2 := by linarith
  have hl11 : l 1 1 = -l 0 0 - 2 * l 0 1 := by linarith
  have hl12 : l 1 2 = -l 0 2 := by linarith
  have hl13 : l 1 3 = -l 0 3 := by linarith
  have hl33 : l 3 3 = -l 2 2 := by linarith
  simp [physicalPairing, tensorPairing, metricTrace, minkowskiInverse,
    Fin.sum_univ_succ, Fin.isValue]
  rw [hkSymm 1 0, hkSymm 2 0, hkSymm 3 0, hkSymm 2 1,
    hkSymm 3 1, hkSymm 3 2, hlSymm 1 0, hlSymm 2 0, hlSymm 3 0,
    hlSymm 2 1, hlSymm 3 1, hlSymm 3 2,
    hk11, hk12, hk13, hk33, hl11, hl12, hl13, hl33]
  ring

theorem physicalPairing_self_eq_screen (k : Tensor2)
    (hkSymm : IsSymmetricTensor k)
    (hk : ∀ a b, ricciSymbol minkowskiInverse nullCovector k a b = 0) :
    physicalPairing minkowskiInverse k k = 2 * ((k 2 2)^2 + (k 2 3)^2) := by
  simpa only [pow_two] using physicalPairing_eq_screen k k hkSymm hkSymm hk hk

theorem physicalPairing_self_nonneg (k : Tensor2)
    (hkSymm : IsSymmetricTensor k)
    (hk : ∀ a b, ricciSymbol minkowskiInverse nullCovector k a b = 0) :
    0 ≤ physicalPairing minkowskiInverse k k := by
  rw [physicalPairing_self_eq_screen k hkSymm hk]
  exact mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- On the symmetric kernel, zero physical norm is exactly pure gauge. -/
theorem physicalPairing_self_eq_zero_iff_pureGauge (k : Tensor2)
    (hkSymm : IsSymmetricTensor k)
    (hk : ∀ a b, ricciSymbol minkowskiInverse nullCovector k a b = 0) :
    physicalPairing minkowskiInverse k k = 0 ↔
      ∃ v : Covector, k = pureGauge nullCovector v := by
  constructor
  · intro hz
    have heq := physicalPairing_self_eq_screen k hkSymm hk
    have h22sq : k 2 2 * k 2 2 = 0 := by
      nlinarith [sq_nonneg (k 2 2), sq_nonneg (k 2 3)]
    have h23sq : k 2 3 * k 2 3 = 0 := by
      nlinarith [sq_nonneg (k 2 2), sq_nonneg (k 2 3)]
    have h22 : k 2 2 = 0 := (mul_eq_zero.mp h22sq).elim id id
    have h23 : k 2 3 = 0 := (mul_eq_zero.mp h23sq).elim id id
    refine ⟨gaugeVector k, ?_⟩
    calc
      k = pureGauge nullCovector (gaugeVector k) +
          screenTensor (k 2 2) (k 2 3) := kernel_decomposition k hkSymm hk
      _ = pureGauge nullCovector (gaugeVector k) := by
        rw [h22, h23]
        funext a b
        simp [screenTensor]
  · rintro ⟨v, hv⟩
    calc
      physicalPairing minkowskiInverse k k =
          physicalPairing minkowskiInverse k (pureGauge nullCovector v) := by rw [← hv]
      _ = 0 := physicalPairing_pureGauge_eq_zero_of_null_kernel
        minkowskiInverse nullCovector k v minkowskiInverse_symmetric hkSymm
        nullCovector_ne_zero nullCovector_symbolNorm hk

end Burnett.RicciSymbol.NullScreen
