import Burnett.Algebra.QuadraticDefs

noncomputable section

namespace Burnett.RicciSymbol

open scoped BigOperators

private theorem index_sum_comm (f : Index → Index → ℝ) :
    (∑ a, ∑ b, f a b) = ∑ b, ∑ a, f a b := by
  classical
  have h (s : Finset Index) :
      (∑ a ∈ s, ∑ b, f a b) = ∑ b, ∑ a ∈ s, f a b := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, ih, Finset.sum_add_distrib]
  simpa using h Finset.univ

/-- At a nonzero real null covector, the Ricci-symbol kernel is precisely
the constraint `q = t ξ / 2`. No metric or amplitude symmetry is needed here. -/
theorem null_kernel_iff_contracted
    (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0) :
    (∀ a b, ricciSymbol gInv ξ k a b = 0) ↔
      ∀ b, contracted gInv ξ k b = metricTrace gInv k * ξ b / 2 := by
  classical
  constructor
  · intro hk
    have hex : ∃ i, ξ i ≠ 0 := by
      by_contra h
      apply hξ
      funext i
      apply Classical.byContradiction
      intro hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    have hii := hk i i
    simp only [ricciSymbol, hs, zero_mul, zero_add] at hii
    have hid : ξ i * (metricTrace gInv k * ξ i -
        2 * contracted gInv ξ k i) = 0 := by nlinarith [hii]
    have hiq : contracted gInv ξ k i = metricTrace gInv k * ξ i / 2 := by
      have hz := (mul_eq_zero.mp hid).resolve_left hi
      linarith
    intro b
    have hib := hk i b
    simp only [ricciSymbol, hs, zero_mul, zero_add, hiq] at hib
    have hbd : ξ i * (metricTrace gInv k * ξ b -
        2 * contracted gInv ξ k b) = 0 := by nlinarith [hib]
    have hz := (mul_eq_zero.mp hbd).resolve_left hi
    linarith
  · intro hq a b
    simp only [ricciSymbol, hs, zero_mul, zero_add, hq]
    ring

/-- Ordered contraction of a tensor against an outer product. -/
theorem tensorPairing_outerProduct (gInv k : Tensor2) (u v : Covector) :
    tensorPairing gInv k (fun c d => u c * v d) =
      ∑ a, ∑ b, raiseCovector gInv u a * raiseCovector gInv v b * k a b := by
  simp only [tensorPairing, raiseCovector, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [index_sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The two ordered contractions in a pure gauge tensor agree for symmetric `k`. -/
theorem tensorPairing_pureGauge (gInv k : Tensor2) (ξ v : Covector)
    (hkSymm : IsSymmetricTensor k) :
    tensorPairing gInv k (pureGauge ξ v) =
      2 * ∑ b, contracted gInv ξ k b * raiseCovector gInv v b := by
  have hsplit : tensorPairing gInv k (pureGauge ξ v) =
      tensorPairing gInv k (fun c d => ξ c * v d) +
      tensorPairing gInv k (fun c d => v c * ξ d) := by
    simp only [tensorPairing, pureGauge, mul_add, Finset.sum_add_distrib]
  have hfirst : tensorPairing gInv k (fun c d => ξ c * v d) =
      ∑ b, contracted gInv ξ k b * raiseCovector gInv v b := by
    rw [tensorPairing_outerProduct, index_sum_comm]
    simp only [contracted, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hsecond : tensorPairing gInv k (fun c d => v c * ξ d) =
      tensorPairing gInv k (fun c d => ξ c * v d) := by
    rw [tensorPairing_outerProduct, tensorPairing_outerProduct, index_sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro a ha
    rw [hkSymm b a]
    ring
  rw [hsplit, hsecond, hfirst]
  ring

/-- Trace of a pure gauge tensor for a symmetric inverse metric. -/
theorem metricTrace_pureGauge (gInv : Tensor2) (ξ v : Covector)
    (hgSymm : IsSymmetricTensor gInv) :
    metricTrace gInv (pureGauge ξ v) =
      2 * ∑ a, ξ a * raiseCovector gInv v a := by
  have hsplit : metricTrace gInv (pureGauge ξ v) =
      metricTrace gInv (fun a b => ξ a * v b) +
      metricTrace gInv (fun a b => v a * ξ b) := by
    simp only [metricTrace, pureGauge, mul_add, Finset.sum_add_distrib]
  have hfirst : metricTrace gInv (fun a b => ξ a * v b) =
      ∑ a, ξ a * raiseCovector gInv v a := by
    simp only [metricTrace, raiseCovector, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hsecond : metricTrace gInv (fun a b => v a * ξ b) =
      metricTrace gInv (fun a b => ξ a * v b) := by
    simp only [metricTrace]
    rw [index_sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [hgSymm b a]
    ring
  rw [hsplit, hsecond, hfirst]
  ring

/-- Real physical/gauge cross cancellation on the null Ricci-symbol kernel,
using the original ordered tensor pairing, not a reduced screen contraction. -/
theorem physicalPairing_pureGauge_eq_zero_of_null_kernel
    (gInv : Tensor2) (ξ : Covector) (k : Tensor2) (v : Covector)
    (hgSymm : IsSymmetricTensor gInv) (hkSymm : IsSymmetricTensor k)
    (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0)
    (hk : ∀ a b, ricciSymbol gInv ξ k a b = 0) :
    physicalPairing gInv k (pureGauge ξ v) = 0 := by
  have hq := (null_kernel_iff_contracted gInv ξ k hξ hs).mp hk
  have hsum : (∑ b, contracted gInv ξ k b * raiseCovector gInv v b) =
      metricTrace gInv k / 2 * ∑ b, ξ b * raiseCovector gInv v b := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [hq b]
    ring
  rw [physicalPairing, tensorPairing_pureGauge gInv k ξ v hkSymm,
    metricTrace_pureGauge gInv ξ v hgSymm, hsum]
  ring

end Burnett.RicciSymbol
