import Burnett.Algebra.QuadraticDefs

noncomputable section

namespace Burnett.RicciSymbol

open scoped BigOperators

private theorem qe_finset_sum_comm (s t : Finset Index) (f : Index → Index → ℝ) :
    (∑ a ∈ s, ∑ e ∈ t, f a e) = ∑ e ∈ t, ∑ a ∈ s, f a e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, Finset.sum_add_distrib, ih]

private theorem qe_sum_comm (f : Index → Index → ℝ) :
    (∑ a, ∑ e, f a e) = ∑ e, ∑ a, f a e :=
  qe_finset_sum_comm Finset.univ Finset.univ f

private theorem qe_sum_x_raise (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hg : IsSymmetricTensor gInv) (hk : IsSymmetricTensor k) (b : Index) :
    (∑ a, ξ a * raiseSecond gInv k b a) = contracted gInv ξ k b := by
  unfold raiseSecond contracted raiseCovector
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [qe_sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro a ha
  rw [hg a d, hk b d]
  ring

private theorem qe_sum_x_raised (gInv : Tensor2) (ξ : Covector) :
    (∑ a, ξ a * raiseCovector gInv ξ a) = symbolNorm gInv ξ := by
  unfold raiseCovector symbolNorm
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  ring

private theorem qe_raised_trace (gInv k : Tensor2) :
    (∑ a, raiseSecond gInv k a a) = metricTrace gInv k := by
  rfl

private theorem qe_raise_contract (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (a : Index) :
    (∑ e, raiseSecond gInv k e a * raiseCovector gInv ξ e) =
      ∑ d, gInv a d * contracted gInv ξ k d := by
  unfold raiseSecond contracted
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [qe_sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  ring

private theorem qe_mixed (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hg : IsSymmetricTensor gInv) (b : Index) :
    (∑ a, ∑ e, raiseSecond gInv k e a * raiseCovector gInv ξ e * k b a) =
      ∑ e, raiseSecond gInv k b e * contracted gInv ξ k e := by
  calc
    _ = ∑ a, (∑ e, raiseSecond gInv k e a * raiseCovector gInv ξ e) * k b a := by
      simp only [Finset.sum_mul]
    _ = ∑ a, (∑ d, gInv a d * contracted gInv ξ k d) * k b a := by
      simp only [qe_raise_contract]
    _ = ∑ d, ∑ a, gInv a d * contracted gInv ξ k d * k b a := by
      simp only [Finset.sum_mul]
      rw [qe_sum_comm]
    _ = _ := by
      unfold raiseSecond
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro a ha
      rw [hg a d]
      ring

private theorem qe_square_swap (gInv k : Tensor2)
    (hg : IsSymmetricTensor gInv) (hk : IsSymmetricTensor k) (b c : Index) :
    (∑ a, raiseSecond gInv k c a * k b a) = tensorSquare gInv k b c := by
  simp only [tensorSquare, raiseSecond, Finset.sum_mul]
  rw [qe_sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro a ha
  rw [hg a d, hk c d]
  ring

private theorem qe_pairing (gInv k : Tensor2)
    (hg : IsSymmetricTensor gInv) (hk : IsSymmetricTensor k) :
    (∑ a, ∑ e, raiseSecond gInv k e a * raiseSecond gInv k a e) =
      tensorPairing gInv k k := by
  simp only [raiseSecond, tensorPairing, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ a, ∑ e, ∑ d, ∑ f, gInv a d * k e d * (gInv e f * k a f) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro e he
      rw [qe_sum_comm]
    _ = ∑ e, ∑ d, ∑ f, ∑ a, gInv a d * k e d * (gInv e f * k a f) := by
      rw [qe_sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      rw [qe_sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [qe_sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro f hf
      apply Finset.sum_congr rfl
      intro a ha
      rw [hg a d, hk a f]
      ring

/-- The contracted connection symbol, paper/burnett.tex line 445. -/
theorem connectionSymbol_trace (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hg : IsSymmetricTensor gInv) (hk : IsSymmetricTensor k) (e : Index) :
    (∑ a, connectionSymbol gInv ξ k a a e) =
      ξ e * metricTrace gInv k / 2 := by
  unfold connectionSymbol
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [qe_sum_x_raise gInv ξ k hg hk, qe_raised_trace]
  change (contracted gInv ξ k e + ξ e * metricTrace gInv k -
    contracted gInv ξ k e) / 2 = _
  ring

private theorem qe_mixed_first (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hg : IsSymmetricTensor gInv) (hk : IsSymmetricTensor k) (b : Index) :
    (∑ a, ∑ e, ξ a * raiseSecond gInv k e a * raiseSecond gInv k b e) =
      ∑ e, raiseSecond gInv k b e * contracted gInv ξ k e := by
  rw [qe_sum_comm]
  simp only [← Finset.sum_mul, qe_sum_x_raise gInv ξ k hg hk]
  apply Finset.sum_congr rfl
  intro e he
  ring

private theorem qe_mixed_fourth (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hg : IsSymmetricTensor gInv) (hk : IsSymmetricTensor k) (c : Index) :
    (∑ a, ∑ e, ξ e * raiseSecond gInv k a e * raiseSecond gInv k c a) =
      ∑ a, raiseSecond gInv k c a * contracted gInv ξ k a := by
  simp only [← Finset.sum_mul, qe_sum_x_raise gInv ξ k hg hk]
  apply Finset.sum_congr rfl
  intro a ha
  ring

private theorem qe_mixed_seventh (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hg : IsSymmetricTensor gInv) (c : Index) :
    (∑ a, ∑ e, raiseSecond gInv k a e * raiseCovector gInv ξ a * k c e) =
      ∑ a, raiseSecond gInv k c a * contracted gInv ξ k a := by
  rw [qe_sum_comm]
  exact qe_mixed gInv ξ k hg c

private theorem qe_square_direct (gInv k : Tensor2)
    (hk : IsSymmetricTensor k) (b c : Index) :
    (∑ e, raiseSecond gInv k b e * k c e) = tensorSquare gInv k b c := by
  unfold tensorSquare
  apply Finset.sum_congr rfl
  intro e he
  rw [hk c e]

private theorem qe_contract_swap (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hk : IsSymmetricTensor k) (b : Index) :
    (∑ a, raiseCovector gInv ξ a * k b a) = contracted gInv ξ k b := by
  unfold contracted
  apply Finset.sum_congr rfl
  intro a ha
  rw [hk b a]

/-- The nine-term first connection product, with the cancelling mixed terms
already combined. This is paper/burnett.tex lines 437--443. -/
theorem four_connectionSymbol_first_product
    (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hg : IsSymmetricTensor gInv) (hk : IsSymmetricTensor k) (b c : Index) :
    4 * (∑ a, ∑ e, connectionSymbol gInv ξ k a c e *
      connectionSymbol gInv ξ k e b a) =
    ξ b * ξ c * tensorPairing gInv k k +
      2 * contracted gInv ξ k b * contracted gInv ξ k c -
      2 * symbolNorm gInv ξ * tensorSquare gInv k b c := by
  calc
    _ = ξ b * ξ c * (∑ a, ∑ e, raiseSecond gInv k e a * raiseSecond gInv k a e) +
        ξ c * (∑ a, ∑ e, ξ a * raiseSecond gInv k e a * raiseSecond gInv k b e) -
        ξ c * (∑ a, ∑ e, raiseSecond gInv k e a * raiseCovector gInv ξ e * k b a) +
        ξ b * (∑ a, ∑ e, ξ e * raiseSecond gInv k a e * raiseSecond gInv k c a) +
        (∑ e, ξ e * raiseSecond gInv k b e) * (∑ a, ξ a * raiseSecond gInv k c a) -
        (∑ e, ξ e * raiseCovector gInv ξ e) * (∑ a, raiseSecond gInv k c a * k b a) -
        ξ b * (∑ a, ∑ e, raiseSecond gInv k a e * raiseCovector gInv ξ a * k c e) -
        (∑ e, raiseSecond gInv k b e * k c e) * (∑ a, ξ a * raiseCovector gInv ξ a) +
        (∑ e, raiseCovector gInv ξ e * k c e) *
          (∑ a, raiseCovector gInv ξ a * k b a) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro e he
      unfold connectionSymbol
      ring
    _ = _ := by
      rw [qe_pairing gInv k hg hk, qe_mixed_first gInv ξ k hg hk,
        qe_mixed gInv ξ k hg, qe_mixed_fourth gInv ξ k hg hk,
        qe_mixed_seventh gInv ξ k hg, qe_sum_x_raise gInv ξ k hg hk,
        qe_sum_x_raise gInv ξ k hg hk, qe_square_swap gInv k hg hk,
        qe_sum_x_raised, qe_square_direct gInv k hk,
        qe_contract_swap gInv ξ k hk, qe_contract_swap gInv ξ k hk]
      ring

/-- The traced second connection product in the full quadratic expansion. -/
theorem four_connectionSymbol_second_product
    (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hg : IsSymmetricTensor gInv) (hk : IsSymmetricTensor k) (b c : Index) :
    4 * (∑ a, ∑ e, connectionSymbol gInv ξ k a a e *
      connectionSymbol gInv ξ k e b c) =
    metricTrace gInv k *
      (ξ b * contracted gInv ξ k c + ξ c * contracted gInv ξ k b -
        symbolNorm gInv ξ * k b c) := by
  rw [qe_sum_comm]
  simp only [← Finset.sum_mul, connectionSymbol_trace gInv ξ k hg hk]
  calc
    _ = metricTrace gInv k *
        (ξ b * (∑ e, ξ e * raiseSecond gInv k c e) +
          ξ c * (∑ e, ξ e * raiseSecond gInv k b e) -
          (∑ e, ξ e * raiseCovector gInv ξ e) * k b c) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      unfold connectionSymbol
      ring
    _ = _ := by
      rw [qe_sum_x_raise gInv ξ k hg hk, qe_sum_x_raise gInv ξ k hg hk,
        qe_sum_x_raised]

/-- The complete real ordered-index quadratic algebra identity, exactly
paper/burnett.tex equation (B-algebra), lines 447--448. Symmetry is the only
algebraic hypothesis; no Ricci-kernel or null condition is imposed. -/
theorem four_quadraticSymbol_expansion
    (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hg : IsSymmetricTensor gInv) (hk : IsSymmetricTensor k) (b c : Index) :
    4 * quadraticSymbol gInv ξ k b c =
      ξ b * ξ c * tensorPairing gInv k k +
      2 * contracted gInv ξ k b * contracted gInv ξ k c -
      2 * symbolNorm gInv ξ * tensorSquare gInv k b c -
      metricTrace gInv k *
        (ξ b * contracted gInv ξ k c + ξ c * contracted gInv ξ k b -
          symbolNorm gInv ξ * k b c) := by
  unfold quadraticSymbol
  simp only [Finset.sum_sub_distrib, mul_sub]
  rw [four_connectionSymbol_first_product gInv ξ k hg hk,
    four_connectionSymbol_second_product gInv ξ k hg hk]
  ring

end Burnett.RicciSymbol
