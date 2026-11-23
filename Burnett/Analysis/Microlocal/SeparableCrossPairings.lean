import Burnett.Analysis.Microlocal.FixedSubsequenceSeparableLimits

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.SeparablePositive

open MeasureTheory Filter Set Burnett.Fourier Burnett.Microlocal.AngularCommutator
open scoped InnerProduct Topology ComplexConjugate BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The actual ordered square identity with two possibly different input
components. The commutator acts on the original right input component. -/
theorem separableOperator_cross_difference (a b m n : BoundedSymbol V) (u v : ComplexL2 V) :
    inner ℂ (separableOperator a m u) (separableOperator b n v) -
      inner ℂ (squareSymbolTerm a b m n u) v =
      -inner ℂ (fourierMultiplier m u) (cutoffCommutator n (productSymbol (conjugateSymbol a) b) v) := by
  let c := productSymbol (conjugateSymbol a) b
  have hleft : inner ℂ (separableOperator a m u) (separableOperator b n v) =
      inner ℂ (fourierMultiplier m u) (symbolCLM c (fourierMultiplier n v)) := by
    change inner ℂ (symbolCLM a (fourierMultiplier m u)) (symbolCLM b (fourierMultiplier n v)) = _
    rw [inner_symbolCLM_left, ← symbolCLM_product]
  have hright : inner ℂ (squareSymbolTerm a b m n u) v =
      inner ℂ (fourierMultiplier m u) (fourierMultiplier n (symbolCLM c v)) := by
    change inner ℂ (symbolCLM (productSymbol a (conjugateSymbol b))
      (fourierMultiplier (productSymbol (conjugateSymbol n) m) u)) v = _
    rw [fourierMultiplier_product, inner_symbolCLM_left, conjugateSymbol_productSymbol,
      conjugateSymbol_conjugateSymbol, inner_fourierMultiplier_left, conjugateSymbol_conjugateSymbol]
  rw [hleft, hright]
  change _ = -inner ℂ (fourierMultiplier m u)
    (fourierMultiplier n (symbolCLM c v) - symbolCLM c (fourierMultiplier n v))
  rw [inner_sub_right]
  ring

theorem separableOperator_cross_difference_tendsto_zero
    (a b m n : BoundedSymbol V) (u v : ℕ → ComplexL2 V) (B : ℝ) (hB : ∀ k, ‖u k‖ ≤ B)
    (hcomm : Tendsto (fun k => cutoffCommutator n (productSymbol (conjugateSymbol a) b) (v k))
      atTop (𝓝 0)) :
    Tendsto (fun k => inner ℂ (separableOperator a m (u k)) (separableOperator b n (v k)) -
      inner ℂ (squareSymbolTerm a b m n (u k)) (v k)) atTop (𝓝 0) := by
  simp_rw [separableOperator_cross_difference]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim : Tendsto (fun k => m.bound * B *
      ‖cutoffCommutator n (productSymbol (conjugateSymbol a) b) (v k)‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hcomm.norm.const_mul (m.bound * B)
  apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
  intro k
  rw [norm_neg]
  exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans (mul_le_mul_of_nonneg_right
    ((fourierMultiplier_norm_le m (u k)).trans (mul_le_mul_of_nonneg_left (hB k) m.bound_nonneg))
    (norm_nonneg _))

end Burnett.Microlocal.SeparablePositive
