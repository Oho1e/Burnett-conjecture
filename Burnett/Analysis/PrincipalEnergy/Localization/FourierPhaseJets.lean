import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichSymbol
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option maxHeartbeats 2100000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Burnett.Fourier
open scoped BigOperators ContDiff

private def phaseForm (η : Space) : Space →L[ℝ] ℂ :=
  ((↑(2 * Real.pi) : ℂ) * Complex.I) • Complex.ofRealCLM.comp (innerSL ℝ η)

private theorem phaseForm_apply (η x : Space) :
    phaseForm η x = (↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I := by
  change ((↑(2 * Real.pi) : ℂ) * Complex.I) * (↑(inner ℝ η x) : ℂ) = _
  push_cast
  ring

private theorem phaseForm_norm_le (η : Space) : ‖phaseForm η‖ ≤ (2 * Real.pi) * ‖η‖ := by
  refine (phaseForm η).opNorm_le_bound (by positivity) fun x => ?_
  rw [phaseForm_apply, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  calc
    _ ≤ (2 * Real.pi) * (‖η‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
    _ = _ := by ring

/-- The actual positive Fourier phase has the exact derivative size needed
for the base jets of the cutoff sandwich. -/
theorem fourier_phase_contDiff_and_derivative_bound (η : Space) :
    let Φ (x : Space) := (Real.fourierChar (inner ℝ η x) : ℂ)
    ContDiff ℝ ∞ Φ ∧ ∀ (n : ℕ) (x : Space),
      ‖iteratedFDeriv ℝ n Φ x‖ ≤ ((2 * Real.pi) * ‖η‖)^n := by
  intro Φ
  let L := phaseForm η
  have phase : Φ = fun x => Complex.exp (L x) := by
    funext x
    rw [show Φ x = (Real.fourierChar (inner ℝ η x) : ℂ) from rfl, Real.fourierChar_apply, phaseForm_apply]
  let P (n : ℕ) := (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℂ).compContinuousLinearMap (fun _ => L)
  let p (x : Space) (n : ℕ) := Complex.exp (L x) • P n
  have pEq (x : Space) (n : ℕ) (m : Fin n → Space) :
      p x n m = Complex.exp (L x) * ∏ i, L (m i) := by
    simp only [p, P, ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, smul_eq_mul]
  have hTaylor : HasFTaylorSeriesUpTo ∞ Φ p := by
    refine ⟨?_, ?_, fun n _ => (Complex.continuous_exp.comp L.continuous).smul continuous_const⟩
    · intro x
      rw [ContinuousMultilinearMap.curry0_apply, pEq, phase]
      simp
    · intro n _ x
      have h := (L.hasFDerivAt (x := x)).cexp.smul_const (P n)
      have hStep : (p x (n + 1)).curryLeft = (Complex.exp (L x) • L).smulRight (P n) := by
        ext1 z
        ext1 m
        rw [ContinuousMultilinearMap.curryLeft_apply, pEq, Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply, P,
          ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousMultilinearMap.mkPiAlgebra_apply,
          smul_eq_mul]
        ring
      rw [hStep]
      exact h
  refine ⟨hTaylor.contDiff, fun n x => ?_⟩
  have hP : ‖P n‖ ≤ ‖L‖^n := by
    exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℂ) (fun _ => L)).trans_eq
      (by simp only [ContinuousMultilinearMap.norm_mkPiAlgebra, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, one_mul])
  have hNorm : ‖Complex.exp (L x)‖ = 1 :=
    (congrArg norm (congrFun phase x)).symm.trans (Circle.norm_coe _)
  rw [← hTaylor.eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x]
  change ‖Complex.exp (L x) • P n‖ ≤ _
  rw [norm_smul, hNorm, one_mul]
  exact hP.trans (pow_le_pow_left₀ (norm_nonneg _) (phaseForm_norm_le η) n)

end Burnett.Analysis.CarlesonEmbedding
