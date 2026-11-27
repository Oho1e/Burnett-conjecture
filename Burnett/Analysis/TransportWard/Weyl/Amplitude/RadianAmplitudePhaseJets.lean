import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalAmplitudeShift

set_option autoImplicit false
set_option maxHeartbeats 4300000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal RealInnerProductSpace Topology

private def radianBasePhaseExponent (η : E) : E →L[ℝ] ℂ :=
  ((innerSL ℝ) η).smulRight ((tau : ℂ)*Complex.I)

private theorem radian_base_phase_exponent_arg (η x : E) :
    radianBasePhaseExponent η x = ((tau * inner ℝ η x : ℝ) : ℂ) * Complex.I := by
  change ((inner ℝ η x : ℝ) : ℂ)*((tau : ℂ)*Complex.I) = _
  rw [Complex.ofReal_mul tau (inner ℝ η x),← mul_assoc,
    mul_comm ((inner ℝ η x : ℝ) : ℂ) (tau : ℂ)]

/-- Smoothness of the actual base-dependent Fourier phase. -/
theorem radian_base_phase_smooth (η : E) :
    ContDiff ℝ ∞ (patchFourierPhase η) := by
  have eq : patchFourierPhase η = Complex.exp ∘ radianBasePhaseExponent η := by
    funext x
    simp only [Function.comp_apply,radian_base_phase_exponent_arg]
    rfl
  rw [eq]
  exact Complex.contDiff_exp.comp (radianBasePhaseExponent η).contDiff

private theorem radian_base_phase_exponent_norm (η : E) :
    ‖radianBasePhaseExponent η‖ ≤ tau*‖η‖ := by
  have τ : 0 ≤ tau := mul_nonneg (by norm_num) Real.pi_pos.le
  have q : ‖(innerSL ℝ) η‖ ≤ ‖η‖ := by
    have d : ‖innerSL ℝ (E := E)‖ ≤ 1 := norm_innerSL_le ℝ
    have b := mul_le_mul_of_nonneg_right d (norm_nonneg η)
    rw [one_mul] at b
    exact ((innerSL ℝ).le_opNorm η).trans b
  rw [radianBasePhaseExponent,ContinuousLinearMap.norm_smulRight_apply,norm_mul,
    Complex.norm_real,Complex.norm_I,mul_one,Real.norm_of_nonneg τ,mul_comm]
  exact mul_le_mul_of_nonneg_left q τ

private theorem radian_base_phase_fderiv (η x : E) :
    fderiv ℝ (patchFourierPhase η) x =
      patchFourierPhase η x • radianBasePhaseExponent η := by
  have eq : patchFourierPhase η = Complex.exp ∘ radianBasePhaseExponent η := by
    funext y
    simp only [Function.comp_apply,radian_base_phase_exponent_arg]
    rfl
  rw [eq]
  exact ((radianBasePhaseExponent η).hasFDerivAt.cexp).fderiv

/-- Every genuine base jet of the Fourier phase is bounded by the
corresponding frequency moment with the paper's normalization. -/
theorem norm_radian_base_phase_jet_le (η x : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (patchFourierPhase η) x‖ ≤ (tau*‖η‖)^n := by
  have τ : 0 ≤ tau := mul_nonneg (by norm_num) Real.pi_pos.le
  induction n with
  | zero => simp only [norm_iteratedFDeriv_zero,patch_fourier_phase_norm,pow_zero,le_refl]
  | succ n ih =>
    let L := radianBasePhaseExponent η
    let W : ℂ →L[ℝ] (E →L[ℝ] ℂ) :=
      (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] (E →L[ℝ] ℂ) →L[ℝ] (E →L[ℝ] ℂ)).flip L
    have nW : ‖W‖ ≤ ‖L‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun c => by
        change ‖c • L‖ ≤ ‖L‖ * ‖c‖
        rw [norm_smul,mul_comm])
    rw [← norm_iteratedFDeriv_fderiv]
    have f : fderiv ℝ (patchFourierPhase η) = W ∘ patchFourierPhase η :=
      funext (radian_base_phase_fderiv η)
    rw [f,W.iteratedFDeriv_comp_left (radian_base_phase_smooth η).contDiffAt
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))]
    calc
      _ ≤ ‖W‖ * ‖iteratedFDeriv ℝ n (patchFourierPhase η) x‖ :=
        W.norm_compContinuousMultilinearMap_le _
      _ ≤ (tau*‖η‖)*(tau*‖η‖)^n := mul_le_mul
        (nW.trans (radian_base_phase_exponent_norm η)) ih (norm_nonneg _) (mul_nonneg τ (norm_nonneg _))
      _ = _ := (pow_succ' _ _).symm

end Burnett.A03
