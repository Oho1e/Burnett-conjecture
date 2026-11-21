import Burnett.Analysis.PrincipalEnergy.Commutator.CompactBaseCommutatorL2

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped FourierTransform

private theorem translate_hasTemperateGrowth (c : Space) :
    (fun x : Space => x+c).HasTemperateGrowth := by
  have hF : fderiv ℝ (fun x : Space => x+c)=fun _ => ContinuousLinearMap.id ℝ Space := by
    funext x
    exact ((hasFDerivAt_id x).add_const c).fderiv
  refine Function.HasTemperateGrowth.of_fderiv ?_ (differentiable_id.add_const c)
    (k := 1) (C := 1+‖c‖) (fun x => ?_)
  · rw [hF]
    exact Function.HasTemperateGrowth.const _
  · rw [pow_one]
    exact (norm_add_le _ _).trans (by nlinarith only [mul_nonneg (norm_nonneg c) (norm_nonneg x)])

/-- The Haar translation on the complete Schwartz space, not merely on
compactly supported input tests. -/
def translateSchwartz (c : Space) : SchwartzMap Space ℂ →L[ℂ] SchwartzMap Space ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (translate_hasTemperateGrowth c)
    (show Isometry (fun x : Space => x+c) from Isometry.of_dist_eq fun x y => by
      simp only [dist_eq_norm,add_sub_add_right_eq_sub]).antilipschitz

@[simp] theorem translateSchwartz_apply (c : Space) (f : SchwartzMap Space ℂ) (x : Space) :
    translateSchwartz c f x=f (x+c) := rfl

theorem translateSchwartz_fderiv (c : Space) (f : SchwartzMap Space ℂ) (x : Space) :
    fderiv ℝ (translateSchwartz c f : Space → ℂ) x=fderiv ℝ (f : Space → ℂ) (x+c) := by
  have h₀ : HasFDerivAt (fun y : Space => y+c) (ContinuousLinearMap.id ℝ Space) x :=
    (hasFDerivAt_id x).add_const c
  have h₁ := f.differentiableAt.hasFDerivAt.comp x h₀
  change HasFDerivAt (translateSchwartz c f : Space → ℂ)
    ((fderiv ℝ (f : Space → ℂ) (x+c)).comp (ContinuousLinearMap.id ℝ Space)) x at h₁
  simpa only [ContinuousLinearMap.comp_id] using h₁.fderiv

theorem translateSchwartz_L2_norm (c : Space) (f : SchwartzMap Space ℂ) :
    ‖(translateSchwartz c f).toLp 2 volume‖=‖f.toLp 2 volume‖ := by
  let h := measurePreserving_add_right (volume : Measure Space) c
  have hEq : Lp.compMeasurePreserving (fun x : Space => x+c) h (f.toLp 2 volume)=
      (translateSchwartz c f).toLp 2 volume :=
    Lp.toLp_compMeasurePreserving (f.memLp 2 volume) h
  rw [← hEq,Lp.norm_compMeasurePreserving]

private theorem fourier_translateSchwartz (c : Space) (f : SchwartzMap Space ℂ) (ξ : Space) :
    𝓕 (translateSchwartz c f : Space → ℂ) ξ=Real.fourierChar (inner ℝ c ξ) • 𝓕 (f : Space → ℂ) ξ :=
  congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume (innerₗ Space)
    (f : Space → ℂ) c) ξ

/-- Exact translation covariance of the actual full left quantization with
the inverse Fourier phase used by the source operator. -/
theorem firstOrderAction_translate (a : Space → Space → ℂ) (c : Space)
    (f : SchwartzMap Space ℂ) (x : Space) :
    firstOrderAction (fun y => a (y+c)) (translateSchwartz c f) x=firstOrderAction a f (x+c) := by
  unfold firstOrderAction
  rw [Real.fourierIntegralInv_eq,Real.fourierIntegralInv_eq]
  apply integral_congr_ae
  filter_upwards with ξ
  change (Real.fourierChar (inner ℝ ξ x)) • (a (x+c) ξ*𝓕 (translateSchwartz c f : Space → ℂ) ξ)=
    (Real.fourierChar (inner ℝ ξ (x+c))) • (a (x+c) ξ*𝓕 (f : Space → ℂ) ξ)
  have hPhase : Real.fourierChar (inner ℝ ξ (x+c))=
      (Real.fourierChar (inner ℝ ξ x))*(Real.fourierChar (inner ℝ c ξ)) := by
    rw [inner_add_right,real_inner_comm ξ c,Real.fourierChar.map_add_eq_mul]
  rw [fourier_translateSchwartz,hPhase]
  simp only [Circle.smul_def,Circle.coe_mul,smul_eq_mul]
  ring

theorem actualCoefficientCommutator_translate (a : Space → Space → ℂ) (c : Space)
    (r f : SchwartzMap Space ℂ) (x : Space) :
    actualCoefficientCommutator (fun y => a (y+c)) (translateSchwartz c r) (translateSchwartz c f) x=
      actualCoefficientCommutator a r f (x+c) := by
  have hProduct : scalarSchwartzProduct (translateSchwartz c r) (translateSchwartz c f)=
      translateSchwartz c (scalarSchwartzProduct r f) := by
    ext y
    simp only [scalarSchwartzProduct_apply,translateSchwartz_apply]
  simp only [actualCoefficientCommutator,firstOrderAction_translate,translateSchwartz_apply,hProduct]

end Burnett.Analysis.CarlesonEmbedding
