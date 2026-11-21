import Burnett.Analysis.PrincipalEnergy.Commutator.SchwartzWaveletAction
import Burnett.Analysis.PrincipalEnergy.Commutator.CenteredWaveletPackets
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option maxHeartbeats 3800000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter
open scoped Topology

private theorem hasFDerivAt_schwartz_translate (k : SchwartzMap Space ℂ) (y x : Space) :
    HasFDerivAt (fun u : Space => k (u-y)) (fderiv ℝ (k : Space → ℂ) (x-y)) x := by
  have hA : HasFDerivAt (fun u : Space => u-y) (ContinuousLinearMap.id ℝ Space) x :=
    (hasFDerivAt_id x).sub_const y
  have h := k.differentiableAt.hasFDerivAt.comp x hA
  change HasFDerivAt (fun u : Space => k (u-y))
    ((fderiv ℝ (k : Space → ℂ) (x-y)).comp (ContinuousLinearMap.id ℝ Space)) x at h
  rwa [ContinuousLinearMap.comp_id] at h

theorem centeredWavelet_fderiv_eq_translate
    (θ : SchwartzMap Space ℂ) (hθ : ∀ z, 1<‖z‖ → θ z=0) (s : ℝ) (hs : 0<s) (y x : Space) :
    fderiv ℝ (centeredWavelet θ hθ s hs y : Space → ℂ) x=
      fderiv ℝ (centeredWavelet θ hθ s hs 0 : Space → ℂ) (x-y) := by
  let k := centeredWavelet θ hθ s hs 0
  have h := (hasFDerivAt_schwartz_translate k y x).fderiv
  have he : (centeredWavelet θ hθ s hs y : Space → ℂ)=fun z => k (z-y) := by
    funext z
    simp only [centeredWavelet_apply,k,sub_zero]
  rw [he,h]

/-- The spatial output derivative of the actual wavelet synthesis is the
integral of the derivatives of the translated windows, with the same orientation. -/
theorem schwartzWaveletAction_fderiv_centered_integral
    (θ : SchwartzMap Space ℂ) (hθ : ∀ z, 1<‖z‖ → θ z=0) (s : ℝ) (hs : 0<s)
    (f : SchwartzMap Space ℂ) (z : Space) :
    let G (y : Space) := f y • fderiv ℝ (centeredWavelet θ hθ s hs y : Space → ℂ) z
    Integrable G ∧ fderiv ℝ (schwartzWaveletAction θ s hs f : Space → ℂ) z =∫ y, G y := by
  intro FDeriv
  let w := centeredWavelet θ hθ s hs
  let k := w 0
  let F (x y : Space) := f y • k (x-y)
  let G (x y : Space) := f y • fderiv ℝ (k : Space → ℂ) (x-y)
  let C := (s^5)⁻¹*SchwartzMap.seminorm ℝ 0 1 θ
  let B := (s^4)⁻¹*SchwartzMap.seminorm ℝ 0 0 θ
  have hDiff (y x : Space) : HasFDerivAt (fun z => F z y) (G x y) x :=
    (hasFDerivAt_schwartz_translate k y x).const_smul (f y)
  have hMeas (x : Space) : AEStronglyMeasurable (F x) volume :=
    (f.continuous.smul (k.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hInt : Integrable (F z) volume := by
    refine (f.integrable.norm.const_mul B).mono' (hMeas z) (Eventually.of_forall fun y => ?_)
    change ‖f y • k (z-y)‖≤B*‖f y‖
    rw [norm_smul,mul_comm B]
    exact mul_le_mul_of_nonneg_left (centeredWavelet_norm_le θ hθ s hs 0 (z-y)) (norm_nonneg _)
  have hDerMeas : AEStronglyMeasurable (G z) volume := by
    have hK : Continuous (fderiv ℝ (k : Space → ℂ)) := (SchwartzMap.fderivCLM ℂ k).continuous
    exact (f.continuous.smul (hK.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hDom (y x : Space) : ‖G x y‖≤C*‖f y‖ := by
    dsimp only [G]
    rw [norm_smul,mul_comm C]
    exact mul_le_mul_of_nonneg_left (centeredWavelet_fderiv_bound θ hθ s hs 0 (x-y)) (norm_nonneg _)
  have hDer := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := F) (F' := G) (x₀ := z) (bound := fun y => C*‖f y‖) (ε := 1) (by norm_num)
    (Eventually.of_forall hMeas) hInt hDerMeas
    (Eventually.of_forall fun y x _ => hDom y x) (f.integrable.norm.const_mul C)
    (Eventually.of_forall fun y x _ => hDiff y x)
  have hF : (schwartzWaveletAction θ s hs f : Space → ℂ) = fun x => ∫ y, F x y := by
    rw [schwartzWaveletAction_eq_actual θ s hs f]
    funext x
    unfold compactWaveletAction
    apply integral_congr_ae
    filter_upwards with y
    simp only [F,k,w,centeredWavelet_apply,sub_zero,smul_eq_mul,mul_comm]
  have hEq (y : Space) : FDeriv y=G z y := by
    change f y • fderiv ℝ (w y : Space → ℂ) z=f y • fderiv ℝ (k : Space → ℂ) (z-y)
    rw [centeredWavelet_fderiv_eq_translate θ hθ s hs y z]
  rw [show FDeriv=G z from funext hEq]
  exact ⟨(f.integrable.norm.const_mul C).mono' hDerMeas (Eventually.of_forall fun y => hDom y z),by
    rw [hF,hDer.fderiv]⟩

end Burnett.Analysis.CarlesonEmbedding
