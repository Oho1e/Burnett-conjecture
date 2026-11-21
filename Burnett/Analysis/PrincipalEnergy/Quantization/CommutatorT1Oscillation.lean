import Burnett.Analysis.PrincipalEnergy.Quantization.FullApproximateConstant
import Burnett.Analysis.PrincipalEnergy.Quantization.LowActionSup
import Burnett.Analysis.PrincipalEnergy.Commutator.HighMeanOscillation

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Filter Metric Burnett.Fourier Burnett.Microlocal.AngularDyadicKernel
open Burnett.Microlocal.HminusReverse Burnett.Analysis.SymmetricEnergy

/-- The pointwise representative of the constant-input limit of the actual
coefficient commutator, evaluated with the full original symbol. -/
def coefficientCommutatorConstant (a : E → E → ℂ) (r : SchwartzMap E ℂ) (x : E) : ℂ :=
  r x * a x 0 - firstOrderAction a r x

private theorem square_integral_add_bounded {F G Q : E → ℂ} (m : ℂ) (A : ℝ)
    (hA : 0 ≤ A) (c : E) (R : ℝ) (hR : 0 ≤ R)
    (hF : ∀ x, F x-m = Q x-G x) (hQ : ∀ x, ‖Q x‖ ≤ A)
    (hG : MemLp G 2 (volume : Measure E)) :
    (∫ x in ball c R, ‖F x‖^2) ≤
      2*(∫ x in ball c R, ‖G x-m‖^2) + 2*A^2*(R^4*unitBallVolume) := by
  let μ : Measure E := volume.restrict (ball c R)
  letI : IsFiniteMeasure μ := ⟨by
    change volume.restrict (ball c R) Set.univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  have hGm : MemLp (fun x => G x-m) 2 μ := (hG.restrict (ball c R)).sub (memLp_const m)
  have hSquare : Integrable (fun x => ‖G x-m‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm hGm.aestronglyMeasurable).mp hGm
  have hConst : Integrable (fun _ : E => 2*A^2) μ := integrable_const _
  have hMaj : Integrable (fun x => 2*‖G x-m‖^2+2*A^2) μ :=
    (hSquare.const_mul 2).add hConst
  have hPoint (x : E) : ‖F x‖^2 ≤ 2*‖G x-m‖^2+2*A^2 := by
    have hX := hF x
    have hSubtract : F x = Q x-(G x-m) := by
      calc
        F x = (F x-m)+m := by ring
        _ = (Q x-G x)+m := by rw [hX]
        _ = Q x-(G x-m) := by ring
    have hNorm : ‖F x‖ ≤ A+‖G x-m‖ :=
      by rw [hSubtract]; exact (norm_sub_le _ _).trans (add_le_add_right (hQ x) _)
    exact ((sq_le_sq₀ (norm_nonneg _) (add_nonneg hA (norm_nonneg _))).mpr hNorm).trans
      (by nlinarith only [sq_nonneg (‖G x-m‖-A)])
  have hVol : (volume : Measure E).real (ball c R) = R^4*unitBallVolume := by
    rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball volume c R,
      Measure.addHaar_real_closedBall volume c hR,finrank_euclideanSpace_fin]
    rfl
  change (∫ x, ‖F x‖^2 ∂μ) ≤ _
  refine (integral_mono_of_nonneg (Eventually.of_forall (fun x : E => sq_nonneg ‖F x‖))
    hMaj (Eventually.of_forall hPoint)).trans_eq ?_
  rw [integral_add (hSquare.const_mul 2) hConst,integral_const_mul]
  change _ + (∫ _x in ball c R, (2*A^2)) = _
  rw [setIntegral_const,hVol,smul_eq_mul]
  ring

/-- The constant-input limit of the actual full commutator has a uniform
mean-square oscillation bound over all positive-radius coordinate balls. -/
theorem exists_compactBase_coefficientCommutatorConstant_meanOscillation
    {a : E → E → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hSupport : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : SchwartzMap E ℂ) (L : NNReal) (U : ℝ),
      0 ≤ U → LipschitzWith L r → (∀ y : E, ‖r y‖ ≤ U) → ∀ (c : E) (R : ℝ), 0 < R →
      ∃ m : ℂ, (∫ x in ball c R, ‖coefficientCommutatorConstant a r x-m‖^2) ≤
        C*(U+(L : ℝ))^2*R^4 := by
  obtain ⟨C,hC,hHigh⟩ := exists_compactBase_firstOrderHighAction_meanOscillation ha hSupport hCont
  obtain ⟨J,hJ,hLow⟩ := exists_lowAction_sup_bound ha.frequency
  obtain ⟨D,hD,hOrder⟩ := ha.frequency.order 0
  obtain ⟨_,_,hComp⟩ := exists_compactBase_firstOrderHighAction_h1_to_l2 hSupport hCont
  let V := unitBallVolume
  have hV : 0 ≤ V := unitBallVolume_nonneg
  refine ⟨2*C+2*(D+J)^2*V, by positivity,?_⟩
  intro r L U hU hL hRu c R hR
  obtain ⟨m,hm⟩ := hHigh r L U hU hL hRu c R hR
  let q (x : E) := r x*a x 0 - firstOrderLowAction a r x
  have hQ (x : E) : ‖q x‖ ≤ (D+J)*U := by
    have h0 : ‖a x 0‖ ≤ D := by
      simpa only [pow_zero,mul_one,norm_iteratedFDeriv_zero,norm_zero,add_zero] using hOrder x 0
    calc
      _ ≤ ‖r x*a x 0‖+‖firstOrderLowAction a r x‖ := norm_sub_le _ _
      _ ≤ U*D+J*U := add_le_add
        (by rw [norm_mul]; exact mul_le_mul (hRu x) h0 (norm_nonneg _) hU)
        (hLow r U hU hRu x)
      _ = _ := by ring
  let G (x : E) := firstOrderHighAction a r x
  let F (x : E) := coefficientCommutatorConstant a r x+m
  have hEq (x : E) : F x-m = q x-G x := by
    dsimp [F,G,q,coefficientCommutatorConstant]
    rw [firstOrderAction_eq_low_add_high ha.frequency r x]
    ring
  obtain ⟨hG,_⟩ := hComp r
  have hBound := square_integral_add_bounded (F:=F) (G:=G) (Q:=q) m ((D+J)*U)
    (mul_nonneg (add_nonneg hD hJ) hU) c R hR.le hEq hQ hG
  have hU2 : U^2 ≤ (U+(L:ℝ))^2 :=
    pow_le_pow_left₀ hU (le_add_of_nonneg_right L.coe_nonneg) 2
  have hRadius : 0 ≤ R^4*V := by positivity
  refine ⟨-m,?_⟩
  rw [show (fun x => ‖coefficientCommutatorConstant a r x - -m‖^2) = fun x => ‖F x‖^2 from
    funext fun x => by dsimp [F]; rw [sub_neg_eq_add]]
  refine hBound.trans ?_
  calc
    _ ≤ 2*(C*(U+(L:ℝ))^2*R^4) + 2*((D+J)^2*(U+(L:ℝ))^2)*(R^4*V) := by
      refine add_le_add (mul_le_mul_of_nonneg_left hm (by norm_num)) ?_
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hU2 (sq_nonneg (D+J))) (by norm_num)) hRadius
    _ = _ := by ring

end Burnett.Analysis.FirstOrderDyadic
