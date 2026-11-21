import Burnett.Analysis.PrincipalEnergy.Commutator.LocalOscillationH1
import Burnett.Analysis.PrincipalEnergy.Commutator.StandardOscillationCutoff
import Burnett.Analysis.PrincipalEnergy.Commutator.FarOscillation

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Filter Metric Burnett.Fourier Burnett.Microlocal.AngularDyadicKernel
open Burnett.Microlocal.HminusReverse Burnett.Analysis.SymmetricEnergy

private theorem square_integral_ball_decomposition {F G H : E → ℂ}
    (hG : MemLp G 2 (volume : Measure E))
    (hEq : ∀ x, F x = G x + H x) (m : ℂ) (A : ℝ) (hA : 0 ≤ A)
    (c : E) (R : ℝ) (hR : 0 ≤ R) (hFar : ∀ x ∈ ball c R, ‖H x-m‖ ≤ A) :
    (∫ x in ball c R, ‖F x-m‖^2) ≤
      2*‖hG.toLp G‖^2 + 2*A^2*(R^4*unitBallVolume) := by
  let μ : Measure E := volume.restrict (ball c R)
  letI : IsFiniteMeasure μ := ⟨by
    change volume.restrict (ball c R) Set.univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  have hSq : Integrable (fun x => ‖G x‖^2) (volume : Measure E) :=
    (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  have hSqLocal : Integrable (fun x => ‖G x‖^2) μ := hSq.integrableOn
  have hcLocal : Integrable (fun _ : E => 2*A^2) μ := integrable_const _
  have hPoint (x : E) (hx : x ∈ ball c R) : ‖F x-m‖^2 ≤ 2*‖G x‖^2 + 2*A^2 := by
    have hF' : F x-m = G x+(H x-m) := (congrArg (fun z => z-m) (hEq x)).trans (by ring)
    have hn : ‖F x-m‖ ≤ ‖G x‖+A := by
      rw [hF']
      exact (norm_add_le _ _).trans (add_le_add_left (hFar x hx) _)
    exact ((sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) hA)).mpr hn).trans
      (by nlinarith only [sq_nonneg (‖G x‖-A)])
  have hAE : ∀ᵐ x ∂μ, ‖F x-m‖^2 ≤ 2*‖G x‖^2+2*A^2 :=
    (ae_restrict_mem measurableSet_ball).mono hPoint
  have hPlancherel : ‖hG.toLp G‖^2 = ∫ x, ‖G x‖^2 := by
    rw [l2_norm_sq_integral]
    exact integral_congr_ae ((MemLp.coeFn_toLp hG).mono fun _ hx =>
      congrArg (fun z : ℂ => ‖z‖^2) hx)
  have hVol : (volume : Measure E).real (ball c R) = R^4 * unitBallVolume := by
    rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball volume c R,
      Measure.addHaar_real_closedBall volume c hR,finrank_euclideanSpace_fin]
    rfl
  have hGNonnegative : 0 ≤ᵐ[(volume : Measure E)] (fun x => ‖G x‖^2) :=
    Eventually.of_forall (fun x : E => sq_nonneg ‖G x‖)
  have hRestricted : (∫ x, ‖G x‖^2 ∂μ) ≤ ∫ x, ‖G x‖^2 :=
    setIntegral_le_integral hSq hGNonnegative
  have hDomInt : Integrable (fun x => 2*‖G x‖^2+2*A^2) μ :=
    (hSqLocal.const_mul 2).add hcLocal
  have hLeftNonnegative : 0 ≤ᵐ[μ] (fun x => ‖F x-m‖^2) :=
    Eventually.of_forall (fun x : E => sq_nonneg ‖F x-m‖)
  have hDom : (∫ x, ‖F x-m‖^2 ∂μ) ≤ ∫ x, (2*‖G x‖^2+2*A^2) ∂μ :=
    integral_mono_of_nonneg hLeftNonnegative hDomInt hAE
  have hSeparate : (∫ x, (2*‖G x‖^2+2*A^2) ∂μ) =
      2*(∫ x, ‖G x‖^2 ∂μ) + (2*A^2)*(R^4*unitBallVolume) := by
    rw [integral_add (hSqLocal.const_mul 2) hcLocal,integral_const_mul]
    change _ + (∫ _x in ball c R, (2*A^2)) = _
    rw [setIntegral_const,hVol,smul_eq_mul]
    ring
  have hCompare : 2*(∫ x, ‖G x‖^2 ∂μ) ≤ 2*‖hG.toLp G‖^2 := by
    rw [hPlancherel]
    exact mul_le_mul_of_nonneg_left hRestricted (by norm_num)
  refine hDom.trans ?_
  rw [hSeparate]
  exact add_le_add_right hCompare _

/-- A quantitative mean square oscillation estimate for the actual high
action on the bounded Lipschitz Schwartz coefficient. The reference value is
chosen separately on each ball using its actual complementary input. -/
theorem exists_compactBase_firstOrderHighAction_meanOscillation {a : E → E → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hSupport : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : SchwartzMap E ℂ) (L : NNReal) (U : ℝ),
      0 ≤ U → LipschitzWith L r → (∀ y : E, ‖r y‖ ≤ U) → ∀ (c : E) (R : ℝ), 0 < R →
      ∃ m : ℂ, (∫ x in ball c R, ‖firstOrderHighAction a r x-m‖^2) ≤ C*(U+(L : ℝ))^2*R^4 := by
  obtain ⟨χ,D,hD,hχC,hχS,hχOne,hχVal,hχComp,hχDer⟩ := exists_standardOscillationCutoff
  obtain ⟨K,hK,hAction⟩ := exists_compactBase_firstOrderHighAction_h1_to_l2 hSupport hCont
  obtain ⟨J,hJ,hFar⟩ := exists_firstOrderHighAction_far_oscillation ha
  let V := unitBallVolume
  have hV : 0 ≤ V := unitBallVolume_nonneg
  let Q := 4+4*(1+2*D)^2
  let C := 2*K^2*V*4^4*Q + 2*J^2*V
  have hC : 0 ≤ C := by dsimp [C,Q]; positivity
  refine ⟨C,hC,?_⟩
  intro r L U hU hLip hr c R hR
  let f := localOscillationRamp r χ hχC c hR
  let g := r-f
  let B (v : SchwartzMap E ℂ) (y : E) := firstOrderHighAction a v y
  let m := B g c
  obtain ⟨hg,hgBound⟩ := localOscillationRamp_complement r χ L hLip hχC hχOne hχComp c hR
  have hPointFar (x : E) (hx : x ∈ ball c R) : ‖B g x - m‖ ≤ J*(L:ℝ) :=
    hFar g χ hχC hχOne hχVal c x (r c) R L hR L.coe_nonneg hg hgBound
      (show ‖x-c‖ ≤ R by exact (show ‖x-c‖ < R by simpa only [mem_ball,dist_eq_norm] using hx).le)
  obtain ⟨hF2,hFbound⟩ := hAction f
  have hSplit (x : E) : B r x = B f x+B g x := by
    have h := firstOrderHighAction_sub_smul a ha.frequency x r f 1
    change firstOrderHighAction a (r - (1:ℂ) • f : SchwartzMap E ℂ) x = _ at h
    simp only [one_smul,one_mul] at h
    change B g x = B r x-B f x at h
    rw [h]
    ring
  have hBallEstimate := square_integral_ball_decomposition hF2 hSplit m (J*(L:ℝ))
    (mul_nonneg hJ L.coe_nonneg) c R hR.le hPointFar
  have hLocalEnergy : schwartzH1Energy f ≤ V*(4*R)^4 * ((2*U)^2+4*((1+2*D)*(L:ℝ))^2) :=
    localOscillationRamp_H1_le r χ L hLip U D hU hD hr hχC hχS hχVal hχDer c hR
  have hMonotone : (2*U)^2+4*((1+2*D)*(L:ℝ))^2 ≤ Q*(U+(L:ℝ))^2 := by
    have hU₂ := pow_le_pow_left₀ hU (le_add_of_nonneg_right L.coe_nonneg : U ≤ U+(L:ℝ)) 2
    have hL₂ := pow_le_pow_left₀ L.coe_nonneg (le_add_of_nonneg_left hU : (L:ℝ) ≤ U+(L:ℝ)) 2
    dsimp only [Q]
    nlinarith only [hU₂,mul_le_mul_of_nonneg_left hL₂ (sq_nonneg (1+2*D))]
  have hFarMonotone : (J*(L:ℝ))^2 ≤ J^2 * (U+(L:ℝ))^2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ L.coe_nonneg (le_add_of_nonneg_left hU) 2) (sq_nonneg _)
  refine ⟨m,?_⟩
  calc
    _ ≤ 2*‖hF2.toLp (B f)‖^2 + (2*(J*(L:ℝ))^2)*(R^4*V) := hBallEstimate
    _ ≤ 2*(K^2*(V*(4*R)^4*(Q*(U+(L:ℝ))^2))) +
        (2*(J^2*(U+(L:ℝ))^2))*(R^4*V) := by
      refine add_le_add (mul_le_mul_of_nonneg_left (hFbound.trans ?_) (by norm_num)) ?_
      · exact mul_le_mul_of_nonneg_left
          (hLocalEnergy.trans (mul_le_mul_of_nonneg_left hMonotone (by positivity))) (sq_nonneg _)
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFarMonotone (by norm_num)) (by positivity)
    _ = _ := by dsimp [C]; ring

end Burnett.Analysis.FirstOrderDyadic
