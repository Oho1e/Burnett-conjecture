import Burnett.Analysis.PrincipalEnergy.Quantization.FiniteMeasureMean

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Set Filter Metric Burnett.Microlocal.AngularDyadicKernel
open Burnett.Analysis.SymmetricEnergy

theorem coefficientCommutatorConstant_memLp {a : E → E → ℂ} (ha : FrequencyOrderOne a)
    (hBase : CompactBaseOrderOne a) (hCont : Continuous (Function.uncurry a))
    (r : SchwartzMap E ℂ) : MemLp (coefficientCommutatorConstant a r) 2 (volume : Measure E) := by
  obtain ⟨D,_,hOrder⟩ := ha.order 0
  obtain ⟨_,_,hL2⟩ := exists_compactBase_firstOrderAction_h1_to_l2 hBase hCont
  obtain ⟨hB,_⟩ := hL2 r
  have hSec : Continuous (fun x => a x 0) := hCont.comp (continuous_id.prodMk continuous_const)
  have hM : MemLp (fun x => r x*a x 0) 2 (volume : Measure E) := by
    refine (r.memLp 2 volume).of_le_mul (c := D) ((r.continuous.mul hSec).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [norm_mul,mul_comm ‖r x‖]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [pow_zero,mul_one,norm_iteratedFDeriv_zero,norm_zero,add_zero] using hOrder x 0
  exact hM.sub hB

/-- A genuine BMO square-mean estimate against the actual local average
of the compact-base commutator's constant-input representative. -/
theorem exists_coefficientCommutatorConstant_avgSquare_bound {a : E → E → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : SchwartzMap E ℂ) (L : NNReal) (U : ℝ),
      0 ≤ U → LipschitzWith L r → (∀ y, ‖r y‖ ≤ U) → ∀ (c : E) (R : ℝ), 0 < R →
      let μ := (volume : Measure E).restrict (ball c R)
      (μ.real univ)⁻¹ * (∫ x, ‖coefficientCommutatorConstant a r x -
        finiteMeasureMean μ (coefficientCommutatorConstant a r)‖^2 ∂μ) ≤ C*(U+(L:ℝ))^2 := by
  obtain ⟨C,hC,hTest⟩ := exists_compactBase_coefficientCommutatorConstant_meanOscillation ha hBase hCont
  let V := unitBallVolume
  have hV : 0 < V := by
    unfold V unitBallVolume
    exact ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne
  refine ⟨C/V,div_nonneg hC hV.le,?_⟩
  intro r L U hU hLip hr c R hR μ
  let G := coefficientCommutatorConstant a r
  letI : IsFiniteMeasure μ := ⟨by
    change (volume : Measure E).restrict (ball c R) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  have hv : μ.real univ = R^4*V := by
    change ((volume : Measure E).restrict (ball c R)).real univ = R^4*V
    rw [measureReal_def,Measure.restrict_apply_univ,← measureReal_def,
      ← Measure.addHaar_real_closedBall_eq_addHaar_real_ball volume c R,
      Measure.addHaar_real_closedBall volume c hR.le,finrank_euclideanSpace_fin]
    rfl
  have hμ : 0 < μ.real univ := by rw [hv]; exact mul_pos (pow_pos hR _) hV
  obtain ⟨m,hm⟩ := hTest r L U hU hLip hr c R hR
  have hL := (coefficientCommutatorConstant_memLp ha.frequency hBase hCont r).restrict (ball c R)
  have hId := squareOscillation_eq_mean_add_constant μ hμ G hL m
  have hMm : (∫ x, ‖G x-finiteMeasureMean μ G‖^2 ∂μ) ≤ C*(U+(L:ℝ))^2*R^4 := by
    calc
      _ ≤ (∫ x, ‖G x-m‖^2 ∂μ) := by
        rw [hId]
        exact le_add_of_nonneg_right (mul_nonneg hμ.le (sq_nonneg _))
      _ ≤ _ := hm
  refine (mul_le_mul_of_nonneg_left hMm (inv_nonneg.mpr hμ.le)).trans_eq ?_
  rw [hv]
  field_simp [hV.ne',hR.ne']

end Burnett.Analysis.FirstOrderDyadic
