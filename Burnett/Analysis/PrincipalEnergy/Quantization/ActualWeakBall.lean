import Burnett.Analysis.PrincipalEnergy.Quantization.ActualWeakPair

set_option autoImplicit false
set_option maxHeartbeats 1900000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Filter Burnett.Microlocal.AngularDyadicKernel
open Burnett.Analysis.SymmetricEnergy
open scoped ComplexConjugate ENNReal

private theorem actualProduct_bound (r f : SchwartzMap E ℂ) (U : ℝ)
    (hU : 0 ≤ U) (hR : ∀ x, ‖r x‖ ≤ U) :
    ‖(scalarSchwartzProduct r f).toLp 2 volume‖ ≤ U*‖f.toLp 2 volume‖ := by
  rw [SchwartzMap.norm_toLp,SchwartzMap.norm_toLp]
  apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg hU ENNReal.toReal_nonneg)
  rw [ENNReal.ofReal_mul hU,ENNReal.ofReal_toReal (f.memLp 2 volume).eLpNorm_ne_top]
  let A : NNReal := ⟨U,hU⟩
  have hPoint : ∀ᵐ z ∂(volume : Measure E), ‖scalarSchwartzProduct r f z‖₊ ≤ A*‖f z‖₊ := by
    filter_upwards with z
    have h : ‖scalarSchwartzProduct r f z‖ ≤ (A : ℝ)*‖f z‖ := by
      rw [scalarSchwartzProduct_apply,norm_mul]
      exact mul_le_mul_of_nonneg_right (hR z) (norm_nonneg _)
    exact_mod_cast h
  have hA : (A : ℝ≥0∞) = ENNReal.ofReal U := ENNReal.ofReal_coe_nnreal.symm
  simpa only [ENNReal.smul_def,smul_eq_mul,hA] using eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hPoint 2

private theorem centeredActualProduct_bound (r f : SchwartzMap E ℂ) (L : NNReal)
    (hL : LipschitzWith L r) (c : E) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hF : tsupport (f : E → ℂ) ⊆ Metric.closedBall c ρ) :
    ‖(scalarSchwartzProduct r f-r c • f).toLp 2 volume‖ ≤ ((L : ℝ)*ρ)*‖f.toLp 2 volume‖ := by
  have h := centeredScalarMultiplier_ball_norm_le r L hL c ρ hρ f hF
  have hEq : scalarSchwartzMultiplier r f = scalarSchwartzProduct r f := by
    ext x
    rw [scalarSchwartzMultiplier_apply,scalarSchwartzProduct_apply,smul_eq_mul]
  simpa only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
    transportSchwartzOp_on_equiv,← map_sub,← map_smul,hEq] using h

/-- Weak boundedness for the actual common scalar operator, at every ball scale.
Its Fourier action needs the true H¹-to-L² bound and need not return a Schwartz test. -/
theorem exists_actualCoefficientCommutator_normalizedBall_weakBound {a : E → E → ℂ}
    (ha : FrequencyOrderOne a) (hBase : CompactBaseOrderOne a) (hCont : Continuous (Function.uncurry a))
    (hSym : FirstOrderFormalSymmetry a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : SchwartzMap E ℂ) (L : NNReal) (U : ℝ),
      0 ≤ U → (∀ x, conj (r x) = r x) → LipschitzWith L r → (∀ x, ‖r x‖ ≤ U) →
      ∀ (c : E) (ρ : ℝ), 0 < ρ → ∀ (f g : SchwartzMap E ℂ),
      tsupport (f : E → ℂ) ⊆ Metric.closedBall c ρ →
      tsupport (g : E → ℂ) ⊆ Metric.closedBall c ρ →
      (∀ x, ‖f x‖ ≤ 1) → (∀ x, ‖g x‖ ≤ 1) →
      (∀ (j : Fin 4) x, ‖fderiv ℝ (⇑f) x (coordinateDirection j)‖ ≤ ρ⁻¹) →
      (∀ (j : Fin 4) x, ‖fderiv ℝ (⇑g) x (coordinateDirection j)‖ ≤ ρ⁻¹) →
      ‖∫ x, conj (g x)*actualCoefficientCommutator a r f x‖ ≤ C*(U+(L:ℝ))*ρ^4 := by
  obtain ⟨K,hK,hPair⟩ := exists_actualCoefficientCommutator_weakPair_bound ha hBase hCont hSym
  let A := Real.sqrt (5*unitBallVolume)
  let B := Real.sqrt unitBallVolume
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  refine ⟨2*K*A*B,by positivity,?_⟩
  intro r L U hU hR hL hVal c ρ hρ f g hf hg hf0 hg0 hf1 hg1
  by_cases hSmall : ρ ≤ 1
  · obtain ⟨hF2,hF1⟩ := normalizedBallTest_norms f c ρ hρ hSmall hf hf0 hf1
    obtain ⟨hG2,hG1⟩ := normalizedBallTest_norms g c ρ hρ hSmall hg hg0 hg1
    have hP := hPair r f g (r c) (hR c) hR ((L:ℝ)*ρ) (mul_nonneg L.coe_nonneg hρ.le)
      (centeredActualProduct_bound r f L hL c ρ hρ.le hf)
      (centeredActualProduct_bound r g L hL c ρ hρ.le hg)
    have hFirst : coordinateH1 f*‖g.toLp 2 volume‖ ≤ (ρ*A)*(ρ^2*B) :=
      mul_le_mul hF1 hG2 (norm_nonneg _) (mul_nonneg hρ.le hA)
    have hSecond : ‖f.toLp 2 volume‖*coordinateH1 g ≤ (ρ^2*B)*(ρ*A) :=
      mul_le_mul hF2 hG1 (Real.sqrt_nonneg _) (mul_nonneg (sq_nonneg _) hB)
    refine hP.trans ((mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond)
      (mul_nonneg hK (mul_nonneg L.coe_nonneg hρ.le))).trans ?_)
    rw [show K*((L:ℝ)*ρ)*((ρ*A)*(ρ^2*B)+(ρ^2*B)*(ρ*A)) =
      (2*K*A*B)*(L:ℝ)*ρ^4 by ring]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left hU) (by positivity)) (by positivity)
  · have hLarge : 1 ≤ ρ := le_of_lt (lt_of_not_ge hSmall)
    obtain ⟨hF2,hF1⟩ := normalizedLargeBallTest_norms f c ρ hLarge hf hf0 hf1
    obtain ⟨hG2,hG1⟩ := normalizedLargeBallTest_norms g c ρ hLarge hg hg0 hg1
    have hF : ‖(scalarSchwartzProduct r f-(0:ℂ) • f).toLp 2 volume‖ ≤ U*‖f.toLp 2 volume‖ := by
      simpa only [zero_smul,sub_zero] using actualProduct_bound r f U hU hVal
    have hG : ‖(scalarSchwartzProduct r g-(0:ℂ) • g).toLp 2 volume‖ ≤ U*‖g.toLp 2 volume‖ := by
      simpa only [zero_smul,sub_zero] using actualProduct_bound r g U hU hVal
    have hP := hPair r f g 0 (by simp) hR U hU hF hG
    have hFirst : coordinateH1 f*‖g.toLp 2 volume‖ ≤ (ρ^2*A)*(ρ^2*B) :=
      mul_le_mul hF1 hG2 (norm_nonneg _) (mul_nonneg (sq_nonneg _) hA)
    have hSecond : ‖f.toLp 2 volume‖*coordinateH1 g ≤ (ρ^2*B)*(ρ^2*A) :=
      mul_le_mul hF2 hG1 (Real.sqrt_nonneg _) (mul_nonneg (sq_nonneg _) hB)
    refine hP.trans ((mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) (mul_nonneg hK hU)).trans ?_)
    rw [show K*U*((ρ^2*A)*(ρ^2*B)+(ρ^2*B)*(ρ^2*A))=(2*K*A*B)*U*ρ^4 by ring]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right L.coe_nonneg) (by positivity)) (by positivity)

end Burnett.Analysis.FirstOrderDyadic
