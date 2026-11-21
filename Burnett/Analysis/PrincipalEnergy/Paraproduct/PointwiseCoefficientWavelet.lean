import Burnett.Analysis.PrincipalEnergy.Paraproduct.CompactWaveletConvolution
import Burnett.Analysis.PrincipalEnergy.Commutator.ActualConstantCarleson

set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Set Metric
open Burnett.Analysis.FirstOrderDyadic
open scoped NNReal

private theorem integral_norm_le_local_sq (μ : Measure Space) [IsFiniteMeasure μ]
    {f : Space → ℂ} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ Real.sqrt (∫ x, ‖f x‖^2 ∂μ)*Real.sqrt (μ.real univ) := by
  have hExponents : Real.HolderConjugate 2 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h₁ : MemLp (fun _ : Space => (1:ℂ)) 2 μ := memLp_const 1
  have h := integral_mul_norm_le_Lp_mul_Lq (p := (2:ℝ)) (q := (2:ℝ)) hExponents
    (show MemLp f (ENNReal.ofReal 2) μ by simpa using hf)
    (show MemLp (fun _ : Space => (1:ℂ)) (ENNReal.ofReal 2) μ by simpa using h₁)
  simpa only [norm_one,mul_one,Real.rpow_two,← Real.sqrt_eq_rpow,one_pow,integral_const,smul_eq_mul] using h

/-- Each actual filtered coefficient is uniformly bounded pointwise, with
the coefficient's Lipschitz control and no scale dependence. This feeds the
off-diagonal kernel estimates for the paraproduct. -/
theorem exists_compactBase_commutatorConstant_wavelet_sup_bound
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (ψ : SchwartzMap Space ℂ)
    (hψ : ∀ z, 1<‖z‖ → ψ z = 0) (hMean : (∫ z, ψ z)=0) :
    ∃ C : ℝ, 0≤C ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0≤U → LipschitzWith L r → (∀ x, ‖r x‖≤U) → ∀ (s : ℝ), 0<s → ∀ x,
        ‖compactWaveletAction ψ s (coefficientCommutatorConstant a r) x‖ ≤ C*(U+(L:ℝ)) := by
  obtain ⟨A,hA,hOsc⟩ := exists_compactBase_coefficientCommutatorConstant_meanOscillation ha hBase hCont
  let V := (volume : Measure Space).real (ball (0:Space) 1)
  let M := SchwartzMap.seminorm ℝ 0 0 ψ
  have hM : 0≤M := apply_nonneg _ _
  have hV : 0≤V := ENNReal.toReal_nonneg
  refine ⟨16*M*Real.sqrt A*Real.sqrt V,by positivity,?_⟩
  intro r L U hU hLip hR s hs x
  let b := coefficientCommutatorConstant a r
  let S := ball x (2*s)
  let μ := (volume : Measure Space).restrict S
  obtain ⟨m,hm⟩ := hOsc r L U hU hLip hR x (2*s) (by positivity)
  let g := S.indicator (fun y => b y-m)
  letI : IsFiniteMeasure μ := ⟨by
    change (volume : Measure Space).restrict S univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  have hb : MemLp b 2 volume := coefficientCommutatorConstant_memLp ha.frequency hBase hCont r
  have hbM : MemLp (fun y => b y-m) 2 μ := (hb.restrict S).sub (memLp_const m)
  have hg : Integrable g volume := (integrable_indicator_iff measurableSet_ball).mpr (hbM.integrable (by norm_num))
  have hInt : (∫ y, ‖g y‖) = ∫ y, ‖b y-m‖ ∂μ := by
    change (∫ y, ‖g y‖) = ∫ y in S, ‖b y-m‖
    rw [← integral_indicator measurableSet_ball]
    apply congrArg (fun f : Space → ℝ => ∫ y, f y)
    funext y
    change ‖g y‖ = S.indicator (fun z => ‖b z-m‖) y
    by_cases hy : y∈S
    · simp only [g,indicator_of_mem hy]
    · simp only [g,indicator_of_notMem hy,norm_zero]
  have hVol : μ.real univ = (2*s)^4*V := by
    change ((volume : Measure Space).restrict S).real univ = _
    rw [measureReal_def,Measure.restrict_apply_univ,← measureReal_def]
    change (volume : Measure Space).real (ball x (2*s)) = _
    rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball volume x (2*s),
      Measure.addHaar_real_closedBall volume x (by positivity),finrank_euclideanSpace_fin]
  have hLoc := compactWaveletAction_localize ψ hψ hMean b hb m x x s s hs le_rfl (mem_ball_self hs)
  have hHolder := integral_norm_le_local_sq μ hbM
  have hScale : Real.sqrt ((2*s)^4) = (2*s)^2 := by
    rw [show (2*s)^4=((2*s)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  have hSize : (∫ y, ‖g y‖) ≤ (Real.sqrt A*(U+(L:ℝ)) * (2*s)^2) * ((2*s)^2 * Real.sqrt V) := by
    rw [hInt]
    have hVolSqrt : Real.sqrt (μ.real univ) = (2*s)^2 * Real.sqrt V := by
      rw [hVol,Real.sqrt_mul (pow_nonneg (by positivity : 0≤2*s) _),hScale]
    have hOscSqrt : Real.sqrt (A * (U+(L:ℝ))^2 * (2*s)^4) =
        Real.sqrt A*(U+(L:ℝ)) * (2*s)^2 := by
      rw [Real.sqrt_mul (mul_nonneg hA (sq_nonneg _)),Real.sqrt_mul hA,
        Real.sqrt_sq (add_nonneg hU L.coe_nonneg),hScale]
    refine hHolder.trans ?_
    rw [hVolSqrt,← hOscSqrt]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hm)
      (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
  rw [hLoc]
  refine (compactWaveletAction_norm_le_integral_norm ψ s hg x).trans ?_
  refine (mul_le_mul_of_nonneg_left hSize (mul_nonneg (abs_nonneg _) hM)).trans_eq ?_
  rw [abs_of_nonneg (by positivity : 0≤(s^4)⁻¹)]
  field_simp [hs.ne']
  ring

end Burnett.Analysis.CarlesonEmbedding
