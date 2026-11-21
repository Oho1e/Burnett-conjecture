import Burnett.Analysis.PrincipalEnergy.Paraproduct.ParaproductMassEstimates
import Burnett.Analysis.PrincipalEnergy.Paraproduct.ActualCoefficientLipschitz
import Burnett.Analysis.PrincipalEnergy.Paraproduct.ActualParaproductResolution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
set_option maxHeartbeats 2900000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators Topology NNReal ENNReal

private theorem bilateral_scale_nat (t : ℝ) (n : ℕ) :
    bilateralWaveletScale t (n:ℤ)=t*(1/2:ℝ)^n := by
  rw [bilateralWaveletScale,zpow_natCast,div_eq_mul_inv,← inv_pow]
  norm_num

private theorem bilateral_scale_neg_inv_four (t : ℝ) (n : ℕ) :
    (bilateralWaveletScale t (-((n:ℤ)+1))^4)⁻¹=(t^4)⁻¹*(1/16:ℝ)^(n+1) := by
  have hFour : ((2:ℝ)^(n+1))^4=(16:ℝ)^(n+1) := by
    rw [← pow_mul,Nat.mul_comm (n+1) 4,pow_mul]
    norm_num
  rw [show -((n:ℤ)+1) = -((n+1:ℕ):ℤ) by omega,
    bilateralWaveletScale,zpow_neg,zpow_natCast,div_inv_eq_mul,mul_pow,hFour,mul_inv_rev,← inv_pow]
  norm_num [mul_comm]

private theorem lp_finset_sum_ae {p : ℝ≥0∞} {g : ℤ → Space → ℂ}
    {v : ℤ → Lp ℂ p (volume : Measure Space)} (h : ∀ j, (v j : Space → ℂ) =ᵐ[volume] g j)
    (J : Finset ℤ) :
    ((∑ j ∈ J, v j : Lp ℂ p (volume : Measure Space)) : Space → ℂ) =ᵐ[volume]
      fun x => ∑ j ∈ J, g j x := by
  classical
  induction J using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (Lp.coeFn_zero ℂ p (volume : Measure Space))
  | insert j J hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (v j) (∑ k ∈ J, v k),h j,ih] with x h₁ h₂ h₃
    rw [h₁,Pi.add_apply,h₂,h₃]

/-- The actual $L^2$ sum of the two-window paraproduct also has an
integrable representative with zero total mass on each Schwartz test. -/
theorem exists_compactBase_bilateral_two_window_paraproduct_integral_zero
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z=0) (hψ : ∀ z, 1<‖z‖ → ψ z=0)
    (hψ₀ : (∫ z, ψ z)=0) (hθ₀ : (∫ z, θ z)=0)
    (r f : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ) (hU : 0≤U)
    (hLip : LipschitzWith L r) (hR : ∀ x, ‖r x‖≤U) (t : ℝ) (ht : 0<t) :
    let b := coefficientCommutatorConstant a r
    let T (j : ℤ) := compactWaveletParaproductAtScale φ ψ θ (bilateralWaveletScale t j) b f
    ∃ hTerm : ∀ j, MemLp (T j) 2 volume,
      let v := fun j => (hTerm j).toLp (T j)
      Summable v ∧ Integrable (fun x => (∑' j, v j) x) volume ∧ (∫ x, (∑' j, v j) x)=0 := by
  obtain ⟨_,_,hL2⟩ := exists_compactBase_bilateral_two_window_paraproduct ha hBase hCont φ ψ θ hφ hψ hψ₀ hθ₀
  intro b T
  obtain ⟨hTerm,hSum,_,_⟩ := hL2 r f L U hU hLip hR t ht
  let v (j : ℤ) := (hTerm j).toLp (T j)
  have hv : Summable v := hSum
  have hb : Integrable b volume := coefficientCommutatorConstant_integrable ha.frequency hBase hCont r
  obtain ⟨M,hM⟩ := exists_coefficientCommutatorConstant_lipschitz ha r L U hU hLip hR
  let s := bilateralWaveletScale t
  have hs (j : ℤ) : 0<s j := div_pos ht (zpow_pos (by norm_num) _)
  have hB (j : ℤ) := compactWaveletParaproduct_scale_L1_bounds φ ψ θ hψ hψ₀ (s j) (hs j) hb
    (f.integrable (μ := (volume : Measure Space))) M hM
  have hTI (j : ℤ) : Integrable (T j) volume := (hB j).1
  let u (j : ℤ) := (hTI j).toL1 (T j)
  let fine := (M:ℝ)*(∫ z, ‖θ z‖)*(∫ z, ‖ψ z‖)*(∫ z, ‖φ z‖)*(∫ z, ‖f z‖)
  let coarse := SchwartzMap.seminorm ℝ 0 0 φ*(∫ z, ‖θ z‖)*(∫ z, ‖ψ z‖)*
    (∫ z, ‖b z‖)*(∫ z, ‖f z‖)
  have hFine (j : ℤ) : ‖u j‖ ≤ fine*s j := by
    rw [show ‖u j‖ = ∫ x, ‖T j x‖ from L1.norm_of_fun_eq_integral_norm (hTI j)]
    exact ((hB j).2.1).trans_eq (by dsimp only [fine]; ring)
  have hCoarse (j : ℤ) : ‖u j‖ ≤ coarse*((s j)^4)⁻¹ := by
    rw [show ‖u j‖ = ∫ x, ‖T j x‖ from L1.norm_of_fun_eq_integral_norm (hTI j)]
    exact ((hB j).2.2).trans_eq (by dsimp only [coarse]; ring)
  have hUNorm : Summable (fun j => ‖u j‖) := by
    apply Summable.of_nat_of_neg_add_one
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
        ((summable_geometric_of_lt_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num)).mul_left (fine*t))
      intro n
      exact (hFine (n:ℤ)).trans_eq (by
        dsimp only [s,fine]
        rw [bilateral_scale_nat]
        ring)
    · have hGeom := ((summable_geometric_of_lt_one (by norm_num : 0≤(1/16:ℝ))
          (by norm_num)).mul_left (coarse*(t^4)⁻¹)).comp_injective Nat.succ_injective
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hGeom
      intro n
      exact (hCoarse (-((n:ℤ)+1))).trans_eq (by
        dsimp only [s,coarse,Function.comp_def,Nat.succ_eq_add_one]
        rw [bilateral_scale_neg_inv_four]
        ring)
  have hu : Summable u := hUNorm.of_norm
  let I (N : ℕ) := Finset.Ico (-(N:ℤ)) (N:ℤ)
  let w (N : ℕ) (x : Space) := ∑ j ∈ I N, T j x
  have hMu : TendstoInMeasure volume w atTop
      ((∑' j, u j : Space →₁[(volume : Measure Space)] ℂ) : Space → ℂ) :=
    TendstoInMeasure.congr_left
      (fun N => lp_finset_sum_ae (fun j => (hTI j).coeFn_toL1) (I N))
      (tendstoInMeasure_of_tendsto_Lp (hu.hasSum.comp tendsto_two_ended_integer_intervals))
  have hMv : TendstoInMeasure volume w atTop ((∑' j, v j : ComplexL2 Space) : Space → ℂ) :=
    TendstoInMeasure.congr_left
      (fun N => lp_finset_sum_ae (fun j => MemLp.coeFn_toLp (hTerm j)) (I N))
      (tendstoInMeasure_of_tendsto_Lp (hv.hasSum.comp tendsto_two_ended_integer_intervals))
  have hEq := tendstoInMeasure_ae_unique hMv hMu
  refine ⟨hTerm,hv,(L1.integrable_coeFn (∑' j, u j)).congr hEq.symm,?_⟩
  rw [integral_congr_ae hEq,← L1.integral_eq_integral,L1.integral_eq]
  let J : (Space →₁[(volume : Measure Space)] ℂ) →L[ℝ] ℂ := L1.integralCLM
  change J (∑' j, u j)=0
  rw [J.map_tsum hu]
  have hZero (j : ℤ) : J (u j)=0 := by
    change L1.integralCLM (u j)=0
    rw [← L1.integral_eq,L1.integral_eq_integral,integral_congr_ae (hTI j).coeFn_toL1]
    let G := fun y => compactWaveletAction ψ (s j) b y*compactWaveletAction φ (s j) f y
    have hG : Integrable G volume := by
      have hψL1 := compactWaveletAction_integrable ψ (s j) (hs j) hb
      have hφL1 := compactWaveletAction_integrable φ (s j) (hs j) (f.integrable (μ := (volume : Measure Space)))
      simpa only [G,mul_comm] using hψL1.bdd_mul hφL1.aestronglyMeasurable
        ⟨_,compactWaveletAction_norm_le_integral_norm φ (s j) f.integrable⟩
    change (∫ x, compactWaveletAction θ (s j) G x)=0
    rw [compactWaveletAction_integral θ (s j) (hs j) hG,hθ₀,zero_mul]
  simp only [hZero,tsum_zero]

end Burnett.Analysis.CarlesonEmbedding
