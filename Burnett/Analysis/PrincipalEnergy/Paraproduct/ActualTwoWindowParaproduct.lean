import Burnett.Analysis.PrincipalEnergy.Paraproduct.ParaproductConstantTruncations
import Burnett.Analysis.PrincipalEnergy.Paraproduct.WaveletSynthesis
import Burnett.Analysis.PrincipalEnergy.Commutator.ActualParaproduct

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators NNReal ENNReal

theorem coefficientCommutatorConstant_integrable {a : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (r : SchwartzMap Space ℂ) :
    Integrable (coefficientCommutatorConstant a r) volume := by
  obtain ⟨D,_,hOrd⟩ := ha.order 0
  have hC : Continuous (fun x => a x 0) := hCont.comp (continuous_id.prodMk continuous_const)
  have hp : Integrable (fun x => r x*a x 0) volume := by
    have h := (r.integrable (μ := (volume : Measure Space))).bdd_mul hC.aestronglyMeasurable
      ⟨D,fun x => by simpa only [pow_zero,mul_one,norm_iteratedFDeriv_zero,norm_zero,add_zero] using hOrd x 0⟩
    simpa only [mul_comm] using h
  exact hp.sub (firstOrderAction_integrable_of_compactBase hBase hCont r)

private theorem lp_sq_as_lintegral {f : Space → ℂ} (hf : MemLp f 2 volume) :
    ENNReal.ofReal (‖hf.toLp f‖^2) = ∫⁻ x, ‖f x‖ₑ^(2:ℕ) := by
  rw [l2_norm_sq_integral]
  have hAE : (∫ x, ‖hf.toLp f x‖^2) = ∫ x, ‖f x‖^2 :=
    integral_congr_ae ((MemLp.coeFn_toLp hf).fun_comp (fun z : ℂ => ‖z‖^2))
  rw [hAE,ofReal_integral_eq_lintegral_ofReal
    (hf.integrable_norm_pow (p := 2) (by decide)) (Eventually.of_forall fun _ => sq_nonneg _)]
  simp only [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm_eq_enorm]

/-- On the actual compact-base constant distribution, the physical
two-window paraproduct truncations obey the uniform Lipschitz-to-L² bound. -/
theorem exists_compactBase_two_window_paraproduct_L2_bound
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z = 0) (hψ : ∀ z, 1<‖z‖ → ψ z = 0)
    (hψ₀ : (∫ z, ψ z)=0) (hθ₀ : (∫ z, θ z)=0) :
    ∃ C : ℝ, 0≤C ∧ ∀ (r f : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0≤U → LipschitzWith L r → (∀ x, ‖r x‖≤U) → ∀ (t : ℝ), 0<t → ∀ (N : ℕ),
      let b := coefficientCommutatorConstant a r
      ∃ hP : MemLp (compactWaveletParaproductTruncation φ ψ θ t N b f) 2 volume,
        ‖hP.toLp (compactWaveletParaproductTruncation φ ψ θ t N b f)‖ ≤
          C*(U+(L:ℝ))*‖f.toLp 2 volume‖ := by
  obtain ⟨A,hA,hWeighted⟩ := exists_compactBase_commutatorConstant_weighted_wavelet_square_bound
    ha hBase hCont ψ φ hψ hψ₀ hφ
  obtain ⟨D,hD,hSynthesis⟩ := exists_finite_waveletSynthesis_bound θ hθ₀
  refine ⟨D*Real.sqrt A.toReal,by positivity,?_⟩
  intro r f L U hU hLip hVal t ht N b
  let q := t*(2:ℝ)^N
  let s := compactWaveletScale q
  let J := Finset.range (N+N)
  let G (j : ℕ) := compactWaveletAction ψ (s j) b
  let P (j : ℕ) := compactWaveletAction φ (s j) f
  let F (j : ℕ) (x : Space) := G j x*P j x
  have hq : 0<q := mul_pos ht (pow_pos (by norm_num) _)
  have hs (j : ℕ) : 0<s j := div_pos hq (pow_pos (by norm_num) _)
  have hb₁ : Integrable b volume := coefficientCommutatorConstant_integrable ha.frequency hBase hCont r
  have hb₂ : MemLp b 2 volume := coefficientCommutatorConstant_memLp ha.frequency hBase hCont r
  have hPcont (j : ℕ) : Continuous (P j) := compactWaveletAction_continuous φ (s j) (hs j) f f.integrable
  have hPB (j : ℕ) := compactWaveletAction_norm_le_integral_norm φ (s j) f.integrable
  have hF₁ (j : ℕ) : Integrable (F j) volume := by
    have hG := compactWaveletAction_integrable ψ (s j) (hs j) hb₁
    simpa only [F,mul_comm] using hG.bdd_mul (hPcont j).aestronglyMeasurable ⟨_,hPB j⟩
  have hF₂ (j : ℕ) : MemLp (F j) 2 volume := by
    have hG : MemLp (G j) 2 volume := MemLp.ae_eq
      (waveletMultiplier_ae_eq_action ψ (s j) (hs j) b hb₁ hb₂) (Lp.memLp _)
    let C := (|(s j^4)⁻¹| * SchwartzMap.seminorm ℝ 0 0 φ) * (∫ y, ‖f y‖)
    refine hG.of_le_mul (c := C) (hF₁ j).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    change ‖G j x*P j x‖ ≤ C*‖G j x‖
    rw [norm_mul,mul_comm ‖G j x‖]
    exact mul_le_mul_of_nonneg_right (hPB j x) (norm_nonneg _)
  let u (j : ℕ) := (hF₂ j).toLp (F j)
  let Y (j : ℕ) := fourierMultiplier (waveletSymbol θ (s j)) (u j)
  let S := ∑ j ∈ J, Y j
  let Q (j : ℕ) := compactWaveletAction θ (s j) (F j)
  have hQ (j : ℕ) : (Y j : Space → ℂ) =ᵐ[volume] Q j :=
    waveletMultiplier_ae_eq_action θ (s j) (hs j) (F j) (hF₁ j) (hF₂ j)
  have hPair (I : Finset ℕ) : ((∑ j ∈ I, Y j : ComplexL2 Space) : Space → ℂ) =ᵐ[volume]
      fun x => ∑ j ∈ I, Q j x := by
    classical
    induction I using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (Lp.coeFn_zero ℂ 2 (volume : Measure Space))
    | insert j I hj ih =>
      simp only [Finset.sum_insert hj]
      filter_upwards [Lp.coeFn_add (Y j) (∑ i ∈ I, Y i), hQ j, ih] with x h₁ h₂ h₃
      rw [h₁,Pi.add_apply,h₂,h₃]
  have hOut : (S : Space → ℂ) =ᵐ[volume] compactWaveletParaproductTruncation φ ψ θ t N b f := hPair J
  let hOutLp := MemLp.ae_eq hOut (Lp.memLp S)
  have hLpEq : S = hOutLp.toLp (compactWaveletParaproductTruncation φ ψ θ t N b f) :=
    Lp.ext (hOut.trans (MemLp.coeFn_toLp hOutLp).symm)
  refine ⟨hOutLp,?_⟩
  rw [← hLpEq]
  have hU₀ : 0≤U+(L:ℝ) := add_nonneg hU L.coe_nonneg
  have hULp : (∑ j ∈ J, ‖u j‖^2) ≤ A.toReal*(U+(L:ℝ))^2*‖f.toLp 2 volume‖^2 := by
    have h := hWeighted r f L U hU hLip hVal q hq J
    change (∑ j ∈ J, ∫⁻ x, ‖F j x‖ₑ^(2:ℕ)) ≤ _ at h
    simp_rw [← lp_sq_as_lintegral (hF₂ _)] at h
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
      ← lp_sq_as_lintegral (f.memLp 2 volume), ← ENNReal.ofReal_pow hU₀,← ENNReal.ofReal_toReal hA,
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  calc
    _ ≤ D*Real.sqrt (∑ j ∈ J, ‖u j‖^2) := hSynthesis q hq J u
    _ ≤ D*Real.sqrt (A.toReal*(U+(L:ℝ))^2*‖f.toLp 2 volume‖^2) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hULp) hD
    _ = _ := by
      rw [Real.sqrt_mul (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)),
        Real.sqrt_mul ENNReal.toReal_nonneg,Real.sqrt_sq hU₀,Real.sqrt_sq (norm_nonneg _)]
      ring

end Burnett.Analysis.CarlesonEmbedding
