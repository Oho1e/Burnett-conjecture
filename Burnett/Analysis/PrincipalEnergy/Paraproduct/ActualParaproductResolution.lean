import Burnett.Analysis.PrincipalEnergy.Paraproduct.ActualTwoWindowParaproduct
import Burnett.Analysis.PrincipalEnergy.Paraproduct.BilateralWaveletSynthesis

set_option autoImplicit false
set_option maxHeartbeats 3500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators Topology NNReal ENNReal

/-- The physical paraproduct contribution at one scale. -/
def compactWaveletParaproductAtScale (φ ψ θ : SchwartzMap Space ℂ) (s : ℝ)
    (b f : Space → ℂ) : Space → ℂ :=
  compactWaveletAction θ s (fun y => compactWaveletAction ψ s b y * compactWaveletAction φ s f y)

private theorem real_lintegral_square_to_lp {f : Space → ℂ} (hf : MemLp f 2 volume) :
    (∫⁻ x, ‖f x‖ₑ^(2:ℕ)).toReal = ‖hf.toLp f‖^2 := by
  rw [l2_norm_sq_integral]
  have hAE : (∫ x, ‖hf.toLp f x‖^2) = ∫ x, ‖f x‖^2 :=
    integral_congr_ae ((MemLp.coeFn_toLp hf).fun_comp (fun z : ℂ => ‖z‖^2))
  rw [hAE]
  have hEq := ofReal_integral_eq_lintegral_ofReal
    (hf.integrable_norm_pow (p := 2) (by decide)) (Eventually.of_forall fun _ => sq_nonneg _)
  simp only [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm_eq_enorm] at hEq
  rw [← hEq,ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]

private theorem lintegral_square_ne_top {f : Space → ℂ} (hf : MemLp f 2 volume) :
    (∫⁻ x, ‖f x‖ₑ^(2:ℕ)) ≠ ⊤ := by
  have h := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg ‖f x‖)).mp
    (hf.integrable_norm_pow (p := 2) (by decide)).2
  simpa only [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm_eq_enorm] using h.ne

private theorem two_ended_scale_match (t : ℝ) (N j : ℕ) :
    bilateralWaveletScale t ((j:ℤ)-(N:ℤ)) = reproducingScale t N j := by
  rw [bilateralWaveletScale,reproducingScale,compactWaveletScale,zpow_sub₀ (by norm_num),
    zpow_natCast,zpow_natCast,div_div_eq_mul_div]

private theorem two_ended_interval_eq_image (N : ℕ) :
    Finset.Ico (-(N:ℤ)) (N:ℤ) =
      (Finset.range (N+N)).image (fun j : ℕ => (j:ℤ)-(N:ℤ)) := by
  ext j
  simp only [Finset.mem_Ico,Finset.mem_image,Finset.mem_range]
  constructor
  · intro hj
    refine ⟨(j+(N:ℤ)).toNat,?_,?_⟩ <;> omega
  · rintro ⟨k,hk,rfl⟩
    omega

/-- The physical paraproduct contributions of the actual compact-base
commutator coefficient sum unconditionally in L², with the same bound
as the finite cuts. The two-ended physical cutoffs converge to this sum. -/
theorem exists_compactBase_bilateral_two_window_paraproduct
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z = 0) (hψ : ∀ z, 1<‖z‖ → ψ z = 0)
    (hψ₀ : (∫ z, ψ z)=0) (hθ₀ : (∫ z, θ z)=0) :
    ∃ C : ℝ, 0≤C ∧ ∀ (r f : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0≤U → LipschitzWith L r → (∀ x, ‖r x‖≤U) → ∀ (t : ℝ), 0<t →
      let b := coefficientCommutatorConstant a r
      let T (j : ℤ) := compactWaveletParaproductAtScale φ ψ θ (bilateralWaveletScale t j) b f
      ∃ hTerm : ∀ j, MemLp (T j) 2 volume,
        let v (j : ℤ) := (hTerm j).toLp (T j)
        Summable v ∧ ‖∑' j, v j‖ ≤ C*(U+(L:ℝ))*‖f.toLp 2 volume‖ ∧
          ∃ hN : ∀ N, MemLp (compactWaveletParaproductTruncation φ ψ θ t N b f) 2 volume,
            Tendsto (fun N => (hN N).toLp (compactWaveletParaproductTruncation φ ψ θ t N b f))
              atTop (𝓝 (∑' j, v j)) := by
  obtain ⟨A,hA,hWeighted⟩ := exists_compactBase_commutatorConstant_weighted_wavelet_square_bound
    ha hBase hCont ψ φ hψ hψ₀ hφ
  obtain ⟨D,hD,hSynthesis⟩ := exists_bilateral_waveletSynthesis_bound θ hθ₀
  obtain ⟨C,hC,hTrunc⟩ := exists_compactBase_two_window_paraproduct_L2_bound
    ha hBase hCont φ ψ θ hφ hψ hψ₀ hθ₀
  refine ⟨C,hC,?_⟩
  intro r f L U hU hLip hR t ht b T
  let F (s : ℝ) (x : Space) := compactWaveletAction ψ s b x * compactWaveletAction φ s f x
  have hb₁ : Integrable b volume := coefficientCommutatorConstant_integrable ha.frequency hBase hCont r
  have hb₂ : MemLp b 2 volume := coefficientCommutatorConstant_memLp ha.frequency hBase hCont r
  have hF₁ (s : ℝ) (hs : 0<s) : Integrable (F s) volume := by
    have hG := compactWaveletAction_integrable ψ s hs hb₁
    have hP := compactWaveletAction_continuous φ s hs f (f.integrable (μ := (volume : Measure Space)))
    simpa only [F,mul_comm] using hG.bdd_mul hP.aestronglyMeasurable
      ⟨_,compactWaveletAction_norm_le_integral_norm φ s f.integrable⟩
  have hF₂ (s : ℝ) (hs : 0<s) : MemLp (F s) 2 volume := by
    have hG : MemLp (compactWaveletAction ψ s b) 2 volume := MemLp.ae_eq
      (waveletMultiplier_ae_eq_action ψ s hs b hb₁ hb₂) (Lp.memLp _)
    exact hG.of_le_mul (hF₁ s hs).aestronglyMeasurable <| Eventually.of_forall fun x => by
      rw [show ‖F s x‖ = ‖compactWaveletAction φ s f x‖ * ‖compactWaveletAction ψ s b x‖ by
        simp only [F,norm_mul,mul_comm]]
      exact mul_le_mul_of_nonneg_right (compactWaveletAction_norm_le_integral_norm φ s f.integrable x)
        (norm_nonneg _)
  let q := bilateralWaveletScale t
  have hq (j : ℤ) : 0<q j := div_pos ht (zpow_pos (by norm_num) _)
  let u (j : ℤ) := (hF₂ (q j) (hq j)).toLp (F (q j))
  let v (j : ℤ) := fourierMultiplier (waveletSymbol θ (q j)) (u j)
  have hV (j : ℤ) : (v j : Space → ℂ) =ᵐ[volume] T j :=
    waveletMultiplier_ae_eq_action θ (q j) (hq j) (F (q j)) (hF₁ (q j) (hq j)) (hF₂ (q j) (hq j))
  let hTerm (j : ℤ) := MemLp.ae_eq (hV j) (Lp.memLp (v j))
  have hTermEq (j : ℤ) : (hTerm j).toLp (T j) = v j :=
    Lp.ext ((MemLp.coeFn_toLp (hTerm j)).trans (hV j).symm)
  refine ⟨hTerm,?_⟩
  simp only [hTermEq]
  let W (s : ℝ) : ℝ := (∫⁻ x, ‖F s x‖ₑ^(2:ℕ)).toReal
  let K := A.toReal*(U+(L:ℝ))^2*‖f.toLp 2 volume‖^2
  have hK : 0≤K := mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)) (sq_nonneg _)
  have hFin (p : ℝ) (hp : 0<p) (J : Finset ℕ) :
      (∑ j ∈ J, W (compactWaveletScale p j)) ≤ K := by
    have H := hWeighted r f L U hU hLip hR p hp J
    let s := compactWaveletScale p
    have hs (j : ℕ) : 0<s j := div_pos hp (pow_pos (by norm_num) _)
    change (∑ j ∈ J, ∫⁻ x, ‖F (s j) x‖ₑ^(2:ℕ)) ≤ _ at H
    have hFin₀ (j : ℕ) : (∫⁻ x, ‖F (s j) x‖ₑ^(2:ℕ)) ≠ ⊤ :=
      lintegral_square_ne_top (hF₂ (s j) (hs j))
    have H₀ : A * ENNReal.ofReal (U+(L:ℝ))^2 * (∫⁻ x, ‖f x‖ₑ^(2:ℕ)) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top hA (ENNReal.pow_ne_top (by simp)))
        (lintegral_square_ne_top (f.memLp 2 volume))
    have H' := ENNReal.toReal_mono H₀ H
    rw [ENNReal.toReal_sum (fun j _ => hFin₀ j),ENNReal.toReal_mul,ENNReal.toReal_mul,
      ENNReal.toReal_pow,ENNReal.toReal_ofReal (add_nonneg hU L.coe_nonneg),
      real_lintegral_square_to_lp (f.memLp 2 volume)] at H'
    exact H'
  have hWSq (j : ℤ) : W (q j) = ‖u j‖^2 := real_lintegral_square_to_lp (hF₂ (q j) (hq j))
  have hWeights : Summable (fun j => ‖u j‖^2) := by
    apply summable_of_sum_le (c := K) (fun _ => sq_nonneg _)
    intro J
    simp_rw [← hWSq]
    exact bilateral_wavelet_square_sum_le W K t hK ht hFin J
  have hSum : Summable v :=
    summable_of_finite_synthesis_bound hD hWeights (fun J => hSynthesis t ht J u)
  let w := ∑' j, v j
  have hCutFun (J : Finset ℤ) :
      ((∑ j ∈ J, v j : ComplexL2 Space) : Space → ℂ) =ᵐ[volume] fun x => ∑ j ∈ J, T j x := by
    classical
    induction J using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (Lp.coeFn_zero ℂ 2 (volume : Measure Space))
    | insert j J hj ih =>
      simp only [Finset.sum_insert hj]
      filter_upwards [Lp.coeFn_add (v j) (∑ i ∈ J, v i), hV j, ih] with x h₁ h₂ h₃
      rw [h₁,Pi.add_apply,h₂,h₃]
  let I (N : ℕ) := Finset.Ico (-(N:ℤ)) (N:ℤ)
  have hI (N : ℕ) (x : Space) : (∑ j ∈ I N, T j x) = compactWaveletParaproductTruncation φ ψ θ t N b f x := by
    rw [show I N = _ from two_ended_interval_eq_image N,
      Finset.sum_image (fun j _ k _ h => by omega)]
    unfold compactWaveletParaproductTruncation
    refine Finset.sum_congr rfl fun j _ => ?_
    change compactWaveletParaproductAtScale φ ψ θ (bilateralWaveletScale t ((j:ℤ)-(N:ℤ))) b f x = _
    rw [two_ended_scale_match]
    rfl
  let hN (N : ℕ) := Classical.choose (hTrunc r f L U hU hLip hR t ht N)
  have hCutEq (N : ℕ) : (hN N).toLp (compactWaveletParaproductTruncation φ ψ θ t N b f) =
      ∑ j ∈ I N, v j := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (hN N), hCutFun (I N)] with x hx hy
    exact hx.trans ((hI N x).symm.trans hy.symm)
  have hLim : Tendsto (fun N => (hN N).toLp (compactWaveletParaproductTruncation φ ψ θ t N b f))
      atTop (𝓝 w) :=
    (hSum.hasSum.comp tendsto_two_ended_integer_intervals).congr fun N => (hCutEq N).symm
  refine ⟨hSum,?_,hN,hLim⟩
  exact le_of_tendsto hLim.norm <| Eventually.of_forall fun N =>
    Classical.choose_spec (hTrunc r f L U hU hLip hR t ht N)

end Burnett.Analysis.CarlesonEmbedding
