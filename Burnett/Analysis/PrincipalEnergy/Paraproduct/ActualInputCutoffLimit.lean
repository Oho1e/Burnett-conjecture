import Burnett.Analysis.PrincipalEnergy.Paraproduct.BilateralReproduction
import Burnett.Analysis.PrincipalEnergy.Paraproduct.ExpandingAverageWindows

set_option autoImplicit false
set_option maxHeartbeats 3700000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators Topology NNReal

private theorem summable_square_weights_tendsto {W : ℤ → ℝ} (hW : Summable W)
    {F : ℕ → ℤ → ℝ} (hF : ∀ n j, 0≤F n j) (hBound : ∀ n j, F n j≤W j)
    (hPoint : ∀ j, Tendsto (fun n => F n j) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' j, F n j) atTop (𝓝 0) := by
  have hW₀ (j : ℤ) : 0≤W j := (hF 0 j).trans (hBound 0 j)
  have hI : Integrable W Measure.count := by
    apply integrable_count_iff.mpr
    simpa only [Real.norm_of_nonneg (hW₀ _)] using hW
  have hMeas (n : ℕ) : AEStronglyMeasurable (F n) Measure.count :=
    (measurable_of_countable (F n)).aestronglyMeasurable
  have hDom (n : ℕ) : ∀ᵐ j ∂(Measure.count : Measure ℤ), ‖F n j‖≤W j :=
    Eventually.of_forall fun j => by rw [Real.norm_of_nonneg (hF n j)]; exact hBound n j
  have h := tendsto_integral_of_dominated_convergence (μ := (Measure.count : Measure ℤ)) W
    hMeas hI hDom (Eventually.of_forall hPoint)
  rw [integral_zero] at h
  refine h.congr fun n => ?_
  rw [integral_countable' (hI.mono' (hMeas n) (hDom n))]
  simp only [count_real_singleton,one_smul]

/-- The actual paraproduct's expanding constant input converges strongly
in $L^2$ to the original compact-base commutator constant representative. -/
theorem exists_compactBase_bilateral_paraproduct_input_expanding_tendsto
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z=0) (hψ : ∀ z, 1<‖z‖ → ψ z=0)
    (hφ₁ : (∫ z, φ z)=1) (hψ₀ : (∫ z, ψ z)=0) (hθ₀ : (∫ z, θ z)=0)
    (hFac : WaveletFactorization φ ψ θ)
    (r χ : SchwartzMap Space ℂ) (hχ : HasCompactSupport (χ : Space → ℂ))
    (hχ₁ : ∀ x : Space, ‖x‖≤1 → χ x=1)
    (L : NNReal) (U : ℝ) (hU : 0≤U)
    (hLip : LipschitzWith L r) (hR : ∀ x, ‖r x‖≤U) (t : ℝ) (ht : 0<t) :
    let b := coefficientCommutatorConstant a r
    let F := expandingTestSchwartz χ hχ
    let T (n : ℕ) (j : ℤ) := compactWaveletParaproductAtScale φ ψ θ (bilateralWaveletScale t j) b (F n)
    ∃ (hCoeff : MemLp b 2 volume) (hTerm : ∀ n j, MemLp (T n j) 2 volume),
      let v (n : ℕ) (j : ℤ) := (hTerm n j).toLp (T n j)
      (∀ n, Summable (v n)) ∧ Tendsto (fun n => ∑' j, v n j) atTop (𝓝 (hCoeff.toLp b)) := by
  obtain ⟨_,_,hPara⟩ := exists_compactBase_bilateral_two_window_paraproduct ha hBase hCont φ ψ θ hφ hψ hψ₀ hθ₀
  obtain ⟨C,_,hProfile⟩ := compactWaveletAction_expandingInput_profile φ hφ hφ₁ χ hχ₁
  obtain ⟨D,_,hS⟩ := exists_bilateral_waveletSynthesis_tsum_bound θ hθ₀
  intro b F T
  have hb₁ : Integrable b volume := coefficientCommutatorConstant_integrable ha.frequency hBase hCont r
  have hb₂ : MemLp b 2 volume := coefficientCommutatorConstant_memLp ha.frequency hBase hCont r
  let hTerm (n : ℕ) := Classical.choose (hPara r (F n) L U hU hLip hR t ht)
  let v (n : ℕ) (j : ℤ) := (hTerm n j).toLp (T n j)
  have hv (n : ℕ) : Summable (v n) := (Classical.choose_spec (hPara r (F n) L U hU hLip hR t ht)).1
  refine ⟨hb₂,hTerm,hv,?_⟩
  let s := bilateralWaveletScale t
  have hs (j : ℤ) : 0<s j := div_pos ht (zpow_pos (by norm_num) _)
  let q (j : ℤ) := fourierMultiplier (waveletSymbol ψ (s j)) (hb₂.toLp b)
  let Z (j : ℤ) := fourierMultiplier (waveletSymbol θ (s j)) (q j)
  have hZ : HasSum Z (hb₂.toLp b) :=
    hasSum_bilateral_reproducing_wavelets φ ψ θ hφ₁ hψ₀ hθ₀ hFac t ht (hb₂.toLp b)
  let Q (j : ℤ) := compactWaveletAction ψ (s j) b
  have hQ (j : ℤ) : (q j : Space → ℂ) =ᵐ[volume] Q j :=
    waveletMultiplier_ae_eq_action ψ (s j) (hs j) b hb₁ hb₂
  have hQ₁ (j : ℤ) : Integrable (Q j) volume := compactWaveletAction_integrable ψ (s j) (hs j) hb₁
  have hQ₂ (j : ℤ) : MemLp (Q j) 2 volume := MemLp.ae_eq (hQ j) (Lp.memLp _)
  let P (n : ℕ) (j : ℤ) := compactWaveletAction φ (s j) (F n)
  have hP₁ (n : ℕ) (j : ℤ) : Continuous (P n j) :=
    compactWaveletAction_continuous φ (s j) (hs j) (F n) ((F n).integrable (μ := (volume : Measure Space)))
  have hPB (n : ℕ) (j : ℤ) (x : Space) : ‖P n j x‖≤C := by
    simpa only [P,F,expandingTestSchwartz_apply] using (hProfile (s j) (hs j) x).1 n
  have hPE (j : ℤ) (x : Space) : (fun n => P n j x) =ᶠ[atTop] fun _ => 1 := by
    simpa only [P,F,expandingTestSchwartz_apply] using (hProfile (s j) (hs j) x).2
  let G (n : ℕ) (j : ℤ) (x : Space) := Q j x*P n j x
  have hG₁ (n : ℕ) (j : ℤ) : Integrable (G n j) volume := by
    simpa only [G,mul_comm] using (hQ₁ j).bdd_mul (hP₁ n j).aestronglyMeasurable ⟨C,hPB n j⟩
  have hG₂ (n : ℕ) (j : ℤ) : MemLp (G n j) 2 volume := by
    refine (hQ₂ j).of_le_mul (c := C) (hG₁ n j).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    change ‖Q j x*P n j x‖≤C*‖Q j x‖
    rw [norm_mul,mul_comm ‖Q j x‖]
    exact mul_le_mul_of_nonneg_right (hPB n j x) (norm_nonneg _)
  let p (n : ℕ) (j : ℤ) := (hG₂ n j).toLp (G n j)
  have hV (n : ℕ) (j : ℤ) : fourierMultiplier (waveletSymbol θ (s j)) (p n j) = v n j :=
    Lp.ext ((waveletMultiplier_ae_eq_action θ (s j) (hs j) (G n j) (hG₁ n j) (hG₂ n j)).trans
      (MemLp.coeFn_toLp (hTerm n j)).symm)
  let u (n : ℕ) (j : ℤ) := p n j-q j
  have hUeq (n : ℕ) (j : ℤ) : (u n j : Space → ℂ) =ᵐ[volume]
      fun x => Q j x*(P n j x-1) := by
    filter_upwards [Lp.coeFn_sub (p n j) (q j),MemLp.coeFn_toLp (hG₂ n j),hQ j] with x h₁ h₂ h₃
    rw [h₁,Pi.sub_apply,h₂,h₃]
    dsimp only [G]
    ring
  let E (n : ℕ) (j : ℤ) (x : Space) := ‖Q j x*(P n j x-1)‖^2
  have hUE (n : ℕ) (j : ℤ) : ‖u n j‖^2 = ∫ x, E n j x := by
    rw [l2_norm_sq_integral]
    exact integral_congr_ae ((hUeq n j).fun_comp (fun z : ℂ => ‖z‖^2))
  have hE₁ (n : ℕ) (j : ℤ) : Integrable (E n j) volume :=
    ((Lp.memLp (u n j)).integrable_norm_pow (p := 2) (by decide)).congr
      ((hUeq n j).fun_comp (fun z : ℂ => ‖z‖^2))
  let B (j : ℤ) (x : Space) := (C+1)^2*‖Q j x‖^2
  have hB₁ (j : ℤ) : Integrable (B j) volume :=
    ((hQ₂ j).integrable_norm_pow (p := 2) (by decide)).const_mul _
  have hEB (n : ℕ) (j : ℤ) (x : Space) : E n j x≤B j x := by
    have hP : ‖P n j x-1‖≤C+1 := by
      calc
        _ ≤ ‖P n j x‖+‖(1:ℂ)‖ := norm_sub_le _ _
        _ ≤ _ := by rw [norm_one]; exact add_le_add_right (hPB n j x) 1
    dsimp only [E,B]
    rw [norm_mul,mul_pow,mul_comm (‖Q j x‖^2)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hP 2) (sq_nonneg _)
  let W (j : ℤ) := (C+1)^2*‖q j‖^2
  have hW : Summable W := (summable_bilateral_wavelet_norm_sq ψ hψ₀ t ht (hb₂.toLp b)).mul_left _
  have hUC (n : ℕ) (j : ℤ) : ‖u n j‖^2≤W j := by
    rw [hUE]
    refine (integral_mono (hE₁ n j) (hB₁ j) (hEB n j)).trans_eq ?_
    dsimp only [B,W]
    rw [integral_const_mul,l2_norm_sq_integral]
    exact congrArg (fun y : ℝ => (C+1)^2*y)
      (integral_congr_ae ((hQ j).fun_comp (fun z : ℂ => ‖z‖^2))).symm
  have hPoint (j : ℤ) : Tendsto (fun n => ‖u n j‖^2) atTop (𝓝 0) := by
    have hEPoint (x : Space) : Tendsto (fun n => E n j x) atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hPE j x] with n hn
      change P n j x=1 at hn
      simp only [E,hn,sub_self,mul_zero,norm_zero,zero_pow (by decide : (2:ℕ)≠0)]
    have hLim := tendsto_integral_of_dominated_convergence (B j)
      (fun n => (hE₁ n j).aestronglyMeasurable) (hB₁ j)
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (show 0≤E n j x from sq_nonneg _)]
        exact hEB n j x) (Eventually.of_forall hEPoint)
    rw [integral_zero] at hLim
    exact hLim.congr fun n => (hUE n j).symm
  have hEnergy : Tendsto (fun n => ∑' j, ‖u n j‖^2) atTop (𝓝 0) :=
    summable_square_weights_tendsto hW (fun _ _ => sq_nonneg _) hUC hPoint
  have hWeight (n : ℕ) : Summable (fun j => ‖u n j‖^2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (hUC n) hW
  have hDiff (n : ℕ) : (∑' j, v n j)-hb₂.toLp b =
      ∑' j, fourierMultiplier (waveletSymbol θ (s j)) (u n j) := by
    rw [← hZ.tsum_eq,← (hv n).tsum_sub hZ.summable]
    simp only [u,map_sub,hV,Z]
  have hNorm (n : ℕ) : ‖(∑' j, v n j)-hb₂.toLp b‖≤D*Real.sqrt (∑' j, ‖u n j‖^2) := by
    rw [hDiff]
    exact (hS t ht (u n) (hWeight n)).2
  have hNormLim : Tendsto (fun n => D*Real.sqrt (∑' j, ‖u n j‖^2)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,mul_zero] using hEnergy.sqrt.const_mul D
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hNormLim (fun _ => norm_nonneg _) hNorm)

end Burnett.Analysis.CarlesonEmbedding
