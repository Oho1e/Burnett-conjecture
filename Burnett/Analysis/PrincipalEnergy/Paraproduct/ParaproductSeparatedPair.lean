import Burnett.Analysis.PrincipalEnergy.Paraproduct.BilateralParaproductKernel

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped Topology ComplexConjugate NNReal BigOperators InnerProductSpace

/-- On genuinely separated Schwartz inputs the actual bilateral paraproduct
pairing is integration against the bilateral physical kernel. -/
theorem exists_compactBase_bilateral_paraproduct_separated_pair_eq_kernel
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z=0) (hψ : ∀ z, 1<‖z‖ → ψ z=0) (hθ : ∀ z, 1<‖z‖ → θ z=0)
    (hψ₀ : (∫ z, ψ z)=0) (hθ₀ : (∫ z, θ z)=0)
    (r f g : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ) (hU : 0≤U)
    (hLip : LipschitzWith L r) (hR : ∀ x, ‖r x‖≤U)
    (t : ℝ) (ht : 0<t) (d : ℝ) (hd : 0<d)
    (hGap : ∀ x y : Space, f y≠0 → g x≠0 → d≤‖x-y‖) :
    let b := coefficientCommutatorConstant a r
    let T (j : ℤ) := compactWaveletParaproductAtScale φ ψ θ (bilateralWaveletScale t j) b f
    ∃ hTerm : ∀ j, MemLp (T j) 2 volume,
      let v (j : ℤ) := (hTerm j).toLp (T j)
      Summable v ∧
        inner ℂ (g.toLp 2 volume) (∑' j, v j) =
          ∫ p : Space × Space,
            conj (g p.1) * (bilateralParaproductKernel φ ψ θ t b p.1 p.2 * f p.2)
            ∂((volume : Measure Space).prod volume) := by
  obtain ⟨_,_,hL2⟩ := exists_compactBase_bilateral_two_window_paraproduct ha hBase hCont φ ψ θ hφ hψ hψ₀ hθ₀
  obtain ⟨A,hA,hCoef⟩ := exists_compactBase_commutatorConstant_wavelet_sup_bound ha hBase hCont ψ hψ hψ₀
  intro b T
  obtain ⟨hTerm,hSum,_,_⟩ := hL2 r f L U hU hLip hR t ht
  let v (j : ℤ) := (hTerm j).toLp (T j)
  have hv : Summable v := hSum
  refine ⟨hTerm,hv,?_⟩
  have hb : Integrable b volume := coefficientCommutatorConstant_integrable ha.frequency hBase hCont r
  let B := A*(U+(L:ℝ))
  have hB : 0≤B := mul_nonneg hA (add_nonneg hU L.coe_nonneg)
  let s := bilateralWaveletScale t
  have hs (j : ℤ) : 0<s j := div_pos ht (zpow_pos (by norm_num) _)
  have hQ (j : ℤ) (z : Space) : ‖compactWaveletAction ψ (s j) b z‖≤B :=
    hCoef r L U hU hLip hR _ (hs j) z
  let k (j : ℤ) := compactWaveletParaproductKernelAtScale φ ψ θ (s j) b
  let F (j : ℤ) (p : Space × Space) := conj (g p.1)*(k j p.1 p.2*f p.2)
  let μ : Measure (Space × Space) := (volume : Measure Space).prod volume
  let H (p : Space × Space) := ‖g p.1‖*‖f p.2‖
  have hH : Integrable H μ := (g.integrable (μ := (volume : Measure Space))).norm.mul_prod
    (f.integrable (μ := (volume : Measure Space))).norm
  have hFc (j : ℤ) : Continuous (F j) :=
    (g.continuous.comp continuous_fst).star.mul
      ((compactWaveletParaproductKernelAtScale_continuous φ ψ θ (s j) (hs j) hb hB (hQ j)).mul
        (f.continuous.comp continuous_snd))
  have hFi (j : ℤ) : Integrable (F j) μ := by
    let C := B*SchwartzMap.seminorm ℝ 0 0 φ*(∫ z, ‖θ z‖)*((s j)^4)⁻¹
    refine (hH.const_mul C).mono' (hFc j).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    change ‖F j p‖≤C*H p
    have hEq : ‖F j p‖ = ‖k j p.1 p.2‖*H p := by
      dsimp only [F,H]
      rw [norm_mul,Complex.norm_conj,norm_mul]
      ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_right
      (compactWaveletParaproductKernelAtScale_size φ ψ θ (s j) (hs j) hB (hQ j) p.1 p.2)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hPair (j : ℤ) : inner ℂ (g.toLp 2 volume) (v j) = ∫ p, F j p ∂μ := by
    rw [L2.inner_def,integral_prod _ (hFi j)]
    have hEq (x : Space) : (∫ y, k j x y*f y)=T j x :=
      (compactWaveletParaproductAtScale_eq_integral_kernel φ ψ θ (s j) (hs j) hb hB (hQ j) f x).symm
    change (∫ x, inner ℂ ((g.toLp 2 volume) x) (v j x)) =
      ∫ x, ∫ y, conj (g x)*(k j x y*f y)
    simp_rw [integral_const_mul,hEq]
    apply integral_congr_ae
    filter_upwards [g.coeFn_toLp 2 volume,MemLp.coeFn_toLp (hTerm j)] with x hg hx
    rw [hg,hx,RCLike.inner_apply']
  let I (N : ℕ) := Finset.Ico (-(N:ℤ)) (N:ℤ)
  let G (N : ℕ) (p : Space × Space) := ∑ j ∈ I N, F j p
  let K := bilateralParaproductKernel φ ψ θ t b
  let Glimit (p : Space × Space) := conj (g p.1)*(K p.1 p.2*f p.2)
  have hPairN (N : ℕ) : inner ℂ (g.toLp 2 volume) (∑ j ∈ I N, v j) = ∫ p, G N p ∂μ := by
    rw [inner_sum,show (∫ p, G N p ∂μ) = (∫ p, ∑ j ∈ I N, F j p ∂μ) from rfl,
      integral_finset_sum _ (fun j _ => hFi j)]
    exact Finset.sum_congr rfl fun j _ => hPair j
  let D := (256/15:ℝ)*B*SchwartzMap.seminorm ℝ 0 0 φ*(∫ z, ‖θ z‖)
  have hD : 0≤D := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB)
    (apply_nonneg _ _)) (integral_nonneg fun _ => norm_nonneg _)
  let M := D*(d^4)⁻¹
  have hDistinct (p : Space × Space) (hf : f p.2≠0) (hg : g p.1≠0) : p.1≠p.2 := by
    intro hp
    have hk := hGap p.1 p.2 hf hg
    rw [hp,sub_self,norm_zero] at hk
    exact (not_le_of_gt hd) hk
  have hDom (N : ℕ) (p : Space × Space) : ‖G N p‖≤M*H p := by
    by_cases hf : f p.2=0
    · simp [G,F,H,hf]
    by_cases hg : g p.1=0
    · simp [G,F,H,hg]
    obtain ⟨hAbs,hSize,_⟩ := bilateralParaproductKernel_size φ ψ θ hφ hθ t ht hB hQ p.1 p.2
      (hDistinct p hf hg)
    have hdist := hGap p.1 p.2 hf hg
    have hInv : (‖p.1-p.2‖^4)⁻¹≤(d^4)⁻¹ :=
      (inv_le_inv₀ (pow_pos (hd.trans_le hdist) _) (pow_pos hd _)).mpr (pow_le_pow_left₀ hd.le hdist _)
    have hSumBound : (∑ j ∈ I N, ‖k j p.1 p.2‖)≤M :=
      (hAbs.sum_le_tsum (I N) (fun _ _ => norm_nonneg _)).trans
        (hSize.trans (mul_le_mul_of_nonneg_left hInv hD))
    calc
      _ ≤ ∑ j ∈ I N, ‖F j p‖ := norm_sum_le _ _
      _ = ∑ j ∈ I N, ‖k j p.1 p.2‖*H p := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [F,H]
        rw [norm_mul,Complex.norm_conj,norm_mul]
        ring
      _ = (∑ j ∈ I N, ‖k j p.1 p.2‖)*H p := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hSumBound (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hPoint (p : Space × Space) : Tendsto (fun N => G N p) atTop (𝓝 (Glimit p)) := by
    by_cases hf : f p.2=0
    · simp [G,F,Glimit,hf]
    by_cases hg : g p.1=0
    · simp [G,F,Glimit,hg]
    have hK := (bilateralParaproductKernel_size φ ψ θ hφ hθ t ht hB hQ p.1 p.2
      (hDistinct p hf hg)).1.of_norm
    have hT := ((hK.hasSum.comp tendsto_two_ended_integer_intervals).mul_const (f p.2)).const_mul (conj (g p.1))
    apply hT.congr
    intro N
    change conj (g p.1)*((∑ j ∈ I N, k j p.1 p.2)*f p.2) = ∑ j ∈ I N, F j p
    simp only [Finset.sum_mul,Finset.mul_sum,F]
  have hGmeas (N : ℕ) : AEStronglyMeasurable (G N) μ :=
    (continuous_finset_sum _ (fun j _ => hFc j)).aestronglyMeasurable
  have hLimitI := tendsto_integral_of_dominated_convergence (fun p => M*H p) hGmeas (hH.const_mul M)
    (fun N => Eventually.of_forall (hDom N)) (Eventually.of_forall hPoint)
  have hInner : Continuous (fun u : ComplexL2 Space => inner ℂ (g.toLp 2 volume) u) :=
    continuous_const.inner continuous_id
  have hLimitL := (hInner.continuousAt.tendsto.comp
    (hv.hasSum.comp tendsto_two_ended_integer_intervals)).congr hPairN
  exact tendsto_nhds_unique hLimitL hLimitI

end Burnett.Analysis.CarlesonEmbedding
