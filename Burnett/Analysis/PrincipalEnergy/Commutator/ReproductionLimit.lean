import Burnett.Analysis.PrincipalEnergy.Commutator.ReproducingWindows

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter
open scoped Topology BigOperators

def reproducingScale (t : ℝ) (N j : ℕ) : ℝ := compactWaveletScale (t*(2:ℝ)^N) j

def WaveletFactorization (φ ψ θ : SchwartzMap Space ℂ) : Prop :=
  ∀ ξ : Space, compactWaveletFrequency ψ ξ * compactWaveletFrequency θ ξ =
    waveletCubic (compactWaveletFrequency φ ((1/2:ℝ) • ξ)) -
      waveletCubic (compactWaveletFrequency φ ξ)

/-- The same two compact windows give an exact identity for every finite
consecutive block of physical scales. -/
theorem reproducing_windows_telescoping (φ ψ θ : SchwartzMap Space ℂ)
    (hF : WaveletFactorization φ ψ θ) (q : ℝ) (ξ : Space) (n : ℕ) :
    (∑ j ∈ Finset.range n, compactWaveletFrequency ψ (compactWaveletScale q j • ξ) *
      compactWaveletFrequency θ (compactWaveletScale q j • ξ)) =
      waveletCubic (compactWaveletFrequency φ (compactWaveletScale q n • ξ)) -
        waveletCubic (compactWaveletFrequency φ (q • ξ)) := by
  have hNext (j : ℕ) : (1/2:ℝ) • (compactWaveletScale q j • ξ) =
      compactWaveletScale q (j+1) • ξ := by
    rw [smul_smul,compactWaveletScale,compactWaveletScale,pow_succ]
    congr 1
    field_simp [pow_ne_zero j (by norm_num : (2:ℝ) ≠ 0)]
  induction n with
  | zero => simp [compactWaveletScale]
  | succ n ih =>
      rw [Finset.sum_range_succ,ih,hF,hNext]
      ring

private theorem frequency_small_scale (φ : SchwartzMap Space ℂ) (t : ℝ) (ξ : Space) :
    Tendsto (fun N : ℕ => compactWaveletFrequency φ ((t/(2:ℝ)^N) • ξ)) atTop
      (𝓝 (compactWaveletFrequency φ 0)) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)).const_mul t
  have hS : Tendsto (fun N : ℕ => t/(2:ℝ)^N) atTop (𝓝 (0:ℝ)) := by
    rw [mul_zero] at h
    refine h.congr (fun N => ?_)
    rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num,inv_pow,div_eq_mul_inv]
  have hs : Tendsto (fun N : ℕ => (t/(2:ℝ)^N) • ξ) atTop (𝓝 (0:Space)) := by
    simpa only [zero_smul] using hS.smul (tendsto_const_nhds (x := ξ))
  exact (compactWaveletFrequency φ).continuous.continuousAt.tendsto.comp hs

private theorem frequency_large_scale (φ : SchwartzMap Space ℂ) (t : ℝ) (ht : 0<t)
    (ξ : Space) (hξ : ξ≠0) :
    Tendsto (fun N : ℕ => compactWaveletFrequency φ ((t*(2:ℝ)^N) • ξ)) atTop (𝓝 0) := by
  let A := compactWaveletFrequency φ
  let C := SchwartzMap.seminorm ℝ 1 0 A
  let x (N : ℕ) := (t*(2:ℝ)^N) • ξ
  have hr : 0<‖ξ‖ := norm_pos_iff.mpr hξ
  have hxN (N : ℕ) : ‖x N‖ = (t*‖ξ‖)*(2:ℝ)^N := by
    dsimp only [x]
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]
    ring
  have hx : Tendsto (fun N => ‖x N‖) atTop atTop := by
    simpa only [hxN] using (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).const_mul_atTop
      (mul_pos ht hr)
  have hSmall := (tendsto_inv_atTop_zero.comp hx).const_mul C
  apply (tendsto_zero_iff_norm_tendsto_zero).mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) (by simpa only [mul_zero] using hSmall)
  have ob : 0<‖x N‖ := by rw [hxN]; positivity
  change ‖A (x N)‖ ≤ C*‖x N‖⁻¹
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ ob).mpr
  simpa only [pow_one,mul_comm] using SchwartzMap.norm_pow_mul_le_seminorm ℝ A 1 (x N)

def reproducingPartialSymbol (ψ θ : SchwartzMap Space ℂ) (t : ℝ) (N : ℕ) (ξ : Space) : ℂ :=
  ∑ j ∈ Finset.range (N+N), compactWaveletFrequency ψ (reproducingScale t N j • ξ) *
    compactWaveletFrequency θ (reproducingScale t N j • ξ)

private theorem reproducingPartialSymbol_eq (φ ψ θ : SchwartzMap Space ℂ)
    (hF : WaveletFactorization φ ψ θ) (t : ℝ) (N : ℕ) (ξ : Space) :
    reproducingPartialSymbol ψ θ t N ξ =
      waveletCubic (compactWaveletFrequency φ ((t/(2:ℝ)^N) • ξ)) -
        waveletCubic (compactWaveletFrequency φ ((t*(2:ℝ)^N) • ξ)) := by
  unfold reproducingPartialSymbol reproducingScale
  rw [reproducing_windows_telescoping φ ψ θ hF]
  have hEq : compactWaveletScale (t*(2:ℝ)^N) (N+N) = t/(2:ℝ)^N := by
    unfold compactWaveletScale
    rw [pow_add]
    field_simp [pow_ne_zero N (by norm_num : (2:ℝ) ≠ 0)]
  rw [hEq]

/-- Both dyadic tails disappear at each nonzero frequency. -/
theorem reproducing_windows_symbol_tendsto (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : (∫ x, φ x)=1) (hF : WaveletFactorization φ ψ θ) (t : ℝ) (ht : 0<t)
    (ξ : Space) (hξ : ξ≠0) :
    Tendsto (fun N => reproducingPartialSymbol ψ θ t N ξ) atTop (𝓝 1) := by
  have h0 : compactWaveletFrequency φ 0 = 1 := by
    change Real.fourierIntegral (φ : Space → ℂ) 0 = 1
    simpa [Real.fourierIntegral_eq] using hφ
  have hC : Continuous waveletCubic := by unfold waveletCubic; fun_prop
  have lo := frequency_small_scale φ t ξ
  rw [h0] at lo
  have hi := frequency_large_scale φ t ht ξ hξ
  have h := ((hC.continuousAt (x := (1:ℂ))).tendsto.comp lo).sub
    ((hC.continuousAt (x := (0:ℂ))).tendsto.comp hi)
  have limiting : waveletCubic 1-waveletCubic 0 = 1 := by norm_num [waveletCubic]
  rw [limiting] at h
  exact h.congr (fun N => (reproducingPartialSymbol_eq φ ψ θ hF t N ξ).symm)

/-- The pointwise reconstruction sums are uniformly bounded independently
of both cutoffs and the initial dilation. -/
theorem exists_reproducingPartialSymbol_norm_le (φ ψ θ : SchwartzMap Space ℂ)
    (hF : WaveletFactorization φ ψ θ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (t : ℝ) (N : ℕ) (ξ : Space), ‖reproducingPartialSymbol ψ θ t N ξ‖ ≤ C := by
  let A := compactWaveletFrequency φ
  let M := SchwartzMap.seminorm ℝ 0 0 A
  let K := 3*M^2+2*M^3
  have hM : 0≤M := apply_nonneg _ _
  have hK : 0≤K := by dsimp only [K]; positivity
  have hCube (z : Space) : ‖waveletCubic (A z)‖ ≤ K := by
    have hA : ‖A z‖≤M := SchwartzMap.norm_le_seminorm ℝ A z
    unfold waveletCubic
    refine (norm_sub_le _ _).trans ?_
    simp only [norm_mul,norm_pow,show ‖(3:ℂ)‖=3 by norm_num,show ‖(2:ℂ)‖=2 by norm_num]
    exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hA _) (by norm_num))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hA _) (by norm_num))
  refine ⟨K+K,add_nonneg hK hK,fun t N ξ => ?_⟩
  rw [reproducingPartialSymbol_eq φ ψ θ hF]
  exact (norm_sub_le _ _).trans (add_le_add (hCube _) (hCube _))

end Burnett.Analysis.CarlesonEmbedding
