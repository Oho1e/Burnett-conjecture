import Burnett.Analysis.PrincipalEnergy.Paraproduct.ActualParaproductResolution

set_option autoImplicit false
set_option maxHeartbeats 2300000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier
open scoped BigOperators Topology

theorem summable_bilateral_wavelet_norm_sq (ψ : SchwartzMap Space ℂ)
    (hψ : (∫ z, ψ z)=0) (t : ℝ) (ht : 0<t) (u : ComplexL2 Space) :
    Summable (fun j : ℤ => ‖fourierMultiplier (waveletSymbol ψ (bilateralWaveletScale t j)) u‖^2) := by
  obtain ⟨D,hD,hS⟩ := exists_waveletMultiplier_square_bound ψ hψ
  refine summable_of_sum_le (c := D*‖u‖^2) (fun _ => sq_nonneg _) fun J => ?_
  exact bilateral_wavelet_square_sum_le (fun s => ‖fourierMultiplier (waveletSymbol ψ s) u‖^2)
    (D*‖u‖^2) t (mul_nonneg hD (sq_nonneg _)) ht (fun q hq I => hS q hq I u) J

theorem exists_bilateral_waveletSynthesis_tsum_bound (θ : SchwartzMap Space ℂ)
    (hθ : (∫ z, θ z)=0) :
    ∃ D : ℝ, 0≤D ∧ ∀ (t : ℝ), 0<t → ∀ (u : ℤ → ComplexL2 Space),
      Summable (fun j => ‖u j‖^2) →
      let v (j : ℤ) := fourierMultiplier (waveletSymbol θ (bilateralWaveletScale t j)) (u j)
      Summable v ∧ ‖∑' j, v j‖ ≤ D*Real.sqrt (∑' j, ‖u j‖^2) := by
  obtain ⟨D,hD,hS⟩ := exists_bilateral_waveletSynthesis_bound θ hθ
  refine ⟨D,hD,?_⟩
  intro t ht u hU v
  have hFin (J : Finset ℤ) : ‖∑ j ∈ J, v j‖ ≤ D*Real.sqrt (∑ j ∈ J, ‖u j‖^2) :=
    hS t ht J u
  have hSum : Summable v := summable_of_finite_synthesis_bound hD hU hFin
  refine ⟨hSum,le_of_tendsto' hSum.hasSum.norm fun J => ?_⟩
  exact (hFin J).trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (hU.sum_le_tsum J (fun j _ => sq_nonneg ‖u j‖))) hD)

/-- The wavelet reconstruction is an unconditional bilateral $L^2$ identity. -/
theorem hasSum_bilateral_reproducing_wavelets (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : (∫ z, φ z)=1) (hψ : (∫ z, ψ z)=0) (hθ : (∫ z, θ z)=0)
    (hFactor : WaveletFactorization φ ψ θ) (t : ℝ) (ht : 0<t) (u : ComplexL2 Space) :
    HasSum (fun j : ℤ => fourierMultiplier (waveletSymbol θ (bilateralWaveletScale t j))
      (fourierMultiplier (waveletSymbol ψ (bilateralWaveletScale t j)) u)) u := by
  let v (j : ℤ) := fourierMultiplier (waveletSymbol θ (bilateralWaveletScale t j))
    (fourierMultiplier (waveletSymbol ψ (bilateralWaveletScale t j)) u)
  obtain ⟨_,_,hS⟩ := exists_bilateral_waveletSynthesis_tsum_bound θ hθ
  have hV : Summable v := (hS t ht _ (summable_bilateral_wavelet_norm_sq ψ hψ t ht u)).1
  have hCut (N : ℕ) : (∑ j ∈ Finset.Ico (-(N:ℤ)) (N:ℤ), v j) =
      reproducingPartialAction ψ θ t N u := by
    have hI : Finset.Ico (-(N:ℤ)) (N:ℤ) =
        (Finset.range (N+N)).image (fun j : ℕ => (j:ℤ)-(N:ℤ)) := by
      ext j
      simp only [Finset.mem_Ico,Finset.mem_image,Finset.mem_range]
      constructor
      · intro h
        refine ⟨(j+(N:ℤ)).toNat,?_,?_⟩ <;> omega
      · rintro ⟨m,hm,rfl⟩
        omega
    rw [hI,Finset.sum_image (fun j _ k _ h => by omega)]
    unfold reproducingPartialAction
    refine Finset.sum_congr rfl fun j _ => ?_
    have hScale : bilateralWaveletScale t ((j:ℤ)-(N:ℤ)) = reproducingScale t N j := by
      rw [bilateralWaveletScale,reproducingScale,compactWaveletScale,zpow_sub₀ (by norm_num),
        zpow_natCast,zpow_natCast,div_div_eq_mul_div]
    simp only [v,hScale]
  have hLimit := (hV.hasSum.comp tendsto_two_ended_integer_intervals).congr hCut
  have hEq := tendsto_nhds_unique hLimit (reproducing_windows_L2_tendsto φ ψ θ hφ hFactor t ht u)
  change HasSum v u
  rw [← hEq]
  exact hV.hasSum

end Burnett.Analysis.CarlesonEmbedding
