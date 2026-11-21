import Burnett.Analysis.PrincipalEnergy.Paraproduct.WaveletSynthesis
import Burnett.Analysis.PrincipalEnergy.Commutator.ParaproductAllScales
import Mathlib.Analysis.Normed.Group.InfiniteSum

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier
open scoped BigOperators Topology

theorem bilateral_wavelet_reindex (t : ℝ) {j k : ℤ} (h : k ≤ j) :
    bilateralWaveletScale t j = compactWaveletScale (bilateralWaveletScale t k) (j-k).toNat := by
  rw [compactWaveletScale,bilateralWaveletScale,bilateralWaveletScale,div_div,← zpow_natCast,
    Int.toNat_of_nonneg (sub_nonneg.mpr h),← zpow_add₀ (by norm_num),show k+(j-k)=j by omega]

private theorem reindex_wavelet_finite {A : Type*} [AddCommMonoid A]
    (F : ℝ → ℤ → A) (t : ℝ) (J : Finset ℤ) (hJ : J.Nonempty) :
    (∑ j ∈ J, F (bilateralWaveletScale t j) j) =
      ∑ n ∈ J.image (fun j => (j-J.min' hJ).toNat),
        F (compactWaveletScale (bilateralWaveletScale t (J.min' hJ)) n) (J.min' hJ+(n:ℤ)) := by
  let k := J.min' hJ
  let N (j : ℤ) := (j-k).toNat
  have hMin (j : ℤ) (hj : j∈J) : k≤j := J.min'_le j hj
  have hLeft (j : ℤ) (hj : j∈J) : k+(N j : ℤ)=j := by
    change k+((j-k).toNat : ℤ)=j
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr (hMin j hj))]
    omega
  have hInj : Set.InjOn N (J : Set ℤ) := by
    intro i hi j hj h
    rw [← hLeft i hi,← hLeft j hj,h]
  rw [Finset.sum_image hInj]
  refine Finset.sum_congr rfl fun j hj => ?_
  change F (bilateralWaveletScale t j) j =
    F (compactWaveletScale (bilateralWaveletScale t k) (N j)) (k+(N j : ℤ))
  rw [bilateral_wavelet_reindex t (hMin j hj),hLeft j hj]

/-- A finite square-sum estimate on natural scales valid at every base
scale also holds for arbitrary finite sets of signed scales. -/
theorem bilateral_wavelet_square_sum_le (F : ℝ → ℝ) (C t : ℝ) (hC : 0≤C) (ht : 0<t)
    (hFin : ∀ q : ℝ, 0<q → ∀ J : Finset ℕ, (∑ j ∈ J, F (compactWaveletScale q j)) ≤ C)
    (J : Finset ℤ) : (∑ j ∈ J, F (bilateralWaveletScale t j)) ≤ C := by
  by_cases hJ : J.Nonempty
  · rw [reindex_wavelet_finite (fun s _ => F s) t J hJ]
    exact hFin _ (div_pos ht (zpow_pos (by norm_num) _)) _
  · rw [Finset.not_nonempty_iff_eq_empty.mp hJ,Finset.sum_empty]
    exact hC

theorem exists_bilateral_waveletSynthesis_bound (θ : SchwartzMap Space ℂ)
    (hθ : (∫ z, θ z)=0) :
    ∃ C : ℝ, 0≤C ∧ ∀ (t : ℝ), 0<t → ∀ (J : Finset ℤ) (u : ℤ → ComplexL2 Space),
      ‖∑ j ∈ J, fourierMultiplier (waveletSymbol θ (bilateralWaveletScale t j)) (u j)‖ ≤
        C * Real.sqrt (∑ j ∈ J, ‖u j‖^2) := by
  obtain ⟨C,hC,hS⟩ := exists_finite_waveletSynthesis_bound θ hθ
  refine ⟨C,hC,?_⟩
  intro t ht J u
  by_cases hJ : J.Nonempty
  · rw [reindex_wavelet_finite (fun s j => fourierMultiplier (waveletSymbol θ s) (u j)) t J hJ]
    have hSum := reindex_wavelet_finite (fun _ j => ‖u j‖^2) t J hJ
    rw [hSum]
    exact hS _ (div_pos ht (zpow_pos (by norm_num) _)) _ (fun j => u (J.min' hJ+(j:ℤ)))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hJ,Finset.sum_empty,Finset.sum_empty,
      norm_zero,Real.sqrt_zero,mul_zero]

/-- A finite synthesis estimate controlled by summable nonnegative
square weights gives an unconditional sum in a complete normed group. -/
theorem summable_of_finite_synthesis_bound {ι E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {v : ι → E} {W : ι → ℝ} {D : ℝ} (hD : 0≤D) (hW : Summable W)
    (hFin : ∀ J : Finset ι, ‖∑ j ∈ J, v j‖ ≤ D*Real.sqrt (∑ j ∈ J, W j)) :
    Summable v := by
  refine summable_iff_vanishing_norm.mpr fun ε hε => ?_
  have hD₁ : 0<D+1 := by linarith
  have hδ : 0<ε/(D+1) := div_pos hε hD₁
  obtain ⟨I,hI⟩ := summable_iff_vanishing_norm.mp hW ((ε/(D+1))^2) (pow_pos hδ 2)
  refine ⟨I,fun J hJ => ?_⟩
  have hS : Real.sqrt (∑ j ∈ J, W j) < ε/(D+1) :=
    (Real.sqrt_lt' hδ).mpr ((le_abs_self _).trans_lt (hI J hJ))
  calc
    _ ≤ D*Real.sqrt (∑ j ∈ J, W j) := hFin J
    _ ≤ (D+1)*Real.sqrt (∑ j ∈ J, W j) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Real.sqrt_nonneg _)
    _ < (D+1)*(ε/(D+1)) := mul_lt_mul_of_pos_left hS hD₁
    _ = ε := by field_simp [hD₁.ne']

theorem tendsto_two_ended_integer_intervals :
    Tendsto (fun N : ℕ => Finset.Ico (-(N:ℤ)) (N:ℤ)) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone
  · intro a b hab j hj
    have hCast : (a:ℤ) ≤ (b:ℤ) := by exact_mod_cast hab
    simp only [Finset.mem_Ico] at hj ⊢
    omega
  · intro j
    refine ⟨j.natAbs+1,?_⟩
    simp only [Finset.mem_Ico,Int.natCast_add,Int.cast_ofNat_Int]
    omega

end Burnett.Analysis.CarlesonEmbedding
