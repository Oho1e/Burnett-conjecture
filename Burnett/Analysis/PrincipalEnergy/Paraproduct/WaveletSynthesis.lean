import Burnett.Analysis.PrincipalEnergy.Commutator.WaveletOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option maxHeartbeats 2600000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier
open scoped BigOperators ComplexConjugate

private def conjugateSymbol (m : BoundedSymbol Space) : BoundedSymbol Space where
  toFun := fun ξ => conj (m ξ)
  measurable := m.measurable.star
  bound := m.bound
  bound_nonneg := m.bound_nonneg
  norm_le ξ := by rw [Complex.norm_conj]; exact m.norm_le ξ

private theorem fourierMultiplier_adjoint (m : BoundedSymbol Space) :
    (fourierMultiplier m).adjoint = fourierMultiplier (conjugateSymbol m) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [← fourierL2Equiv.inner_map_map (fourierMultiplier m v) u,
    ← fourierL2Equiv.inner_map_map v (fourierMultiplier (conjugateSymbol m) u)]
  simp only [fourier_fourierMultiplier,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [symbolL2_ae m (fourierL2Equiv v),symbolL2_ae (conjugateSymbol m) (fourierL2Equiv u)]
    with ξ hx hy
  simp only [RCLike.inner_apply',hx,hy,map_mul]
  change conj (m ξ)*conj (fourierL2Equiv v ξ)*fourierL2Equiv u ξ =
    conj (fourierL2Equiv v ξ)*(conj (m ξ)*fourierL2Equiv u ξ)
  ring

private theorem norm_adjoint_fourierMultiplier_apply (m : BoundedSymbol Space) (u : ComplexL2 Space) :
    ‖(fourierMultiplier m).adjoint u‖ = ‖fourierMultiplier m u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [fourierMultiplier_adjoint]
  simp only [fourierMultiplier_apply,LinearIsometryEquiv.norm_map]
  rw [l2_norm_sq_integral,l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [symbolL2_ae (conjugateSymbol m) (fourierL2Equiv u),symbolL2_ae m (fourierL2Equiv u)]
    with ξ h₁ h₂
  rw [h₁,h₂]
  change ‖conj (m ξ)*fourierL2Equiv u ξ‖^2 = ‖m ξ*fourierL2Equiv u ξ‖^2
  rw [norm_mul,norm_mul,Complex.norm_conj]

/-- Synthesis by the actual wavelet Fourier multipliers is uniformly
bounded from a finite square sum of inputs to the physical L² space. -/
theorem exists_finite_waveletSynthesis_bound (θ : SchwartzMap Space ℂ) (hMean : (∫ z, θ z)=0) :
    ∃ C : ℝ, 0≤C ∧ ∀ (t : ℝ), 0<t → ∀ (J : Finset ℕ) (u : ℕ → ComplexL2 Space),
      ‖∑ j ∈ J, fourierMultiplier (waveletSymbol θ (compactWaveletScale t j)) (u j)‖ ≤
        C * Real.sqrt (∑ j ∈ J, ‖u j‖^2) := by
  obtain ⟨D,hD,hAnalysis⟩ := exists_waveletMultiplier_square_bound θ hMean
  refine ⟨Real.sqrt D,Real.sqrt_nonneg _,?_⟩
  intro t ht J u
  let Q (j : ℕ) := fourierMultiplier (waveletSymbol θ (compactWaveletScale t j))
  let S := ∑ j ∈ J, Q j (u j)
  let U := ∑ j ∈ J, ‖u j‖^2
  have hU : 0≤U := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hAdj (v : ComplexL2 Space) : (∑ j ∈ J, ‖(Q j).adjoint v‖^2) ≤ D*‖v‖^2 := by
    simp_rw [show ∀ j, ‖(Q j).adjoint v‖ = ‖Q j v‖ from fun j => norm_adjoint_fourierMultiplier_apply _ v]
    exact hAnalysis t ht J v
  have hPair (v : ComplexL2 Space) : ‖inner ℂ v S‖ ≤ Real.sqrt D * Real.sqrt U * ‖v‖ := by
    have hTerm : ‖inner ℂ v S‖ ≤ ∑ j ∈ J, ‖(Q j).adjoint v‖*‖u j‖ := by
      unfold S
      rw [inner_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [← ContinuousLinearMap.adjoint_inner_left]
      exact norm_inner_le_norm _ _
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    calc
      _ ≤ (∑ j ∈ J, ‖(Q j).adjoint v‖*‖u j‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hTerm 2
      _ ≤ (∑ j ∈ J, ‖(Q j).adjoint v‖^2)*U := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (D*‖v‖^2)*U := mul_le_mul_of_nonneg_right (hAdj v) hU
      _ = _ := by rw [mul_pow,mul_pow,Real.sq_sqrt hD,Real.sq_sqrt hU]; ring
  have h := hPair S
  rw [← inner_self_re_eq_norm (𝕜 := ℂ) S,← norm_sq_eq_re_inner (𝕜 := ℂ) S,pow_two] at h
  change ‖S‖ ≤ Real.sqrt D * Real.sqrt U
  by_cases hZero : ‖S‖=0
  · rw [hZero]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · have hS : 0 < ‖S‖ := lt_of_le_of_ne (norm_nonneg S) (fun he => hZero he.symm)
    exact le_of_mul_le_mul_right h hS

end Burnett.Analysis.CarlesonEmbedding
