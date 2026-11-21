import Burnett.Analysis.PrincipalEnergy.Commutator.ReproductionLimit

set_option autoImplicit false
set_option maxHeartbeats 2100000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier
open scoped Topology BigOperators

def reproducingPartialAction (ψ θ : SchwartzMap Space ℂ) (t : ℝ) (N : ℕ)
    (u : ComplexL2 Space) : ComplexL2 Space :=
  ∑ j ∈ Finset.range (N+N),
    fourierMultiplier (waveletSymbol θ (reproducingScale t N j))
      (fourierMultiplier (waveletSymbol ψ (reproducingScale t N j)) u)

private theorem fourier_pair_action_ae (ψ θ : SchwartzMap Space ℂ) (s : ℝ) (u : ComplexL2 Space) :
    (fourierL2Equiv (fourierMultiplier (waveletSymbol θ s) (fourierMultiplier (waveletSymbol ψ s) u)) :
      Space → ℂ) =ᵐ[volume] fun ξ => compactWaveletFrequency ψ (s • ξ)*
        compactWaveletFrequency θ (s • ξ)*fourierL2Equiv u ξ := by
  rw [fourier_fourierMultiplier,fourier_fourierMultiplier]
  let v := fourierL2Equiv u
  filter_upwards [symbolL2_ae (waveletSymbol θ s) (symbolL2 (waveletSymbol ψ s) v),
    symbolL2_ae (waveletSymbol ψ s) v] with ξ hx hy
  change symbolL2 (waveletSymbol θ s) (symbolL2 (waveletSymbol ψ s) v) ξ = _ at hx
  change _ = compactWaveletFrequency ψ (s • ξ)*compactWaveletFrequency θ (s • ξ)*v ξ
  rw [hx]
  change compactWaveletFrequency θ (s • ξ) * symbolL2 (waveletSymbol ψ s) v ξ = _
  rw [hy]
  change compactWaveletFrequency θ (s • ξ)*(compactWaveletFrequency ψ (s • ξ)*v ξ) = _
  ring

private theorem lp_finset_sum_ae {ι : Type*} (J : Finset ι) (F : ι → ComplexL2 Space) :
    ((∑ j ∈ J, F j : ComplexL2 Space) : Space → ℂ) =ᵐ[volume] fun ξ => ∑ j ∈ J, F j ξ := by
  classical
  induction J using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero ℂ 2 volume
  | insert j J hj ih =>
      simp only [Finset.sum_insert hj]
      filter_upwards [Lp.coeFn_add (F j) (∑ i ∈ J, F i),ih] with x hx hy
      change _ = F j x + (∑ i ∈ J, F i x)
      rw [hx,Pi.add_apply,hy]

private theorem fourier_reproducingPartialAction_ae
    (ψ θ : SchwartzMap Space ℂ) (t : ℝ) (N : ℕ) (u : ComplexL2 Space) :
    (fourierL2Equiv (reproducingPartialAction ψ θ t N u) : Space → ℂ) =ᵐ[volume]
      fun ξ => reproducingPartialSymbol ψ θ t N ξ * fourierL2Equiv u ξ := by
  let s := reproducingScale t N
  let F (j : ℕ) := fourierL2Equiv (fourierMultiplier (waveletSymbol θ (s j))
    (fourierMultiplier (waveletSymbol ψ (s j)) u))
  have hAll : ∀ᵐ (ξ : Space) ∂(volume : Measure Space), ∀ j : ℕ,
      F j ξ = compactWaveletFrequency ψ (s j • ξ)*compactWaveletFrequency θ (s j • ξ)*
        fourierL2Equiv u ξ := ae_all_iff.mpr (fun j => fourier_pair_action_ae ψ θ (s j) u)
  unfold reproducingPartialAction
  rw [map_sum]
  change ((∑ j ∈ Finset.range (N+N), F j : ComplexL2 Space) : Space → ℂ) =ᵐ[volume] _
  filter_upwards [lp_finset_sum_ae (Finset.range (N+N)) F,hAll] with ξ hξ hP
  rw [hξ,reproducingPartialSymbol,Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j _ => hP j)

/-- The actual compositions of bounded wavelet multipliers reconstruct every
physical L² input strongly as the two cuts move to the ends of the scale axis. -/
theorem reproducing_windows_L2_tendsto (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : (∫ x, φ x)=1) (hF : WaveletFactorization φ ψ θ) (t : ℝ) (ht : 0<t)
    (u : ComplexL2 Space) :
    Tendsto (fun N => reproducingPartialAction ψ θ t N u) atTop (𝓝 u) := by
  let v := fourierL2Equiv u
  let R (N : ℕ) := reproducingPartialAction ψ θ t N u
  let m (N : ℕ) := reproducingPartialSymbol ψ θ t N
  let E (N : ℕ) (ξ : Space) := ‖m N ξ-1‖^2*‖v ξ‖^2
  obtain ⟨C,hC,hCbound⟩ := exists_reproducingPartialSymbol_norm_le φ ψ θ hF
  have hFourier (N : ℕ) : (fourierL2Equiv (R N-u) : Space → ℂ) =ᵐ[volume]
      fun ξ => (m N ξ-1)*v ξ := by
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (fourierL2Equiv (R N)) v,
      fourier_reproducingPartialAction_ae ψ θ t N u] with ξ h₁ h₂
    rw [h₁,Pi.sub_apply,h₂]
    change m N ξ*v ξ-v ξ = _
    ring
  have hNorm (N : ℕ) : ‖R N-u‖^2 = ∫ ξ, E N ξ := by
    rw [← LinearIsometryEquiv.norm_map (fourierL2Equiv (V := Space)) (R N-u),l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [hFourier N] with ξ hξ
    rw [hξ]
    rw [norm_mul,mul_pow]
  have hM (N : ℕ) : Continuous (m N) := by
    unfold m reproducingPartialSymbol
    apply continuous_finset_sum
    intro j _
    exact ((compactWaveletFrequency ψ).continuous.comp (continuous_const.smul continuous_id)).mul
      ((compactWaveletFrequency θ).continuous.comp (continuous_const.smul continuous_id))
  have hMeas (N : ℕ) : AEStronglyMeasurable (E N) (volume : Measure Space) :=
    (((hM N).sub continuous_const).norm.pow 2).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable v).norm.pow 2)
  have hIntegrable : Integrable (fun ξ => ((C+1)^2)*‖v ξ‖^2) (volume : Measure Space) :=
    ((Lp.memLp v).integrable_norm_pow (p := 2) (by decide)).const_mul _
  have hMajor (N : ℕ) (ξ : Space) : ‖E N ξ‖ ≤ ((C+1)^2)*‖v ξ‖^2 := by
    have h1 : ‖m N ξ-1‖ ≤ C+1 := by
      have h := norm_sub_le (m N ξ) (1:ℂ)
      rw [norm_one] at h
      exact h.trans (add_le_add_right (hCbound t N ξ) 1)
    have hE : 0≤E N ξ := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [Real.norm_of_nonneg hE]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h1 2) (sq_nonneg _)
  have hLim : ∀ᵐ (ξ : Space) ∂(volume : Measure Space), Tendsto (fun N => E N ξ) atTop (𝓝 0) := by
    filter_upwards [Set.countable_singleton (0:Space) |>.ae_notMem (volume : Measure Space)] with ξ hξ
    have hf := reproducing_windows_symbol_tendsto φ ψ θ hφ hF t ht ξ hξ
    have h := (((hf.sub_const (1:ℂ)).norm.pow 2).mul_const (‖v ξ‖^2))
    simpa only [E,m,sub_self,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul] using h
  have hIntegral := tendsto_integral_of_dominated_convergence
    (f := fun _ : Space => (0:ℝ)) (fun ξ => (C+1)^2*‖v ξ‖^2) hMeas hIntegrable
    (fun N => Eventually.of_forall (hMajor N)) hLim
  rw [integral_zero] at hIntegral
  have hSq : Tendsto (fun N => ‖R N-u‖^2) atTop (𝓝 0) := hIntegral.congr (fun N => (hNorm N).symm)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using hSq.sqrt

/-- Existence of an actual pair of compactly supported, mean-zero wavelets
implementing a reproducing identity on the whole complex L² space. -/
theorem exists_compact_wavelet_resolution :
    ∃ φ ψ θ : SchwartzMap Space ℂ,
      (∫ x, φ x) = 1 ∧ (∀ x, 1/2<‖x‖ → φ x = 0) ∧
      (∫ x, ψ x) = 0 ∧ (∀ x, 1<‖x‖ → ψ x = 0) ∧
      (∫ x, θ x) = 0 ∧ (∀ x, 1<‖x‖ → θ x = 0) ∧
      ∀ (t : ℝ), 0<t → ∀ (u : ComplexL2 Space),
        Tendsto (fun N => reproducingPartialAction ψ θ t N u) atTop (𝓝 u) := by
  obtain ⟨φ,ψ,θ,hφ,hφs,hψ,hψs,hθ,hθs,hFact⟩ := exists_compact_reproducing_windows
  exact ⟨φ,ψ,θ,hφ,hφs,hψ,hψs,hθ,hθs,fun t ht u => reproducing_windows_L2_tendsto φ ψ θ hφ hFact t ht u⟩

end Burnett.Analysis.CarlesonEmbedding
