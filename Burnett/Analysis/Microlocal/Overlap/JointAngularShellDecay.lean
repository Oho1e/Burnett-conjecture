import Burnett.Analysis.Microlocal.Overlap.JointAngularAnnularFamily
import Burnett.Analysis.Microlocal.Overlap.DyadicKernelRemainder

/-! Compact sets of positions control the actual annular kernels with uniform constants. -/
set_option autoImplicit false
set_option maxRecDepth 4400
set_option maxHeartbeats 3200000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Set Burnett.Fourier
open Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff BoundedContinuousFunction

open private fderiv_norm_le_iterated from Burnett.Analysis.Microlocal.Overlap.DyadicKernelRemainder

private theorem uniform_schwartzFamily_decay
    (p : E → SchwartzMap E ℂ) (hp : Continuous p) (S : Set E) (hS : IsCompact S) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ z : E,
      (1 + ‖z‖)^7 * ‖iteratedFDeriv ℝ n (p x : E → ℂ) z‖ ≤ C := by
  let J (x : E) : ℝ := max (SchwartzMap.seminorm ℝ 0 n (p x)) (SchwartzMap.seminorm ℝ 7 n (p x))
  have hJ : Continuous J := by
    exact (((schwartz_withSeminorms ℝ E ℂ).continuous_seminorm (0, n)).comp hp).max
      (((schwartz_withSeminorms ℝ E ℂ).continuous_seminorm (7, n)).comp hp)
  obtain ⟨B, hB⟩ := (hS.image hJ).isBounded.exists_norm_le
  let D := max 0 B
  have hD : 0 ≤ D := le_max_left _ _
  refine ⟨(2 : ℝ)^7 * D, by positivity, fun x hx z => ?_⟩
  have hJx : J x ≤ D :=
    (le_abs_self _).trans ((hB _ (mem_image_of_mem J hx)).trans (le_max_right _ _))
  have h₀ : ‖iteratedFDeriv ℝ n (p x : E → ℂ) z‖ ≤ D :=
    (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ (p x) n z).trans
      ((le_max_left _ _).trans hJx)
  have h₇ : ‖z‖^7 * ‖iteratedFDeriv ℝ n (p x : E → ℂ) z‖ ≤ D :=
    (SchwartzMap.le_seminorm ℝ 7 n (p x) z).trans ((le_max_right _ _).trans hJx)
  by_cases hz : ‖z‖ ≤ 1
  · exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) 7)
      h₀ (norm_nonneg _) (by positivity)
  · have hTwo : 1 + ‖z‖ ≤ 2 * ‖z‖ := by linarith [lt_of_not_ge hz]
    calc
      _ ≤ (2 * ‖z‖)^7 * ‖iteratedFDeriv ℝ n (p x : E → ℂ) z‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hTwo _) (norm_nonneg _)
      _ = (2 : ℝ)^7 * (‖z‖^7 * ‖iteratedFDeriv ℝ n (p x : E → ℂ) z‖) := by rw [mul_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left h₇ (by positivity)

theorem continuous_shellKernel_family (a : E → BoundedSymbol E)
    (ha : ContDiffOn ℝ ∞ (fun z : E × E => a z.1 z.2) (univ ×ˢ ({0}ᶜ : Set E)))
    (haSlice : ∀ x, ContDiffOn ℝ ∞ (a x : E → ℂ) ({0}ᶜ : Set E))
    (j : ℕ) :
    Continuous (fun z : E × E => shellKernel (a z.1) (haSlice z.1) j z.2) := by
  let p (x : E) := inverseAnnularSchwartz (a x) (haSlice x)
  have hp := continuous_inverseAnnularSchwartz_family a ha haSlice
  let Q := SchwartzMap.toBoundedContinuousFunctionCLM ℂ E ℂ
  have hEval : Continuous (fun z : E × E => (Q (p z.1)) (dyadicScale j • z.2)) :=
    BoundedContinuousFunction.continuous_eval.comp
      ((Q.continuous.comp (hp.comp continuous_fst)).prodMk (continuous_const.smul continuous_snd))
  exact continuous_const.smul hEval

theorem shellKernel_decay_bounds_uniform_on_compact (a : E → BoundedSymbol E)
    (ha : ContDiffOn ℝ ∞ (fun z : E × E => a z.1 z.2) (univ ×ˢ ({0}ᶜ : Set E)))
    (haSlice : ∀ x, ContDiffOn ℝ ∞ (a x : E → ℂ) ({0}ᶜ : Set E))
    (S : Set E) (hS : IsCompact S) :
    ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ x ∈ S, ∀ (j : ℕ) (z : E),
      let s := dyadicScale j
      let k := shellKernel (a x) (haSlice x) j
      (1 + s * ‖z‖)^7 * ‖k z‖ ≤ C₀ * s^4 ∧
      (1 + s * ‖z‖)^7 * ‖fderiv ℝ k z‖ ≤ C₁ * s^5 := by
  let p (x : E) := inverseAnnularSchwartz (a x) (haSlice x)
  have hp := continuous_inverseAnnularSchwartz_family a ha haSlice
  obtain ⟨C₀, hC₀, h₀⟩ := uniform_schwartzFamily_decay p hp S hS 0
  obtain ⟨C₁, hC₁, h₁⟩ := uniform_schwartzFamily_decay p hp S hS 1
  refine ⟨C₀, C₁, hC₀, hC₁, fun x hx j z => ?_⟩
  let s := dyadicScale j
  have hs : 0 ≤ s := by unfold s dyadicScale; positivity
  have hnorm : ‖s • z‖ = s * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg hs]
  have h₀' : (1 + s * ‖z‖)^7 * ‖p x (s • z)‖ ≤ C₀ := by
    simpa only [hnorm, norm_iteratedFDeriv_zero] using h₀ x hx (s • z)
  have h₁' : (1 + s * ‖z‖)^7 * ‖fderiv ℝ (p x : E → ℂ) (s • z)‖ ≤ C₁ :=
    (mul_le_mul_of_nonneg_left (fderiv_norm_le_iterated _ _) (by positivity)).trans
      (by simpa only [hnorm] using h₁ x hx (s • z))
  change (1 + s * ‖z‖)^7 * ‖s^4 • p x (s • z)‖ ≤ C₀ * s^4 ∧ _
  constructor
  · rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hs 4), mul_left_comm, mul_comm C₀]
    exact mul_le_mul_of_nonneg_left h₀' (pow_nonneg hs 4)
  · rw [(shellKernel_hasFDerivAt (a x) (haSlice x) j z).fderiv, norm_smul,
      Real.norm_of_nonneg (pow_nonneg hs 5)]
    change (1 + s * ‖z‖)^7 * (s^5 * ‖fderiv ℝ (p x : E → ℂ) (s • z)‖) ≤ C₁ * s^5
    rw [mul_left_comm, mul_comm C₁]
    exact mul_le_mul_of_nonneg_left h₁' (pow_nonneg hs 5)

end Burnett.Microlocal.AtlasOverlapKernel
