import Burnett.Analysis.PrincipalEnergy.Commutator.ReproductionL2
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option maxHeartbeats 2100000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier
open scoped ComplexConjugate Topology

-- Reuse the exact frozen windows. The extra properties can live next to the
-- original construction when it moves from the isolated replay into the project.
open private normalizedHalfBump normalizedHalfBump_integral normalizedHalfBump_outside
  wavelet_frequency_zero smallerBump smallerBump_fourier smallerBump_apply smallerBump_outside
  convolutionSchwartz convolutionSchwartz_fourier convolutionSchwartz_apply convolutionSchwartz_outside
  from Burnett.Analysis.PrincipalEnergy.Commutator.ReproducingWindows

private theorem normalizedHalfBump_conj (x : Space) :
    conj (normalizedHalfBump x) = normalizedHalfBump x := by
  let χ : ContDiffBump (0 : Space) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  exact Complex.conj_ofReal (χ.normed volume x)

private theorem smallerBump_conj {f : SchwartzMap Space ℂ}
    (hf : ∀ x, conj (f x) = f x) (x : Space) :
    conj (smallerBump f x) = smallerBump f x := by
  rw [smallerBump_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, hf]

private theorem convolutionSchwartz_conj {f g : SchwartzMap Space ℂ}
    (hf : ∀ x, conj (f x) = f x) (hg : ∀ x, conj (g x) = g x) (x : Space) :
    conj (convolutionSchwartz f g x) = convolutionSchwartz f g x := by
  rw [convolutionSchwartz_apply, ← integral_conj]
  simp only [map_mul, hf, hg]

/-- The same normalized lowpass window gives two real mean-zero Schwartz
wavelets, both supported in the closed unit ball. The half-scale uses the
physical four-dimensional dilation. -/
theorem exists_real_compact_wavelet_factorization :
    ∃ φ φHalf ψ θ : SchwartzMap Space ℂ,
      (∫ x, φ x) = 1 ∧
      (∀ x, 1 / 2 < ‖x‖ → φ x = 0) ∧
      (∀ x, φHalf x = compactWaveletKernel φ (1 / 2) x) ∧
      (∀ x, conj (φ x) = φ x ∧ conj (φHalf x) = φHalf x ∧
        conj (ψ x) = ψ x ∧ conj (θ x) = θ x) ∧
      (∫ x, ψ x) = 0 ∧ (∀ x, 1 < ‖x‖ → ψ x = 0) ∧
      (∫ x, θ x) = 0 ∧ (∀ x, 1 < ‖x‖ → θ x = 0) ∧
      WaveletFactorization φ ψ θ := by
  let φ := normalizedHalfBump
  let φHalf := smallerBump φ
  let u := convolutionSchwartz φHalf φHalf
  let v := convolutionSchwartz φHalf φ
  let w := convolutionSchwartz φ φ
  let ψ := φHalf - φ
  let θ := (3 : ℂ) • (φHalf + φ) - (2 : ℂ) • (u + v + w)
  have hφ (x : Space) : conj (φ x) = φ x := normalizedHalfBump_conj x
  have hh (x : Space) : conj (φHalf x) = φHalf x := smallerBump_conj hφ x
  have hu (x : Space) : conj (u x) = u x := convolutionSchwartz_conj hh hh x
  have hv (x : Space) : conj (v x) = v x := convolutionSchwartz_conj hh hφ x
  have hw (x : Space) : conj (w x) = w x := convolutionSchwartz_conj hφ hφ x
  have hψ (ξ : Space) : compactWaveletFrequency ψ ξ =
      compactWaveletFrequency φ ((1 / 2 : ℝ) • ξ) - compactWaveletFrequency φ ξ := by
    change SchwartzMap.fourierTransformCLM ℂ (φHalf - φ) ξ = _
    rw [map_sub, SchwartzMap.sub_apply]
    exact congrArg (fun z : ℂ => z - compactWaveletFrequency φ ξ) (smallerBump_fourier φ ξ)
  have hθ (ξ : Space) : compactWaveletFrequency θ ξ =
      3 * (compactWaveletFrequency φ ((1 / 2 : ℝ) • ξ) + compactWaveletFrequency φ ξ) -
        2 * ((compactWaveletFrequency φ ((1 / 2 : ℝ) • ξ)) ^ 2 +
          compactWaveletFrequency φ ((1 / 2 : ℝ) • ξ) * compactWaveletFrequency φ ξ +
          (compactWaveletFrequency φ ξ) ^ 2) := by
    change SchwartzMap.fourierTransformCLM ℂ ((3 : ℂ) • (φHalf + φ) - (2 : ℂ) • (u + v + w)) ξ = _
    simp only [map_sub, map_smul, map_add, SchwartzMap.sub_apply, SchwartzMap.smul_apply,
      SchwartzMap.add_apply, smul_eq_mul]
    change 3 * (compactWaveletFrequency φHalf ξ + compactWaveletFrequency φ ξ) -
      2 * (compactWaveletFrequency u ξ + compactWaveletFrequency v ξ + compactWaveletFrequency w ξ) = _
    dsimp only [φHalf, u, v, w]
    simp only [convolutionSchwartz_fourier, smallerBump_fourier, pow_two]
  have h0 : compactWaveletFrequency φ 0 = 1 :=
    (wavelet_frequency_zero φ).trans normalizedHalfBump_integral
  refine ⟨φ, φHalf, ψ, θ, normalizedHalfBump_integral, normalizedHalfBump_outside,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change smallerBump φ x = compactWaveletKernel φ (1 / 2) x
    rw [smallerBump_apply, compactWaveletKernel]
    norm_num
  · intro x
    refine ⟨hφ x, hh x, ?_, ?_⟩
    · change conj (φHalf x - φ x) = φHalf x - φ x
      rw [map_sub, hh, hφ]
    · change conj (3 * (φHalf x + φ x) - 2 * (u x + v x + w x)) =
        3 * (φHalf x + φ x) - 2 * (u x + v x + w x)
      simp only [map_sub, map_add, map_mul, map_ofNat, hh, hφ, hu, hv, hw]
  · rw [← wavelet_frequency_zero, hψ, smul_zero, sub_self]
  · intro x hx
    change φHalf x - φ x = 0
    rw [smallerBump_outside _ (by linarith), normalizedHalfBump_outside _ (by linarith), sub_zero]
  · rw [← wavelet_frequency_zero, hθ, smul_zero, h0]
    norm_num
  · intro x hx
    have hp : φ x = 0 := normalizedHalfBump_outside _ (by linarith)
    have hq : φHalf x = 0 := smallerBump_outside _ (by linarith)
    have hu0 : u x = 0 := convolutionSchwartz_outside φHalf φHalf (1 / 4) (1 / 4)
      smallerBump_outside smallerBump_outside x (by linarith)
    have hv0 : v x = 0 := convolutionSchwartz_outside φHalf φ (1 / 4) (1 / 2)
      smallerBump_outside normalizedHalfBump_outside x (by linarith)
    have hw0 : w x = 0 := convolutionSchwartz_outside φ φ (1 / 2) (1 / 2)
      normalizedHalfBump_outside normalizedHalfBump_outside x (by linarith)
    change 3 * (φHalf x + φ x) - 2 * (u x + v x + w x) = 0
    rw [hp, hq, hu0, hv0, hw0]
    simp
  · intro ξ
    rw [hψ, hθ]
    unfold waveletCubic
    ring

/-- The same real unit-ball windows realize strong reproduction for every
positive scale and every complex L² input. -/
theorem exists_real_compact_wavelet_resolution :
    ∃ φ ψ θ : SchwartzMap Space ℂ,
      (∫ x, φ x) = 1 ∧ (∀ x, 1 / 2 < ‖x‖ → φ x = 0) ∧
      (∀ x, conj (φ x) = φ x ∧ conj (ψ x) = ψ x ∧ conj (θ x) = θ x) ∧
      (∫ x, ψ x) = 0 ∧ (∀ x, 1 < ‖x‖ → ψ x = 0) ∧
      (∫ x, θ x) = 0 ∧ (∀ x, 1 < ‖x‖ → θ x = 0) ∧
      WaveletFactorization φ ψ θ ∧
      ∀ (t : ℝ), 0 < t → ∀ (f : ComplexL2 Space),
        Tendsto (fun N => reproducingPartialAction ψ θ t N f) atTop (𝓝 f) := by
  obtain ⟨φ, _, ψ, θ, hφ, hφs, _, hReal, hψ, hψs, hθ, hθs, hFac⟩ :=
    exists_real_compact_wavelet_factorization
  refine ⟨φ, ψ, θ, hφ, hφs, ?_, hψ, hψs, hθ, hθs, hFac, ?_⟩
  · intro x
    exact ⟨(hReal x).1, (hReal x).2.2⟩
  · intro t ht f
    exact reproducing_windows_L2_tendsto φ ψ θ hφ hFac t ht f

end Burnett.Analysis.CarlesonEmbedding
