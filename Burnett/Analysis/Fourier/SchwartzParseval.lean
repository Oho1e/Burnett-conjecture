import Burnett.Analysis.Fourier.SchwartzTail

noncomputable section

namespace Burnett.Fourier

open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem fourier_conj_eq_conj_inverse (f : V → ℂ) (ξ : V) :
    𝓕 (fun x => conj (f x)) ξ = conj (𝓕⁻ f ξ) := by
  rw [Real.fourierIntegral_eq', Real.fourierIntegralInv_eq', ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 2
  push_cast
  ring

theorem fourier_integral_pairing (f g : V → ℂ)
    (hf : Integrable f (volume : Measure V)) (hg : Integrable g volume) :
    (∫ ξ, 𝓕 f ξ * g ξ) = ∫ x, f x * 𝓕 g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ V) Real.continuous_fourierChar continuous_inner hf hg
  simpa only [Real.fourierIntegral, flip_innerₗ, smul_eq_mul] using h

/-- Plancherel's energy equality for actual Schwartz functions on the
Euclidean space, derived here from the library's L¹ Fourier Fubini theorem
and Schwartz inversion. This does not yet construct the L² extension. -/
theorem schwartz_parseval (f : SchwartzMap V ℂ) :
    (∫ ξ, ‖𝓕 (f : V → ℂ) ξ‖^2) = ∫ x, ‖f x‖^2 := by
  let F : SchwartzMap V ℂ := SchwartzMap.fourierTransformCLM ℂ f
  have hFc : Integrable (fun ξ => conj (F ξ)) (volume : Measure V) := by
    apply F.integrable.norm.mono' (Complex.continuous_conj.comp F.continuous).aestronglyMeasurable
    filter_upwards with ξ
    simp
  have hpair := fourier_integral_pairing (f : V → ℂ) (fun ξ => conj (F ξ))
    f.integrable hFc
  have hi : ∀ x, 𝓕 (fun ξ => conj (F ξ)) x = conj (f x) := by
    intro x
    rw [fourier_conj_eq_conj_inverse]
    change conj (𝓕⁻ (𝓕 (f : V → ℂ)) x) = _
    rw [Continuous.fourier_inversion f.continuous f.integrable F.integrable]
  simp only [hi] at hpair
  have hnorm (z : ℂ) : z * conj z = (‖z‖^2 : ℝ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  change (∫ ξ, F ξ * conj (F ξ)) = ∫ x, f x * conj (f x) at hpair
  simp only [hnorm] at hpair
  have hreal : ((∫ ξ, ‖F ξ‖^2 : ℝ) : ℂ) = ((∫ x, ‖f x‖^2 : ℝ) : ℂ) :=
    (integral_ofReal (𝕜 := ℂ) (f := fun ξ : V => ‖F ξ‖^2)).symm.trans
      (hpair.trans (integral_ofReal (𝕜 := ℂ) (f := fun x : V => ‖f x‖^2)))
  exact_mod_cast hreal

end Burnett.Fourier
