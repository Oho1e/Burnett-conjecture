import Burnett.Analysis.CubicEnergy.CompleteEnergy.OutputPairing
import Burnett.Analysis.Fourier.SchwartzParseval

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.Fourier Burnett.RicciSymbol
open scoped FourierTransform RealInnerProductSpace ComplexConjugate ContDiff BigOperators

private def schwartzProduct (f v : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) v.hasTemperateGrowth f

def physicalCommutator (b : E → ℝ) (f v : SchwartzMap E ℂ) (x : E) : ℂ :=
  orderOneAction b (schwartzProduct f v) x - f x*orderOneAction b v x

private theorem conj_int {g : E → ℂ} (hg : Integrable g) : Integrable (fun x => conj (g x)) := by
  apply hg.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable)
  filter_upwards with x
  simp

private theorem fourier_test (g : E → ℂ) (hg : Integrable g) (w : SchwartzMap E ℂ) :
    (∫ ζ, 𝓕 g ζ * conj (𝓕 (w : E → ℂ) ζ)) = ∫ x, g x * conj (w x) := by
  let W := SchwartzMap.fourierTransformCLM ℂ w
  have h := fourier_integral_pairing g (fun ζ => conj (W ζ)) hg (conj_int W.integrable)
  have hi (x : E) : 𝓕 (fun ζ => conj (W ζ)) x = conj (w x) := by
    rw [fourier_conj_eq_conj_inverse]
    exact congrArg (fun k : E → ℂ => conj (k x)) (w.continuous.fourier_inversion w.integrable W.integrable)
  simpa only [hi] using h

private theorem inverse_test (G : E → ℂ) (hG : Integrable G) (w : SchwartzMap E ℂ) :
    (∫ x, (𝓕⁻ G) x * conj (w x)) = ∫ ζ, G ζ * conj (𝓕 (w : E → ℂ) ζ) := by
  have h := congrArg (starRingEnd ℂ) (fourier_integral_pairing (w : E → ℂ) (fun ζ => conj (G ζ)) w.integrable (conj_int hG))
  simp only [← integral_conj,map_mul,starRingEnd_self_apply,fourier_conj_eq_conj_inverse] at h
  simpa only [mul_comm] using h.symm

private theorem fourier_control (G : E → ℂ) (hG : Integrable G) :
    Continuous (𝓕 G) ∧ ∀ z, ‖𝓕 G z‖ ≤ ∫ ξ, ‖G ξ‖ :=
  ⟨VectorFourier.fourierIntegral_continuous (L := innerₗ E) Real.continuous_fourierChar continuous_inner hG,
    VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ E) G⟩

private theorem inverse_control (G : E → ℂ) (hG : Integrable G) :
    Continuous (𝓕⁻ G) ∧ ∃ C : ℝ, ∀ z, ‖𝓕⁻ G z‖ ≤ C := by
  have h := fourier_control G hG
  have hi : 𝓕⁻ G = fun x => 𝓕 G (-x) := funext (Real.fourierIntegralInv_eq_fourierIntegral_neg G)
  rw [hi]
  exact ⟨h.1.comp continuous_neg,_,fun z => h.2 (-z)⟩

theorem physical_commutator_pairing_decomposition (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ z, b (t • z)=t*b z) (f v w : SchwartzMap E ℂ) :
    Integrable (fun x => physicalCommutator b f v x * conj (w x)) ∧
    (∫ x, physicalCommutator b f v x * conj (w x)) =
      (∑ j, ∫ p, weightedFourier (lowTerm b j) f v w p) +
      (∑ j, ∫ p, weightedFourier (productTerm b j) f v w p) -
       ∑ j, ∫ p, weightedFourier (inputTerm b j) f v w p := by
  let G := fun ξ => (b ξ : ℂ)*𝓕 (v : E → ℂ) ξ
  let H := fun ξ => (b ξ : ℂ)*𝓕 (schwartzProduct f v : E → ℂ) ξ
  let a := fun x => f x*(𝓕⁻ G) x
  let W := SchwartzMap.fourierTransformCLM ℂ w
  have hG : Integrable G := orderOne_spectrum_integrable b hb hh v
  have hH : Integrable H := orderOne_spectrum_integrable b hb hh _
  obtain ⟨hcG,bG⟩ := inverse_control G hG
  obtain ⟨hcH,bH⟩ := inverse_control H hH
  have ha : Integrable a := by
    simpa only [a,mul_comm] using f.integrable.bdd_mul hcG.aestronglyMeasurable bG
  have wc : AEStronglyMeasurable (fun x => conj (w x)) (volume : Measure E) := (conj_int w.integrable).aestronglyMeasurable
  have Wc : AEStronglyMeasurable (fun x => conj (W x)) (volume : Measure E) := (conj_int W.integrable).aestronglyMeasurable
  have wb : ∃ D, ∀ x, ‖conj (w x)‖ ≤ D := ⟨_, fun x => by rw [Complex.norm_conj]; exact w.norm_le_seminorm ℝ x⟩
  have Wb : ∃ D, ∀ x, ‖conj (W x)‖ ≤ D := ⟨_, fun x => by rw [Complex.norm_conj]; exact W.norm_le_seminorm ℝ x⟩
  have A : Integrable (fun x => (𝓕⁻ H) x * conj (w x)) := (conj_int w.integrable).bdd_mul hcH.aestronglyMeasurable bH
  have B : Integrable (fun x => a x * conj (w x)) := by simpa only [mul_comm] using ha.bdd_mul wc wb
  have C : Integrable (fun ξ => H ξ * conj (W ξ)) := by simpa only [mul_comm] using hH.bdd_mul Wc Wb
  have D : Integrable (fun ξ => 𝓕 a ξ * conj (W ξ)) :=
    (conj_int W.integrable).bdd_mul (fourier_control a ha).1.aestronglyMeasurable ⟨_,(fourier_control a ha).2⟩
  have idP (x : E) : physicalCommutator b f v x * conj (w x) = 𝓕⁻ H x * conj (w x) - a x * conj (w x) := sub_mul _ _ _
  have idF (ζ : E) : commutatorSpectrum b f v ζ * conj (W ζ) = H ζ*conj (W ζ) - 𝓕 a ζ*conj (W ζ) := sub_mul _ _ _
  simp_rw [idP]
  refine ⟨A.sub B,?_⟩
  rw [integral_sub A B,inverse_test H hH w,← fourier_test a ha w]
  have final := (commutatorSpectrum_pairing_decomposition b hb hh f v w).2
  change (∫ ζ, commutatorSpectrum b f v ζ * conj (W ζ)) = _ at final
  simp_rw [idF] at final
  rw [integral_sub C D] at final
  exact final

end Burnett.A02.FrequencySplit
