import Burnett.Analysis.CubicEnergy.BilinearMultiplier.FourierConvention
import Burnett.Analysis.CubicEnergy.CompleteEnergy.PhysicalPairing

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.Fourier Burnett.RicciSymbol
open scoped FourierTransform ComplexConjugate ContDiff BigOperators

private def conjugateTest (w : SchwartzMap E ℂ) : SchwartzMap E ℂ where
  toFun := Complex.conjLIE ∘ (w : E → ℂ)
  smooth' := Complex.conjCLE.contDiff.comp (w.smooth _)
  decay' := by
    intro k n
    obtain ⟨C,hC⟩ := w.decay' k n
    exact ⟨C,fun x => by rw [Complex.conjLIE.norm_iteratedFDeriv_comp_left]; exact hC x⟩

private theorem negative_frequency_test (a : Joint → ℝ) (f v w : SchwartzMap E ℂ) :
    weightedFourier a f v (conjugateTest w) = bilinearFourierWeight a f v w := by
  funext p
  change _ * conj (𝓕 (fun x => conj (w x)) (p.1+p.2)) = _ * 𝓕 (w : E → ℂ) (-(p.1+p.2))
  rw [fourier_conj_eq_conj_inverse,starRingEnd_self_apply,Real.fourierIntegralInv_eq_fourierIntegral_neg]
  rfl

/-- The same spatial commutator with an ordinary bilinear test. The test
Fourier transform is evaluated at minus the sum of the input frequencies. -/
theorem physical_commutator_bilinear_test (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ z, b (t • z)=t*b z) (f v w : SchwartzMap E ℂ) :
    Integrable (fun x => physicalCommutator b f v x * w x) ∧
    (∫ x, physicalCommutator b f v x * w x) =
      (∑ j, ∫ p, bilinearFourierWeight (lowTerm b j) f v w p) +
      (∑ j, ∫ p, bilinearFourierWeight (productTerm b j) f v w p) -
       ∑ j, ∫ p, bilinearFourierWeight (inputTerm b j) f v w p := by
  have h := physical_commutator_pairing_decomposition b hb hh f v (conjugateTest w)
  have hconj (x : E) : conj (conjugateTest w x) = w x := by
    change conj (conj (w x)) = w x
    exact starRingEnd_self_apply _
  simpa only [hconj,negative_frequency_test] using h

end Burnett.A02.FrequencySplit
