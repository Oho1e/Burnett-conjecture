import Burnett.Analysis.CubicEnergy.CompleteEnergy.PhysicalCommutator
import Mathlib.MeasureTheory.Group.Prod

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory Set Burnett.RicciSymbol
open scoped FourierTransform ComplexConjugate ContDiff BigOperators

private def outputChange : Joint ≃ᵐ Joint where
  toFun := fun p => (p.1-p.2,p.2)
  invFun := fun p => (p.1+p.2,p.2)
  left_inv := fun _ => Prod.ext (sub_add_cancel _ _) rfl
  right_inv := fun _ => Prod.ext (add_sub_cancel_right _ _) rfl
  measurable_toFun := (measurable_fst.sub measurable_snd).prodMk measurable_snd
  measurable_invFun := (measurable_fst.add measurable_snd).prodMk measurable_snd

private theorem outputChange_mp : MeasurePreserving outputChange (volume : Measure Joint) volume := by
  rw [Measure.volume_eq_prod E E]
  have he : (outputChange : Joint → Joint) = Prod.swap ∘ (fun p : Joint => (p.2,-p.2+p.1)) := by
    funext p
    exact Prod.ext (by change p.1-p.2 = -p.2+p.1; rw [sub_eq_add_neg,add_comm]) rfl
  rw [he]
  exact Measure.measurePreserving_swap.comp (measurePreserving_prod_neg_add_swap (volume : Measure E) volume)

def commutatorSpectrum (b : E → ℝ) (f v : SchwartzMap E ℂ) (ζ : E) : ℂ :=
  (b ζ : ℂ) * 𝓕 (fun x => f x*v x) ζ - 𝓕 (fun x => f x*orderOneAction b v x) ζ

/-- The Fourier representative of the actual commutator paired with a
Schwartz test is exactly the sum of the three integrable symbol pairings. -/
theorem commutatorSpectrum_pairing_decomposition (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ z, b (t • z)=t*b z) (f v w : SchwartzMap E ℂ) :
    Integrable (fun ζ => commutatorSpectrum b f v ζ * conj (𝓕 (w : E → ℂ) ζ)) ∧
    (∫ ζ, commutatorSpectrum b f v ζ * conj (𝓕 (w : E → ℂ) ζ)) =
      (∑ j, ∫ p, weightedFourier (lowTerm b j) f v w p) +
      (∑ j, ∫ p, weightedFourier (productTerm b j) f v w p) -
       ∑ j, ∫ p, weightedFourier (inputTerm b j) f v w p := by
  let F := weightedFourier (fun p => b (p.1+p.2)-b p.2) f v w
  obtain ⟨hf,eq⟩ := fourier_trilinear_identity b hb hh f v w
  have hc : Integrable (F ∘ outputChange) (volume : Measure Joint) := outputChange_mp.integrable_comp_of_integrable hf
  rw [Measure.volume_eq_prod E E] at hc
  have inner_eq (ζ : E) : commutatorSpectrum b f v ζ * conj (𝓕 (w : E → ℂ) ζ) =
      ∫ ξ, (F ∘ outputChange) (ζ,ξ) := by
    unfold commutatorSpectrum
    rw [orderOne_commutator_fourier b hb hh,← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with ξ
    change _ = ((b ((ζ-ξ)+ξ)-b ξ : ℝ) : ℂ)*𝓕 (f : E → ℂ) (ζ-ξ)*𝓕 (v : E → ℂ) ξ*conj (𝓕 (w : E → ℂ) ((ζ-ξ)+ξ))
    rw [sub_add_cancel,Complex.ofReal_sub]
  simp_rw [inner_eq]
  refine ⟨hc.integral_prod_left,?_⟩
  rw [← integral_prod _ hc]
  change (∫ p, (F ∘ outputChange) p ∂(volume : Measure Joint)) = _
  exact (outputChange_mp.integral_comp' F).trans eq

end Burnett.A02.FrequencySplit
