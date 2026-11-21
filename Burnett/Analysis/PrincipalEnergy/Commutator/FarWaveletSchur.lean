import Burnett.Analysis.PrincipalEnergy.Commutator.FarWaveletPair
import Burnett.Analysis.PrincipalEnergy.Commutator.InverseFifthTail

set_option autoImplicit false
set_option maxHeartbeats 2700000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Burnett.Analysis.FirstOrderDyadic
open scoped ComplexConjugate

/-- The nonnegative translation-invariant envelope of the far wavelet
pairing, with the actual cutoff at four times the coarser scale. -/
def farWaveletKernelEnvelope (s t : ℝ) (x y : Space) : ℝ :=
  s*inverseFifthTail (4*t) (x-y)

/-- Both integrals of the far envelope have the same inverse-linear scale
ratio, with no dependence on the centers. -/
theorem farWaveletKernelEnvelope_integrals {s t : ℝ} (ht : 0<t) (c : Space) :
    (Integrable (farWaveletKernelEnvelope s t c) ∧
      (∫ y, farWaveletKernelEnvelope s t c y) =
        (s/t)*((∫ z, inverseFifthTail 1 z)/4)) ∧
    (Integrable (fun x => farWaveletKernelEnvelope s t x c) ∧
      (∫ x, farWaveletKernelEnvelope s t x c) =
        (s/t)*((∫ z, inverseFifthTail 1 z)/4)) := by
  obtain ⟨hI,hInt⟩ := inverseFifthTail_about_center (mul_pos (by norm_num : (0:ℝ)<4) ht) c
  have hRow : Integrable (farWaveletKernelEnvelope s t c) ∧
      (∫ y, farWaveletKernelEnvelope s t c y) =
        (s/t)*((∫ z, inverseFifthTail 1 z)/4) := by
    refine ⟨hI.const_mul s,?_⟩
    simp only [farWaveletKernelEnvelope,integral_const_mul,hInt]
    field_simp [ht.ne']
  have hSym : (fun x => farWaveletKernelEnvelope s t x c) = farWaveletKernelEnvelope s t c := by
    funext x
    simp only [farWaveletKernelEnvelope,inverseFifthTail,norm_sub_rev x c]
  exact ⟨hRow,hSym ▸ hRow⟩

/-- Pointwise domination of the actual far-cutoff wavelet pairing by the
envelope whose two integrals are evaluated above. -/
theorem centeredWaveletPair_far_envelope {K : Space → Space → ℂ} {C : ℝ}
    (hK : CalderonZygmundKernelBounds K C)
    (R : SchwartzMap Space ℂ → SchwartzMap Space ℂ → ℂ)
    (hPair : ∀ (f g : SchwartzMap Space ℂ), HasCompactSupport (f : Space → ℂ) →
      ∀ d : ℝ, 0<d → (∀ x y : Space, f y≠0 → g x≠0 → d≤‖x-y‖) →
      R f g = ∫ p : Space × Space, conj (g p.1)*(K p.1 p.2*f p.2)
        ∂((volume : Measure Space).prod volume))
    (θ η : SchwartzMap Space ℂ) (hθ : ∀ z, 1<‖z‖ → θ z=0) (hη : ∀ z, 1<‖z‖ → η z=0)
    (hη₀ : (∫ z, η z)=0) (s t : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≤t) (x y : Space) :
    ‖if 4*t≤‖x-y‖ then R (centeredWavelet θ hθ t ht y) (centeredWavelet η hη s hs x) else 0‖≤
      32*C*(∫ z, ‖θ z‖)*(∫ z, ‖η z‖)*farWaveletKernelEnvelope s t x y := by
  by_cases hFar : 4*t≤‖x-y‖
  · rw [if_pos hFar,farWaveletKernelEnvelope,inverseFifthTail,if_pos hFar]
    convert centeredWaveletPair_far_bound hK R hPair θ η hθ hη hη₀ s t hs ht hst x y hFar using 1
    ring
  · simp [hFar,farWaveletKernelEnvelope,inverseFifthTail]

end Burnett.Analysis.CarlesonEmbedding
