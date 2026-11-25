import Burnett.Analysis.Microlocal.Overlap.ActualClassicalFullSymbol

/-! The exact left Fourier action of a compact smoothing kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Function MeasureTheory Set
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.AngularDyadicKernel (E inverseFourier_mul_fourier_eq_convolution)
open scoped ContDiff FourierTransform

/-- Fourier transformation in the displacement variable gives the exact
left symbol. Fourier inversion uses the actual fixed output point. -/
theorem firstOrderAction_fourier_displacementKernel
    (k : E → E → ℂ) (u : SchwartzMap E ℂ) (x : E)
    (hk : ContDiff ℝ ∞ (k x)) (hkc : HasCompactSupport (k x)) :
    firstOrderAction (fun y ξ => 𝓕 (k y) ξ) u x = ∫ y, k x (x - y) * u y := by
  let K := hkc.toSchwartzMap hk
  have hK : Integrable (k x) := K.integrable
  have hF : Integrable (𝓕 (k x)) := (SchwartzMap.fourierTransformCLE ℂ K).integrable
  have hInv : 𝓕⁻ (𝓕 (k x)) = k x := hk.continuous.fourier_inversion hK hF
  rw [firstOrderAction, inverseFourier_mul_fourier_eq_convolution _ _ hF u.integrable, hInv]

/-- For a compactly supported kernel in the two input coordinates, changing to
displacement coordinates keeps fixed compact support in both variables. -/
theorem compactSmoothKernel_displacement
    (k : E → E → ℂ) (S T : Set E) (hS : IsCompact S) (hT : IsCompact T)
    (hk : ContDiff ℝ ∞ (uncurry k))
    (hSupp : ∀ x y, x ∉ S ∨ y ∉ T → k x y = 0) :
    let d (x z : E) := k x (x - z)
    let U := (fun q : E × E => q.1 - q.2) '' (S ×ˢ T)
    IsCompact U ∧ ContDiff ℝ ∞ (uncurry d) ∧ (∀ x z, x ∉ S ∨ z ∉ U → d x z = 0) := by
  intro d U
  have hU : IsCompact U := (hS.prod hT).image (continuous_fst.sub continuous_snd)
  refine ⟨hU, hk.comp (contDiff_fst.prodMk (contDiff_fst.sub contDiff_snd)), ?_⟩
  intro x z hz
  by_cases hx : x ∈ S
  · apply hSupp x (x - z)
    right
    intro hy
    exact (hz.resolve_left (fun hn => hn hx)) ⟨(x, x - z), ⟨hx, hy⟩, sub_sub_cancel _ _⟩
  · exact hSupp x (x-z) (Or.inl hx)

/-- On both windows the smoothing term is exactly its displaced full symbol. -/
theorem firstOrderAction_compactSmoothKernel
    (k : E → E → ℂ) (S T : Set E) (hS : IsCompact S) (hT : IsCompact T)
    (hk : ContDiff ℝ ∞ (uncurry k))
    (hSupp : ∀ x y, x ∉ S ∨ y ∉ T → k x y = 0)
    (u : SchwartzMap E ℂ) (x : E) :
    firstOrderAction (fun y ξ => 𝓕 (fun z => k y (y - z)) ξ) u x = ∫ y, k x y * u y := by
  obtain ⟨hU, hD, hSupport⟩ := compactSmoothKernel_displacement k S T hS hT hk hSupp
  let d (y z : E) := k y (y-z)
  have hSmooth : ContDiff ℝ ∞ (d x) := hD.comp (contDiff_const.prodMk contDiff_id)
  have hCompact : HasCompactSupport (d x) := by
    apply hU.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hU.isClosed
    intro z hz
    by_contra h
    exact hz (hSupport x z (Or.inr h))
  rw [firstOrderAction_fourier_displacementKernel d u x hSmooth hCompact]
  simp only [d, sub_sub_cancel]

end Burnett.Microlocal.Overlap
