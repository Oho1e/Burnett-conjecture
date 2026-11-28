import Burnett.Analysis.TransportWard.Weyl.VariableDensityWeylAction

set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option maxRecDepth 1600

noncomputable section

namespace Burnett.V03

open Function Set Filter MeasureTheory Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic (baseDirectionSymbol)
open scoped ContDiff FourierTransform Topology

/-- The exact left-reduced symbol has the output support of the original
physical window, including when the enclosing compact ball is larger. -/
theorem windowedWeylLeftSymbol_eq_zero_of_output (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (x ξ : E) (hx : θ x = 0) : windowedWeylLeftSymbol θ β R h x ξ = 0 := by
  let A := compactRadianTwoPointSlice (windowedWeylAmplitude θ β) R R h
  have hz (ζ : E) : A x ζ = 0 := by
    ext y
    change windowedWeylAmplitude θ β x y ζ = 0
    simp only [windowedWeylAmplitude,hx,Complex.ofReal_zero,zero_mul]
  change radianAmplitudeReduced (radianSchwartzAmplitudeProfile A) x (tau • ξ) = 0
  unfold radianAmplitudeReduced
  have heq : (fun η : E => patchFourierPhase η x *
      radianSchwartzAmplitudeProfile A x η (tau • ξ + tau • η)) = fun _ => 0 := by
    funext η
    change patchFourierPhase η x * 𝓕 (A x (tau • ξ + tau • η) : E → ℂ) η = 0
    rw [hz]
    change patchFourierPhase η x * 𝓕 (fun _ : E => (0 : ℂ)) η = 0
    rw [Real.fourierIntegral_eq']
    simp
  rw [heq]
  simp

theorem normalizedWeylSymbol_eq_zero_of_output {θ : E → ℝ} {β : E → E → ℂ}
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1) {x ξ : E} (hx : θ x = 0) :
    normalizedWeylSymbol β x ξ = 0 := by
  change β x (tau • ξ) = 0
  by_contra hne
  have bad := hx.symm.trans (hPlateau x (tau • ξ) hne)
  exact zero_ne_one bad

theorem baseDirectionSymbol_eq_zero_off_closed {a : E → E → ℂ} {K : Set E}
    (hK : IsClosed K) (ha : ∀ x ∉ K, ∀ ξ, a x ξ = 0) (e : E)
    {x ξ : E} (hx : x ∉ K) : baseDirectionSymbol a e x ξ = 0 := by
  have hNear : ∀ᶠ y in 𝓝 x, y ∉ K := hK.isOpen_compl.mem_nhds hx
  have hGerm : (fun y => a y ξ) =ᶠ[𝓝 x] (fun _ => 0) := hNear.mono (fun y hy => ha y hy ξ)
  rw [baseDirectionSymbol,hGerm.fderiv_eq,fderiv_const_apply,ContinuousLinearMap.zero_apply]

theorem coefficientCommutatorSymbol_eq_zero_of_zero_row {a : E → E → ℂ} (c : SchwartzMap E ℂ)
    {x ξ : E} (hx : ∀ ν, a x ν = 0) : coefficientCommutatorSymbol a c x ξ = 0 := by
  unfold coefficientCommutatorSymbol rightSchwartzSymbol
  simp only [hx,mul_zero,integral_zero,sub_zero]

theorem coefficientCommutatorLeading_eq_zero_of_zero_row {a : E → E → ℂ} (c : SchwartzMap E ℂ)
    {x ξ : E} (hx : ∀ ν, a x ν = 0) : coefficientCommutatorLeading a c x ξ = 0 := by
  have hRow : a x = fun _ => 0 := funext hx
  unfold coefficientCommutatorLeading
  simp only [hRow,fderiv_const_apply,ContinuousLinearMap.zero_apply,mul_zero,Finset.sum_const_zero]

end Burnett.V03
