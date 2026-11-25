import Burnett.Analysis.AllScaleTransfer.RadianFirstLowSupport
import Burnett.Analysis.AllScaleTransfer.ActualCapAxialWindows
import Burnett.Analysis.AllScaleTransfer.SignedCapEndpointM0

set_option autoImplicit false
set_option maxHeartbeats 5600000

noncomputable section

namespace Burnett.A05

open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier
open Set

private theorem signedChartLift_endpointDirection_of_axis (s : Bool) (x : E)
    (hs : 0 < signedAxis s x) :
    signedChartLift s (endpointTail (endpointDirection x)) = endpointDirection x := by
  have hX : x ≠ 0 := by
    intro h
    cases s <;> simp [h,signedAxis] at hs
  apply signedChartLift_endpointTail s (endpointDirection_mem_sphere hX)
  have e : signedAxis s (endpointDirection x) = ‖x‖⁻¹ * signedAxis s x := by
    cases s
    · change -(‖x‖⁻¹ * x 0) = ‖x‖⁻¹ * -(x 0)
      ring
    · rfl
  rw [e]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hX)) hs

/-- Identify the exact low-ratio difference in each signed chart of the
same physical cap. The original zero-ratio trace is used in all signs. -/
theorem radianFirstLowRemainder_eq_signedCapChart
    (χ : ℝ → ℝ) (χ0 : χ 0 = 1) (A : E ≃L[ℝ] E) (m : Joint → ℂ)
    (M : E → E → ℝ → ℂ) (p : Joint) (signs : CapSigns)
    (hp : 0 < signedAxis signs.1 p.1) (hq : 0 < signedAxis signs.2 p.2)
    (hM : m p = M (endpointDirection p.1) (endpointDirection p.2) (‖A p.1‖/‖A p.2‖)) :
    let M₀ (x : Joint) := M x.1 x.2 0
    let ρ := ‖A p.1‖/‖A p.2‖
    let ωθ := (endpointTail (endpointDirection p.1),endpointTail (endpointDirection p.2))
    radianFirstLowRemainder χ A M₀ m p = ρ •
      Burnett.Analysis.LowRatio.remainder (signedEndpointProfile M signs) χ (ωθ,ρ) := by
  intro M₀ ρ ωθ
  have hq0 : p.2 ≠ 0 := by
    intro h
    rcases signs with ⟨s₁,s₂⟩
    cases s₂ <;> simp [h,signedAxis] at hq
  have eval (t : ℝ) : signedEndpointProfile M signs (ωθ,t) =
      M (endpointDirection p.1) (endpointDirection p.2) t := by
    simp only [signedEndpointProfile,ωθ,signedChartLift_endpointDirection_of_axis _ _ hp,
      signedChartLift_endpointDirection_of_axis _ _ hq]
  exact radianFirstLowRemainder_eq_original χ χ0 A M₀ m (signedEndpointProfile M signs) p hq0 ωθ
    (hM.trans (eval ρ).symm) (eval 0).symm

/-- Localizing the actual coefficient and its zero-ratio trace uses the
same axial multiplier in the exact decomposition. -/
theorem axialLocalizeRatio_radianRatioRemainderSymbol (α : ℝ) (χ : ℝ → ℝ)
    (A : E ≃L[ℝ] E) (M₀ m : Joint → ℂ) (p : Joint) :
    radianRatioRemainderSymbol χ A (axialLocalizeEndpoint α M₀)
      (fun p => (axialCapPairWindow α p : ℂ) * m p) p =
      (axialCapPairWindow α p : ℂ) * radianRatioRemainderSymbol χ A M₀ m p := by
  unfold radianRatioRemainderSymbol radianEndpointAngular
  change _ - axialLocalizeEndpoint α M₀ (endpointDirection p.1,endpointDirection p.2) *
    (χ (‖A p.1‖/‖A p.2‖) : ℂ) = _
  rw [axialLocalizeEndpoint_eval]
  simp only [endpointDirection]
  ring

end Burnett.A05
