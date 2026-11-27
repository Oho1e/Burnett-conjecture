import Burnett.Analysis.TransportWard.Weyl.Amplitude.AmplitudeJointMixedRemainder
import Burnett.Analysis.TransportWard.Weyl.Amplitude.PhasedJointProfileShift
import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactAmplitudeRapidProfile
import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactAmplitudeShiftIdentity
import Burnett.Analysis.TransportWard.Weyl.Amplitude.DirectionalAmplitudeSymbolBounds
import Burnett.Analysis.TransportWard.Weyl.Amplitude.ScaledMixedJetConversion

set_option autoImplicit false
set_option maxHeartbeats 6900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal FourierTransform Topology

/-- The complete left symbol from the already established cutoff
reduction, minus the literal diagonal of the original amplitude,
has the ordinary mixed order-zero symbol seminorms. -/
theorem compact_radian_two_point_left_diagonal_remainder_order_zero
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianScaledOrderOne a Rx Ry) :
    let F := radianSchwartzAmplitudeProfile (compactRadianTwoPointSlice a Rx Ry h.toCompactRadianTwoPointOrderOne)
    RadianOrderZeroSymbolSeminorms (fun x ξ => radianAmplitudeReduced F x ξ - a x x ξ) := by
  let H := h.toCompactRadianTwoPointOrderOne
  let A := compactRadianTwoPointSlice a Rx Ry H
  let F := radianSchwartzAmplitudeProfile A
  let J := compactRadianParameterProfile a Rx Ry H
  have e (x ξ : E) : radianAmplitudeReduced F x ξ - a x x ξ = radianShiftedProfileRemainder J x ξ :=
    compact_radian_two_point_shifted_profile_identity a Rx Ry H x ξ
  change RadianOrderZeroSymbolSeminorms (fun x ξ => radianAmplitudeReduced F x ξ - a x x ξ)
  rw [funext fun x => funext (e x)]
  have rapid := compact_radian_parameter_profile_rapid_joint a Rx Ry h
  obtain ⟨sm,b⟩ := radian_shifted_profile_remainder_scaled_jet_bounds J rapid
    (exists_radian_phased_joint_profile_shift_scaled_bound J rapid)
  exact radian_order_zero_of_scaled_joint_jets _ sm b

/-- The same ordinary compact two-point amplitude has an exact
left action and a first remainder of order zero. The left symbol is
shared by the physical cutoff limit, the support, and the estimate. -/
theorem exists_compact_radian_two_point_left_action_with_remainder
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne a Rx Ry)
    (directions : RadianOrdinaryDirectionalAmplitudeBounds a) :
    ∃ b : E → E → ℂ,
      (∀ x ξ, x ∉ closedBall (0 : E) Rx → b x ξ = 0) ∧
      RadianOrderZeroSymbolSeminorms (fun x ξ => b x ξ - a x x ξ) ∧
      ∀ (κ : ℕ → SchwartzMap E ℂ), (∀ n ξ, ‖κ n ξ‖ ≤ 1) →
        (∀ ξ, Tendsto (fun n => κ n ξ) atTop (𝓝 1)) →
        ∀ u x, Tendsto (fun n => radianTwoPointCutoffAction a (κ n) u x) atTop
          (𝓝 (radianLeftQuantization b u x)) := by
  let A := compactRadianTwoPointSlice a Rx Ry h
  let b := radianAmplitudeReduced (radianSchwartzAmplitudeProfile A)
  have scaled := compact_radian_scaled_order_one_of_directional a Rx Ry h directions
  exact ⟨b,compact_radian_two_point_amplitude_reduced_support a Rx Ry h,
    compact_radian_two_point_left_diagonal_remainder_order_zero a Rx Ry scaled,
    compact_radian_two_point_amplitude_cutoff_tendsto_left a Rx Ry h⟩

end Burnett.A03
