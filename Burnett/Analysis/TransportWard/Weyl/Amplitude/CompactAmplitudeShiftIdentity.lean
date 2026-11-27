import Burnett.Analysis.TransportWard.Weyl.Amplitude.RadianJointProfileData
import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactAmplitudeActualFourierJets

set_option autoImplicit false
set_option maxHeartbeats 4400000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal FourierTransform Topology

/-- The difference between the actual reduced left symbol and the
literal amplitude diagonal is the same phased shifted integral. -/
theorem compact_radian_two_point_shifted_profile_identity
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne a Rx Ry) (x ξ : E) :
    let A := compactRadianTwoPointSlice a Rx Ry h
    let J := compactRadianParameterProfile a Rx Ry h
    radianAmplitudeReduced (radianSchwartzAmplitudeProfile A) x ξ - a x x ξ =
      ∫ η : E, radianPhasedJointProfileShift J η (x,ξ) := by
  let A := compactRadianTwoPointSlice a Rx Ry h
  let F := radianSchwartzAmplitudeProfile A
  let J := compactRadianParameterProfile a Rx Ry h
  change radianAmplitudeReduced F x ξ - a x x ξ = ∫ η : E, radianPhasedJointProfileShift J η (x,ξ)
  obtain ⟨w,wB⟩ := exists_radian_amplitude_fourier_bounds A
    (compact_radian_two_point_slice_order_one a Rx Ry h)
    (compact_radian_two_point_profile_measurable a Rx Ry h)
  have τ : 0 ≤ tau := mul_nonneg (by norm_num) Real.pi_pos.le
  have S := radian_amplitude_spectral_integrable F w wB x ξ tau τ le_rfl
  have L : Integrable (fun η : E => patchFourierPhase η x * F x η ξ) volume := by
    simpa only [zero_smul,add_zero] using
      radian_amplitude_spectral_integrable F w wB x ξ 0 le_rfl τ
  rw [← compact_radian_two_point_amplitude_diagonal a Rx Ry h, radianAmplitudeReduced,
    radianAmplitudeDiagonal,← integral_sub S L]
  apply integral_congr_ae
  filter_upwards with η
  change patchFourierPhase η x * F x η (ξ+tau • η)-patchFourierPhase η x * F x η ξ =
    patchFourierPhase η x * (F (x+0) η (ξ+tau • η)-F x η ξ)
  rw [add_zero,mul_sub]

end Burnett.A03
