import Burnett.Analysis.TransportWard.Weyl.Amplitude.RadianJointProfileData
import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactAmplitudeProfileJointSmooth

set_option autoImplicit false
set_option maxHeartbeats 3800000
noncomputable section

namespace Burnett.A03

open Burnett.A02.FrequencySplit

/-- All the required material in the Fourier profile comes from the
same original compact amplitude and its ordinary directional symbol
estimates. -/
theorem compact_radian_parameter_profile_rapid_joint
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianScaledOrderOne a Rx Ry) :
    RadianRapidJointProfiles (compactRadianParameterProfile a Rx Ry h.toCompactRadianTwoPointOrderOne) := by
  refine ⟨compact_radian_parameter_profile_joint_smooth a Rx Ry h.toCompactRadianTwoPointOrderOne,fun n N => ?_⟩
  obtain ⟨C,C0,hC⟩ := exists_compact_radian_scaled_input_jet_fourier_decay a Rx Ry h n N
  refine ⟨C,C0,fun η p => ?_⟩
  rw [compact_radian_scaled_profile_jet_eq_fourier a Rx Ry h]
  exact hC p η

end Burnett.A03
