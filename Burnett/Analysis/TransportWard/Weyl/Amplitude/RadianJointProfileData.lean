import Burnett.Analysis.TransportWard.Weyl.Amplitude.ScaledJointProfileShift

set_option autoImplicit false
set_option maxHeartbeats 3600000
noncomputable section

namespace Burnett.A03

open Burnett.A02.FrequencySplit
open scoped ContDiff

/-- The order-one joint symbol estimates of the actual input Fourier
profile. The estimates require rapid decay in the input Fourier parameter. -/
structure RadianRapidJointProfiles (F : E → RadianParameter → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ (Function.uncurry F)
  orderOne : ∀ k N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ η p,
    ‖radianScaledParameterJet (F η) k p‖ ≤
      C*(1+‖η‖) ^ (-(N : ℝ))*radianFrequencyWeight p.2

/-- The actual shifted Fourier integral's integrand minus the diagonal
amplitude's integrand. -/
def radianPhasedJointProfileShift (F : E → RadianParameter → ℂ) (η : E) (p : RadianParameter) : ℂ :=
  patchFourierPhase η p.1 * radianJointProfileShift (F η) (tau • η) p

theorem radian_phased_joint_profile_shift_smooth
    (F : E → RadianParameter → ℂ) (h : RadianRapidJointProfiles F) :
    ContDiff ℝ ∞ (Function.uncurry (radianPhasedJointProfileShift F)) := by
  let phaseArgs (z : E × RadianParameter) := (z.1,z.2.1)
  let shiftArgs (z : E × RadianParameter) := (z.1,z.2 + (0,tau • z.1))
  have phaseS : ContDiff ℝ ∞ (fun p : E × E => patchFourierPhase p.1 p.2) := by
    have inn : ContDiff ℝ ∞ (fun p : E × E => inner ℝ p.1 p.2) := contDiff_inner
    exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul inn)).mul contDiff_const)
  have cs : ContDiff ℝ ∞ phaseArgs := contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have ss : ContDiff ℝ ∞ shiftArgs := contDiff_fst.prodMk
    (contDiff_snd.add (contDiff_const.prodMk (contDiff_const.smul contDiff_fst)))
  change ContDiff ℝ ∞ (fun z => ((fun p : E × E => patchFourierPhase p.1 p.2) ∘ phaseArgs) z *
    ((Function.uncurry F ∘ shiftArgs) z - Function.uncurry F z))
  exact (phaseS.comp cs).mul ((h.smooth.comp ss).sub h.smooth)

/-- A rapid majorant for the scaled joint jets of the actual phased
shift, including its polynomial loss in the input Fourier parameter. -/
def RadianPhasedShiftBounds (F : E → RadianParameter → ℂ) : Prop :=
  ∀ k N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ η p,
    ‖radianScaledParameterJet (radianPhasedJointProfileShift F η) k p‖ ≤
      C*((1+‖η‖) ^ (-(N : ℝ))*(1+tau*‖η‖)^(k+1))

end Burnett.A03
