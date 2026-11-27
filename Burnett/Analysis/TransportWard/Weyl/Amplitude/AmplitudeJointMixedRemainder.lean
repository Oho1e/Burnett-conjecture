import Burnett.Analysis.TransportWard.Weyl.Amplitude.RadianJointProfileData
import Burnett.Analysis.FrozenTransport.GaugeCorrection.DominatedIntegralJets
import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalSymbolMixedJets
import Burnett.Analysis.TransportWard.Weyl.Amplitude.RadianProfilePolynomialMoments

set_option autoImplicit false
set_option maxHeartbeats 6600000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal Topology

private theorem dominated_phased_joint_profile_shift
    (F : E → RadianParameter → ℂ) (h : RadianRapidJointProfiles F) (bounds : RadianPhasedShiftBounds F) :
    DominatedIntegralJets (volume : Measure E) (fun p η => radianPhasedJointProfileShift F η p) := by
  have s : ContDiff ℝ ∞ (Function.uncurry (radianPhasedJointProfileShift F)) :=
    radian_phased_joint_profile_shift_smooth F h
  have sectionSmooth (η : E) : ContDiff ℝ ∞ (radianPhasedJointProfileShift F η) := by
    let arg (p : RadianParameter) : E × RadianParameter := (η,p)
    have sa : ContDiff ℝ ∞ arg := contDiff_const.prodMk contDiff_id
    change ContDiff ℝ ∞ (Function.uncurry (radianPhasedJointProfileShift F) ∘ arg)
    exact s.comp sa
  refine ⟨sectionSmooth,fun n p => ?_,fun n p => ?_⟩
  · let arg (η : E) : E × RadianParameter := (η,p)
    have ca : Continuous arg := continuous_id.prodMk continuous_const
    have c := smooth_right_slice_iterated_fderiv (radianPhasedJointProfileShift F) s n
    change AEStronglyMeasurable ((fun z : E × RadianParameter =>
      iteratedFDeriv ℝ n (radianPhasedJointProfileShift F z.1) z.2) ∘ arg) volume
    exact (c.continuous.comp ca).aestronglyMeasurable
  · let N := (volume : Measure E).integrablePower+(n+1)
    obtain ⟨C,_,cb⟩ := bounds n N
    refine ⟨1,zero_lt_one,_,(integrable_radian_shift_polynomial_decay (n+1)).const_mul C,fun q _ η => ?_⟩
    exact (radian_parameter_jet_norm_le_scaled (radianPhasedJointProfileShift F η) n q).trans (cb η q)

/-- The actual difference integrand, integrated in the input Fourier
parameter. The same integrand arises from subtracting the complete
left symbol and its diagonal. -/
def radianShiftedProfileRemainder (F : E → RadianParameter → ℂ) (x ξ : E) : ℂ :=
  ∫ η : E, radianPhasedJointProfileShift F η (x,ξ)

/-- Every scaled joint jet of the literal shifted integral is finite
and bounded uniformly over both symbol parameters. -/
theorem radian_shifted_profile_remainder_scaled_jet_bounds
    (F : E → RadianParameter → ℂ) (h : RadianRapidJointProfiles F) (bounds : RadianPhasedShiftBounds F) :
    ContDiff ℝ ∞ (Function.uncurry (radianShiftedProfileRemainder F)) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : RadianParameter,
        ‖radianScaledParameterJet (Function.uncurry (radianShiftedProfileRemainder F)) n p‖ ≤ C := by
  let J (p : RadianParameter) (η : E) := radianPhasedJointProfileShift F η p
  have dom : DominatedIntegralJets (volume : Measure E) J := dominated_phased_joint_profile_shift F h bounds
  have sm : ContDiff ℝ ∞ (Function.uncurry (radianShiftedProfileRemainder F)) :=
    contDiff_integral_of_dominated_jets volume J dom
  refine ⟨sm,?_⟩
  intro n
  let N := (volume : Measure E).integrablePower+(n+1)
  obtain ⟨C,C0,hC⟩ := bounds n N
  let D (η : E) := C*((1+‖η‖) ^ (-(N : ℝ))*(1+tau*‖η‖)^(n+1))
  have D0 (η : E) : 0 ≤ D η := (norm_nonneg (radianScaledParameterJet
    (radianPhasedJointProfileShift F η) n (0,0))).trans (hC η (0,0))
  have DI : Integrable D volume := (integrable_radian_shift_polynomial_decay (n+1)).const_mul C
  refine ⟨∫ η : E, D η,integral_nonneg D0,fun p => ?_⟩
  let T : RadianParameterJet n ℂ →L[ℝ] RadianParameterJet n ℂ :=
    ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => radianParameterScale (radianFrequencyWeight p.2))
  let W (η : E) := iteratedFDeriv ℝ n (fun y => J y η) p
  let V (η : E) := T (W η)
  have WI : Integrable W volume := by
    obtain ⟨ε,εp,b,bi,bd⟩ := dom.locallyDominated n p
    exact bi.mono' (dom.measurable n p) (Eventually.of_forall (bd p (mem_ball_self εp)))
  have VI : Integrable V volume := T.integrable_comp WI
  change ‖T (iteratedFDeriv ℝ n (fun q => ∫ η : E, J q η) p)‖ ≤ _
  rw [iteratedFDeriv_integral_eq_of_dominated_jets volume J dom,
    ← T.integral_comp_comm WI]
  calc
    _ ≤ ∫ η : E, ‖V η‖ := norm_integral_le_integral_norm V
    _ ≤ _ := integral_mono VI.norm DI (fun η => hC η p)

end Burnett.A03
