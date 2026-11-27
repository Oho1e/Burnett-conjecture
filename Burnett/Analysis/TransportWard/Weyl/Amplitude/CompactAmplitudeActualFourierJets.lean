import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactAmplitudeWeightedInputJets
import Burnett.Analysis.FrozenTransport.GaugeCorrection.DominatedIntegralJets
import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalSymbolMixedJets

set_option autoImplicit false
set_option maxHeartbeats 6600000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal FourierTransform RealInnerProductSpace Topology

/-- The genuine input Fourier profile of the same compact amplitude,
written in the two joint symbol parameters. -/
def compactRadianParameterProfile (a : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianTwoPointOrderOne a Rx Ry) (η : E) (p : RadianParameter) : ℂ :=
  radianSchwartzAmplitudeProfile (compactRadianTwoPointSlice a Rx Ry h) p.1 η p.2

theorem radian_fourier_neg_phase_smul_integral {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] (f : E → V) (η : E) :
    𝓕 f η = ∫ y : E, patchFourierPhase (-η) y • f y := by
  rw [Real.fourierIntegral_eq']
  apply integral_congr_ae
  filter_upwards with y
  have t : -2 * Real.pi * inner ℝ y η = tau * inner ℝ (-η) y := by
    rw [inner_neg_left,real_inner_comm η y]
    ring
  unfold patchFourierPhase Burnett.Microlocal.Overlap.baseFourierPhase
  rw [t]

private def profileInputIntegrand (a : E → E → E → ℂ) (η : E) (p : RadianParameter) (y : E) : ℂ :=
  patchFourierPhase (-η) y • radianTwoPointParameter a y p

private theorem profile_input_integrand_jet (a : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianTwoPointOrderOne a Rx Ry) (η y : E) (p : RadianParameter) (n : ℕ) :
    iteratedFDeriv ℝ n (fun q => profileInputIntegrand a η q y) p =
      patchFourierPhase (-η) y • iteratedFDeriv ℝ n (radianTwoPointParameter a y) p := by
  let L : ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℂ (patchFourierPhase (-η) y)
  have eq : (fun q => profileInputIntegrand a η q y) = L ∘ radianTwoPointParameter a y := rfl
  rw [eq,L.iteratedFDeriv_comp_left (radian_two_point_parameter_smooth a Rx Ry h y).contDiffAt
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))]
  rfl

theorem radian_frequency_weight_le_near_parameter (p q : RadianParameter)
    (hq : q ∈ ball p 1) : radianFrequencyWeight q.2 ≤ 2+‖p.2‖ := by
  have b : ‖q-p‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hq
  have t : ‖q.2-p.2‖ ≤ 1 := (norm_snd_le (q-p)).trans b.le
  have eq : p.2+(q.2-p.2) = q.2 := by abel
  have j := norm_add_le p.2 (q.2-p.2)
  rw [eq] at j
  dsimp only [radianFrequencyWeight]
  linarith

private theorem profile_input_jet_norm_le (a : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianScaledOrderOne a Rx Ry) (η : E) (n : ℕ) (C : ℝ) (C0 : 0 ≤ C)
    (hC : ∀ (p : RadianParameter) (y : E),
      ‖iteratedFDeriv ℝ 0 (fun z => radianScaledParameterJet (radianTwoPointParameter a z) n p) y‖ ≤
        C*radianFrequencyWeight p.2)
    (p q : RadianParameter) (hq : q ∈ ball p 1) (y : E) :
    ‖patchFourierPhase (-η) y • iteratedFDeriv ℝ n (radianTwoPointParameter a y) q‖ ≤
      (closedBall (0 : E) Ry).indicator (fun _ => C*(2+‖p.2‖)) y := by
  rw [norm_smul,patch_fourier_phase_norm,one_mul]
  by_cases yin : y ∈ closedBall (0 : E) Ry
  · rw [indicator_of_mem yin]
    have b : ‖radianScaledParameterJet (radianTwoPointParameter a y) n q‖ ≤ C*radianFrequencyWeight q.2 := by
      simpa only [norm_iteratedFDeriv_zero] using hC q y
    exact (radian_parameter_jet_norm_le_scaled _ n q).trans (b.trans
      (mul_le_mul_of_nonneg_left (radian_frequency_weight_le_near_parameter p q hq) C0))
  · rw [indicator_of_notMem yin,radian_two_point_parameter_jet_zero_off_input a Rx Ry
      h.toCompactRadianTwoPointOrderOne n y q yin,norm_zero]

theorem profile_compact_bound_integrable (Ry C : ℝ) (p : RadianParameter) :
    Integrable ((closedBall (0 : E) Ry).indicator (fun _ => C*(2+‖p.2‖))) volume :=
  (integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const (isCompact_closedBall (0 : E) Ry).measure_ne_top)

private theorem profile_input_jets_measure (a : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianTwoPointOrderOne a Rx Ry) (η : E) (n : ℕ) (p : RadianParameter) :
    AEStronglyMeasurable (fun y => patchFourierPhase (-η) y •
      iteratedFDeriv ℝ n (radianTwoPointParameter a y) p) volume :=
  ((radian_amplitude_phase_base_continuous (-η)).smul
    ((radian_two_point_parameter_jet_joint_smooth a Rx Ry h n).continuous.comp
      (continuous_id.prodMk continuous_const))).aestronglyMeasurable

private theorem dominated_profile_input_jets (a : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianScaledOrderOne a Rx Ry) (η : E) :
    DominatedIntegralJets (volume : Measure E) (profileInputIntegrand a η) := by
  let H := h.toCompactRadianTwoPointOrderOne
  refine ⟨fun y => ?_,fun n p => ?_,fun n p => ?_⟩
  · let L : ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℂ (patchFourierPhase (-η) y)
    change ContDiff ℝ ∞ ((L : ℂ → ℂ) ∘ radianTwoPointParameter a y)
    exact L.contDiff.comp (radian_two_point_parameter_smooth a Rx Ry H y)
  · have eq := funext (fun y => profile_input_integrand_jet a Rx Ry H η y p n)
    rw [eq]
    exact profile_input_jets_measure a Rx Ry H η n p
  · obtain ⟨C,C0,hC⟩ := h.scaledInputJetEstimate n 0
    refine ⟨1,zero_lt_one,_,profile_compact_bound_integrable Ry C p,fun q hq y => ?_⟩
    rw [profile_input_integrand_jet a Rx Ry H]
    exact profile_input_jet_norm_le a Rx Ry h η n C C0 hC p q hq y

private theorem compact_parameter_profile_eq_integral (a : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianTwoPointOrderOne a Rx Ry) (η : E) :
    compactRadianParameterProfile a Rx Ry h η = fun p => ∫ y : E, profileInputIntegrand a η p y := by
  funext p
  exact radian_fourier_neg_phase_smul_integral
    ((compactRadianTwoPointSlice a Rx Ry h p.1 p.2 : SchwartzMap E ℂ) : E → ℂ) η

theorem compact_radian_parameter_profile_smooth (a : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianScaledOrderOne a Rx Ry) (η : E) :
    ContDiff ℝ ∞ (compactRadianParameterProfile a Rx Ry h.toCompactRadianTwoPointOrderOne η) := by
  rw [compact_parameter_profile_eq_integral]
  exact contDiff_integral_of_dominated_jets volume _ (dominated_profile_input_jets a Rx Ry h η)

/-- Genuine joint base-frequency derivatives commute with the actual
input-variable Fourier integral. -/
theorem compact_radian_parameter_profile_jet_eq_integral (a : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianScaledOrderOne a Rx Ry) (η : E) (p : RadianParameter) (n : ℕ) :
    iteratedFDeriv ℝ n (compactRadianParameterProfile a Rx Ry h.toCompactRadianTwoPointOrderOne η) p =
      ∫ y : E, patchFourierPhase (-η) y • iteratedFDeriv ℝ n (radianTwoPointParameter a y) p := by
  rw [compact_parameter_profile_eq_integral,iteratedFDeriv_integral_eq_of_dominated_jets volume _
    (dominated_profile_input_jets a Rx Ry h η)]
  apply integral_congr_ae
  filter_upwards with y
  exact profile_input_integrand_jet a Rx Ry h.toCompactRadianTwoPointOrderOne η y p n

/-- Joint continuity in the Fourier input parameter and the left
symbol variables of each actual joint parameter jet. -/
theorem compact_radian_parameter_profile_jet_continuous (a : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianScaledOrderOne a Rx Ry) (n : ℕ) :
    Continuous (fun q : E × RadianParameter =>
      iteratedFDeriv ℝ n (compactRadianParameterProfile a Rx Ry h.toCompactRadianTwoPointOrderOne q.1) q.2) := by
  let H := h.toCompactRadianTwoPointOrderOne
  let W (q : E × RadianParameter) (y : E) :=
    patchFourierPhase (-q.1) y • iteratedFDeriv ℝ n (radianTwoPointParameter a y) q.2
  have formula : (fun q : E × RadianParameter =>
      iteratedFDeriv ℝ n (compactRadianParameterProfile a Rx Ry H q.1) q.2) =
        (fun q => ∫ y : E, W q y) :=
    funext (fun q => compact_radian_parameter_profile_jet_eq_integral a Rx Ry h q.1 q.2 n)
  rw [formula]
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨C,C0,hC⟩ := h.scaledInputJetEstimate n 0
  have hb : ∀ᶠ q' in 𝓝 q, q'.2 ∈ ball q.2 1 :=
    continuous_snd.continuousAt.eventually (ball_mem_nhds q.2 zero_lt_one : ball q.2 1 ∈ 𝓝 q.2)
  have ea : ∀ᶠ q' in 𝓝 q, ∀ᵐ y ∂(volume : Measure E), ‖W q' y‖ ≤
      (closedBall (0 : E) Ry).indicator (fun _ => C*(2+‖q.2.2‖)) y :=
    hb.mono (fun q' hq' => Eventually.of_forall (profile_input_jet_norm_le
      a Rx Ry h q'.1 n C C0 hC q.2 q'.2 hq'))
  refine tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall fun q' =>
    profile_input_jets_measure a Rx Ry H q'.1 n q'.2) ea (profile_compact_bound_integrable Ry C q.2) ?_
  refine Eventually.of_forall (fun y => ?_)
  have c : Continuous (fun q' : E × RadianParameter => W q' y) :=
    ((radian_amplitude_phase_frequency_continuous y).comp continuous_fst.neg).smul
      ((radian_two_point_parameter_jet_joint_smooth a Rx Ry H n).continuous.comp
        (continuous_const.prodMk continuous_snd))
  exact c.continuousAt

private theorem profile_input_parameter_jet_integrable (a : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianScaledOrderOne a Rx Ry) (η : E) (n : ℕ) (p : RadianParameter) :
    Integrable (fun y => patchFourierPhase (-η) y •
      iteratedFDeriv ℝ n (radianTwoPointParameter a y) p) volume := by
  obtain ⟨C,C0,hC⟩ := h.scaledInputJetEstimate n 0
  exact (profile_compact_bound_integrable Ry C p).mono' (profile_input_jets_measure a Rx Ry
    h.toCompactRadianTwoPointOrderOne η n p) (Eventually.of_forall
      (profile_input_jet_norm_le a Rx Ry h η n C C0 hC p p (mem_ball_self zero_lt_one)))

/-- The true Fourier transform of the scaled input-jet slice is
the corresponding scaled jet of the genuine profile. -/
theorem compact_radian_scaled_profile_jet_eq_fourier (a : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianScaledOrderOne a Rx Ry) (η : E) (p : RadianParameter) (n : ℕ) :
    radianScaledParameterJet (compactRadianParameterProfile a Rx Ry h.toCompactRadianTwoPointOrderOne η) n p =
      𝓕 (compactRadianScaledInputJet a Rx Ry h.toCompactRadianTwoPointOrderOne n p :
        E → RadianParameterJet n ℂ) η := by
  let T : RadianParameterJet n ℂ →L[ℝ] RadianParameterJet n ℂ :=
    ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => radianParameterScale (radianFrequencyWeight p.2))
  change T (iteratedFDeriv ℝ n (compactRadianParameterProfile a Rx Ry h.toCompactRadianTwoPointOrderOne η) p) = _
  rw [compact_radian_parameter_profile_jet_eq_integral a Rx Ry h,radian_fourier_neg_phase_smul_integral,
    ← T.integral_comp_comm (profile_input_parameter_jet_integrable a Rx Ry h η n p)]
  apply integral_congr_ae
  filter_upwards with y
  ext v
  rfl

end Burnett.A03
