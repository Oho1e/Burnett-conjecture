import Burnett.Analysis.TransportWard.Weyl.Amplitude.WeightedParameterJets
import Burnett.Analysis.TransportWard.Weyl.Amplitude.WeightedSchwartzFourierFamily
import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactClassicalAmplitudeReduction

set_option autoImplicit false
set_option maxHeartbeats 5700000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal FourierTransform Topology

/-- The actual two-point amplitude with its input point held fixed. -/
def radianTwoPointParameter (a : E → E → E → ℂ) (y : E) (p : RadianParameter) : ℂ :=
  a p.1 y p.2

/-- The usual compact amplitude estimates in normalized directional
form. A frequency argument in the joint jet is scaled by the symbol
weight once for each occurrence. Input-base derivatives cost no
frequency power. -/
structure CompactRadianScaledOrderOne (a : E → E → E → ℂ) (Rx Ry : ℝ) : Prop
    extends CompactRadianTwoPointOrderOne a Rx Ry where
  scaledInputJetEstimate : ∀ m j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : RadianParameter, ∀ y : E,
    ‖iteratedFDeriv ℝ j (fun z =>
      radianScaledParameterJet (radianTwoPointParameter a z) m p) y‖ ≤ C*radianFrequencyWeight p.2

theorem radian_two_point_parameter_joint_smooth (a : E → E → E → ℂ)
    (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne a Rx Ry) :
    ContDiff ℝ ∞ (Function.uncurry (radianTwoPointParameter a)) := by
  let args (p : E × RadianParameter) : E × E × E := (p.2.1,p.1,p.2.2)
  have argsSmooth : ContDiff ℝ ∞ args := (contDiff_fst.comp contDiff_snd).prodMk
    (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd))
  change ContDiff ℝ ∞ ((fun p : E × E × E => a p.1 p.2.1 p.2.2) ∘ args)
  exact h.jointSmooth.comp argsSmooth

theorem radian_two_point_parameter_smooth (a : E → E → E → ℂ)
    (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne a Rx Ry) (y : E) :
    ContDiff ℝ ∞ (radianTwoPointParameter a y) :=
  (radian_two_point_parameter_joint_smooth a Rx Ry h).comp (contDiff_const.prodMk contDiff_id)

theorem radian_two_point_parameter_jet_joint_smooth (a : E → E → E → ℂ)
    (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne a Rx Ry) (n : ℕ) :
    ContDiff ℝ ∞ (fun q : E × RadianParameter =>
      iteratedFDeriv ℝ n (radianTwoPointParameter a q.1) q.2) :=
  smooth_right_slice_iterated_fderiv (radianTwoPointParameter a)
    (radian_two_point_parameter_joint_smooth a Rx Ry h) n

theorem radian_two_point_parameter_jet_zero_off_input
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne a Rx Ry)
    (n : ℕ) (y : E) (p : RadianParameter) (outside : y ∉ closedBall (0 : E) Ry) :
    iteratedFDeriv ℝ n (radianTwoPointParameter a y) p = 0 := by
  have zero : radianTwoPointParameter a y = (fun _ : RadianParameter => (0 : ℂ)) :=
    funext fun q => h.inputSupport q.1 y q.2 outside
  rw [zero,iteratedFDeriv_zero_fun,Pi.zero_apply]

private theorem scaled_parameter_jet_zero_off_input
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne a Rx Ry)
    (n : ℕ) (y : E) (p : RadianParameter) (outside : y ∉ closedBall (0 : E) Ry) :
    radianScaledParameterJet (radianTwoPointParameter a y) n p = 0 := by
  unfold radianScaledParameterJet
  rw [radian_two_point_parameter_jet_zero_off_input a Rx Ry h n y p outside]
  rfl

/-- The actual scaled parameter jet is a Schwartz function of the fixed
compact input base variable. -/
def compactRadianScaledInputJet (a : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianTwoPointOrderOne a Rx Ry) (n : ℕ) (p : RadianParameter) :
    SchwartzMap E (RadianParameterJet n ℂ) := by
  let J (y : E) := radianScaledParameterJet (radianTwoPointParameter a y) n p
  let T := ContinuousMultilinearMap.compContinuousLinearMapL (G := ℂ)
    (fun _ : Fin n => radianParameterScale (radianFrequencyWeight p.2))
  have sub : tsupport J ⊆ closedBall (0 : E) Ry := by
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    by_contra out
    exact hy (scaled_parameter_jet_zero_off_input a Rx Ry h n y p out)
  have s : HasCompactSupport J :=
    (isCompact_closedBall (0 : E) Ry).of_isClosed_subset isClosed_closure sub
  have smooth : ContDiff ℝ ∞ J := by
    change ContDiff ℝ ∞ (T ∘ fun y => iteratedFDeriv ℝ n (radianTwoPointParameter a y) p)
    exact T.contDiff.comp ((radian_two_point_parameter_jet_joint_smooth a Rx Ry h n).comp
      (contDiff_id.prodMk contDiff_const))
  exact s.toSchwartzMap smooth

@[simp] theorem compact_radian_scaled_input_jet_apply (a : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianTwoPointOrderOne a Rx Ry) (n : ℕ) (p : RadianParameter) (y : E) :
    compactRadianScaledInputJet a Rx Ry h n p y =
      radianScaledParameterJet (radianTwoPointParameter a y) n p := rfl

theorem compact_radian_scaled_input_jet_seminorms
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianScaledOrderOne a Rx Ry) (n k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : RadianParameter,
      SchwartzMap.seminorm ℝ k j
        (compactRadianScaledInputJet a Rx Ry h.toCompactRadianTwoPointOrderOne n p) ≤
          C*radianFrequencyWeight p.2 := by
  obtain ⟨C,C0,B⟩ := h.scaledInputJetEstimate n j
  let R := max 0 Ry
  have R0 : 0 ≤ R := le_max_left _ _
  refine ⟨R^k*C,by positivity,fun p => ?_⟩
  have Fp := radian_frequency_weight_pos p.2
  apply SchwartzMap.seminorm_le_bound ℝ k j _ (by positivity)
  intro y
  change ‖y‖^k * ‖iteratedFDeriv ℝ j (fun z =>
    radianScaledParameterJet (radianTwoPointParameter a z) n p) y‖ ≤ _
  by_cases yin : y ∈ closedBall (0 : E) Ry
  · have q : ‖y‖ ≤ R :=
      (show ‖y‖ ≤ Ry from by simpa only [mem_closedBall,dist_zero_right] using yin).trans
        (le_max_right _ _)
    calc
      _ ≤ R^k * (C*radianFrequencyWeight p.2) := mul_le_mul
        (pow_le_pow_left₀ (norm_nonneg _) q k) (B p y) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have z : (fun y => radianScaledParameterJet (radianTwoPointParameter a y) n p) =ᶠ[𝓝 y]
        (fun _ : E => (0 : RadianParameterJet n ℂ)) := by
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds yin] with q hq
      exact scaled_parameter_jet_zero_off_input a Rx Ry h.toCompactRadianTwoPointOrderOne n q p hq
    rw [(z.iteratedFDeriv ℝ j).self_of_nhds,iteratedFDeriv_zero_fun,Pi.zero_apply,norm_zero,mul_zero]
    positivity

/-- Compactness and the original input derivatives provide rapid
Fourier decay of the genuine scaled jet slices. -/
theorem exists_compact_radian_scaled_input_jet_fourier_decay
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianScaledOrderOne a Rx Ry) (n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : RadianParameter, ∀ η : E,
      ‖𝓕 (compactRadianScaledInputJet a Rx Ry h.toCompactRadianTwoPointOrderOne n p :
        E → RadianParameterJet n ℂ) η‖ ≤ C*(1+‖η‖) ^ (-(N : ℝ))*radianFrequencyWeight p.2 :=
  exists_weighted_schwartz_family_fourier_decay
    (compactRadianScaledInputJet a Rx Ry h.toCompactRadianTwoPointOrderOne n)
    (fun p => radianFrequencyWeight p.2)
    (fun p => radian_frequency_weight_pos p.2)
    (compact_radian_scaled_input_jet_seminorms a Rx Ry h n) N

end Burnett.A03
