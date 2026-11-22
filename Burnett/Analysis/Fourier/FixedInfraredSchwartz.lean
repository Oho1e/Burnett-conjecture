import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency
import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWindowTest
import Burnett.Analysis.ShiftedFourierWindow.LowPassLp

set_option autoImplicit false
set_option maxHeartbeats 3800000

noncomputable section

namespace Burnett.A07

open Filter Set Metric MeasureTheory
open Burnett.A02.FrequencySplit (E radianFourier radianFourier_scaled tau windowTest
  windowTest_fourier windowTest_translate)
open Burnett.Analysis.CenteredMaximal (maximalConstant maximalConstant_finite)
open Burnett.Analysis.ShiftedFourierWindow
open scoped Topology ContDiff FourierTransform ENNReal

private theorem infrared_tau_positive : 0 < tau := mul_pos (by norm_num) Real.pi_pos

private def lowInfraredComplement (η : ℝ → ℝ) (p : E) : ℂ :=
  ((1 - η (tau * ‖p‖) : ℝ) : ℂ)

private theorem lowInfraredComplement_contDiff
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) {r : ℝ} (hr : 0 < r)
    (hzero : ∀ s ≤ r, η s = 0) :
    ContDiff ℝ ∞ (lowInfraredComplement η) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p = 0
  · have hsmall : tau * ‖p‖ < r := by simpa [hp] using hr
    have hnear := (isOpen_lt (continuous_const.mul continuous_norm) continuous_const).mem_nhds hsmall
    refine (contDiffAt_const (c := (1 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hnear] with q hq
    simp [lowInfraredComplement, hzero _ hq.le]
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp p
      (contDiffAt_const.sub <| hη.contDiffAt.comp p <|
        contDiffAt_const.mul (contDiffAt_id.norm ℝ hp))

private theorem lowInfraredComplement_hasCompactSupport
    (η : ℝ → ℝ) {R : ℝ} (hone : ∀ s ≥ R, η s = 1) :
    HasCompactSupport (lowInfraredComplement η) := by
  have hsupport : Function.support (lowInfraredComplement η) ⊆
      closedBall (0 : E) (R / tau) := by
    intro p hp
    by_contra hout
    rw [mem_closedBall_zero_iff] at hout
    have hlarge : R ≤ tau * ‖p‖ := by
      have h := (div_lt_iff₀ infrared_tau_positive).mp (lt_of_not_ge hout)
      simpa only [mul_comm] using h.le
    exact hp (by simp [lowInfraredComplement, hone _ hlarge])
  exact (isCompact_closedBall (0 : E) (R / tau)).of_isClosed_subset isClosed_closure
    (closure_minimal hsupport isClosed_closedBall)

private def lowInfraredSchwartz (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η)
    (r R : ℝ) (hr : 0 < r) (hzero : ∀ s ≤ r, η s = 0) (hone : ∀ s ≥ R, η s = 1) :
    SchwartzMap E ℂ :=
  (lowInfraredComplement_hasCompactSupport η hone).toSchwartzMap
    (lowInfraredComplement_contDiff η hη hr hzero)

/-- The actual fixed high infrared multiplier takes a Schwartz field to
itself minus the compact low-frequency complement evaluated by A02's window. -/
def fixedInfraredSchwartz (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η)
    (r R : ℝ) (hr : 0 < r) (hzero : ∀ s ≤ r, η s = 0) (hone : ∀ s ≥ R, η s = 1)
    (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  f - windowTest (lowInfraredSchwartz η hη r R hr hzero hone) f 1

private theorem fixedInfraredSchwartz_fourier
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (r R : ℝ) (hr : 0 < r)
    (hzero : ∀ s ≤ r, η s = 0) (hone : ∀ s ≥ R, η s = 1)
    (f : SchwartzMap E ℂ) (p : E) :
    𝓕 (fixedInfraredSchwartz η hη r R hr hzero hone f : E → ℂ) p =
      (η (tau * ‖p‖) : ℂ) * 𝓕 (f : E → ℂ) p := by
  let φ := lowInfraredSchwartz η hη r R hr hzero hone
  change SchwartzMap.fourierTransformCLM ℂ (f - windowTest φ f 1) p = _
  rw [map_sub, SchwartzMap.sub_apply]
  change 𝓕 (f : E → ℂ) p - 𝓕 (windowTest φ f 1 : E → ℂ) p = _
  rw [windowTest_fourier, one_smul]
  change 𝓕 (f : E → ℂ) p - 𝓕 (f : E → ℂ) p * ((1 - η (tau * ‖p‖) : ℝ) : ℂ) = _
  rw [Complex.ofReal_sub, Complex.ofReal_one]
  ring

theorem fixedInfraredSchwartz_radianFourier
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (r R : ℝ) (hr : 0 < r)
    (hzero : ∀ s ≤ r, η s = 0) (hone : ∀ s ≥ R, η s = 1)
    (f : SchwartzMap E ℂ) (p : E) :
    radianFourier (fixedInfraredSchwartz η hη r R hr hzero hone f) p =
      (η ‖p‖ : ℂ) * radianFourier f p := by
  have hscale : tau • (tau⁻¹ • p) = p := by
    rw [smul_smul, mul_inv_cancel₀ infrared_tau_positive.ne', one_smul]
  have ht : tau * ‖tau⁻¹ • p‖ = ‖p‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr infrared_tau_positive.le),
      ← mul_assoc, mul_inv_cancel₀ infrared_tau_positive.ne', one_mul]
  calc
    _ = 𝓕 (fixedInfraredSchwartz η hη r R hr hzero hone f : E → ℂ) (tau⁻¹ • p) := by
      rw [← radianFourier_scaled, hscale]
    _ = _ := by rw [fixedInfraredSchwartz_fourier, ht, ← radianFourier_scaled, hscale]

/-- At every finite exponent greater than one, the fixed high-pass operator is bounded
by the single-window maximal estimate at scale one and shift zero. -/
theorem exists_fixedInfraredSchwartz_Lp_bound
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (r R : ℝ) (hr : 0 < r)
    (hzero : ∀ s ≤ r, η s = 0) (hone : ∀ s ≥ R, η s = 1)
    (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : SchwartzMap E ℂ,
      eLpNorm (fixedInfraredSchwartz η hη r R hr hzero hone f : E → ℂ) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume := by
  let φ := lowInfraredSchwartz η hη r R hr hzero hone
  obtain ⟨K, hK, est⟩ := maximalShiftedWindow_Lp φ
  let D := K * maximalConstant p ^ (1 / p)
  have hD : D < ⊤ :=
    ENNReal.mul_lt_top hK
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) (maximalConstant_finite p).ne)
  refine ⟨1+D, ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hD⟩, ?_⟩
  intro f
  have hpoint (x : E) : ‖windowTest φ f 1 x‖ₑ ≤ maximalShiftedWindow φ f 0 x := by
    have eq := windowTest_translate φ f 1 1 one_pos x (0 : E)
    simp only [smul_zero, sub_zero] at eq
    rw [eq]
    exact le_iSup_of_le ⟨1, one_pos⟩ le_rfl
  have hw : eLpNorm (windowTest φ f 1 : E → ℂ) (ENNReal.ofReal p) volume ≤
      D * eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume := by
    calc
      _ ≤ eLpNorm (maximalShiftedWindow φ f 0) (ENNReal.ofReal p) volume :=
        eLpNorm_mono_enorm (fun x => by simpa only [enorm_eq_self] using hpoint x)
      _ ≤ _ := by simpa [D] using est f (0 : E) p hp
  change eLpNorm ((f : E → ℂ) - (windowTest φ f 1 : E → ℂ)) (ENNReal.ofReal p) volume ≤ _
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  calc
    _ ≤ eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume +
        eLpNorm (windowTest φ f 1 : E → ℂ) (ENNReal.ofReal p) volume :=
      eLpNorm_sub_le f.continuous.aestronglyMeasurable
        (windowTest φ f 1).continuous.aestronglyMeasurable hp1
    _ ≤ _ := by rw [add_mul, one_mul]; exact add_le_add_left hw _

end Burnett.A07
