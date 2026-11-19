import Burnett.Analysis.SignedFourierWindow.SignedWindowAllLp
import Burnett.Analysis.CubicEnergy.JointMultiplier.BandPartition

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Metric Filter Set
open scoped Topology ContDiff ENNReal

def mikhlinBall : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩

def mikhlinWindow (ξ : E) : ℝ := mikhlinBall ξ - mikhlinBall ((2:ℝ) • ξ)

private theorem inside (ξ : E) (h : ‖ξ‖ ≤ 1) : mikhlinBall ξ = 1 :=
  mikhlinBall.one_of_mem_closedBall (by simpa only [mem_closedBall,dist_zero_right] using h)

private theorem outside (ξ : E) (h : 2 ≤ ‖ξ‖) : mikhlinBall ξ = 0 :=
  mikhlinBall.zero_of_le_dist (by simpa only [dist_zero_right] using h)

private theorem at_small (ξ : E) (h : ‖ξ‖ ≤ 1/2) : mikhlinWindow ξ = 0 := by
  rw [mikhlinWindow,inside ξ (by linarith),inside _ ?_,sub_self]
  rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  linarith

private theorem at_large (ξ : E) (h : 2 ≤ ‖ξ‖) : mikhlinWindow ξ = 0 := by
  rw [mikhlinWindow,outside ξ h,outside _ ?_,sub_self]
  rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  linarith

theorem mikhlin_profile_exists (m : E → ℝ) (hm : ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0}) :
    ∃ a : SchwartzMap E ℂ, (∀ ξ, a ξ = ((mikhlinWindow ξ * m ξ : ℝ) : ℂ)) ∧
      HasCompactSupport (a : E → ℂ) ∧ (∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) := by
  let A : E → ℂ := fun ξ => ((mikhlinWindow ξ * m ξ : ℝ) : ℂ)
  have support : HasCompactSupport A := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:E) 2)
    intro ξ hξ
    by_contra h
    have hx : 2 < ‖ξ‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using h
    exact hξ (by simp [A,at_large ξ hx.le])
  have cw : ContDiff ℝ ∞ mikhlinWindow :=
    mikhlinBall.contDiff.sub (mikhlinBall.contDiff.comp (contDiff_const.smul contDiff_id))
  have smooth : ContDiff ℝ ∞ A := by
    apply contDiff_iff_contDiffAt.mpr
    intro ξ
    by_cases hx : ξ=0
    · subst ξ
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E => (0:ℂ)) 0).congr_of_eventuallyEq
      filter_upwards [ball_mem_nhds (0:E) (by norm_num : 0 < (1:ℝ)/2)] with v hv
      have hv' : ‖v‖ < 1/2 := by simpa only [mem_ball,dist_zero_right] using hv
      simp [A,at_small v hv'.le]
    · exact Complex.ofRealCLM.contDiff.contDiffAt.comp ξ
        (cw.contDiffAt.mul (hm.contDiffAt (isOpen_compl_singleton.mem_nhds hx)))
  refine ⟨support.toSchwartzMap smooth,fun _ => rfl,support,?_⟩
  intro ξ hn
  change A ξ ≠ 0 at hn
  constructor
  · by_contra! h
    exact hn (by simp [A,at_small ξ h])
  · by_contra! h
    exact hn (by simp [A,at_large ξ h])

/-- The finite band multiplier has precisely its two endpoint cutoffs. -/
theorem mikhlin_telescope (m : E → ℝ) (hh : ∀ t : ℝ, 0<t → ∀ ξ, m (t • ξ) = m ξ)
    (a : SchwartzMap E ℂ) (ha : ∀ ξ, a ξ = ((mikhlinWindow ξ * m ξ : ℝ) : ℂ))
    (t : ℝ) (ht : 0<t) (ξ : E) (l : ℕ) :
    (∑ k ∈ Finset.range l, a (((2:ℝ)^k*t) • ξ)) =
      ((mikhlinBall (t • ξ) - mikhlinBall (((2:ℝ)^l*t) • ξ) : ℝ) : ℂ) * (m ξ : ℂ) := by
  induction l with
  | zero => simp
  | succ l ih =>
    have hs : 0 < (2:ℝ)^l*t := mul_pos (by positivity) ht
    rw [Finset.sum_range_succ,ih,ha,hh _ hs,mikhlinWindow,smul_smul,pow_succ',
      ← mul_assoc 2 ((2:ℝ)^l) t]
    push_cast
    ring

theorem mikhlin_scale_partition (m : E → ℝ) (hh : ∀ t : ℝ, 0<t → ∀ ξ, m (t • ξ) = m ξ)
    (a : SchwartzMap E ℂ) (ha : ∀ ξ, a ξ = ((mikhlinWindow ξ * m ξ : ℝ) : ℂ))
    (ξ : E) (hne : ξ ≠ 0) :
    ∀ᶠ N : ℕ in atTop, (∑ k ∈ Finset.range (N+N), a (bandFactor N k • ξ)) = (m ξ : ℂ) := by
  have hn := norm_pos_iff.mpr hne
  have big := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).eventually
    (eventually_ge_atTop (max ‖ξ‖ (2/‖ξ‖)))
  filter_upwards [big] with N hN
  have hd : 0 < (2:ℝ)^N := pow_pos (by norm_num) _
  have lo : ‖((2:ℝ)^N)⁻¹ • ξ‖ ≤ 1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
    exact (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hN) (inv_nonneg.mpr hd.le)).trans_eq
      (inv_mul_cancel₀ hd.ne')
  have hi : 2 ≤ ‖(2:ℝ)^N • ξ‖ := by
    rw [norm_smul,Real.norm_of_nonneg hd.le]
    exact (div_le_iff₀ hn).mp ((le_max_right _ _).trans hN)
  have collapse : (2:ℝ)^(N+N)*((2:ℝ)^N)⁻¹ = (2:ℝ)^N := by
    rw [pow_add,mul_assoc,mul_inv_cancel₀ hd.ne',mul_one]
  simp only [bandFactor,mikhlin_telescope m hh a ha _ (inv_pos.mpr hd),collapse,inside _ lo,outside _ hi,
    sub_zero,Complex.ofReal_one,one_mul]

end Burnett.A02.FrequencySplit
