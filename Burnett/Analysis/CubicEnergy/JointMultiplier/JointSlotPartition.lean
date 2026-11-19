import Burnett.Analysis.CubicEnergy.JointMultiplier.MikhlinPartition
import Burnett.Analysis.CubicEnergy.JointMultiplier.BlockMultiplier

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Metric Finset
open scoped ContDiff RealInnerProductSpace

def slotWhole (ξ : E) : ℝ := mikhlinBall ((1/4:ℝ) • ξ)
def slotLow (ξ : E) : ℝ := mikhlinBall ((32:ℝ) • ξ)
def slotHigh (ξ : E) : ℝ := slotWhole ξ - slotLow ξ

private theorem norm_join (η ξ : E) :
    ‖splitFreq.symm (η,ξ)‖^2 = ‖η‖^2+‖ξ‖^2 := by
  simpa only [real_inner_self_eq_norm_sq,ContinuousLinearEquiv.apply_symm_apply] using
    splitFreq_inner (splitFreq.symm (η,ξ)) (splitFreq.symm (η,ξ))

private theorem support_joint (m : Joint → ℝ) (η ξ : E) (h : symbolBlock m (η,ξ) ≠ 0) :
    1/2 < ‖splitFreq.symm (η,ξ)‖ ∧ ‖splitFreq.symm (η,ξ)‖ < 2 := by
  let u := splitFreq.symm (η,ξ)
  have inn (z : Freq8) (hz : ‖z‖ ≤ 1) : ballWindow z=1 :=
    ballWindow.one_of_mem_closedBall (by simpa only [mem_closedBall,dist_zero_right] using hz)
  have out (z : Freq8) (hz : 2 ≤ ‖z‖) : ballWindow z=0 :=
    ballWindow.zero_of_le_dist (by simpa only [dist_zero_right] using hz)
  have scale : ‖(2:ℝ) • u‖=2*‖u‖ := by rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
  have ne : ballWindow u-ballWindow ((2:ℝ)•u) ≠ 0 := fun hz =>
    h (by change (( (ballWindow u-ballWindow ((2:ℝ)•u))*m (η,ξ) : ℝ) : ℂ)=0; simp [hz])
  constructor
  · by_contra! small
    exact ne (by rw [inn u (by change ‖u‖ ≤ 1/2 at small; linarith),inn _ (by rw [scale]; change ‖u‖ ≤ 1/2 at small; linarith),sub_self])
  · by_contra! big
    exact ne (by rw [out u big,out _ (by rw [scale]; change 2≤‖u‖ at big; linarith),sub_self])

private theorem whole_one (x : E) (hx : ‖x‖≤4) : slotWhole x = 1 := by
  apply mikhlinBall.one_of_mem_closedBall
  change dist ((1/4:ℝ) • x) 0 ≤ 1
  rw [dist_zero_right,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/4)]
  linarith

private theorem low_small (x : E) (hx : slotLow x ≠ 0) : ‖x‖ < 1/16 := by
  by_contra! h
  apply hx
  apply mikhlinBall.zero_of_le_dist
  change 2 ≤ dist ((32:ℝ) • x) 0
  rw [dist_zero_right,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤32)]
  linarith

/-- On the actual eight-dimensional joint annulus, at least two of the input,
input and sum-frequency slots are outside the tiny ball. This is an exact
three-term partition, including at zero product frequency. -/
theorem symbolBlock_three_slots (m : Joint → ℝ) (η ξ : E) :
    let M := symbolBlock m (η,ξ)
    M = M * ((slotHigh η * slotHigh ξ * slotWhole (η+ξ) +
      slotLow η * slotHigh ξ * slotHigh (η+ξ) + slotHigh η * slotLow ξ * slotHigh (η+ξ) : ℝ) : ℂ) := by
  by_cases h : symbolBlock m (η,ξ)=0
  · simp [h]
  obtain ⟨lo,hi⟩ := support_joint m η ξ h
  have eq := norm_join η ξ
  have non := norm_nonneg (splitFreq.symm (η,ξ))
  have hη : ‖η‖≤2 := by nlinarith [sq_nonneg ‖ξ‖,sq_nonneg (‖splitFreq.symm (η,ξ)‖ - 2),norm_nonneg η]
  have hξ : ‖ξ‖≤2 := by nlinarith [sq_nonneg ‖η‖,sq_nonneg (‖splitFreq.symm (η,ξ)‖ - 2),norm_nonneg ξ]
  have add := norm_add_le η ξ
  have join : ‖splitFreq.symm (η,ξ)‖ ≤ ‖η‖+‖ξ‖ := by
    nlinarith [mul_nonneg (norm_nonneg η) (norm_nonneg ξ),norm_nonneg η,norm_nonneg ξ]
  have subt : ‖ξ‖ ≤ ‖η+ξ‖+‖η‖ := by simpa using norm_sub_le (η+ξ) η
  have subu : ‖η‖ ≤ ‖η+ξ‖+‖ξ‖ := by simpa using norm_sub_le (η+ξ) ξ
  have hslots : slotHigh η * slotHigh ξ * slotWhole (η+ξ) +
      slotLow η * slotHigh ξ * slotHigh (η+ξ) + slotHigh η * slotLow ξ * slotHigh (η+ξ) = 1 := by
    simp only [slotHigh,whole_one η (by linarith),whole_one ξ (by linarith),whole_one (η+ξ) (by linarith)]
    by_cases h₁ : slotLow η=0
    · by_cases h₂ : slotLow ξ=0
      · simp [h₁,h₂]
      · have h₃ : slotLow (η+ξ)=0 := by by_contra hn; linarith [low_small _ h₂,low_small _ hn]
        rw [h₁,h₃]; ring
    · have h₂ : slotLow ξ=0 := by by_contra hn; linarith [low_small _ h₁,low_small _ hn]
      have h₃ : slotLow (η+ξ)=0 := by by_contra hn; linarith [low_small _ h₁,low_small _ hn]
      rw [h₂,h₃]; ring
  simp [hslots]

/-- Each broad high factor in the three-slot identity is exactly seven
ordinary annular windows at fixed dyadic offsets. -/
theorem slot_high_seven :
    ∃ a : SchwartzMap E ℂ, HasCompactSupport (a : E → ℂ) ∧ (∀ ξ, a ξ ≠ 0 → 1/2<‖ξ‖ ∧ ‖ξ‖<2) ∧
      ∀ ξ : E, (slotHigh ξ : ℂ) = ∑ k ∈ range 7, a (((2:ℝ)^k*(1/4)) • ξ) := by
  obtain ⟨a,ha,hc,cut⟩ := mikhlin_profile_exists (fun _ => (1:ℝ)) contDiffOn_const
  refine ⟨a,hc,cut,?_⟩
  intro ξ
  have tel := mikhlin_telescope (fun _ => (1:ℝ)) (fun _ _ _ => rfl) a ha (1/4) (by norm_num) ξ 7
  simpa only [slotHigh,slotWhole,slotLow,show (2:ℝ)^7*(1/4)=32 by norm_num,Complex.ofReal_one,mul_one] using tel.symm

end Burnett.A02.FrequencySplit
