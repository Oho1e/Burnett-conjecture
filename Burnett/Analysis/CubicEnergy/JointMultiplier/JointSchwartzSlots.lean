import Burnett.Analysis.CubicEnergy.JointMultiplier.JointSlotPartition

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Finset
open scoped ContDiff

/-- Both low radii use one Schwartz window. The same even annular window
serves all three slots. The output frequency is written with the negative
sign of the bilinear Fourier pairing, including the case where it vanishes. -/
theorem symbolBlock_schwartz_slots :
    ∃ (a d : SchwartzMap E ℂ), HasCompactSupport (a : E → ℂ) ∧
      (∀ z, a z ≠ 0 → 1/2 < ‖z‖ ∧ ‖z‖ < 2) ∧
      (∀ z, a (-z) = a z) ∧ (∀ z, d (-z) = d z) ∧
      ∀ (m : Joint → ℝ) (s : ℝ) (η ξ : E),
      let H := fun z : E => ∑ k ∈ range 7, a (((2:ℝ)^k*(s/4)) • z)
      let L := fun z : E => d ((32*s) • z)
      let W := fun z : E => d ((s/4) • z)
      let M := symbolBlock m (s • η,s • ξ)
      M = M*(H η*H ξ*W (-(η+ξ)) + L η*H ξ*H (-(η+ξ)) + H η*L ξ*H (-(η+ξ))) := by
  obtain ⟨a,ha,hc,cut⟩ := mikhlin_profile_exists (fun _ => (1:ℝ)) contDiffOn_const
  let d' : E → ℂ := fun z => (mikhlinBall z : ℂ)
  have hd : HasCompactSupport d' :=
    mikhlinBall.hasCompactSupport.comp_left (show ((0:ℝ):ℂ)=0 by simp)
  let d := hd.toSchwartzMap (Complex.ofRealCLM.contDiff.comp mikhlinBall.contDiff)
  have de (z : E) : d z = (mikhlinBall z : ℂ) := rfl
  have ea (z : E) : a (-z) = a z := by
    rw [ha,ha]; simp only [mikhlinWindow,smul_neg,ContDiffBump.neg]
  have ed (z : E) : d (-z) = d z := by simp only [de,ContDiffBump.neg]
  refine ⟨a,d,hc,cut,ea,ed,?_⟩
  intro m s η ξ
  have high (z : E) : (slotHigh (s • z) : ℂ) = ∑ k ∈ range 7, a (((2:ℝ)^k*(s/4)) • z) := by
    have tel := mikhlin_telescope (fun _ => (1:ℝ)) (fun _ _ _ => rfl) a ha (1/4) (by norm_num) (s • z) 7
    simp only [show (2:ℝ)^7*(1/4)=32 by norm_num,Complex.ofReal_one,mul_one] at tel
    unfold slotHigh slotWhole slotLow
    rw [← tel]
    apply sum_congr rfl
    intro k _
    rw [smul_smul]
    rw [show 2^k*(1/4:ℝ)*s = 2^k*(s/4) by ring]
  have low (z : E) : (slotLow (s • z) : ℂ) = d ((32*s) • z) := by
    simp only [slotLow,smul_smul,de]
  have whole (z : E) : (slotWhole (s • z) : ℂ) = d ((s/4) • z) := by
    simp only [slotWhole,smul_smul,de,show (1/4:ℝ)*s=s/4 by ring]
  have part := symbolBlock_three_slots m (s • η) (s • ξ)
  dsimp only at part ⊢
  push_cast at part
  simpa only [← smul_add,high,low,whole,smul_neg,ed,ea] using part

end Burnett.A02.FrequencySplit
