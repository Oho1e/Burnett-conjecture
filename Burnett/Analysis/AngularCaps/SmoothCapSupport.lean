import Burnett.Analysis.AngularCaps.SmoothCapSymbols

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set Finset Function
open scoped ContDiff

theorem capMultiplier_nonzero_bounds {t : Finset Vec} {m : Form} {δ η inner outer : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hIn : 0 ≤ inner) (hIO : inner < outer) {w ξ : Vec}
    (h : capMultiplier t m δ η inner outer w ξ ≠ 0) :
    ξ ≠ 0 ∧ projectiveWedgeSq ξ w < δ^2 ∧ |quadratic m ξ| < outer*η*‖ξ‖^2 := by
  have hξ : ξ ≠ 0 := fun he => h (by simp [he])
  rw [capMultiplier_at_nonzero _ _ _ _ _ _ _ hξ] at h
  have hFactors := mul_ne_zero_iff.mp h
  have hAngle : capAngularProfile δ (3/4) 1 w ξ ≠ 0 :=
    fun hz => hFactors.2 (by rw [hz,zero_div])
  have hAngle' : projectiveWedgeSq ξ w < δ^2 := by
    simpa only [one_mul] using capAngularProfile_nonzero_angle hδ
      (show (0 : ℝ) ≤ 3/4 by norm_num) (show (3/4 : ℝ) < 1 by norm_num) hAngle
  exact ⟨hξ,hAngle',thinConeProfile_nonzero_cone hη hIn hIO hξ hFactors.1⟩

theorem enlargedCapMultiplier_nonzero_bounds {m : Form} {δ η outer enlarged : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hOut : 0 ≤ outer) (hOE : outer < enlarged) {w ξ : Vec}
    (h : enlargedCapMultiplier m δ η outer enlarged w ξ ≠ 0) :
    ξ ≠ 0 ∧ projectiveWedgeSq ξ w < (5*δ)^2 ∧ |quadratic m ξ| < enlarged*η*‖ξ‖^2 := by
  have hξ : ξ ≠ 0 := fun he => h (by simp [he])
  rw [enlargedCapMultiplier_at_nonzero _ _ _ _ _ _ hξ] at h
  have hFactors := mul_ne_zero_iff.mp h
  exact ⟨hξ,capAngularProfile_nonzero_angle hδ
    (show (0 : ℝ) ≤ 4 by norm_num) (show (4 : ℝ) < 5 by norm_num) hFactors.2,
    thinConeProfile_nonzero_cone hη hOut hOE hξ hFactors.1⟩

private theorem upper_bound_mem_closure {S : Set Vec} {ξ : Vec} {f : Vec → ℝ} {b : ℝ}
    (hξ : ξ ∈ closure S) (hc : ContinuousAt f ξ) (h : ∀ x ∈ S, f x ≤ b) : f ξ ≤ b := by
  have hMap : MapsTo f S (Iic b) := fun x hx => h x hx
  have hT := hc.continuousWithinAt.mem_closure hξ hMap
  rw [isClosed_Iic.closure_eq] at hT
  exact hT

private theorem cap_closed_bounds {σ : Vec → ℝ} {m : Form} {η outer radius : ℝ} {w ξ : Vec}
    (hw : w ≠ 0) (hξ : ξ ≠ 0) (hSupp : ξ ∈ tsupport σ)
    (h : ∀ x, σ x ≠ 0 → projectiveWedgeSq x w ≤ radius^2 ∧ |quadratic m x| ≤ outer*η*‖x‖^2) :
    projectiveWedgeSq ξ w ≤ radius^2 ∧ |quadratic m ξ| ≤ outer*η*‖ξ‖^2 := by
  have hW : ContinuousAt (fun x => projectiveWedgeSq x w) ξ :=
    (projectiveWedgeSq_contDiffOn_left hw).continuousOn.continuousAt
      (isOpen_puncturedFrequency.mem_nhds hξ)
  have hC : Continuous (fun x : Vec => |quadratic m x| - outer*η*‖x‖^2) :=
    (quadratic_contDiff m).continuous.abs.sub (continuous_const.mul (continuous_norm.pow 2))
  have hW' := upper_bound_mem_closure (f := fun x => projectiveWedgeSq x w) hSupp hW
    (fun x hx => (h x hx).1)
  have hC' : |quadratic m ξ| - outer*η*‖ξ‖^2 ≤ 0 :=
    upper_bound_mem_closure hSupp hC.continuousAt (fun x hx => sub_nonpos.mpr (h x hx).2)
  exact ⟨hW',sub_nonpos.mp hC'⟩

theorem capMultiplier_tsupport_bounds {t : Finset Vec} {m : Form} {δ η inner outer : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hIn : 0 ≤ inner) (hIO : inner < outer) {w ξ : Vec}
    (hw : w ≠ 0) (hξ : ξ ≠ 0) (hSupp : ξ ∈ tsupport (capMultiplier t m δ η inner outer w)) :
    projectiveWedgeSq ξ w ≤ δ^2 ∧ |quadratic m ξ| ≤ outer*η*‖ξ‖^2 := by
  refine cap_closed_bounds hw hξ hSupp (fun x hNZ => ?_)
  have h := capMultiplier_nonzero_bounds hδ hη hIn hIO hNZ
  exact ⟨h.2.1.le,h.2.2.le⟩

theorem enlargedCapMultiplier_tsupport_bounds {m : Form} {δ η outer enlarged : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hOut : 0 ≤ outer) (hOE : outer < enlarged) {w ξ : Vec}
    (hw : w ≠ 0) (hξ : ξ ≠ 0) (hSupp : ξ ∈ tsupport (enlargedCapMultiplier m δ η outer enlarged w)) :
    projectiveWedgeSq ξ w ≤ (5*δ)^2 ∧ |quadratic m ξ| ≤ enlarged*η*‖ξ‖^2 := by
  refine cap_closed_bounds hw hξ hSupp (fun x hNZ => ?_)
  have h := enlargedCapMultiplier_nonzero_bounds hδ hη hOut hOE hNZ
  exact ⟨h.2.1.le,h.2.2.le⟩

theorem enlargedCapMultiplier_eq_one_on_capSupport {t : Finset Vec} {m : Form}
    {δ η inner outer enlarged : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hIn : 0 ≤ inner)
    (hIO : inner < outer) (hOE : outer < enlarged) {w ξ : Vec} (hw : w ≠ 0) (hξ : ξ ≠ 0)
    (hSupp : ξ ∈ tsupport (capMultiplier t m δ η inner outer w)) :
    enlargedCapMultiplier m δ η outer enlarged w ξ = 1 := by
  have h := capMultiplier_tsupport_bounds hδ hη hIn hIO hw hξ hSupp
  have hScale : δ^2 ≤ (4*δ)^2 :=
    pow_le_pow_left₀ hδ.le (by linarith only [hδ]) 2
  exact enlargedCapMultiplier_eq_one m hδ hη (hIn.trans hIO.le) hOE hξ (h.1.trans hScale) h.2

/-- The enlarged multiplier is exactly one on all three near slots having
the designated cap index and the fixed outer cone bound on the other slots. -/
theorem enlargedCapMultiplier_eq_one_on_three_nearSlots {t : Finset Vec} {m : Form}
    {δ η inner outer enlarged : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hIn : 0 ≤ inner)
    (hIO : inner < outer) (hOE : outer < enlarged) {w p q r : Vec}
    (hw : w ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hCap : p ∈ tsupport (capMultiplier t m δ η inner outer w))
    (hPQ : projectiveWedgeSq p q ≤ δ^2) (hPR : projectiveWedgeSq p r ≤ δ^2)
    (hQ : |quadratic m q| ≤ outer*η*‖q‖^2) (hR : |quadratic m r| ≤ outer*η*‖r‖^2) :
    enlargedCapMultiplier m δ η outer enlarged w p = 1 ∧
      enlargedCapMultiplier m δ η outer enlarged w q = 1 ∧
      enlargedCapMultiplier m δ η outer enlarged w r = 1 := by
  have h := capMultiplier_tsupport_bounds hδ hη hIn hIO hw hp hCap
  have hNear := near_wedge_slots_same_wedge_enlargement hδ hp hq hr hw h.1 hPQ hPR
  have hOut := hIn.trans hIO.le
  exact ⟨enlargedCapMultiplier_eq_one_on_capSupport hδ hη hIn hIO hOE hw hp hCap,
    enlargedCapMultiplier_eq_one m hδ hη hOut hOE hq hNear.1 hQ,
    enlargedCapMultiplier_eq_one m hδ hη hOut hOE hr hNear.2 hR⟩

/-- At a fixed frequency, this counts cap labels whose closed support meets it. -/
def capSupportCenters (t : Finset Vec) (σ : Vec → Vec → ℝ) (ξ : Vec) : Finset Vec := by
  classical
  exact t.filter fun w => ξ ∈ tsupport (σ w)

theorem capSupportCenters_card_le_wedge {t : Finset Vec} {σ : Vec → Vec → ℝ} {ξ : Vec} {radius : ℝ}
    (h : ∀ w ∈ t, ξ ∈ tsupport (σ w) → projectiveWedgeSq ξ w ≤ radius^2) :
    ((capSupportCenters t σ ξ).card : ℝ) ≤ ((wedgeCentersMeeting t ξ radius).card : ℝ) := by
  classical
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro w hw
  simp only [capSupportCenters,Finset.mem_filter] at hw
  simp only [wedgeCentersMeeting,Finset.mem_filter]
  exact ⟨hw.1,h w hw.1 hw.2⟩

end Burnett.Analysis.ProjectiveNullCaps
