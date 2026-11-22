import Burnett.Analysis.AngularCaps.ParabolicCapSupport
import Burnett.Analysis.AngularCaps.SmoothCapSupport

set_option autoImplicit false
set_option maxHeartbeats 11000000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set Filter Function
open scoped ContDiff Topology BigOperators

def activeAngularCenters (t : Finset Vec) (δ : ℝ) (ξ : Vec) : Finset Vec :=
  capSupportCenters t (capAngularProfile δ (3/4) 1) ξ

theorem angularProfile_tsupport_angle {δ : ℝ} (hδ : 0 < δ) {w ξ : Vec} (hw : w ≠ 0) (hξ : ξ ≠ 0)
    (h : ξ ∈ tsupport (capAngularProfile δ (3/4) 1 w)) : projectiveWedgeSq ξ w ≤ δ^2 := by
  have hC : ContinuousAt (fun x => projectiveWedgeSq x w) ξ :=
    (projectiveWedgeSq_contDiffOn_left hw).continuousOn.continuousAt (isOpen_puncturedFrequency.mem_nhds hξ)
  have hMap : MapsTo (fun x => projectiveWedgeSq x w)
      (Function.support (capAngularProfile δ (3/4) 1 w)) (Iic (δ^2)) := by
    intro x hx
    have hB := capAngularProfile_nonzero_angle hδ (show (0:ℝ) ≤ 3/4 by norm_num)
      (show (3/4:ℝ) < 1 by norm_num) (show capAngularProfile δ (3/4) 1 w x ≠ 0 from hx)
    simpa only [Set.mem_Iic,one_mul] using hB.le
  have ht := hC.continuousWithinAt.mem_closure h hMap
  rw [isClosed_Iic.closure_eq] at ht
  exact ht

/-- Outside the closed support of an angular weight that weight is zero
on a neighborhood. Hence the actual denominator can be restricted locally
to this one finite set, without altering any derivative at the tested point. -/
theorem capAngularMass_locally_active (t : Finset Vec) (δ : ℝ) (ξ : Vec) :
    capAngularMass t δ =ᶠ[𝓝 ξ] capAngularMass (activeAngularCenters t δ ξ) δ := by
  classical
  have hEv : ∀ᶠ x in 𝓝 ξ, ∀ w ∈ t,
      ξ ∉ tsupport (capAngularProfile δ (3/4) 1 w) → capAngularProfile δ (3/4) 1 w x = 0 := by
    rw [eventually_all_finset]
    intro w _
    by_cases hw : ξ ∈ tsupport (capAngularProfile δ (3/4) 1 w)
    · exact Filter.Eventually.of_forall fun _ h => (h hw).elim
    · exact (notMem_tsupport_iff_eventuallyEq.mp hw).mono fun _ hz _ => hz
  filter_upwards [hEv] with x hx
  unfold capAngularMass activeAngularCenters capSupportCenters
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun w hw => by
    by_cases h : ξ ∈ tsupport (capAngularProfile δ (3/4) 1 w)
    · rw [if_pos h]
    · rw [if_neg h]
      exact hx w hw h

theorem capMultiplier_locally_active (t : Finset Vec) (m : Form) (δ η inner outer : ℝ) (w ξ : Vec) :
    capMultiplier t m δ η inner outer w =ᶠ[𝓝 ξ]
      capMultiplier (activeAngularCenters t δ ξ) m δ η inner outer w := by
  filter_upwards [capAngularMass_locally_active t δ ξ] with x hx
  by_cases h : x = 0
  · simp [h]
  · rw [capMultiplier_at_nonzero _ _ _ _ _ _ _ h,capMultiplier_at_nonzero _ _ _ _ _ _ _ h,
      capDenominator,capDenominator,hx]

private theorem norm_one_ne_zero {w : Vec} (hw : ‖w‖ = 1) : w ≠ 0 := by
  intro h
  simp [h] at hw

theorem activeAngularCenters_card_le {t : Finset Vec} {δ : ℝ} (hδ : 0 < δ)
    (hUnit : ∀ w ∈ t, ‖w‖ = 1) (hSep : (↑t : Set Vec).Pairwise (fun v w => δ/4 < projectiveDist v w))
    {ξ : Vec} (hξ : ξ ≠ 0) :
    ((activeAngularCenters t δ ξ).card : ℝ) ≤ 17^4 := by
  have hSubset : activeAngularCenters t δ ξ ⊆ centersMeeting t (unitRep ξ) (4*(δ/2)) := by
    classical
    intro w hw
    simp only [activeAngularCenters,capSupportCenters,Finset.mem_filter] at hw
    simp only [centersMeeting,Finset.mem_filter]
    have hUnitW := hUnit w hw.1
    have h := angularProfile_tsupport_angle hδ (norm_one_ne_zero hUnitW) hξ hw.2
    have hP := projectiveDist_unitRep_le_of_wedgeSq_le hξ (norm_one_ne_zero hUnitW) hδ.le h
    have hRep : unitRep w = w := by simp [unitRep,hUnitW]
    rw [hRep] at hP
    exact ⟨hw.1,hP.trans_eq (by ring)⟩
  have hC : ((activeAngularCenters t δ ξ).card : ℝ) ≤
      ((centersMeeting t (unitRep ξ) (4*(δ/2))).card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card hSubset)
  have hSep' : (↑t : Set Vec).Pairwise (fun v w => (δ/2)/2 < projectiveDist v w) := by
    intro v hv w hw hne
    have h := hSep hv hw hne
    linarith only [h]
  have hOverlap := projectiveCaps_bounded_overlap (div_pos hδ zero_lt_two) hSep'
    4 (by norm_num) (unitRep ξ)
  exact hC.trans (by simpa only [show (4:ℝ)*4+1 = 17 by norm_num] using hOverlap)

/-- All centers relevant to the local denominator of one cap have uniformly
bounded scaled coordinates in its chart. Their radial coordinates stay
away from zero, including both possible signs. -/
theorem activeAngularCenter_scaled_bounds {t : Finset Vec} {m : Form} {w ξ z : Vec}
    (F : NullCapChart m w) {B δ : ℝ} (hI : ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B)
    (hδ : 0 < δ) (hSmall : 4*B*(4*δ) ≤ 1)
    (ht : (↑t : Set Vec) ⊆ unitNull m) (hw : ‖w‖ = 1) (hξ : ξ ≠ 0)
    (hW : projectiveWedgeSq ξ w ≤ δ^2) (hz : z ∈ activeAngularCenters t δ ξ) :
    let v := parabolicRescale δ (F.toFrequency.symm z)
    1/2 ≤ |v.1| ∧ |v.1| ≤ B ∧ ‖v.2.2‖ ≤ 16*B^2 ∧ |v.2.1| ≤ (16*B)^2*B := by
  have hz' : z ∈ t ∧ ξ ∈ tsupport (capAngularProfile δ (3/4) 1 z) := by
    classical
    simpa only [activeAngularCenters,capSupportCenters,Finset.mem_filter] using hz
  have hzNull : z ∈ unitNull m := ht hz'.1
  have hz0 := norm_one_ne_zero hzNull.1
  have hXZ := angularProfile_tsupport_angle hδ hz0 hξ hz'.2
  have hZW := (near_wedge_slots_same_wedge_enlargement hδ hξ hz0 hz0 (norm_one_ne_zero hw)
    hW hXZ hXZ).1
  have hQ : |quadratic m z| ≤ (0:ℝ)*δ^2*‖z‖^2 := by rw [hzNull.2]; simp
  obtain ⟨hs,hs',hZ,hT⟩ := scaled_cap_coordinate_bounds F hI (show (0:ℝ) ≤ 4 by norm_num)
    hδ (show (0:ℝ) ≤ 0 from le_rfl) hSmall hw hz0 hZW hQ
  let v := parabolicRescale δ (F.toFrequency.symm z)
  have hsUpper : |v.1| ≤ B := by simpa only [hzNull.1,mul_one] using hs'
  have hZ' : ‖v.2.2‖ ≤ (16*B)*|v.1| := by convert hZ using 1; ring
  have hT' : |v.2.1| ≤ (16*B)^2*|v.1| := by convert hT using 1; ring
  have hB : 0 ≤ B := (norm_nonneg _).trans hI
  refine ⟨?_,hsUpper,hZ'.trans ?_,hT'.trans (mul_le_mul_of_nonneg_left hsUpper (sq_nonneg _))⟩
  · rw [hzNull.1] at hs
    linarith only [hs]
  · exact (mul_le_mul_of_nonneg_left hsUpper (mul_nonneg (by norm_num) hB)).trans_eq (by ring)

end Burnett.Analysis.ProjectiveNullCaps
