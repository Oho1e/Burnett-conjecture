import Burnett.Analysis.AllScaleTransfer.CapCorrectionGeometry
import Burnett.Analysis.AllScaleTransfer.SignedCapEndpointM0
import Burnett.Analysis.AllScaleTransfer.PositiveRatioTrace
import Burnett.Analysis.AllScaleTransfer.LowPassCorrectionNormalized

set_option autoImplicit false
set_option maxHeartbeats 4800000
noncomputable section

namespace Burnett.A05

open Set Metric Filter Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier (frequencyCoordinates)
open Burnett.Analysis.LowRatio (Angles Point Window zeroRatioTraceExtension
  zeroRatioTraceExtension_jets_of_oneSidedC100)
open scoped ContDiff Topology Nat

def capCorrectionAngles (R : ℝ) : Set Angles :=
  ball (0 : EndpointAngle) R ×ˢ ball (0 : EndpointAngle) R

def capCorrectionTrace (α : ℝ) (M : E → E → ℝ → ℂ) : Joint → ℂ :=
  axialLocalizeEndpoint α (fun uv => M uv.1 uv.2 0)

private theorem sign_axis_continuous (sign : Bool) : Continuous (signedAxis sign) := by
  have h : Continuous (fun x : E => x 0) := frequencyCoordinates.continuous.fst
  cases sign
  · exact h.neg
  · exact h

private theorem sign_axis_exists {p : E} (hp : 0 < |p 0|) : ∃ s : Bool, 0 < signedAxis s p := by
  by_cases h : 0 < p 0
  · exact ⟨true,h⟩
  · have hp0 : p 0 ≠ 0 := abs_pos.mp hp
    have hn : p 0 < 0 := lt_of_le_of_ne (le_of_not_gt h) hp0
    exact ⟨false,neg_pos.mpr hn⟩

private theorem sign_chart_recovers (s : Bool) {p : E} (hp : p ≠ 0) (ha : 0 < signedAxis s p) :
    signedChartLift s (endpointTail (endpointDirection p)) = endpointDirection p := by
  apply signedChartLift_endpointTail s (endpointDirection_mem_sphere hp)
  have hInv : 0 < ‖p‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hp)
  cases s
  · change 0 < -(‖p‖⁻¹*p 0)
    change 0 < -(p 0) at ha
    rw [← mul_neg]
    exact mul_pos hInv ha
  · exact mul_pos hInv ha

/-- The same masked endpoint has the one-sided chart budget on the actual
correction domain, with one constant for all four signed pieces. -/
theorem exists_capCorrection_trace_budget (α R b : ℝ) (hα : 0 < α) (hb : 0 < b)
    {K : Set BoxSpace} (hK : IsCompact K) (hKV : K ⊆ capCorrectionDomain α R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : E → E → ℝ → ℂ) (A : ℝ), 0 ≤ A →
      (∀ s : CapSigns, ContDiffOn ℝ 100 (signedEndpointProfile M s)
        (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b)) →
      (∀ (s : CapSigns) n, n ≤ 100 → ∀ z ∈ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b,
        ‖iteratedFDerivWithin ℝ n (signedEndpointProfile M s)
          (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) z‖ ≤ A) →
      let E₀ (z : BoxSpace) := radianEndpointAngular (capCorrectionTrace α M) (firstInput z) (secondInput z)
      ContDiffOn ℝ 100 E₀ (capCorrectionDomain α R) ∧
      ∀ n ≤ 40, ∀ z ∈ K, ‖iteratedFDeriv ℝ n E₀ z‖ ≤ C*A := by
  let V := capCorrectionDomain α R
  let U := capCorrectionAngles R
  let W := Window U (-1) 1
  have hV := capCorrectionDomain_open α R
  have hU : IsOpen U := isOpen_ball.prod isOpen_ball
  have hW : IsOpen W := hU.prod isOpen_Ioo
  have hUbound : U ⊆ closedBall (0 : Angles) R := by
    intro x hx
    apply mem_closedBall_zero_iff.mpr
    rw [Prod.norm_def]
    exact max_le (mem_ball_zero_iff.mp hx.1).le (mem_ball_zero_iff.mp hx.2).le
  obtain ⟨D,hD,localized⟩ := exists_axialLocalizeChart_oneSidedC100_bound α R b U hU hUbound
  have sf : ContDiff ℝ ∞ firstInput := boxToPair.toContinuousLinearMap.contDiff.fst
  have sg : ContDiff ℝ ∞ secondInput := boxToPair.toContinuousLinearMap.contDiff.snd
  let Φ (z : BoxSpace) : Point :=
    ((endpointTail (endpointDirection (firstInput z)),endpointTail (endpointDirection (secondInput z))),0)
  have hΦ : ContDiffOn ℝ ∞ Φ V := by
    have p : ContDiffOn ℝ ∞ (fun z => endpointTail (endpointDirection (firstInput z))) V :=
      endpointTail.contDiff.comp_contDiffOn (endpointDirection_contDiffOn.comp sf.contDiffOn
        (fun _ hz => capCorrectionSlot_ne_zero (capCorrectionDomain_left_right hz).1))
    have q : ContDiffOn ℝ ∞ (fun z => endpointTail (endpointDirection (secondInput z))) V :=
      endpointTail.contDiff.comp_contDiffOn (endpointDirection_contDiffOn.comp sg.contDiffOn
        (fun _ hz => capCorrectionSlot_ne_zero (capCorrectionDomain_left_right hz).2))
    exact (p.prodMk q).prodMk contDiffOn_const
  have mapΦ : MapsTo Φ V W := by
    intro z hz
    obtain ⟨hp,hq⟩ := capCorrectionDomain_left_right hz
    exact ⟨⟨hp.2,hq.2⟩,by norm_num,by norm_num⟩
  obtain ⟨J,hJ,bΦ⟩ := exists_compact_contDiffOn_jet_bound hK hV hKV hΦ 40
  let L := max 1 J
  have hL : 1 ≤ L := le_max_left _ _
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  let C : ℝ := ((40 ! : ℕ) : ℝ) * D * L^40
  refine ⟨C,by positivity,?_⟩
  intro M A hA hM jets E₀
  let Mloc (s : CapSigns) := axialLocalizeChart α (signedEndpointProfile M s)
  let Z (s : CapSigns) := zeroRatioTraceExtension (Mloc s)
  have zData (s : CapSigns) := by
    obtain ⟨sm,bb⟩ := localized (signedEndpointProfile M s) A hA (hM s) (jets s)
    exact zeroRatioTraceExtension_jets_of_oneSidedC100 hU hb (-1) 1 (Mloc s) (D*A)
      (mul_nonneg hD hA) sm bb
  let Ω (s : CapSigns) : Set BoxSpace := V ∩
    ({z | 0 < signedAxis s.1 (firstInput z)} ∩ {z | 0 < signedAxis s.2 (secondInput z)})
  have hΩ (s : CapSigns) : IsOpen (Ω s) := hV.inter
    ((isOpen_lt continuous_const ((sign_axis_continuous s.1).comp sf.continuous)).inter
      (isOpen_lt continuous_const ((sign_axis_continuous s.2).comp sg.continuous)))
  have select (z : BoxSpace) (hz : z ∈ V) : ∃ s, z ∈ Ω s := by
    obtain ⟨hp,hq⟩ := capCorrectionDomain_left_right hz
    have p : 0 < |firstInput z 0| := (mul_pos (by positivity : 0 < α/4)
      (norm_pos_iff.mpr (capCorrectionSlot_ne_zero hp))).trans hp.1.2.2
    have q : 0 < |secondInput z 0| := (mul_pos (by positivity : 0 < α/4)
      (norm_pos_iff.mpr (capCorrectionSlot_ne_zero hq))).trans hq.1.2.2
    obtain ⟨sp,hsp⟩ := sign_axis_exists p
    obtain ⟨sq,hsq⟩ := sign_axis_exists q
    exact ⟨(sp,sq),hz,hsp,hsq⟩
  have localEq (s : CapSigns) : EqOn E₀ (Z s ∘ Φ) (Ω s) := by
    intro z hz
    obtain ⟨hp,hq⟩ := capCorrectionDomain_left_right hz.1
    have hp0 := capCorrectionSlot_ne_zero hp
    have hq0 := capCorrectionSlot_ne_zero hq
    have lp := sign_chart_recovers s.1 hp0 hz.2.1
    have lq := sign_chart_recovers s.2 hq0 hz.2.2
    calc
      E₀ z = (axialCapPairWindow α (firstInput z,secondInput z) : ℂ) *
          M (endpointDirection (firstInput z)) (endpointDirection (secondInput z)) 0 :=
        axialLocalizeEndpoint_eval α (fun uv => M uv.1 uv.2 0) (firstInput z,secondInput z)
      _ = (Z s ∘ Φ) z := by
        symm
        change axialLocalizeChart α (signedEndpointProfile M s) (Φ z) = _
        rw [axialLocalizeChart_eval α (signedEndpointProfile M s) hp0 hq0 0]
        simp only [signedEndpointProfile,lp,lq]
  have phi (s : CapSigns) : ContDiffOn ℝ 100 Φ (Ω s) :=
    ((hΦ.of_le (WithTop.coe_le_coe.mpr le_top)).mono inter_subset_left)
  have maps (s : CapSigns) : MapsTo Φ (Ω s) W := mapΦ.mono_left inter_subset_left
  refine ⟨?_,?_⟩
  · intro z hz
    obtain ⟨s,hs⟩ := select z hz
    have loc := ((zData s).1.comp (phi s) (maps s)).contDiffAt ((hΩ s).mem_nhds hs)
    exact (loc.congr_of_eventuallyEq (by
      filter_upwards [(hΩ s).mem_nhds hs] with y hy
      exact localEq s hy)).contDiffWithinAt
  · intro n hn z hz
    have hzV := hKV hz
    obtain ⟨s,hs⟩ := select z hzV
    have hn' : (n : WithTop ℕ∞) ≤ 100 := by exact_mod_cast (show n ≤ 100 by omega)
    rw [← iteratedFDerivWithin_of_isOpen n (hΩ s) hs,iteratedFDerivWithin_congr (localEq s) hs n]
    refine (norm_iteratedFDerivWithin_comp_le (zData s).1 (phi s) hn'
      hW.uniqueDiffOn (hΩ s).uniqueDiffOn (maps s) hs (C := D*A) (D := L)
      (fun j hj => by
        rw [iteratedFDerivWithin_of_isOpen j hW (maps s hs)]
        exact (zData s).2 j (by omega) _ (maps s hs))
      (fun j hj hjn => by
        rw [iteratedFDerivWithin_of_isOpen j (hΩ s) hs]
        exact ((bΦ j (hjn.trans hn) z hz).trans (le_max_right _ _)).trans
          (by simpa only [pow_one] using pow_le_pow_right₀ hL hj))).trans ?_
    calc
      _ ≤ ((40 ! : ℕ) : ℝ) * (D*A) * L^40 := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hn) (mul_nonneg hD hA))
          (pow_le_pow_right₀ hL hn) (pow_nonneg hL0 _) (by positivity)
      _ = C*A := by unfold C; ring

end Burnett.A05
