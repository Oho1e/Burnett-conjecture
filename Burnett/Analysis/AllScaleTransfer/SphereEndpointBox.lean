import Burnett.Analysis.AllScaleTransfer.EndpointAngularTraceSeries
import Burnett.Analysis.AllScaleTransfer.FixedAnnularCutoff
import Burnett.Analysis.AllScaleTransfer.RadialThirdCutoff
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option maxHeartbeats 4100000
noncomputable section

namespace Burnett.A05

open Set Metric Filter Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier
open scoped ContDiff Topology Nat

/-- The fixed off-axis box neighborhood for the two actual angular directions. -/
def sphereEndpointAnnuli : Set BoxSpace :=
  {z | (1 / 4 : ℝ) < ‖firstInput z‖ ∧ ‖firstInput z‖ < 3 ∧
    (1 / 4 : ℝ) < ‖secondInput z‖ ∧ ‖secondInput z‖ < 3}

def sphereEndpointBoxPullback (M₀ : Joint → ℂ) (z : BoxSpace) : ℂ :=
  M₀ (endpointDirection (firstInput z), endpointDirection (secondInput z))

def sphereEndpointRadialCutoff (z : BoxSpace) : ℝ :=
  radialAnnularCutoff 1 (firstInput z) * radialAnnularCutoff 1 (secondInput z)

private theorem sphereEndpointAnnuli_open : IsOpen sphereEndpointAnnuli := by
  have f : Continuous firstInput := boxToPair.continuous.fst
  have g : Continuous secondInput := boxToPair.continuous.snd
  exact (isOpen_lt continuous_const f.norm).inter ((isOpen_lt f.norm continuous_const).inter
    ((isOpen_lt continuous_const g.norm).inter (isOpen_lt g.norm continuous_const)))

private theorem sphereEndpointRadialCutoff_contDiff : ContDiff ℝ ∞ sphereEndpointRadialCutoff := by
  have f : ContDiff ℝ ∞ firstInput := boxToPair.toContinuousLinearMap.contDiff.fst
  have g : ContDiff ℝ ∞ secondInput := boxToPair.toContinuousLinearMap.contDiff.snd
  have s (r : ℝ) : ContDiff ℝ ∞ (radialLowCutoff r) := by
    unfold radialLowCutoff
    exact radialBallBump.contDiff.comp (contDiff_const.smul contDiff_id)
  exact (((s 1).sub (s (1 / 2))).comp f).mul (((s 1).sub (s (1 / 2))).comp g)

private theorem sphereEndpointRadialCutoff_tsupport :
    tsupport sphereEndpointRadialCutoff ⊆ sphereEndpointAnnuli := by
  let K : Set BoxSpace := {z | (1 / 2 : ℝ) ≤ ‖firstInput z‖ ∧ ‖firstInput z‖ ≤ 2 ∧
    (1 / 2 : ℝ) ≤ ‖secondInput z‖ ∧ ‖secondInput z‖ ≤ 2}
  have f : Continuous firstInput := boxToPair.continuous.fst
  have g : Continuous secondInput := boxToPair.continuous.snd
  have hc : IsClosed K := (isClosed_le continuous_const f.norm).inter
    ((isClosed_le f.norm continuous_const).inter ((isClosed_le continuous_const g.norm).inter
      (isClosed_le g.norm continuous_const)))
  have hk : Function.support sphereEndpointRadialCutoff ⊆ K := by
    intro z hz
    have ht : radialAnnularCutoff 1 (firstInput z) * radialAnnularCutoff 1 (secondInput z) ≠ 0 := hz
    have h₁ := radialAnnularCutoff_nonzero (r := 1) (by norm_num) (left_ne_zero_of_mul ht)
    have h₂ := radialAnnularCutoff_nonzero (r := 1) (by norm_num) (right_ne_zero_of_mul ht)
    exact ⟨h₁.1.le,by simpa only [mul_one] using h₁.2.le,
      h₂.1.le,by simpa only [mul_one] using h₂.2.le⟩
  exact (closure_minimal hk hc).trans (fun z hz => ⟨(by norm_num : (1 / 4 : ℝ) < 1 / 2).trans_le hz.1,
    hz.2.1.trans_lt (by norm_num), (by norm_num : (1 / 4 : ℝ) < 1 / 2).trans_le hz.2.2.1,
    hz.2.2.2.trans_lt (by norm_num)⟩)

theorem sphereEndpointRadialCutoff_one (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    sphereEndpointRadialCutoff (joinedInputs u v) = 1 := by
  have H (w : E) (hw : ‖w‖ = 1) : radialAnnularCutoff 1 w = 1 := by
    rw [radialAnnularCutoff, radialLowCutoff_eq_one (by norm_num) hw.le,
      radialLowCutoff_eq_zero (by norm_num) (by rw [hw]; norm_num), sub_zero]
  simp only [sphereEndpointRadialCutoff,firstInput_joined,secondInput_joined,H u hu,H v hv,mul_one]

def sphereEndpointBoxProfile (M₀ : Joint → ℂ) (z : BoxSpace) : ℂ :=
  sphereEndpointRadialCutoff z • sphereEndpointBoxPullback M₀ z

private theorem exists_sphereEndpointBoxProfile_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (M₀ : Joint → ℂ) (A : ℝ), 0 ≤ A →
      ContDiffOn ℝ 100 (sphereEndpointBoxPullback M₀) sphereEndpointAnnuli →
      (∀ j ≤ 100, ∀ z ∈ sphereEndpointAnnuli, ‖iteratedFDeriv ℝ j (sphereEndpointBoxPullback M₀) z‖ ≤ A) →
      ContDiff ℝ 100 (sphereEndpointBoxProfile M₀) ∧
        ∀ j ≤ 40, ∀ z ∈ ball (0 : BoxSpace) 3, ‖iteratedFDeriv ℝ j (sphereEndpointBoxProfile M₀) z‖ ≤ B * A := by
  let D := sphereEndpointAnnuli
  let β := sphereEndpointRadialCutoff
  have hD := sphereEndpointAnnuli_open
  have hβ : ContDiff ℝ ∞ β := sphereEndpointRadialCutoff_contDiff
  have supportβ : tsupport β ⊆ D := sphereEndpointRadialCutoff_tsupport
  obtain ⟨K,hK,jets⟩ := exists_compact_contDiffOn_jet_bound
    (isCompact_closedBall (0 : BoxSpace) 3) isOpen_univ (subset_univ _) hβ.contDiffOn 40
  refine ⟨2^40*K,by positivity,?_⟩
  intro M₀ A hA hm bm
  let G := sphereEndpointBoxPullback M₀
  let f := sphereEndpointBoxProfile M₀
  have hb : ContDiffOn ℝ 100 β D := (hβ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have locally : ContDiffOn ℝ 100 f D := hb.smul hm
  have zeroOutside (z : BoxSpace) (hz : z ∉ D) : f =ᶠ[𝓝 z] 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (supportβ h))] with y hy
    change β y = 0 at hy
    change β y • G y = 0
    rw [hy,zero_smul]
  refine ⟨contDiff_iff_contDiffAt.mpr (fun x => ?_),?_⟩
  · by_cases hx : x ∈ D
    · exact locally.contDiffAt (hD.mem_nhds hx)
    · exact contDiffAt_const.congr_of_eventuallyEq (zeroOutside x hx)
  intro j hj z hz
  by_cases hd : z ∈ D
  · rw [← iteratedFDerivWithin_of_isOpen j hD hd]
    have hOrder : (j : WithTop ℕ∞) ≤ 100 := by exact_mod_cast (show j ≤ 100 by omega)
    refine (norm_iteratedFDerivWithin_smul_le hb hm hD.uniqueDiffOn hd hOrder).trans ?_
    calc
      _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*K*A := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [iteratedFDerivWithin_of_isOpen i hD hd,iteratedFDerivWithin_of_isOpen (j-i) hD hd]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (jets i (hi'.trans hj) z (ball_subset_closedBall hz))
            (by positivity)) (bm (j-i) (by omega) z hd) (norm_nonneg _) (by positivity)
      _ = (2 : ℝ)^j*K*A := by rw [← Finset.sum_mul,← Finset.sum_mul]; norm_cast; rw [Nat.sum_range_choose]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hK) hA
  · have hn := notMem_tsupport_iff_eventuallyEq.mpr (zeroOutside z hd)
    have hzero : iteratedFDeriv ℝ j f z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hn (tsupport_iteratedFDeriv_subset j h))
    change ‖iteratedFDeriv ℝ j f z‖ ≤ _
    rw [hzero,norm_zero]
    positivity

/-- Full signed sphere directions give the same modes as the existing physical
angular multipliers. The only data is the fixed off-axis C¹⁰⁰ box budget. -/
theorem exists_sphereEndpoint_angular_series :
    ∃ (χ : BoxSpace → ℝ) (C : ℝ), ContDiff ℝ ∞ χ ∧ 0 ≤ C ∧
      ∀ (M₀ : Joint → ℂ) (A : ℝ), 0 ≤ A →
        ContDiffOn ℝ 100 (sphereEndpointBoxPullback M₀) sphereEndpointAnnuli →
        (∀ j ≤ 100, ∀ z ∈ sphereEndpointAnnuli, ‖iteratedFDeriv ℝ j (sphereEndpointBoxPullback M₀) z‖ ≤ A) →
        let c (ab : FourierModePair) :=
          boxCubeFourierCoefficient 3 (modeIndex ab) (fun z => χ z • sphereEndpointBoxProfile M₀ z)
        (∀ ab, ‖c ab‖ ≤ C*A*modePairDecay ab) ∧
          Summable (weightedModeCoefficient c) ∧
          (∑' ab, weightedModeCoefficient c ab) ≤ C*A*modePairSummationConstant ∧
          ∀ p q : E, p ≠ 0 → q ≠ 0 →
            HasSum (fun ab => c ab * (endpointModeSymbol 3 ab.1 p * endpointModeSymbol 3 ab.2 q))
              (M₀ (endpointDirection p,endpointDirection q)) := by
  obtain ⟨χ,C₀,hχ,_,_,hC₀,series⟩ := exists_normalized_gap_box_series 2 3 (by norm_num) (by norm_num)
  obtain ⟨B,hB,profile⟩ := exists_sphereEndpointBoxProfile_bound
  refine ⟨χ,C₀*B,hχ,by positivity,?_⟩
  intro M₀ A hA hM budget c
  let f := sphereEndpointBoxProfile M₀
  obtain ⟨smooth,bound⟩ := profile M₀ A hA hM budget
  let F (s : ℕ) : BoxSpace → ℂ := if s = 0 then f else 0
  have hF (s : ℕ) : ContDiffOn ℝ 99 (F s) (ball (0 : BoxSpace) 3) := by
    by_cases hs : s = 0
    · simpa only [F,hs,if_true] using (smooth.of_le (by norm_num : (99 : WithTop ℕ∞) ≤ 100)).contDiffOn
    · simpa only [F,hs,if_false] using (contDiffOn_const : ContDiffOn ℝ 99 (0 : BoxSpace → ℂ) (ball 0 3))
  have hJet (s j : ℕ) (hj : j ≤ 40) (z : BoxSpace) (hz : z ∈ ball (0 : BoxSpace) 3) :
      ‖iteratedFDeriv ℝ j (F s) z‖ ≤ (B * A) * radialGapDecay s := by
    by_cases hs : s = 0
    · simpa only [F,hs,if_true,radialGapDecay,pow_zero,mul_one] using bound j hj z hz
    · have hzF : F s = fun _ : BoxSpace => (0 : ℂ) := if_neg hs
      rw [hzF,iteratedFDeriv_zero_fun,Pi.zero_apply,norm_zero]
      unfold radialGapDecay
      positivity
  obtain ⟨coeff,values⟩ := series F (B*A) (by positivity) hF hJet 0
  have hc (ab : FourierModePair) : ‖c ab‖ ≤ C₀*B*A*modePairDecay ab := by
    simpa only [c,F,if_true,radialGapDecay,pow_zero,mul_one,mul_assoc] using coeff ab
  have hc0 (ab : FourierModePair) : ‖c ab‖ ≤ (C₀*B*A)*radialGapDecay 0*modePairDecay ab := by
    simpa only [radialGapDecay,pow_zero,mul_one] using hc ab
  obtain ⟨w,hw,_⟩ := weighted_fourier_modes_at_gap c (C₀*B*A) (by positivity) 0 hc0
  refine ⟨hc,w,by simpa only [radialGapDecay,pow_zero,mul_one] using hw,?_⟩
  intro p q hp hq
  let u := endpointDirection p
  let v := endpointDirection q
  let z := joinedInputs u v
  have hu : ‖u‖ = 1 := by simpa only [u,mem_sphere,dist_zero_right] using endpointDirection_mem_sphere hp
  have hv : ‖v‖ = 1 := by simpa only [v,mem_sphere,dist_zero_right] using endpointDirection_mem_sphere hq
  have hz : z ∈ closedBall (0 : BoxSpace) 2 := by
    apply mem_closedBall_zero_iff.mpr
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mp
    change ‖joinedInputs u v‖ ^ 2 ≤ 2 ^ 2
    rw [norm_joinedInputs_sq,hu,hv]
    norm_num
  have unitU : endpointDirection u = u := by rw [endpointDirection,hu,inv_one,one_smul]
  have unitV : endpointDirection v = v := by rw [endpointDirection,hv,inv_one,one_smul]
  have htrace : F 0 z = M₀ (u,v) := by
    simp only [F,f,z,sphereEndpointBoxProfile,sphereEndpointBoxPullback,if_true,
      sphereEndpointRadialCutoff_one u v hu hv,one_smul,firstInput_joined,secondInput_joined,unitU,unitV]
  have hs := (values z hz).2
  rw [htrace] at hs
  simpa only [F,c,if_true,z,u,v,separatedBoxMode_endpoint] using hs

end Burnett.A05
