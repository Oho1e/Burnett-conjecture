import Burnett.Analysis.AllScaleTransfer.SignedEndpointWindows
import Burnett.Analysis.AllScaleTransfer.ActualCapSignedBoxes
import Burnett.Analysis.AllScaleTransfer.RadianLowEndpointAllScales

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.A05

open Set Metric Filter MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis CapFourier ProjectiveNullCaps
open Burnett.Analysis.LowRatio (Angles Point Window endpoint)
open scoped ContDiff ENNReal Topology

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

/-- The same original angular symbol expressed in one of the four signed charts. -/
def signedEndpointProfile (M : E → E → ℝ → ℂ) (signs : CapSigns) (z : Point) : ℂ :=
  M (signedChartLift signs.1 z.1.1) (signedChartLift signs.2 z.1.2) z.2

/-- The unseparated trace evaluated at the two actual signed directions. -/
def capEndpointM0Symbol (M : E → E → ℝ → ℂ) (p : Joint) : ℂ :=
  M (endpointDirection p.1) (endpointDirection p.2) 0

def capEndpointWindowSum (gap : ℕ) (p : Joint) : ℂ := ∑' j, lowEndpointRadianWindows gap j p

private theorem unit_axis_margin {α : ℝ} {ξ : E} (hξ : ξ ≠ 0)
    (h : α * ‖ξ‖ ≤ |ξ 0|) : α ≤ |endpointDirection ξ 0| := by
  have hn := norm_pos_iff.mpr hξ
  change α ≤ |‖ξ‖⁻¹ * ξ 0|
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr hn.le),inv_mul_eq_div]
  exact (le_div_iff₀ hn).mpr h

private theorem lift_capHemisphere {α : ℝ} (hα : 0 < α) {ξ : E} (hξ : ξ ≠ 0)
    (h : α ≤ |endpointDirection ξ 0|) :
    signedChartLift (capHemisphere ξ) (endpointTail (endpointDirection ξ)) = endpointDirection ξ := by
  apply signedChartLift_endpointTail _ (endpointDirection_mem_sphere hξ)
  by_cases hx : 0 ≤ endpointDirection ξ 0
  · simpa only [capHemisphere,hx,decide_true,signedAxis,if_true] using
      hα.trans_le (by simpa only [abs_of_nonneg hx] using h)
  · have hneg := lt_of_not_ge hx
    simpa only [capHemisphere,hx,decide_false,signedAxis,if_false] using neg_pos.mpr hneg

private theorem windowSum_measurable_bounded (gap : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ Measurable (capEndpointWindowSum gap) ∧
      ∀ p, ‖capEndpointWindowSum gap p‖ ≤ B := by
  let W := lowEndpointRadianWindows gap
  let B := SchwartzMap.seminorm ℝ 0 0 endpointLowProfile * SchwartzMap.seminorm ℝ 0 0 endpointHighProfile *
    SchwartzMap.seminorm ℝ 0 0 endpointThickProfile
  have hB : 0 ≤ B := by unfold B; positivity
  have con (j : ℤ) : Continuous (W j) := by
    change Continuous (fun p : Joint => lowEndpointRadianWindows gap j p)
    simp only [lowEndpointRadianWindows_eq_profiles]
    fun_prop
  have normW (j : ℤ) (p : Joint) : ‖W j p‖ ≤ B := by
    change ‖lowEndpointRadianWindows gap j p‖ ≤ B
    rw [lowEndpointRadianWindows_eq_profiles,norm_mul,norm_mul]
    exact mul_le_mul
      (mul_le_mul (endpointLowProfile.norm_le_seminorm ℝ _) (endpointHighProfile.norm_le_seminorm ℝ _)
        (norm_nonneg _) (apply_nonneg _ _))
      (endpointThickProfile.norm_le_seminorm ℝ _) (norm_nonneg _) (by positivity)
  have loc (p : Joint) : ∃ I : Finset ℤ, I.card ≤ 3 ∧ ∀ j ∉ I, W j p = 0 := by
    obtain ⟨I,hI,hzero⟩ := exists_integerRadialWindow_support_card_le_three p.2
    refine ⟨I,hI,fun j hj => ?_⟩
    have hz : radialAnnularCutoff ((2 : ℝ)^j) p.2 = 0 := hzero j hj
    simp only [W,lowEndpointRadianWindows,hz,Complex.ofReal_zero,mul_zero,zero_mul]
  refine ⟨3*B,by positivity,?_,?_⟩
  · refine measurable_of_tendsto_metrizable' atTop
      (fun I : Finset ℤ => I.measurable_fun_sum (fun j _ => (con j).measurable)) ?_
    rw [tendsto_pi_nhds]
    intro p
    obtain ⟨I,_,hzero⟩ := loc p
    have hs : HasSum (fun j : ℤ => W j p) (capEndpointWindowSum gap p) :=
      (summable_of_ne_finset_zero hzero).hasSum
    exact hs
  · intro p
    obtain ⟨I,hI,hzero⟩ := loc p
    change ‖∑' j, W j p‖ ≤ 3*B
    rw [tsum_eq_sum hzero]
    calc
      _ ≤ ∑ j ∈ I, B := norm_sum_le_of_le _ (fun j _ => normW j p)
      _ = (I.card : ℝ) * B := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hI) hB

private theorem signed_chart_weight_integrable {U : Set Angles} {a b r R A : ℝ}
    (ha : a < 0) (hb : 0 < b) (hrR : r ≤ R) (hA0 : 0 ≤ A)
    (hChart : closedBall (0 : EndpointAngle) R ×ˢ closedBall (0 : EndpointAngle) R ⊆ U)
    (M : Point → ℂ) (hM : ContinuousOn M (Window U a b)) (hA : ∀ z ∈ Window U a b, ‖M z‖ ≤ A)
    (f g h : SchwartzMap E ℂ) (gap : ℕ)
    (htest : ∀ p : Joint, radianWeight (fun _ => 1) f g h p ≠ 0 →
      ‖endpointTail (endpointDirection p.1)‖ ≤ r ∧ ‖endpointTail (endpointDirection p.2)‖ ≤ r) :
    Integrable (radianTrilinearWeight (fun p => lowEndpointM0Symbol M p * capEndpointWindowSum gap p) f g h) := by
  classical
  obtain ⟨B,hB,mW,bW⟩ := windowSum_measurable_bounded gap
  let S : Set Angles := closedBall (0 : EndpointAngle) r ×ˢ closedBall (0 : EndpointAngle) r
  let θ (p : Joint) : Angles := (endpointTail (endpointDirection p.1),endpointTail (endpointDirection p.2))
  let c := S.piecewise (endpoint M) (fun _ => 0)
  have mp : MapsTo (fun z : Angles => (z,(0:ℝ))) S (Window U a b) := by
    intro z hz
    exact ⟨hChart ⟨closedBall_subset_closedBall hrR hz.1,closedBall_subset_closedBall hrR hz.2⟩,ha,hb⟩
  have con : ContinuousOn (endpoint M) S := hM.comp (by fun_prop) mp
  have mc : Measurable c := con.measurable_piecewise continuousOn_const
    (measurableSet_closedBall.prod measurableSet_closedBall)
  have md : Measurable endpointDirection := by unfold endpointDirection; fun_prop
  have mθ : Measurable θ :=
    (endpointTail.continuous.measurable.comp (md.comp measurable_fst)).prodMk
      (endpointTail.continuous.measurable.comp (md.comp measurable_snd))
  have bnd (p : Joint) : ‖c (θ p)‖ ≤ A := by
    by_cases hp : θ p ∈ S
    · rw [show c (θ p) = endpoint M (θ p) from piecewise_eq_of_mem S _ _ hp]
      exact hA _ (mp hp)
    · simpa only [c,piecewise_eq_of_notMem S _ _ hp,norm_zero] using hA0
  have integrable := integrable_radianTrilinearWeight_of_bounded
    (fun p => c (θ p) * capEndpointWindowSum gap p) (((mc.comp mθ).mul mW).aestronglyMeasurable)
    (A*B) (fun p => by rw [norm_mul]; exact mul_le_mul (bnd p) (bW p) (norm_nonneg _) hA0) f g h
  refine integrable.congr (Eventually.of_forall fun p => ?_)
  by_cases hp : radianWeight (fun _ => 1) f g h p = 0
  · change ((c (θ p) * capEndpointWindowSum gap p) * radianWeight (fun _ => 1) f g h p) = _
    simp only [radianTrilinearWeight,hp,mul_zero]
  · have hp' : θ p ∈ S := ⟨mem_closedBall_zero_iff.mpr (htest p hp).1,mem_closedBall_zero_iff.mpr (htest p hp).2⟩
    simp only [radianTrilinearWeight, show c (θ p) = endpoint M (θ p) from piecewise_eq_of_mem S _ _ hp']
    rfl

private theorem four_signed_weights_eq {α : ℝ} (hα : 0 < α)
    (M : E → E → ℝ → ℂ) (W : Joint → ℂ) (f g h : SchwartzMap E ℂ)
    (hf : EndpointFiniteAnnulus f) (hg : EndpointFiniteAnnulus g)
    (af : ∀ p, radianFourier f p ≠ 0 → α * ‖p‖ ≤ |p 0|)
    (ag : ∀ q, radianFourier g q ≠ 0 → α * ‖q‖ ≤ |q 0|) (p : Joint) :
    (∑ signs : CapSigns, radianTrilinearWeight
      (fun y => lowEndpointM0Symbol (signedEndpointProfile M signs) y * W y)
      (signedEndpointFactor α signs.1 f hf) (signedEndpointFactor α signs.2 g hg) h p) =
      radianTrilinearWeight (fun y => capEndpointM0Symbol M y * W y) f g h p := by
  classical
  by_cases hp : radianFourier f p.1 = 0
  · simp only [radianTrilinearWeight,radianWeight,signedEndpointFactor_radian,hp,mul_zero,zero_mul,Finset.sum_const_zero]
  by_cases hq : radianFourier g p.2 = 0
  · simp only [radianTrilinearWeight,radianWeight,signedEndpointFactor_radian,hq,mul_zero,zero_mul,Finset.sum_const_zero]
  have up := unit_axis_margin (hf.radian_ne_zero hp) (af p.1 hp)
  have uq := unit_axis_margin (hg.radian_ne_zero hq) (ag p.2 hq)
  let S : CapSigns := (capHemisphere p.1,capHemisphere p.2)
  rw [Finset.sum_eq_single S]
  · simp only [radianTrilinearWeight,radianWeight,signedEndpointFactor_radian,capSignWindow_eq_selector hα _ _ up,
      capSignWindow_eq_selector hα _ _ uq,S,if_true,Complex.ofReal_one,one_mul,lowEndpointM0Symbol,
      signedEndpointProfile,endpoint,capEndpointM0Symbol,lift_capHemisphere hα (hf.radian_ne_zero hp) up,
      lift_capHemisphere hα (hg.radian_ne_zero hq) uq]
  · intro signs _ hs
    by_cases hpS : signs.1 = capHemisphere p.1
    · have hqS : signs.2 ≠ capHemisphere p.2 := fun h => hs (Prod.ext hpS h)
      simp only [radianTrilinearWeight,radianWeight,signedEndpointFactor_radian,capSignWindow_eq_selector hα _ _ uq,
        if_neg hqS,Complex.ofReal_zero,zero_mul,mul_zero]
    · simp only [radianTrilinearWeight,radianWeight,signedEndpointFactor_radian,capSignWindow_eq_selector hα _ _ up,
        if_neg hpS,Complex.ofReal_zero,zero_mul,mul_zero]
  · simp

/-- The actual normalized cap endpoint is the sum over its four signed chart inputs.
Each input is already localized to a finite frequency annulus and has the exact cap support.
The bound is independent of the radii, cap, frame and low/high gap under the displayed geometry. -/
theorem exists_actual_cap_radian_M0_bound (B tube outer enlarged : ℝ)
    (hB : 0 < B) (hTube : 0 < tube) (hOut : 0 ≤ outer) (hOE : outer < enlarged) :
    ∃ α r R : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < r ∧ r < R ∧ R < 1 ∧
      ∀ (U : Set Angles), IsOpen U → ∀ (a b period : ℝ), a < 0 → 0 < b → 2 < period →
        closedBall (0 : EndpointAngle) R ×ˢ closedBall (0 : EndpointAngle) R ⊆ U →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : E → E → ℝ → ℂ) (A : ℝ), 0 ≤ A →
          (∀ signs : CapSigns, ContDiffOn ℝ 100 (signedEndpointProfile M signs) (Window U a b) ∧
            ∀ j ≤ 100, ∀ z ∈ Window U a b, ‖iteratedFDeriv ℝ j (signedEndpointProfile M signs) z‖ ≤ A) →
          ∀ (m : Form) (u : Vec) (F : NullCapChart m u),
            ‖u‖ = 1 → ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
            ∀ (δ : ℝ) (hδ : 0 < δ), 4 * B * (5 * δ) ≤ 1 → ∀ (gap : ℕ) (f g h : SchwartzMap E ℂ)
              (hf : EndpointFiniteAnnulus f) (hg : EndpointFiniteAnnulus g),
              let L := capFrequencyEquiv F hδ.ne'
              let K := tsupport (enlargedCapMultiplier m δ (tube * δ^2) outer enlarged u)
              (∀ p, radianFourier f p ≠ 0 → L p ∈ K) → (∀ q, radianFourier g q ≠ 0 → L q ∈ K) →
              let T := radianTrilinearForm (fun p => capEndpointM0Symbol M p * capEndpointWindowSum gap p) f g h
              T = ∑ signs : CapSigns, radianTrilinearForm
                  (fun p => lowEndpointM0Symbol (signedEndpointProfile M signs) p * capEndpointWindowSum gap p)
                  (signedEndpointFactor α signs.1 f hf) (signedEndpointFactor α signs.2 g hg) h ∧
              ‖T‖ ≤ C * A * ‖f.toLp (ENNReal.ofReal 3) volume‖ * ‖g.toLp (ENNReal.ofReal 3) volume‖ *
                ‖h.toLp (ENNReal.ofReal 3) volume‖ := by
  obtain ⟨α,hα,hα1,axis⟩ := exists_enlarged_cap_support_axial_margin B tube outer enlarged hB hTube hOut hOE
  obtain ⟨r,R,hr,hrR,hR,tail⟩ := exists_endpointTail_radii (half_pos hα)
    (by linarith only [hα,hα1] : α / 2 ≤ 1)
  obtain ⟨D,hD,splitBound⟩ := exists_signedEndpointFactor_L3_bound α
  refine ⟨α,r,R,hα,hα1,hr,hrR,hR,?_⟩
  intro U hU a b period ha hb hp hChart
  obtain ⟨C,hC,full⟩ := exists_radian_lowEndpoint_M0_full_bound hU ha hb hr hrR hp hChart
  refine ⟨4*C*D^2,by positivity,?_⟩
  intro M A hA jets m u F hu hInv δ hδ hSmall gap f g h hf hg L K hF hG T
  let fS (s : Bool) := signedEndpointFactor α s f hf
  let gS (s : Bool) := signedEndpointFactor α s g hg
  let bS (s : CapSigns) (p : Joint) := lowEndpointM0Symbol (signedEndpointProfile M s) p * capEndpointWindowSum gap p
  have af (p : E) (hp : radianFourier f p ≠ 0) : α * ‖p‖ ≤ |p 0| := axis m u F hu hInv δ hδ hSmall p (hF p hp)
  have ag (q : E) (hq : radianFourier g q ≠ 0) : α * ‖q‖ ≤ |q 0| := axis m u F hu hInv δ hδ hSmall q (hG q hq)
  have onChart (s : CapSigns) (p : Joint) (hp : radianWeight (fun _ => 1) (fS s.1) (gS s.2) h p ≠ 0) :
      ‖endpointTail (endpointDirection p.1)‖ ≤ r ∧ ‖endpointTail (endpointDirection p.2)‖ ≤ r := by
    have hf' : radianFourier f p.1 ≠ 0 := by
      intro hf'
      exact hp (by simp only [fS,radianWeight,signedEndpointFactor_radian,hf',mul_zero,zero_mul])
    have hg' : radianFourier g p.2 ≠ 0 := by
      intro hg'
      exact hp (by simp only [gS,radianWeight,signedEndpointFactor_radian,hg',mul_zero,zero_mul])
    have hp' := hf.radian_ne_zero hf'
    have hq' := hg.radian_ne_zero hg'
    have ap := (show α / 2 ≤ α from (half_lt_self hα).le).trans (unit_axis_margin hp' (af p.1 hf'))
    have aq := (show α / 2 ≤ α from (half_lt_self hα).le).trans (unit_axis_margin hq' (ag p.2 hg'))
    exact ⟨tail _ (endpointDirection_mem_sphere hp') ap, tail _ (endpointDirection_mem_sphere hq') aq⟩
  have hi (s : CapSigns) : Integrable (radianTrilinearWeight (bS s) (fS s.1) (gS s.2) h) :=
    signed_chart_weight_integrable ha hb hrR.le hA hChart _ (jets s).1.continuousOn
      (fun z hz => by simpa only [norm_iteratedFDeriv_zero] using (jets s).2 0 (by omega) z hz)
      _ _ _ gap (onChart s)
  have equality : T = ∑ s : CapSigns, radianTrilinearForm (bS s) (fS s.1) (gS s.2) h := by
    unfold T radianTrilinearForm
    rw [← Finset.smul_sum,← integral_finset_sum _ (fun s _ => hi s)]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => (four_signed_weights_eq hα M (capEndpointWindowSum gap) f g h hf hg af ag p).symm)
  refine ⟨equality,?_⟩
  have per (s : CapSigns) : ‖radianTrilinearForm (bS s) (fS s.1) (gS s.2) h‖ ≤
      (C*D^2)*A*‖f.toLp (ENNReal.ofReal 3) volume‖*‖g.toLp (ENNReal.ofReal 3) volume‖*
        ‖h.toLp (ENNReal.ofReal 3) volume‖ := by
    refine (full _ A hA (jets s).1 (jets s).2 gap _ _ h (Eventually.of_forall (onChart s))).2.trans ?_
    calc
      _ ≤ C*A*(D * ‖f.toLp (ENNReal.ofReal 3) volume‖)*(D * ‖g.toLp (ENNReal.ofReal 3) volume‖)*
          ‖h.toLp (ENNReal.ofReal 3) volume‖ := by gcongr <;> apply splitBound
      _ = _ := by ring
  rw [equality]
  calc
    _ ≤ ∑ _s : CapSigns, (C*D^2)*A*‖f.toLp (ENNReal.ofReal 3) volume‖*‖g.toLp (ENNReal.ofReal 3) volume‖*
        ‖h.toLp (ENNReal.ofReal 3) volume‖ := norm_sum_le_of_le _ (fun s _ => per s)
    _ = _ := by simp [Fintype.card_prod]; ring

end Burnett.A05
