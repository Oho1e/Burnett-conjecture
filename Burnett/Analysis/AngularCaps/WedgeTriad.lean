import Burnett.Analysis.AngularCaps.ProjectiveWedgeCaps
import Mathlib.Analysis.InnerProductSpace.Continuous

set_option autoImplicit false
set_option maxHeartbeats 4200000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set
open scoped BigOperators RealInnerProductSpace

theorem projectiveWedgeSq_nonneg (x y : Vec) : 0 ≤ projectiveWedgeSq x y := by
  refine div_nonneg ?_ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) zero_le_two

theorem triad_third_eq_neg_add {p q r : Vec} (h : p+q+r = 0) : r = -(p+q) := by
  calc
    r = (p+q+r)-(p+q) := by abel
    _ = -(p+q) := by rw [h,zero_sub]

theorem coordinateWedgeSq_third_eq_of_triad {p q r : Vec} (h : p+q+r = 0) :
    coordinateWedgeSq p r = coordinateWedgeSq p q := by
  rw [triad_third_eq_neg_add h]
  unfold coordinateWedgeSq
  congr 1
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp only [PiLp.neg_apply, PiLp.add_apply]
    ring

/-- Exact normalization of the third-slot angular separation at signed Fourier
frequencies satisfying (p+q+r=0). -/
theorem projectiveWedgeSq_third_eq_of_triad {p q r : Vec} (h : p+q+r = 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    projectiveWedgeSq p r = (‖q‖^2/‖r‖^2)*projectiveWedgeSq p q := by
  unfold projectiveWedgeSq
  rw [coordinateWedgeSq_third_eq_of_triad h]
  field_simp [norm_ne_zero_iff.mpr hp, norm_ne_zero_iff.mpr hq, norm_ne_zero_iff.mpr hr]

/-- The manuscript low weight for the designated slot, with its exact frequency
ratios. -/
def lowSlotWeight (ϑ : ℝ → ℝ) (κ : ℝ) (p q r : Vec) : ℝ :=
  ϑ (‖p‖^2/(κ^2*(‖q‖^2+‖r‖^2)))

theorem high_norm_diff_of_triad {p q r : Vec} (h : p+q+r = 0) :
    ‖q‖-‖p‖ ≤ ‖r‖ ∧ ‖r‖ ≤ ‖p‖+‖q‖ := by
  have hr := triad_third_eq_neg_add h
  have hq : q = -(p+r) := by
    apply triad_third_eq_neg_add (p := p) (q := r)
    simpa only [add_right_comm] using h
  constructor
  · have hle : ‖q‖ ≤ ‖p‖+‖r‖ := by rw [hq, norm_neg]; exact norm_add_le _ _
    linarith only [hle]
  · rw [hr, norm_neg]
    exact norm_add_le _ _

theorem lowSlotWeight_nonzero_small {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) {κ : ℝ} (hκ : 0 < κ) (hκ' : κ < 1/16)
    {p q r : Vec} (hTriad : p+q+r = 0) (hq : q ≠ 0)
    (hLow : lowSlotWeight ϑ κ p q r ≠ 0) : ‖p‖ ≤ (2*κ)*‖q‖ := by
  have hDen : 0 < κ^2*(‖q‖^2+‖r‖^2) :=
    mul_pos (pow_pos hκ _) (add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.mpr hq) _) (sq_nonneg _))
  have hRatio : ‖p‖^2/(κ^2*(‖q‖^2+‖r‖^2)) < 1 :=
    lt_of_not_ge fun hn => hLow (hCut _ hn)
  have hSmall := (div_lt_iff₀ hDen).mp hRatio
  by_contra hn
  have hQ : κ*‖q‖ ≤ ‖p‖/2 := by linarith only [lt_of_not_ge hn]
  have hR0 := mul_le_mul_of_nonneg_left (high_norm_diff_of_triad hTriad).2 hκ.le
  have hκP := mul_le_mul_of_nonneg_right hκ'.le (norm_nonneg p)
  have hR : κ*‖r‖ ≤ 3*‖p‖/4 := by linarith only [hR0,hκP,hQ,norm_nonneg p]
  have hQSq := pow_le_pow_left₀ (mul_nonneg hκ.le (norm_nonneg q)) hQ 2
  have hRSq := pow_le_pow_left₀ (mul_nonneg hκ.le (norm_nonneg r)) hR 2
  simp only [one_mul] at hSmall
  nlinarith only [hSmall,hQSq,hRSq,sq_nonneg ‖p‖]

theorem farAngularWeight_nonzero_one_edge {ϑ : ℝ → ℝ}
    (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    {δ : ℝ} (hδ : 0 < δ) {p q r : Vec}
    (hFar : 1-angularNearWeight ϑ δ p q r ≠ 0) :
    δ^2/4 < projectiveWedgeSq p q ∨ δ^2/4 < projectiveWedgeSq p r := by
  by_contra hn
  push_neg at hn
  have hp : 0 < δ^2 := pow_pos hδ _
  have hOne (z : Vec) (hz : projectiveWedgeSq p z ≤ δ^2/4) :
      ϑ (projectiveWedgeSq p z/δ^2) = 1 := by
    apply hFlat _ (div_nonneg (projectiveWedgeSq_nonneg _ _) hp.le)
    exact (div_le_iff₀ hp).mpr (hz.trans_eq (by ring))
  exact hFar (by simp [angularNearWeight, hOne q hn.1, hOne r hn.2])

/-- Each of the two squared angles is uniformly separated on the actual
low/far cutoff, including the case in which the other high slot detects it. -/
theorem lowFarWeight_nonzero_separated {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    {κ δ : ℝ} (hκ : 0 < κ) (hκ' : κ < 1/16) (hδ : 0 < δ)
    {p q r : Vec} (hTriad : p+q+r = 0) (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hFar : lowSlotWeight ϑ κ p q r*(1-angularNearWeight ϑ δ p q r) ≠ 0) :
    ‖p‖ ≤ (2*κ)*‖q‖ ∧ δ^2/16 ≤ projectiveWedgeSq p q ∧ δ^2/16 ≤ projectiveWedgeSq p r := by
  have hFactors := mul_ne_zero_iff.mp hFar
  have hSmall := lowSlotWeight_nonzero_small hCut hκ hκ' hTriad hq hFactors.1
  have hAng := farAngularWeight_nonzero_one_edge hFlat hδ hFactors.2
  have hTri := high_norm_diff_of_triad hTriad
  have hκQ := mul_le_mul_of_nonneg_right hκ'.le (norm_nonneg q)
  have hRUpper : ‖r‖ ≤ 2*‖q‖ := by linarith only [hTri.2,hSmall,hκQ,norm_nonneg q]
  have hQLower : ‖q‖ ≤ 2*‖r‖ := by linarith only [hTri.1,hSmall,hκQ,norm_nonneg q]
  have hRPos : 0 < ‖r‖^2 := pow_pos (norm_pos_iff.mpr hr) _
  have hRatUpper : ‖q‖^2/‖r‖^2 ≤ 4 := (div_le_iff₀ hRPos).mpr (by
    have hSq := pow_le_pow_left₀ (norm_nonneg q) hQLower 2
    nlinarith only [hSq])
  have hRatLower : 1/4 ≤ ‖q‖^2/‖r‖^2 := (le_div_iff₀ hRPos).mpr (by
    have hSq := pow_le_pow_left₀ (norm_nonneg r) hRUpper 2
    nlinarith only [hSq])
  have hIdent := projectiveWedgeSq_third_eq_of_triad hTriad hp hq hr
  refine ⟨hSmall, ?_⟩
  rcases hAng with h | h
  · have hMul := mul_le_mul_of_nonneg_right hRatLower (projectiveWedgeSq_nonneg p q)
    rw [← hIdent] at hMul
    constructor <;> linarith only [hMul,h,sq_nonneg δ]
  · have hMul := mul_le_mul_of_nonneg_right hRatUpper (projectiveWedgeSq_nonneg p q)
    rw [← hIdent] at hMul
    constructor <;> linarith only [hMul,h,sq_nonneg δ]

private abbrev FrequencyTriad := Vec × Vec × Vec

private def nonzeroLowFarTriads (ϑ : ℝ → ℝ) (κ δ : ℝ) : Set FrequencyTriad :=
  {z | z.1+z.2.1+z.2.2 = 0 ∧ z.1 ≠ 0 ∧ z.2.1 ≠ 0 ∧ z.2.2 ≠ 0 ∧
    lowSlotWeight ϑ κ z.1 z.2.1 z.2.2*(1-angularNearWeight ϑ δ z.1 z.2.1 z.2.2) ≠ 0}

/-- Topological support of the exact low/far weight along the nonzero triads. -/
def InLowFarTriadSupport (ϑ : ℝ → ℝ) (κ δ : ℝ) (p q r : Vec) : Prop :=
  (p,q,r) ∈ closure (nonzeroLowFarTriads ϑ κ δ)

theorem inLowFarTriadSupport_of_nonzero {ϑ : ℝ → ℝ} {κ δ : ℝ} {p q r : Vec}
    (hSum : p+q+r = 0) (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hFar : lowSlotWeight ϑ κ p q r*(1-angularNearWeight ϑ δ p q r) ≠ 0) :
    InLowFarTriadSupport ϑ κ δ p q r := subset_closure ⟨hSum,hp,hq,hr,hFar⟩

private theorem continuousAt_projectiveWedgeSq_of {a b : FrequencyTriad → Vec}
    (ha : Continuous a) (hb : Continuous b) {z : FrequencyTriad} (hza : a z ≠ 0) (hzb : b z ≠ 0) :
    ContinuousAt (fun w => projectiveWedgeSq (a w) (b w)) z := by
  have hNorm : Continuous fun w => ‖a w‖^2*‖b w‖^2 := (ha.norm.pow 2).mul (hb.norm.pow 2)
  have hInner : Continuous fun w => ⟪a w,b w⟫ := continuous_inner.comp (ha.prodMk hb)
  simp only [projectiveWedgeSq,coordinateWedgeSq_eq_gram]
  exact (hNorm.sub (hInner.pow 2)).continuousAt.div hNorm.continuousAt
    (mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr hza)) (pow_ne_zero _ (norm_ne_zero_iff.mpr hzb)))

private theorem lower_bound_mem_closure {S : Set FrequencyTriad} {z : FrequencyTriad}
    {f : FrequencyTriad → ℝ} {b : ℝ} (hz : z ∈ closure S) (hc : ContinuousAt f z)
    (h : ∀ x ∈ S, b ≤ f x) : b ≤ f z := by
  have hMap : MapsTo f S (Ici b) := fun x hx => h x hx
  have hT := hc.continuousWithinAt.mem_closure hz hMap
  rw [isClosed_Ici.closure_eq] at hT
  exact hT

/-- The low-frequency and angular inequalities extend to the closed support at
every nonzero triad, including points where the cutoff itself vanishes. -/
theorem lowFarTriadSupport_separated {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    {κ δ : ℝ} (hκ : 0 < κ) (hκ' : κ < 1/16) (hδ : 0 < δ)
    {p q r : Vec} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hFar : InLowFarTriadSupport ϑ κ δ p q r) :
    ‖p‖ ≤ (2*κ)*‖q‖ ∧ δ^2/16 ≤ projectiveWedgeSq p q ∧ δ^2/16 ≤ projectiveWedgeSq p r := by
  let S := nonzeroLowFarTriads ϑ κ δ
  let z₀ : FrequencyTriad := (p,q,r)
  have hz₀ : z₀ ∈ closure S := hFar
  have hGeo (z : FrequencyTriad) (hz : z ∈ S) : ‖z.1‖ ≤ (2*κ)*‖z.2.1‖ ∧
      δ^2/16 ≤ projectiveWedgeSq z.1 z.2.1 ∧ δ^2/16 ≤ projectiveWedgeSq z.1 z.2.2 := by
    have hd : z.1+z.2.1+z.2.2 = 0 ∧ z.1 ≠ 0 ∧ z.2.1 ≠ 0 ∧ z.2.2 ≠ 0 ∧
        lowSlotWeight ϑ κ z.1 z.2.1 z.2.2*(1-angularNearWeight ϑ δ z.1 z.2.1 z.2.2) ≠ 0 := hz
    obtain ⟨hSum,h₁,h₂,h₃,hw⟩ := hd
    exact lowFarWeight_nonzero_separated hCut hFlat hκ hκ' hδ hSum h₁ h₂ h₃ hw
  let lowGap (z : FrequencyTriad) := (2*κ)*‖z.2.1‖-‖z.1‖
  have hLowC : Continuous lowGap :=
    (continuous_const.mul (continuous_fst.comp continuous_snd).norm).sub continuous_fst.norm
  have hLow : 0 ≤ lowGap z₀ := lower_bound_mem_closure hz₀ hLowC.continuousAt
    (fun z hz => sub_nonneg.mpr (hGeo z hz).1)
  let first (z : FrequencyTriad) := z.1
  let second (z : FrequencyTriad) := z.2.1
  let third (z : FrequencyTriad) := z.2.2
  have hAngPQ : ContinuousAt (fun z => projectiveWedgeSq (first z) (second z)) z₀ :=
    continuousAt_projectiveWedgeSq_of (a := first) (b := second) continuous_fst
      (continuous_fst.comp continuous_snd) hp hq
  have hAngPR : ContinuousAt (fun z => projectiveWedgeSq (first z) (third z)) z₀ :=
    continuousAt_projectiveWedgeSq_of (a := first) (b := third) continuous_fst
      (continuous_snd.comp continuous_snd) hp hr
  exact ⟨sub_nonneg.mp hLow,lower_bound_mem_closure hz₀ hAngPQ (fun z hz => (hGeo z hz).2.1),
    lower_bound_mem_closure hz₀ hAngPR (fun z hz => (hGeo z hz).2.2)⟩

end Burnett.Analysis.ProjectiveNullCaps
