import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearRadialCyclicity
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearCompactFamily
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearProfileAxes

set_option autoImplicit false
set_option maxRecDepth 8300
set_option maxHeartbeats 14500000

noncomputable section

namespace Burnett.C02

open Set Metric Burnett.A05 Burnett.Analysis.CapFourier Burnett.Analysis.ProjectiveNullCaps
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.A05.BoxFourier (frequencyCoordinates_axis)

open private wardAxialDirection_lower from Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearProfileAxes

/-- The support inequalities of an actual first-low branch place its
inputs in the compact set on which the normalized extension is one.
The ratio passed to the endpoint profile is the actual physical ratio. -/
theorem wardNearLowEndpointCompact_mem {N : ℕ} {m : Form} {w : E} (F : NullCapChart m w)
    {δ : ℝ} (hδ : δ ≠ 0) (c : E) (vCap : CapNeighborParameters N) {K : Set E}
    (B M R ρMax s₀ e α L U b : ℝ)
    (hParam : ((c,F.toFrequency.toContinuousLinearMap,δ),vCap) ∈ wardNearParameterCompact N K B M)
    (he : 0 < e) (heL : e ≤ L) (hα : 0 ≤ α) (hU : 0 < U)
    (hR : ‖frequencyCoordinates.toContinuousLinearMap‖ ≤ R)
    (hRatioMax : b*U/L ≤ ρMax) (hs₀ : s₀ ≤ α) (hs₀' : s₀ ≤ α*(L/(2*U)))
    (ϑ : ℝ → ℝ) (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (κ : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16)
    (p q : E) (hp : p ≠ 0) (hq : q ≠ 0) :
    let A := capFrequencyEquiv F hδ
    let r := -(p+q)
    let u := endpointDirection p
    let v := endpointDirection q
    let d := ‖A p‖/‖A q‖
    (∀ y, ‖A y‖ ≤ U*‖y‖) →
    (∀ y, α*‖y‖ ≤ |(frequencyCoordinates y).1| → L*‖y‖ ≤ ‖A y‖) →
    α*‖p‖ ≤ |p 0| → α*‖q‖ ≤ |q 0| → α*‖r‖ ≤ |r 0| → d < b →
    lowSlotWeight ϑ κ (A p) (A q) (A r) ≠ 0 →
    wardNearEndpointInput e ((c,F.toFrequency.toContinuousLinearMap,δ),vCap) u v d ∈
      wardNearProfileCompact N K B M R ρMax s₀ := by
  intro A r u v d hUp hLower hpAx hqAx hrAx hd hLow
  let l := ‖p‖/‖q‖
  obtain ⟨hl,hun,hvn,hPair,hRatio⟩ := wardNear_normalizeEndpointRatio F hδ hp hq
  change ‖u‖ = 1 at hun
  change ‖v‖ = 1 at hvn
  change (A p,A q) = ‖q‖ • (A (l • u),A v) at hPair
  have huAx := wardAxialDirection_lower hp hpAx
  have hvAx := wardAxialDirection_lower hq hqAx
  have huL : L ≤ ‖A u‖ := by
    have hu : α*‖u‖ ≤ |(frequencyCoordinates u).1| := by simpa only [hun,mul_one] using huAx
    simpa only [hun,mul_one] using hLower u hu
  have hvL : L ≤ ‖A v‖ := by
    have hv : α*‖v‖ ≤ |(frequencyCoordinates v).1| := by simpa only [hvn,mul_one] using hvAx
    simpa only [hvn,mul_one] using hLower v hv
  have hL : 0 < L := he.trans_le heL
  have e₀ : A p = ‖q‖ • A (l • u) := congrArg Prod.fst hPair
  have e₁ : A q = ‖q‖ • A v := congrArg Prod.snd hPair
  have hqN := norm_pos_iff.mpr hq
  have hqA : A q ≠ 0 := fun h => hq (A.injective (h.trans A.map_zero.symm))
  have hP : p = ‖q‖ • (l • u) := A.injective (e₀.trans (A.map_smul _ _).symm)
  have hQ : q = ‖q‖ • v := A.injective (e₁.trans (A.map_smul _ _).symm)
  have hThird : r = -(‖q‖ • (v+l • u)) := by
    change -(p+q) = _
    apply congrArg Neg.neg
    calc
      _ = ‖q‖ • (l • u)+‖q‖ • v := congrArg₂ (·+·) hP hQ
      _ = _ := by rw [smul_add,add_comm (‖q‖ • v)]
  have hThirdAx : α*‖v+l • u‖ ≤ |(frequencyCoordinates (v+l • u)).1| := by
    have e' := hrAx
    rw [hThird] at e'
    simp only [norm_neg,norm_smul,Real.norm_of_nonneg hqN.le,PiLp.neg_apply,PiLp.smul_apply,smul_eq_mul,
      abs_neg,abs_mul,abs_of_nonneg hqN.le] at e'
    rw [frequencyCoordinates_axis]
    apply (mul_le_mul_iff_right₀ hqN).mp
    linarith only [e']
  have hTri : A p+A q+A r = 0 := by
    simp only [r,map_neg,map_add,add_neg_cancel]
  have hLow' := lowSlotWeight_nonzero_small hCut hκ hκsmall hTri hqA hLow
  rw [e₀,e₁,norm_smul,norm_smul,Real.norm_of_nonneg hqN.le] at hLow'
  have hLowNorm : ‖A (l • u)‖ ≤ 2*κ*‖A v‖ := by
    apply (mul_le_mul_iff_right₀ hqN).mp
    linarith only [hLow']
  have hThirdBound := wardLowEndpoint_third_axis A hα hU hκsmall u v hvL hUp hLowNorm hThirdAx
  have hLup : l ≤ ρMax := by
    change wardParabolicRatioOfPhysical F.toFrequency.toContinuousLinearMap δ
        (frequencyCoordinates u) (frequencyCoordinates v) d = l at hRatio
    have ho : ‖A v‖ ≤ U := by simpa only [hvn,mul_one] using hUp v
    have hUpper : l ≤ b*U/L := by
      rw [← hRatio]
      change d*‖A v‖/‖A u‖ ≤ b*U/L
      have hd0 : 0 ≤ d := div_nonneg (norm_nonneg _) (norm_nonneg _)
      have hb : 0 ≤ b := hd0.trans hd.le
      exact div_le_div₀ (mul_nonneg hb hU.le) (mul_le_mul hd.le ho (norm_nonneg _) hb) hL huL
    exact hUpper.trans hRatioMax
  have hUn : ‖frequencyCoordinates u‖ ≤ R :=
    (frequencyCoordinates.toContinuousLinearMap.le_opNorm u).trans (by simpa only [hun,mul_one] using hR)
  have hVn : ‖frequencyCoordinates v‖ ≤ R :=
    (frequencyCoordinates.toContinuousLinearMap.le_opNorm v).trans (by simpa only [hvn,mul_one] using hR)
  have hExact := wardNearEndpointInput_eq e he ((c,F.toFrequency.toContinuousLinearMap,δ),vCap) u v d
    (heL.trans huL) (heL.trans hvL)
  rw [hExact,hRatio]
  refine ⟨⟨hParam,mem_closedBall_zero_iff.mpr hUn,mem_closedBall_zero_iff.mpr hVn,hl.le,hLup⟩,?_⟩
  intro j
  fin_cases j
  · exact hs₀.trans huAx
  · exact hs₀.trans hvAx
  · change s₀ ≤ |(frequencyCoordinates v+l • frequencyCoordinates u).1|
    rw [← map_smul,← map_add]
    exact hs₀'.trans hThirdBound

/-- The actual shifted comparable box inputs form a subset of the same
compact family whenever the physical comparable branch is active. -/
theorem wardNearComparableBoxCompact_mem {N : ℕ} {m : Form} {w : E} (F : NullCapChart m w)
    {δ : ℝ} (hδ : δ ≠ 0) (c : E) (vCap : CapNeighborParameters N) {K : Set E}
    (B M R ρMax s₀ α L U : ℝ)
    (hParam : ((c,F.toFrequency.toContinuousLinearMap,δ),vCap) ∈ wardNearParameterCompact N K B M)
    (hρ : 1 ≤ ρMax) (hα : 0 < α) (hL : 0 < L) (hU : 0 < U)
    (ϑ : ℝ → ℝ) (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (κ : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16)
    (hs₀ : s₀ ≤ min (α/2) (α*(κ*L/(4*U))))
    (u v : E) (hUn : ‖frequencyCoordinates u‖ ≤ R) (hVn : ‖frequencyCoordinates v‖ ≤ R)
    (hv : 1/2 ≤ ‖v‖) :
    let A := capFrequencyEquiv F hδ
    let r := -(u+v)
    (∀ y, ‖A y‖ ≤ U*‖y‖) →
    L*‖v‖ ≤ ‖A v‖ →
    α*‖u‖ ≤ |(frequencyCoordinates u).1| →
    α*‖v‖ ≤ |(frequencyCoordinates v).1| →
    α*‖r‖ ≤ |(frequencyCoordinates r).1| →
    A u ≠ 0 → A r ≠ 0 → comparableSlotWeight ϑ κ (A u) (A v) (A r) ≠ 0 →
    (((c,F.toFrequency.toContinuousLinearMap,δ),vCap),frequencyCoordinates u,frequencyCoordinates v,1)
      ∈ wardNearProfileCompact N K B M R ρMax s₀ := by
  intro A r hUp hHigh hFirst hSecond hThird hp hr hc
  obtain ⟨h₀,h₁,h₂⟩ := wardComparableBox_slot_axes ϑ hCut hFlat A hα hL hU hκ hκsmall u v hv hUp
    hHigh hFirst hSecond hThird hp hr hc
  refine ⟨⟨hParam,mem_closedBall_zero_iff.mpr hUn,mem_closedBall_zero_iff.mpr hVn,zero_le_one,hρ⟩,?_⟩
  intro j
  fin_cases j
  · exact hs₀.trans h₀
  · exact hs₀.trans h₁
  · change s₀ ≤ |(frequencyCoordinates v+(1:ℝ) • frequencyCoordinates u).1|
    have e : |(frequencyCoordinates r).1| = |(frequencyCoordinates v+frequencyCoordinates u).1| := by
      rw [show frequencyCoordinates r = -(frequencyCoordinates u+frequencyCoordinates v) by
        simp only [r,map_neg,map_add]]
      change abs (-((frequencyCoordinates u).1+(frequencyCoordinates v).1)) =
        |(frequencyCoordinates v).1+(frequencyCoordinates u).1|
      rw [abs_neg,add_comm]
    rw [one_smul,← e]
    exact hs₀.trans h₂

end Burnett.C02
