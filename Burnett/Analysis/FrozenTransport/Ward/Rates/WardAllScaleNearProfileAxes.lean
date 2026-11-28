import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearParabolicSmooth
import Burnett.Analysis.AngularCaps.ComparableTriadAngle
import Burnett.Analysis.AllScaleTransfer.ActualCapAxial
import Burnett.Analysis.AllScaleTransfer.EndpointAngularModeJets

set_option autoImplicit false
set_option maxHeartbeats 11500000

noncomputable section

namespace Burnett.C02

open Set Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.CapFourier
open Burnett.A02.FrequencySplit (E)
open Burnett.A05.BoxFourier (frequencyCoordinates_axis)

open private wardParabolicTestSegment wardParabolicTestDirection from Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearParabolicSmooth

/-- The Taylor interpolation retains exactly the first null coordinate.
A lower bound on that coordinate supplies a single nonsingular window
for the entire Taylor segment, uniformly at zero width. -/
theorem wardParabolicTestDomain_of_axis {F : NullCoordinateMap} {B b : ℝ}
    (hB : 0 ≤ B) (hF : ∀ u, ‖u‖ ≤ B*‖F u‖) (c : E) (δ : ℝ) (u : NullFrequencyCoordinates)
    (hu : B*b < |u.1|) :
    (c,F,δ,u) ∈ wardParabolicTestDomain b := by
  intro t _
  let v : NullFrequencyCoordinates := u.1 • nullAxis + (t*δ) • parabolicRemainder δ u
  have hv : v.1 = u.1 := by simp [v,nullAxis,parabolicRemainder]
  have hs : wardParabolicTestSegment (c,F,δ,u) t = F v := by
    simp only [wardParabolicTestSegment,wardParabolicTestDirection,v,map_add,map_smul,smul_smul]
  rw [hs]
  have hNorm : |u.1| ≤ ‖v‖ := by
    rw [Prod.norm_def,Real.norm_eq_abs,hv]
    exact le_max_left _ _
  by_contra! h
  exact (lt_irrefl _) (hu.trans_le (hNorm.trans ((hF v).trans (mul_le_mul_of_nonneg_left h hB))))

private theorem wardAxialDirection_lower {α : ℝ} {p : E} (hp : p ≠ 0)
    (h : α*‖p‖ ≤ |p 0|) :
    α ≤ |(frequencyCoordinates (Burnett.A05.endpointDirection p)).1| := by
  have hn := norm_pos_iff.mpr hp
  rw [frequencyCoordinates_axis]
  change α ≤ |‖p‖⁻¹ * p 0|
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr hn.le),inv_mul_eq_div]
  exact (le_div_iff₀ hn).mpr h

/-- In the low chart, the third normalized covector stays uniformly
away from the axial origin on the actual radial-cutoff support. The
high leg has normalized length one in this chart. -/
theorem wardLowEndpoint_third_axis (A : E ≃L[ℝ] E) {α L U κ ρ : ℝ}
    (hα : 0 ≤ α) (hU : 0 < U) (hκsmall : κ < 1/16)
    (u v : E) (hHigh : L ≤ ‖A v‖)
    (hUpper : ∀ x, ‖A x‖ ≤ U*‖x‖)
    (hLow : ‖A (ρ • u)‖ ≤ 2*κ*‖A v‖)
    (hAxis : α*‖v+ρ • u‖ ≤ |(frequencyCoordinates (v+ρ • u)).1|) :
    α*(L/(2*U)) ≤ |(frequencyCoordinates (v+ρ • u)).1| := by
  let p := A (ρ • u)
  let q := A v
  let r := -(A (v+ρ • u))
  have hSum : p+q+r = 0 := by
    simp only [p,q,r,map_add]
    abel
  have hR := (high_norm_diff_of_triad hSum).1
  have hSmall : ‖p‖ ≤ ‖q‖/2 := hLow.trans (by
    have e := mul_le_mul_of_nonneg_right (show 2*κ ≤ 1/2 by linarith only [hκsmall]) (norm_nonneg q)
    linarith only [e])
  have hHigh' : L ≤ ‖q‖ := hHigh
  have hRlo : L/2 ≤ ‖r‖ := by linarith only [hR,hSmall,hHigh']
  have hRup : ‖r‖ ≤ U*‖v+ρ • u‖ := by simpa only [r,norm_neg] using hUpper (v+ρ • u)
  refine (mul_le_mul_of_nonneg_left ?_ hα).trans hAxis
  apply (div_le_iff₀ (mul_pos zero_lt_two hU)).mpr
  nlinarith only [hRlo.trans hRup]

/-- On a comparable shifted box every original slot has an axial margin.
The argument keeps the actual third slot; its lower length follows from
the complementary radial cutoff and the second annular input. -/
theorem wardComparableBox_slot_axes (ϑ : ℝ → ℝ)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (A : E ≃L[ℝ] E) {α L U κ : ℝ} (hα : 0 < α) (hL : 0 < L) (hU : 0 < U)
    (hκ : 0 < κ) (hκsmall : κ < 1/16) (u v : E)
    (hv : 1/2 ≤ ‖v‖) (hUpper : ∀ x, ‖A x‖ ≤ U*‖x‖)
    (hHigh : L*‖v‖ ≤ ‖A v‖)
    (hFirst : α*‖u‖ ≤ |(frequencyCoordinates u).1|)
    (hSecond : α*‖v‖ ≤ |(frequencyCoordinates v).1|)
    (hThird : α*‖-(u+v)‖ ≤ |(frequencyCoordinates (-(u+v))).1|)
    (hp : A u ≠ 0) (hr : A (-(u+v)) ≠ 0)
    (hComp : comparableSlotWeight ϑ κ (A u) (A v) (A (-(u+v))) ≠ 0) :
    let s := min (α/2) (α*(κ*L/(4*U)))
    s ≤ |(frequencyCoordinates u).1| ∧ s ≤ |(frequencyCoordinates v).1| ∧
      s ≤ |(frequencyCoordinates (-(u+v))).1| := by
  intro s
  let p := A u
  let q := A v
  let r := A (-(u+v))
  have hqLo : L/2 ≤ ‖q‖ := by
    have hComp := (mul_le_mul_of_nonneg_left hv hL.le).trans hHigh
    change L * (1/2) ≤ ‖q‖ at hComp
    linarith only [hComp]
  have hq : q ≠ 0 := norm_pos_iff.mp ((half_pos hL).trans_le hqLo)
  have hSum : p+q+r = 0 := by simp only [p,q,r,map_neg,map_add,add_neg_cancel]
  have hRsum : r+q+p = 0 := by
    calc
      _ = p+q+r := by abel
      _ = 0 := hSum
  have hPlo := comparableSlotWeight_nonzero_first_ratio hCut hFlat hκ hκsmall hp hq hr hSum hComp
  have hCompR : comparableSlotWeight ϑ κ r q p ≠ 0 := by
    rw [comparableSlotWeight_swap_first,← comparableSlotWeight_rotate ϑ κ p q r]
    exact hComp
  have hRlo := comparableSlotWeight_nonzero_first_ratio hCut hFlat hκ hκsmall hr hq hp hRsum hCompR
  have e (x y : E) (hy : (κ/2)*‖q‖ ≤ ‖x‖) (hUp : ‖x‖ ≤ U*‖y‖) :
      κ*L/(4*U) ≤ ‖y‖ := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hU)).mpr
    have h := mul_le_mul_of_nonneg_left hqLo (half_pos hκ).le
    nlinarith only [h.trans (hy.trans hUp)]
  refine ⟨?_,?_,?_⟩
  · exact (min_le_right _ _).trans ((mul_le_mul_of_nonneg_left (e p u hPlo.le (hUpper u)) hα.le).trans hFirst)
  · have h : α/2 ≤ α*‖v‖ := by
      have hV := mul_le_mul_of_nonneg_left hv hα.le
      linarith only [hV]
    exact (min_le_left _ _).trans (h.trans hSecond)
  · exact (min_le_right _ _).trans
      ((mul_le_mul_of_nonneg_left (e r (-(u+v)) hRlo.le (hUpper (-(u+v)))) hα.le).trans hThird)

end Burnett.C02
