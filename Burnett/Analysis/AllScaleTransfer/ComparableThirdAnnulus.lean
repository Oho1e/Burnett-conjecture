import Burnett.Analysis.AllScaleTransfer.RadialRatioCorrection
import Burnett.Analysis.AngularCaps.ComparableTriadAngle
import Burnett.Analysis.AllScaleTransfer.RadianTrilinearChange

set_option autoImplicit false
set_option maxHeartbeats 1900000

noncomputable section

namespace Burnett.Analysis.CapFourier

open Set Burnett.Analysis.ProjectiveNullCaps
open Burnett.A02.FrequencySplit (Joint)
open scoped ContDiff

private theorem comparableSlotWeight_zero_first {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16) {v : Space} (hv : v ≠ 0) :
    comparableSlotWeight ϑ κ 0 v (-v) = 0 := by
  have hOne : lowSlotWeight ϑ κ 0 v (-v) = 1 := by
    unfold lowSlotWeight
    simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]
    exact hFlat 0 (by norm_num) (by norm_num)
  have hother (x : Space) (hx : x ≠ 0) : lowSlotWeight ϑ κ x (-x) 0 = 0 := by
    by_contra hn
    have h := lowSlotWeight_nonzero_small hCut hκ hκsmall
      (by simp : x + (-x) + 0 = 0) (neg_ne_zero.mpr hx) hn
    rw [norm_neg] at h
    exact (not_lt_of_ge h) (by
      have hs := mul_lt_mul_of_pos_right (show 2*κ < 1 by linarith) (norm_pos_iff.mpr hx)
      simpa only [one_mul] using hs)
  have hLast : lowSlotWeight ϑ κ (-v) 0 v = 0 := by
    rw [lowSlotWeight_swap_high]
    simpa only [neg_neg] using hother (-v) (neg_ne_zero.mpr hv)
  simp [comparableSlotWeight, hOne, hother v hv, hLast]

/-- The original comparable weight forces the first and signed third slots
to be comparable to the nonzero second slot. -/
theorem comparableSlotWeight_signed_triad_bounds {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16) {p q : Space} (hq : q ≠ 0)
    (hComp : comparableSlotWeight ϑ κ p q (-(p+q)) ≠ 0) :
    ((κ/2)*‖q‖ ≤ ‖p‖ ∧ (κ/2)*‖p‖ ≤ ‖q‖) ∧
      ((κ/2)*‖q‖ ≤ ‖-(p+q)‖ ∧ (κ/2)*‖-(p+q)‖ ≤ ‖q‖) := by
  let w := -(p+q)
  change comparableSlotWeight ϑ κ p q w ≠ 0 at hComp
  have hSum : p+q+w = 0 := add_neg_cancel _
  have hp : p ≠ 0 := by
    intro hp
    apply hComp
    simpa only [hp, w, zero_add] using comparableSlotWeight_zero_first hCut hFlat hκ hκsmall hq
  have hCompRot : comparableSlotWeight ϑ κ q w p ≠ 0 := by
    rwa [← comparableSlotWeight_rotate ϑ κ p q w]
  have hw : w ≠ 0 := by
    intro hw
    have hqp : p + q = 0 := neg_eq_zero.mp hw
    have hqneg : q = -p := eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm q p] using hqp)
    apply hCompRot
    rw [comparableSlotWeight_rotate ϑ κ q w p, hw, hqneg]
    exact comparableSlotWeight_zero_first hCut hFlat hκ hκsmall hp
  have hCompSwap : comparableSlotWeight ϑ κ q p w ≠ 0 := by
    rwa [← comparableSlotWeight_swap_first ϑ κ p q w]
  have hCompLast : comparableSlotWeight ϑ κ w q p ≠ 0 := by
    rwa [← comparableSlotWeight_swap_first ϑ κ q w p]
  have hSumSwap : q+p+w = 0 := by simpa only [add_comm q p] using hSum
  have hSumRot : q+w+p = 0 := calc
    _ = p+q+w := by abel
    _ = 0 := hSum
  have hSumLast : w+q+p = 0 := by simpa only [add_comm w q] using hSumRot
  exact ⟨⟨(comparableSlotWeight_nonzero_first_ratio hCut hFlat hκ hκsmall hp hq hw hSum hComp).le,
      (comparableSlotWeight_nonzero_first_ratio hCut hFlat hκ hκsmall hq hp hw hSumSwap hCompSwap).le⟩,
    ⟨(comparableSlotWeight_nonzero_first_ratio hCut hFlat hκ hκsmall hw hq hp hSumLast hCompLast).le,
      (comparableSlotWeight_nonzero_first_ratio hCut hFlat hκ hκsmall hq hw hp hSumRot hCompRot).le⟩⟩

def comparableRadialLower (κ L U : ℝ) : ℝ := min (1/2) (κ*L/(4*U))

def comparableRadialUpper (κ L U : ℝ) : ℝ := max 2 (4*U/(κ*L))

private theorem normalized_band_of_physical_compare {κ L U r : ℝ} {A : Space ≃L[ℝ] Space}
    (hκ : 0 < κ) (hL : 0 < L) (hU : 0 < U) (hr : 0 < r) {u q : Space}
    (hq : r/2 ≤ ‖q‖ ∧ ‖q‖ ≤ 2*r)
    (hComp : (κ/2)*‖A q‖ ≤ ‖A u‖ ∧ (κ/2)*‖A u‖ ≤ ‖A q‖)
    (hu : L*‖u‖ ≤ ‖A u‖ ∧ ‖A u‖ ≤ U*‖u‖)
    (hqA : L*‖q‖ ≤ ‖A q‖ ∧ ‖A q‖ ≤ U*‖q‖) :
    ‖u‖ ∈ Icc (comparableRadialLower κ L U*r) (comparableRadialUpper κ L U*r) := by
  have hk₂ : 0 < κ/2 := by positivity
  constructor
  · calc
      _ ≤ (κ*L/(4*U))*r := mul_le_mul_of_nonneg_right (min_le_right _ _) hr.le
      _ = ((κ/2)*(L*(r/2)))/U := by
        field_simp [hU.ne']
        ring
      _ ≤ _ := (div_le_iff₀ hU).2 (calc
        _ ≤ (κ/2)*(L*‖q‖) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq.1 hL.le) hk₂.le
        _ ≤ (κ/2)*‖A q‖ := mul_le_mul_of_nonneg_left hqA.1 hk₂.le
        _ ≤ ‖A u‖ := hComp.1
        _ ≤ U*‖u‖ := hu.2
        _ = _ := mul_comm _ _)
  · calc
      _ ≤ (U*(2*r))/((κ/2)*L) := (le_div_iff₀ (mul_pos hk₂ hL)).2 (calc
        _ = (κ/2)*(L*‖u‖) := by ring
        _ ≤ (κ/2)*‖A u‖ := mul_le_mul_of_nonneg_left hu.1 hk₂.le
        _ ≤ ‖A q‖ := hComp.2
        _ ≤ U*‖q‖ := hqA.2
        _ ≤ _ := mul_le_mul_of_nonneg_left hq.2 hU.le)
      _ = (4*U/(κ*L))*r := by
        field_simp [hκ.ne', hL.ne']
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hr.le

/-- A fixed band in the normalized variables contains all three slots of
the original comparable branch. -/
theorem comparable_normalized_triad_annulus {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (A : Space ≃L[ℝ] Space) {κ L U r : ℝ}
    (hκ : 0 < κ) (hκsmall : κ < 1/16) (hL : 0 < L) (hU : 0 < U) (hr : 0 < r) {p q : Space}
    (hq : r/2 ≤ ‖q‖ ∧ ‖q‖ ≤ 2*r)
    (hComp : comparableSlotWeight ϑ κ (A p) (A q) (A (-(p+q))) ≠ 0)
    (hpA : L*‖p‖ ≤ ‖A p‖ ∧ ‖A p‖ ≤ U*‖p‖)
    (hqA : L*‖q‖ ≤ ‖A q‖ ∧ ‖A q‖ ≤ U*‖q‖)
    (hwA : L*‖-(p+q)‖ ≤ ‖A (-(p+q))‖ ∧ ‖A (-(p+q))‖ ≤ U*‖-(p+q)‖) :
    let I := Icc (comparableRadialLower κ L U*r) (comparableRadialUpper κ L U*r)
    ‖p‖ ∈ I ∧ ‖q‖ ∈ I ∧ ‖-(p+q)‖ ∈ I := by
  have hq0 : 0 < ‖A q‖ := (mul_pos hL ((by positivity : 0 < r/2).trans_le hq.1)).trans_le hqA.1
  have h := comparableSlotWeight_signed_triad_bounds hCut hFlat hκ hκsmall
    (norm_pos_iff.mp hq0) (by simpa only [map_neg, map_add] using hComp)
  have hw : (κ/2)*‖A q‖ ≤ ‖A (-(p+q))‖ ∧ (κ/2)*‖A (-(p+q))‖ ≤ ‖A q‖ := by
    simpa only [map_neg, map_add] using h.2
  refine ⟨normalized_band_of_physical_compare hκ hL hU hr hq h.1 hpA hqA, ?_,
    normalized_band_of_physical_compare hκ hL hU hr hq hw hwA hqA⟩
  exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le).trans_eq
      (by ring : (1/2 : ℝ)*r = r/2) |>.trans hq.1,
    hq.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr.le)⟩

/-- A radial bump on the comparable third-slot band at scale r. -/
def comparableThirdCutoff (a b r : ℝ) (x : Space) : ℝ :=
  radialLowCutoff (b*r) x - radialLowCutoff (a*r/2) x

theorem comparableThirdCutoff_eq_one {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {x : Space} (hx : ‖x‖ ∈ Icc (a*r) (b*r)) : comparableThirdCutoff a b r x = 1 := by
  have hInner : 2*(a*r/2) ≤ ‖x‖ := by linarith [hx.1]
  unfold comparableThirdCutoff
  rw [radialLowCutoff_eq_one (mul_pos hb hr) hx.2,
    radialLowCutoff_eq_zero (by positivity) hInner, sub_zero]

theorem comparableThirdCutoff_smooth_support {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) :
    ContDiff ℝ ∞ (comparableThirdCutoff a b r) ∧
      tsupport (comparableThirdCutoff a b r) ⊆ {x | ‖x‖ ∈ Icc (a*r/2) (2*b*r)} := by
  have hcomp (s : ℝ) : ContDiff ℝ ∞ (radialLowCutoff s) :=
    radialBallBump.contDiff.comp (contDiff_const.smul contDiff_id)
  refine ⟨(hcomp _).sub (hcomp _), ?_⟩
  apply closure_minimal _ ((isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const))
  intro x hx
  change comparableThirdCutoff a b r x ≠ 0 at hx
  have hb : 0 < b := ha.trans_le hab
  have hbound := mul_le_mul_of_nonneg_right hab hr.le
  change a*r/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 2*b*r
  constructor
  · by_contra! h
    apply hx
    have hHalf : a*r/2 ≤ a*r := by linarith only [mul_pos ha hr]
    have hOuter := h.le.trans (hHalf.trans hbound)
    unfold comparableThirdCutoff
    rw [radialLowCutoff_eq_one (mul_pos hb hr) hOuter,
      radialLowCutoff_eq_one (by positivity) h.le, sub_self]
  · by_contra! h
    apply hx
    have hOuter : 2*(b*r) ≤ ‖x‖ := by simpa only [mul_assoc] using h.le
    have hInner : 2*(a*r/2) ≤ ‖x‖ := calc
      _ = a*r := by ring
      _ ≤ b*r := hbound
      _ ≤ 2*(b*r) := by linarith only [mul_pos hb hr]
      _ ≤ _ := hOuter
    unfold comparableThirdCutoff
    rw [radialLowCutoff_eq_zero (mul_pos hb hr) hOuter,
      radialLowCutoff_eq_zero (by positivity) hInner, sub_self]

def comparableRadialSymbol (ϑ : ℝ → ℝ) (κ r : ℝ) (A : Space ≃L[ℝ] Space)
    (m : Joint → ℂ) (x : Joint) : ℂ :=
  m x * (comparableSlotWeight ϑ κ (A x.1) (A x.2) (A (-(x.1+x.2))) : ℂ) *
    (radialAnnularCutoff r x.2 : ℂ)

/-- Insert the third annulus in the actual radian form before separating the
two frequencies. The symbol already includes the original comparable weight. -/
theorem radianTrilinearForm_comparableThirdCutoff_eq {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (A : Space ≃L[ℝ] Space) {κ L U r : ℝ}
    (hκ : 0 < κ) (hκsmall : κ < 1/16) (hL : 0 < L) (hU : 0 < U) (hr : 0 < r)
    (m : Joint → ℂ)
    (hm : ∀ z : Joint, m z ≠ 0 →
      (L*‖z.1‖ ≤ ‖A z.1‖ ∧ ‖A z.1‖ ≤ U*‖z.1‖) ∧
      (L*‖z.2‖ ≤ ‖A z.2‖ ∧ ‖A z.2‖ ≤ U*‖z.2‖) ∧
      (L*‖-(z.1+z.2)‖ ≤ ‖A (-(z.1+z.2))‖ ∧ ‖A (-(z.1+z.2))‖ ≤ U*‖-(z.1+z.2)‖))
    (f g w : SchwartzMap Space ℂ) :
    let b := comparableRadialSymbol ϑ κ r A m
    let χ := comparableThirdCutoff (comparableRadialLower κ L U) (comparableRadialUpper κ L U) r
    radianTrilinearForm (fun z => b z * (χ (-(z.1+z.2)) : ℂ)) f g w = radianTrilinearForm b f g w := by
  dsimp only
  congr 1
  funext z
  by_cases hm0 : m z = 0
  · simp only [comparableRadialSymbol, hm0, zero_mul]
  by_cases hComp : comparableSlotWeight ϑ κ (A z.1) (A z.2) (A (-(z.1+z.2))) = 0
  · simp only [comparableRadialSymbol, hComp, Complex.ofReal_zero, mul_zero, zero_mul]
  by_cases hq : radialAnnularCutoff r z.2 = 0
  · simp only [comparableRadialSymbol, hq, Complex.ofReal_zero, mul_zero, zero_mul]
  have hAn := radialAnnularCutoff_nonzero hr hq
  obtain ⟨hpN,hqN,hwN⟩ := hm z hm0
  have h := comparable_normalized_triad_annulus hCut hFlat A hκ hκsmall hL hU hr
    ⟨hAn.1.le, hAn.2.le⟩ hComp hpN hqN hwN
  have ha : 0 < comparableRadialLower κ L U :=
    lt_min (by norm_num) (by positivity)
  have hb : 0 < comparableRadialUpper κ L U := (by norm_num : 0 < (2 : ℝ)).trans_le (le_max_left _ _)
  rw [comparableThirdCutoff_eq_one ha hb hr h.2.2, Complex.ofReal_one, mul_one]

/-- The cap case uses the bound on the actual three enlarged-cap supports
and chooses the two constants before the chart and its scale. -/
theorem exists_uniform_cap_comparableThirdCutoff (B a outer enlarged : ℝ)
    (hB : 0 < B) (ha : 0 < a) (hOut : 0 ≤ outer) (hOE : outer < enlarged) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧
      ∀ (metric : Form) (u : Vec) (F : NullCapChart metric u), ‖u‖ = 1 →
        ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
        ∀ (δ : ℝ) (hδ : 0 < δ), 4*B*(5*δ) ≤ 1 →
        ∀ (ϑ : ℝ → ℝ), (∀ t : ℝ, 1 ≤ t → ϑ t = 0) →
          (∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1) →
          ∀ κ : ℝ, 0 < κ → κ < 1/16 → ∀ r : ℝ, 0 < r → ∀ m : Joint → ℂ,
            let A := capFrequencyEquiv F hδ.ne'
            let S := tsupport (enlargedCapMultiplier metric δ (a*δ^2) outer enlarged u)
            (∀ z : Joint, m z ≠ 0 → A z.1 ∈ S ∧ A z.2 ∈ S ∧ A (-(z.1+z.2)) ∈ S) →
            ∀ f g w : SchwartzMap Space ℂ,
              let b := comparableRadialSymbol ϑ κ r A m
              let χ := comparableThirdCutoff (comparableRadialLower κ L U) (comparableRadialUpper κ L U) r
              radianTrilinearForm (fun z => b z * (χ (-(z.1+z.2)) : ℂ)) f g w =
                radianTrilinearForm b f g w := by
  obtain ⟨L,U,hL,hU,hNorm⟩ := exists_uniform_capFrequency_norm_compare B a outer enlarged hB ha hOut hOE
  refine ⟨L,U,hL,hU,?_⟩
  intro metric u F hu hI δ hδ hSmall ϑ hCut hFlat κ hκ hκsmall r hr m
  dsimp only
  intro hm f g w
  have h := hNorm metric u F hu hI δ hδ hSmall
  apply radianTrilinearForm_comparableThirdCutoff_eq hCut hFlat (capFrequencyEquiv F hδ.ne')
    hκ hκsmall hL hU hr m _ f g w
  intro z hz
  obtain ⟨hp,hq,hw⟩ := hm z hz
  exact ⟨h z.1 hp, h z.2 hq, h (-(z.1+z.2)) hw⟩

/-- The uncapped comparable branch uses the same construction with A = I. -/
theorem radianTrilinearForm_comparableThirdCutoff_eq_identity {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    {κ r : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16) (hr : 0 < r)
    (m : Joint → ℂ) (f g w : SchwartzMap Space ℂ) :
    let b := comparableRadialSymbol ϑ κ r (ContinuousLinearEquiv.refl ℝ Space) m
    let χ := comparableThirdCutoff (comparableRadialLower κ 1 1) (comparableRadialUpper κ 1 1) r
    radianTrilinearForm (fun z => b z * (χ (-(z.1+z.2)) : ℂ)) f g w = radianTrilinearForm b f g w := by
  dsimp only
  apply radianTrilinearForm_comparableThirdCutoff_eq hCut hFlat (ContinuousLinearEquiv.refl ℝ Space)
    hκ hκsmall (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) hr m _ f g w
  intro z _
  simp

end Burnett.Analysis.CapFourier
