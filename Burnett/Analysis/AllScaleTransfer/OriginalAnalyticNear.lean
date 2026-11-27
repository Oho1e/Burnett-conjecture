import Burnett.Analysis.AllScaleTransfer.OriginalAtlasRepresentatives
import Burnett.Analysis.AllScaleTransfer.BoundedSignedCapEndpoint
import Burnett.Analysis.AllScaleTransfer.AnalyticNear

set_option autoImplicit false
set_option maxRecDepth 9900
set_option maxHeartbeats 13500000

noncomputable section

namespace Burnett.A05

open Set Metric MeasureTheory
open Burnett.A02.FrequencySplit Burnett.A05.BoxFourier Burnett.C02
open Burnett.Analysis CapFourier ProjectiveNullCaps
open Burnett.Analysis.LowRatio (Point)
open Burnett.RicciSymbol.TensorFrame (LorentzFrame)
open scoped ContDiff ENNReal

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

private theorem fourBranchWeight_zero_on_third_axis (ϑ : ℝ → ℝ)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16)
    (p : Joint) (hp : p.1 ≠ 0) (hr : -(p.1 + p.2) = 0) :
    radianFourBranchWeight ϑ κ 0 p = 0 ∧ radianFourBranchWeight ϑ κ 3 p = 0 := by
  rcases p with ⟨p,q⟩
  change -(p + q) = 0 at hr
  have hpq : p + q = 0 := neg_eq_zero.mp hr
  have hq : q = -p := by
    calc
      q = -p + (p + q) := by abel
      _ = -p := by rw [hpq,add_zero]
  subst q
  have hd : 0 < κ^2*‖p‖^2 := mul_pos (pow_pos hκ _) (pow_pos (norm_pos_iff.mpr hp) _)
  have hκsq : κ^2 ≤ (1 : ℝ)^2 :=
    pow_le_pow_left₀ hκ.le (hκsmall.le.trans (by norm_num)) _
  have hratio : 1 ≤ ‖p‖^2/(κ^2*‖p‖^2) := (le_div_iff₀ hd).mpr (by
    rw [one_mul]
    exact mul_le_of_le_one_left (sq_nonneg ‖p‖) (by simpa only [one_pow] using hκsq))
  have hFirst : lowSlotWeight ϑ κ p (-p) 0 = 0 := by
    simpa [lowSlotWeight] using hCut _ hratio
  have hSecond : lowSlotWeight ϑ κ (-p) 0 p = 0 := by
    simpa [lowSlotWeight] using hCut _ hratio
  have hThird : lowSlotWeight ϑ κ 0 p (-p) = 1 := by
    simpa [lowSlotWeight] using hFlat 0 le_rfl (by norm_num)
  constructor
  · change lowSlotWeight ϑ κ p (-p) (-(p + -p)) = 0
    simpa only [add_neg_cancel, neg_zero] using hFirst
  · change comparableSlotWeight ϑ κ p (-p) (-(p + -p)) = 0
    simp only [add_neg_cancel, neg_zero, comparableSlotWeight, hFirst, hSecond, hThird]
    ring

private theorem nonzeroSignedTriads_radianCycles {p : Joint} (hp : p ∈ nonzeroSignedTriads) :
    radianCycle p ∈ nonzeroSignedTriads ∧ radianCycle.symm p ∈ nonzeroSignedTriads := by
  have h₁ : -(p.2 + -(p.1 + p.2)) = p.1 := by abel
  have h₂ : -(-(p.1 + p.2) + p.1) = p.2 := by abel
  constructor
  · refine ⟨hp.2.1, hp.2.2, ?_⟩
    change -(p.2 + -(p.1 + p.2)) ≠ 0
    rw [h₁]
    exact hp.1
  · refine ⟨hp.2.2, hp.1, ?_⟩
    change -(-(p.1 + p.2) + p.1) ≠ 0
    rw [h₂]
    exact hp.2.1

/-- On the genuine two-input frequencies, each first-low cyclic view is
insensitive to changing the symbol on the degenerate signed triads. -/
theorem radianFourBranchSymbol_low_eq_on_two_nonzero (ϑ : ℝ → ℝ)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16) {m m' : Joint → ℂ} (agree : EqOn m' m nonzeroSignedTriads)
    (i : Fin 3) (p : Joint) (hp : p.1 ≠ 0) (hq : p.2 ≠ 0) :
    radianFourBranchSymbol ϑ κ (radianLowSlotView m' i) 0 p = radianFourBranchSymbol ϑ κ (radianLowSlotView m i) 0 p := by
  by_cases hThird : -(p.1+p.2) = 0
  · simp only [radianFourBranchSymbol, (fourBranchWeight_zero_on_third_axis ϑ hCut hFlat hκ hκsmall p hp hThird).1,
      Complex.ofReal_zero, zero_mul]
  · have hpq : p ∈ nonzeroSignedTriads := ⟨hp,hq,hThird⟩
    have cycles := nonzeroSignedTriads_radianCycles hpq
    have hv : radianLowSlotView m' i p = radianLowSlotView m i p := by
      fin_cases i
      · exact agree hpq
      · exact agree cycles.2
      · exact agree cycles.1
    simp only [radianFourBranchSymbol, hv]

/-- At a box point with two nonzero input frequencies and vanishing
third frequency, the first two low weights vanish and the third is one.
Consequently the comparable value is independent of the axis value. -/
theorem radianFourBranchSymbol_comparable_eq_on_two_nonzero (ϑ : ℝ → ℝ)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16) {m m' : Joint → ℂ} (agree : EqOn m' m nonzeroSignedTriads)
    (p : Joint) (hp : p.1 ≠ 0) (hq : p.2 ≠ 0) :
    radianFourBranchSymbol ϑ κ m' 3 p = radianFourBranchSymbol ϑ κ m 3 p := by
  by_cases hThird : -(p.1+p.2) = 0
  · simp only [radianFourBranchSymbol, (fourBranchWeight_zero_on_third_axis ϑ hCut hFlat hκ hκsmall p hp hThird).2,
      Complex.ofReal_zero, zero_mul]
  · simp only [radianFourBranchSymbol, agree (show p ∈ nonzeroSignedTriads from ⟨hp,hq,hThird⟩)]

private theorem analyticNearComparableBudget_eq_on_two_nonzero {N : ℕ} {A : ℝ} {m m' : Joint → ℂ}
    (agree : ∀ p : Joint, p.1 ≠ 0 → p.2 ≠ 0 → m' p = m p) :
    AnalyticNearComparableBudget N A m → AnalyticNearComparableBudget N A m' := by
  rintro ⟨G,smooth,jets,pointwise⟩
  refine ⟨G,smooth,jets,?_⟩
  intro k hk ζ υ hζ hυ
  have nz (z : E) (hz : endpointHighProfile z ≠ 0) : z ≠ 0 :=
    norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1/2).trans (endpointHighProfile_properties.2.2 z hz).1)
  exact (pointwise k hk ζ υ hζ hυ).trans
    (agree (((2 : ℝ)^k) • ζ,υ) (smul_ne_zero (zpow_pos (by norm_num : (0 : ℝ) < 2) k).ne' (nz ζ hζ)) (nz υ hυ)).symm

/-- The original symbol is specified on the nonzero signed frequency triads. -/
structure AnalyticNearOriginalSymbol (m : Joint → ℂ) : Prop where
  continuous : ContinuousOn m nonzeroSignedTriads
  bounded : ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ nonzeroSignedTriads, ‖m p‖ ≤ B
  homogeneous : ∀ t : ℝ, 0 < t → ∀ p ∈ nonzeroSignedTriads, m (t • p) = m p

/-- The original unscaled atlas identifies all positive-ratio low branches.
The compatibility of the one-sided traces is supplied by the same atlas. -/
def AnalyticNearPositiveAtlas (ϑ : ℝ → ℝ) (κ b A : ℝ) (m : Joint → ℂ) : Prop :=
  ∀ slot : Fin 3, ∃ M : WardPairChart → Point → ℂ,
    (∀ i, ContDiffOn ℝ 100 (M i) (wardPairChartDomain i ×ˢ Ico (0 : ℝ) b)) ∧
    (∀ i n, n ≤ 100 → ∀ z ∈ wardPairChartDomain i ×ˢ Ico (0 : ℝ) b,
      ‖iteratedFDerivWithin ℝ n (M i) (wardPairChartDomain i ×ˢ Ico (0 : ℝ) b) z‖ ≤ A) ∧
    ∀ i pq, pq ∈ wardPairChartAnnulus i → ∀ t : ℝ, 0 < t →
      let ρ := t*(‖pq.1‖/‖pq.2‖)
      ρ ∈ Ioo (0 : ℝ) b →
        radianFourBranchSymbol ϑ κ (radianLowSlotView m slot) 0 (t • pq.1,pq.2) =
          M i (wardPairChartAngles i pq,ρ)

/-- The literal capped comparable boxes and signed low profiles before
constructing the bounded zero-ratio representative. -/
def AnalyticNearSignedCapProfiles (ϑ : ℝ → ℝ) (κ b R A : ℝ) (N : ℕ)
    {metric : Form} {δ η inner outer enlarged D : ℝ} (hδ : δ ≠ 0)
    (S : SmoothThinConeCaps metric δ η inner outer enlarged D)
    (chart : ∀ γ : ↑S.centers, NullCapChart metric γ) (m : Joint → ℂ) : Prop :=
  ∀ γ : ↑S.centers,
    let a := capFrequencyEquiv (chart γ) hδ
    let K := tsupport (enlargedCapMultiplier metric δ η outer enlarged γ)
    let mγ := ((δ^2)⁻¹ • capLocalizedNearSymbol S m γ : Joint → ℂ)
    let low (i : Fin 3) := radianFourBranchSymbol ϑ κ (radianLowSlotView mγ i) 0 ∘ pairedFrequencyEquiv a
    let comparable := radianFourBranchSymbol ϑ κ mγ 3 ∘ pairedFrequencyEquiv a
    (∃ M : Fin 3 → E → E → ℝ → ℂ,
      (∀ i s, ContDiffOn ℝ 100 (signedEndpointProfile (M i) s)
        (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b)) ∧
      (∀ i s n, n ≤ 100 → ∀ z ∈ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b,
        ‖iteratedFDerivWithin ℝ n (signedEndpointProfile (M i) s)
          (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) z‖ ≤ A) ∧
      ∀ (i : Fin 3) (p : Joint), a p.1 ∈ K → a p.2 ∈ K → a (-(p.1+p.2)) ∈ K →
        ‖a p.1‖/‖a p.2‖ ∈ Ioo (0 : ℝ) b →
          low i p = M i (endpointDirection p.1) (endpointDirection p.2) (‖a p.1‖/‖a p.2‖)) ∧
      AnalyticNearComparableBudget N A comparable

private theorem analyticNearPositiveAtlas_congr_nonzero (ϑ : ℝ → ℝ)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    {κ b A : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16) {m m' : Joint → ℂ} (agree : EqOn m' m nonzeroSignedTriads) :
    AnalyticNearPositiveAtlas ϑ κ b A m → AnalyticNearPositiveAtlas ϑ κ b A m' := by
  intro atlas slot
  obtain ⟨M, smooth, jets, positive⟩ := atlas slot
  refine ⟨M, smooth, jets, ?_⟩
  intro i pq hpq t ht ρ hρ
  have hp : pq.1 ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1/4).trans hpq.1.1)
  have hq : pq.2 ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1/4).trans hpq.2.1)
  exact (radianFourBranchSymbol_low_eq_on_two_nonzero ϑ hCut hFlat hκ hκsmall agree slot
    (t • pq.1,pq.2) (smul_ne_zero ht.ne' hp) hq).trans (positive i pq hpq t ht hρ)

private theorem analyticNearSignedCapProfiles_congr_nonzero (ϑ : ℝ → ℝ)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    {κ b R A : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16) (N : ℕ)
    {metric : Form} {δ η inner outer enlarged D : ℝ} (hδ : δ ≠ 0)
    (S : SmoothThinConeCaps metric δ η inner outer enlarged D)
    (chart : ∀ γ : ↑S.centers, NullCapChart metric γ) {m m' : Joint → ℂ} (agree : EqOn m' m nonzeroSignedTriads) :
    AnalyticNearSignedCapProfiles ϑ κ b R A N hδ S chart m →
      AnalyticNearSignedCapProfiles ϑ κ b R A N hδ S chart m' := by
  intro src γ a K m'γ low comparable
  let mγ := ((δ^2)⁻¹ • capLocalizedNearSymbol S m γ : Joint → ℂ)
  have agreeγ : EqOn m'γ mγ nonzeroSignedTriads := by
    intro p hp
    simp only [m'γ,mγ,Pi.smul_apply,capLocalizedNearSymbol,agree hp]
  obtain ⟨⟨M,smooth,jets,positive⟩,comp⟩ := src γ
  refine ⟨⟨M,smooth,jets,?_⟩,?_⟩
  · intro i p h₁ h₂ h₃ hRatio
    have hp : a p.1 ≠ 0 := fun hp => by
      have hpos := hRatio.1
      simp [hp] at hpos
    have hq : a p.2 ≠ 0 := fun hq => by
      have hpos := hRatio.1
      simp [hq] at hpos
    exact (radianFourBranchSymbol_low_eq_on_two_nonzero ϑ hCut hFlat hκ hκsmall agreeγ i (a p.1,a p.2) hp hq).trans
      (positive i p h₁ h₂ h₃ hRatio)
  · apply analyticNearComparableBudget_eq_on_two_nonzero _ comp
    intro p hp hq
    have hn₁ : a p.1 ≠ 0 := fun h => hp (a.injective (h.trans a.map_zero.symm))
    have hn₂ : a p.2 ≠ 0 := fun h => hq (a.injective (h.trans a.map_zero.symm))
    exact radianFourBranchSymbol_comparable_eq_on_two_nonzero ϑ hCut hFlat hκ hκsmall agreeγ (a p.1,a p.2) hn₁ hn₂

private theorem analyticNearFormBound_of_eq_form (windows : Fin 3 → Option AnalyticNearInfraredWindow)
    {m m' : Joint → ℂ} {C : ℝ}
    (same : ∀ f g w : SchwartzMap E ℂ, radianTrilinearForm m' f g w = radianTrilinearForm m f g w) :
    AnalyticNearFormBound windows m' C → AnalyticNearFormBound windows m C := by
  intro h
  refine ⟨fun f g w => ?_, fun I J L a b c ha hb hc f g w => ?_⟩
  · simpa only [same] using h.1 f g w
  · simpa only [same] using h.2 I J L a b c ha hb hc f g w

/-- The original unscaled input goes to the full and finitely truncated
forms. Its one-sided traces and bounded Borel representative are produced
before applying the ordinary estimate. -/
theorem analyticNear_unscaled_originalFormBound
    (ϑ : ℝ → ℝ) (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (κ b : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16) (hb : 0 < b)
    (windows : Fin 3 → Option AnalyticNearInfraredWindow) (N : ℕ) (C : ℝ)
    (estimate : ∀ (m : Joint → ℂ), AnalyticNearSymbol m → ∀ A ≥ 0,
      AnalyticNearUnscaledLowBudget ϑ κ b A m →
      AnalyticNearComparableBudget N A (radianFourBranchSymbol ϑ κ m 3) → AnalyticNearFormBound windows m (C*A))
    (m : Joint → ℂ) (hm : AnalyticNearOriginalSymbol m) (A : ℝ) (hA : 0 ≤ A)
    (atlas : AnalyticNearPositiveAtlas ϑ κ b A m)
    (boxes : AnalyticNearComparableBudget N A (radianFourBranchSymbol ϑ κ m 3)) :
    AnalyticNearFormBound windows m (C*A) := by
  obtain ⟨B,hB,hBound⟩ := hm.bounded
  obtain ⟨m', sym, same, sameForm⟩ := exists_analyticNearSymbol_of_nonzeroSignedTriads m B hB hm.continuous hBound hm.homogeneous
  have atlas' := analyticNearPositiveAtlas_congr_nonzero ϑ hCut hFlat hκ hκsmall same atlas
  have hLow := analyticNearUnscaledLowBudget_of_positiveAtlas ϑ κ b A hb hA m' atlas'
  have hBoxes := analyticNearComparableBudget_eq_on_two_nonzero
    (radianFourBranchSymbol_comparable_eq_on_two_nonzero ϑ hCut hFlat hκ hκsmall same) boxes
  exact analyticNearFormBound_of_eq_form windows sameForm (estimate m' sym A hA hLow hBoxes)

/-- On a fixed actual cap family, apply the near estimate to the original
symbol and signed profiles, with both measurable endpoints constructed. -/
theorem analyticNear_cap_originalFormBound
    (ϑ : ℝ → ℝ) (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (κ b R : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16) (hb : 0 < b) (hR : R < 1)
    (windows : Fin 3 → Option AnalyticNearInfraredWindow) (N : ℕ) (C : ℝ)
    {metric : Form} {δ η inner outer enlarged D : ℝ} (hδ : δ ≠ 0)
    (S : SmoothThinConeCaps metric δ η inner outer enlarged D) (chart : ∀ γ : ↑S.centers, NullCapChart metric γ)
    (estimate : ∀ (m : Joint → ℂ), AnalyticNearSymbol m → AnalyticNearAdjacentSupport metric δ η inner m →
      ∀ A ≥ 0, AnalyticNearCapBudget ϑ κ b R A N hδ S chart m → AnalyticNearFormBound windows m (C*A))
    (m : Joint → ℂ) (hm : AnalyticNearOriginalSymbol m) (adj : AnalyticNearAdjacentSupport metric δ η inner m)
    (A : ℝ) (hA : 0 ≤ A) (profiles : AnalyticNearSignedCapProfiles ϑ κ b R A N hδ S chart m) :
    AnalyticNearFormBound windows m (C*A) := by
  obtain ⟨B,hB,hBound⟩ := hm.bounded
  obtain ⟨m', sym, same, sameForm⟩ := exists_analyticNearSymbol_of_nonzeroSignedTriads m B hB hm.continuous hBound hm.homogeneous
  have adj' : AnalyticNearAdjacentSupport metric δ η inner m' := by
    intro p hmp hp hq hr
    have h := same p (show p ∈ nonzeroSignedTriads from ⟨hp,hq,hr⟩)
    exact adj p (h ▸ hmp) hp hq hr
  have profiles' := analyticNearSignedCapProfiles_congr_nonzero ϑ hCut hFlat hκ hκsmall N hδ S chart same profiles
  have budget := analyticNearCapBudget_of_signed_profiles ϑ κ b R A N hδ S chart m' hR hb hA profiles'
  exact analyticNearFormBound_of_eq_form windows sameForm (estimate m' sym adj' A hA budget)

/-- Original-symbol entrance to the manuscript all-scale theorem, keeping
the same factorwise windows, cap geometry and order of the constants. -/
theorem exists_analyticNear_original_allScale_bound
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (κ b : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16) (hb : 7*κ/4 < b)
    (windows : Fin 3 → Option AnalyticNearInfraredWindow)
    {K : Set Form} (hK : IsCompact K) (hFrame : ∀ metric ∈ K, Nonempty (LorentzFrame metric))
    (hND : ∀ metric ∈ K, Nondegenerate metric)
    (inner outer enlarged : ℝ) (hIn : 0 ≤ inner) (hIO : inner < outer) (hOE : outer < enlarged) :
    ∃ (N₀ : ℕ) (C₀ B D c₀ δ₀ : ℝ),
      0 ≤ C₀ ∧ 0 < B ∧ 0 < D ∧ 0 < c₀ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      (∀ (m : Joint → ℂ), AnalyticNearOriginalSymbol m → ∀ A ≥ 0,
        AnalyticNearPositiveAtlas ϑ κ b A m →
        AnalyticNearComparableBudget N₀ A (radianFourBranchSymbol ϑ κ m 3) →
        AnalyticNearFormBound windows m (C₀*A)) ∧
      ∀ c : ℝ, 0 < c → c ≤ c₀ →
        ∃ (R : ℝ) (N : ℕ) (C₃ : ℝ) (Cang Cnear : {q : ℝ // 3 < q} → ℝ),
          0 < R ∧ R < 1 ∧ 0 ≤ C₃ ∧ (∀ q, 0 ≤ Cang q) ∧ (∀ q, 0 ≤ Cnear q) ∧
          ∀ metric ∈ K, ∀ δ ∈ Ioc (0 : ℝ) δ₀,
            ∃ (hδ : δ ∈ Ioc (0 : ℝ) 1)
              (S : SmoothThinConeCaps metric δ (c*κ*δ^2) inner outer enlarged D)
              (Pplus : ∀ γ : ↑S.centers, CapLpRealization (ENNReal.ofReal 3)
                (enlargedCapMultiplier metric δ (c*κ*δ^2) outer enlarged γ) C₃)
              (chart : ∀ γ : ↑S.centers, NullCapChart metric γ),
              (∀ γ, ‖(chart γ).toFrequency.toContinuousLinearMap‖ ≤ B) ∧
              (∀ γ, ‖(chart γ).toFrequency.symm.toContinuousLinearMap‖ ≤ B) ∧
              (∀ (q : {q : ℝ // 3 < q}) (v : FieldLp Unit (ENNReal.ofReal 3)),
                (∑ γ : ↑S.centers, ‖(Pplus γ).fieldAction v‖^3)^(1/3 : ℝ) ≤
                  Cang q * (S.centers.card : ℝ)^(1/(3*(q.val-2))) * ‖v‖) ∧
              ∀ (pStar : {q : ℝ // 3 < q}) (m : Joint → ℂ), AnalyticNearOriginalSymbol m →
                AnalyticNearAdjacentSupport metric δ (c*κ*δ^2) inner m →
                ∀ A ≥ 0, AnalyticNearSignedCapProfiles ϑ κ b R A N hδ.1.ne' S chart m →
                  AnalyticNearFormBound windows m
                    (Cnear pStar*A*δ^(2*(pStar.val-3)/(pStar.val-2))) := by
  have hb₀ : 0 < b := (by positivity : 0 < 7*κ/4).trans hb
  obtain ⟨N₀,C₀,B,D,c₀,δ₀,hC₀,hB,hD,hc₀,hδ₀,hδone,unscaled,caps⟩ :=
    exists_analyticNear_allScale_bound ϑ hϑ hRange hCut hFlat κ b hκ hκsmall hb windows hK hFrame hND
      inner outer enlarged hIn hIO hOE
  refine ⟨N₀,C₀,B,D,c₀,δ₀,hC₀,hB,hD,hc₀,hδ₀,hδone,
    analyticNear_unscaled_originalFormBound ϑ hCut hFlat κ b hκ hκsmall hb₀ windows N₀ C₀ unscaled, ?_⟩
  intro c hc hcs
  obtain ⟨R,N,C₃,Cang,Cnear,hR,hRone,hC₃,hCang,hCnear,hCaps⟩ := caps c hc hcs
  refine ⟨R,N,C₃,Cang,Cnear,hR,hRone,hC₃,hCang,hCnear,?_⟩
  intro metric hmetric δ hδsmall
  obtain ⟨hδ,S,Pplus,chart,forward,inverse,angular,near⟩ := hCaps metric hmetric δ hδsmall
  refine ⟨hδ,S,Pplus,chart,forward,inverse,angular,?_⟩
  intro pStar m hm adj A hA profiles
  let F := δ^(2*(pStar.val-3)/(pStar.val-2))
  have close (m : Joint → ℂ) (sym : AnalyticNearSymbol m)
      (adj : AnalyticNearAdjacentSupport metric δ (c*κ*δ^2) inner m) (A : ℝ) (hA : 0 ≤ A)
      (budget : AnalyticNearCapBudget ϑ κ b R A N hδ.1.ne' S chart m) :
      AnalyticNearFormBound windows m ((Cnear pStar*F)*A) := by
    have h := near pStar m sym adj A hA budget
    convert h using 1
    dsimp only [F]
    ring
  have h := analyticNear_cap_originalFormBound ϑ hCut hFlat κ b R hκ hκsmall hb₀ hRone windows N
    (Cnear pStar*F) hδ.1.ne' S chart close m hm adj A hA profiles
  convert h using 1
  dsimp only [F]
  ring

end Burnett.A05

#print axioms Burnett.A05.radianFourBranchSymbol_low_eq_on_two_nonzero
#print axioms Burnett.A05.radianFourBranchSymbol_comparable_eq_on_two_nonzero
#print axioms Burnett.A05.analyticNear_unscaled_originalFormBound
#print axioms Burnett.A05.analyticNear_cap_originalFormBound
#print axioms Burnett.A05.exists_analyticNear_original_allScale_bound
