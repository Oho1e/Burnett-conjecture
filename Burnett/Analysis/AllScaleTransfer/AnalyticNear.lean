import Burnett.Analysis.AllScaleTransfer.AnalyticNearData
import Burnett.Analysis.AllScaleTransfer.AnalyticNearCapInputs

set_option autoImplicit false
set_option maxRecDepth 10500
set_option maxHeartbeats 18000000

noncomputable section

namespace Burnett.A05

open Set MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.C02
open Burnett.Analysis CapFourier ProjectiveNullCaps
open Burnett.RicciSymbol.TensorFrame (LorentzFrame)
open scoped ContDiff ENNReal

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

/-- All-scale transfer and angular summation in dimension four.
The unscaled estimate uses the three genuine low traces and the fixed
comparable boxes. For the near estimate a single actual cap family
provides the enlarged projectors, charts and angular bound. The kernel
is tested against arbitrary differentiated factors. -/
theorem exists_analyticNear_allScale_bound
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (κ b : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16) (hb : 7*κ/4 < b)
    (windows : Fin 3 → Option AnalyticNearInfraredWindow)
    {K : Set Form} (hK : IsCompact K) (hFrame : ∀ metric ∈ K, Nonempty (LorentzFrame metric))
    (hND : ∀ metric ∈ K, Nondegenerate metric)
    (inner outer enlarged : ℝ) (hIn : 0 ≤ inner) (hIO : inner < outer) (hOE : outer < enlarged) :
    ∃ (N₀ : ℕ) (C₀ B D c₀ δ₀ : ℝ),
      0 ≤ C₀ ∧ 0 < B ∧ 0 < D ∧ 0 < c₀ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      (∀ (m : Joint → ℂ), AnalyticNearSymbol m → ∀ A ≥ 0,
        AnalyticNearUnscaledLowBudget ϑ κ b A m →
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
              ∀ (pStar : {q : ℝ // 3 < q}) (m : Joint → ℂ), AnalyticNearSymbol m →
                AnalyticNearAdjacentSupport metric δ (c*κ*δ^2) inner m →
                ∀ A ≥ 0, AnalyticNearCapBudget ϑ κ b R A N hδ.1.ne' S chart m →
                  AnalyticNearFormBound windows m
                    (Cnear pStar*A*δ^(2*(pStar.val-3)/(pStar.val-2))) := by
  obtain ⟨N₀,C,hC,unscaled⟩ :=
    exists_wardUnscaledTrilinearForm_full_truncated_bound ϑ hϑ hRange hCut hFlat κ b hκ hκsmall hb
  obtain ⟨B,D,c₀,δ₀,hB,hD,hc₀,hδ₀,hδ₀one,caps⟩ :=
    exists_analyticNear_uniform_capInputs hK hFrame hND hIn hIO hOE
  obtain ⟨W,hW,windowBound⟩ := exists_analyticNear_window_bound windows
  refine ⟨N₀,W*C,B,D,c₀,δ₀,mul_nonneg hW hC,hB,hD,hc₀,hδ₀,hδ₀one,?_,?_⟩
  · intro m sym A hA low comparable
    obtain ⟨M,hM,hBound⟩ := sym.bounded
    have base : AnalyticNearFormBound (fun _ => none) m (C*A) :=
      unscaled m M hM sym.measurable hBound sym.homogeneous A hA low comparable
    simpa only [mul_assoc] using windowBound m (C*A) (mul_nonneg hC hA) base
  · intro c hc hcSmall
    let tube := c*κ
    have hTube : 0 < tube := mul_pos hc hκ
    obtain ⟨C₃,Cang,hC₃,hCang,chooseCaps⟩ := caps κ hκ hκsmall c hc hcSmall
    obtain ⟨R,N,Cκ,hR,hRone,hCκ,near⟩ := exists_adjacentNearTrilinearForm_full_truncated_bound
      ϑ hϑ hRange hCut hFlat B tube outer enlarged κ b hB hTube
      (hIn.trans hIO.le) hOE hκ hκsmall hb
    let Cnear (q : {q : ℝ // 3 < q}) := W*(Cκ*Cang q^3*D^(1/(q.val-2)))
    have hCnear (q : {q : ℝ // 3 < q}) : 0 ≤ Cnear q := by
      have hAng := hCang q
      dsimp only [Cnear]
      positivity
    refine ⟨R,N,C₃,Cang,Cnear,hR,hRone,hC₃,hCang,hCnear,?_⟩
    intro metric hMetric δ hδSmall
    obtain ⟨hδ,hSmall,S,Pplus,chart,hForward,hInverse,angular⟩ :=
      chooseCaps metric hMetric δ hδSmall
    refine ⟨hδ,S,Pplus,chart,hForward,hInverse,angular,?_⟩
    intro pStar m sym adj A hA budget
    have hδ₀' : 0 < δ := hδ.1
    have hη : 0 < tube*δ^2 := mul_pos hTube (pow_pos hδ₀' 2)
    have wider (s : E) (hs : InRelativeCone metric (inner*(tube*δ^2)) s) :
        |quadratic metric s| ≤ outer*(tube*δ^2)*‖s‖^2 :=
      hs.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hIO.le hη.le) (sq_nonneg ‖s‖))
    have plateaux (p : Joint) (hm : m p ≠ 0) (hp : p.1 ≠ 0) (hq : p.2 ≠ 0)
        (hr : -(p.1+p.2) ≠ 0) :
        |quadratic metric p.1| ≤ inner*(tube*δ^2)*‖p.1‖^2 ∧
        ∀ γ : ↑S.centers, capMultiplier S.centers metric δ (tube*δ^2) inner outer γ p.1 ≠ 0 →
          enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged γ p.1 = 1 ∧
          enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged γ p.2 = 1 ∧
          enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged γ (-(p.1+p.2)) = 1 := by
      obtain ⟨thinP,thinQ,thinR,edgeQ,edgeR⟩ := adj p hm hp hq hr
      refine ⟨thinP,fun γ hCap => ?_⟩
      exact S.enlarged_on_three_nearSlots γ γ.property p.1 p.2 (-(p.1+p.2)) hp hq hr
        (subset_tsupport _ hCap) edgeQ edgeR (wider p.2 thinQ) (wider _ thinR)
    obtain ⟨M,_,hBound⟩ := sym.bounded
    let C := Cκ*Cang pStar^3*D^(1/(pStar.val-2))*A*δ^(2*(pStar.val-3)/(pStar.val-2))
    have hCoeff : 0 ≤ C := by
      have hAng := hCang pStar
      dsimp only [C]
      positivity
    have base : AnalyticNearFormBound (fun _ => none) m C :=
      near S Pplus chart hForward hInverse pStar.property hδ hSmall hD hA (hCang pStar)
        (angular pStar) m M sym.measurable hBound sym.homogeneous plateaux budget
    have coeff : W*C = Cnear pStar*A*δ^(2*(pStar.val-3)/(pStar.val-2)) := by
      dsimp only [C,Cnear]
      ring
    exact coeff ▸ windowBound m C hCoeff base

end Burnett.A05
