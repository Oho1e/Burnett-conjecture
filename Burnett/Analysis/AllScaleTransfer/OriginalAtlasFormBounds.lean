import Burnett.Analysis.AllScaleTransfer.OriginalUnscaledAtlasFormBound
import Burnett.Analysis.AllScaleTransfer.OriginalSignedCapRegularity

set_option autoImplicit false
set_option maxRecDepth 9500
set_option maxHeartbeats 15000000

noncomputable section

namespace Burnett.A05

open Metric Set
open Burnett.A02.FrequencySplit Burnett.A05.BoxFourier
open Burnett.Analysis CapFourier ProjectiveNullCaps
open Burnett.RicciSymbol.TensorFrame (LorentzFrame)
open scoped ContDiff ENNReal

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

/-- Restrict the signed chart domains and the interval of comparable
offsets, retaining the original chart functions and pointwise matches. -/
theorem AnalyticNearSignedCapProfiles.restrict (ϑ : ℝ → ℝ) (κ : ℝ) {b R₁ R₂ A : ℝ}
    (hR : R₁ ≤ R₂) {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂)
    {metric : Form} {δ η inner outer enlarged D : ℝ} (hδ : δ ≠ 0)
    (S : SmoothThinConeCaps metric δ η inner outer enlarged D)
    (chart : ∀ γ : ↑S.centers, NullCapChart metric γ) (m : Joint → ℂ)
    (profiles : AnalyticNearSignedCapProfiles ϑ κ b R₂ A N₂ hδ S chart m) :
    AnalyticNearSignedCapProfiles ϑ κ b R₁ A N₁ hδ S chart m := by
  intro γ
  obtain ⟨⟨M,hSmooth,hJets,hMatch⟩,hBoxes⟩ := profiles γ
  let U₁ := capCorrectionAngles R₁ ×ˢ Ico (0 : ℝ) b
  let U₂ := capCorrectionAngles R₂ ×ˢ Ico (0 : ℝ) b
  have sub : U₁ ⊆ U₂ := Set.prod_mono (Set.prod_mono (ball_subset_ball hR) (ball_subset_ball hR)) Subset.rfl
  have diff₁ : UniqueDiffOn ℝ U₁ := (isOpen_ball.prod isOpen_ball).uniqueDiffOn.prod (uniqueDiffOn_Ico 0 b)
  have diff₂ : UniqueDiffOn ℝ U₂ := (isOpen_ball.prod isOpen_ball).uniqueDiffOn.prod (uniqueDiffOn_Ico 0 b)
  refine ⟨⟨M,fun i s => (hSmooth i s).mono sub,?_,hMatch⟩,hBoxes.restrict hN⟩
  intro i s n hn z hz
  have eq : iteratedFDerivWithin ℝ n (signedEndpointProfile (M i) s) U₁ z =
      iteratedFDerivWithin ℝ n (signedEndpointProfile (M i) s) U₂ z :=
    iteratedFDerivWithin_subset sub diff₁ diff₂ ((hSmooth i s).of_le (by exact_mod_cast hn)) hz
  rw [eq]
  exact hJets i s n hn z (sub hz)

/-- Both original A05 bounds from homogeneous symbols and their actual
positive-ratio atlas, comparable boxes, and signed near-cap profiles. -/
theorem exists_analyticNear_original_allScale_of_atlases
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (κ b : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16) (hb : 7*κ/4 < b)
    (windows : Fin 3 → Option AnalyticNearInfraredWindow)
    {K : Set Form} (hK : IsCompact K) (hFrame : ∀ metric ∈ K, Nonempty (LorentzFrame metric))
    (hND : ∀ metric ∈ K, Nondegenerate metric)
    (inner outer enlarged : ℝ) (hIn : 0 ≤ inner) (hIO : inner < outer) (hOE : outer < enlarged) :
    ∃ (N₀ : ℕ) (C₀ B D c₀ δ₀ : ℝ),
      0 ≤ C₀ ∧ 0 < B ∧ 0 < D ∧ 0 < c₀ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      (∀ (m : Joint → ℂ), (∀ t : ℝ, 0 < t → ∀ p ∈ nonzeroSignedTriads, m (t • p) = m p) → ∀ A ≥ 0,
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
                (∑ γ : ↑S.centers, ‖(Pplus γ).fieldAction v‖^3)^((1 : ℝ)/3) ≤
                  Cang q * (S.centers.card : ℝ)^(1/(3*(q.val-2))) * ‖v‖) ∧
              ∀ (pStar : {q : ℝ // 3 < q}) (m : Joint → ℂ),
                (∀ t : ℝ, 0 < t → ∀ p ∈ nonzeroSignedTriads, m (t • p) = m p) →
                AnalyticNearAdjacentSupport metric δ (c*κ*δ^2) inner m → ∀ A ≥ 0,
                AnalyticNearSignedCapProfiles ϑ κ b R A N hδ.1.ne' S chart m →
                AnalyticNearFormBound windows m (Cnear pStar*A*δ^(2*(pStar.val-3)/(pStar.val-2))) := by
  obtain ⟨N₀,C₀,hC₀,unscaled⟩ := exists_analyticNear_original_unscaled_of_atlas ϑ hϑ hRange hCut hFlat
    κ b hκ hκsmall hb windows
  obtain ⟨_,_,B,D,c₀,Δ,_,hB,hD,hc₀,hΔ,hΔ₁,_,caps⟩ := exists_analyticNear_original_allScale_bound
    ϑ hϑ hRange hCut hFlat κ b hκ hκsmall hb windows hK hFrame hND inner outer enlarged hIn hIO hOE
  let δ₀ := min Δ (1/(20*B))
  have hB₀ : 0 < 20*B := by positivity
  refine ⟨N₀,C₀,B,D,c₀,δ₀,hC₀,hB,hD,hc₀,lt_min hΔ (one_div_pos.mpr hB₀),
    (min_le_left _ _).trans hΔ₁,unscaled,?_⟩
  intro c hc hc₀'
  let tube := c*κ
  have hTube : 0 < tube := mul_pos hc hκ
  obtain ⟨R₁,N₁,C₃,Cang,Cnear,hR₁,hR₁one,hC₃,hCang,hCnear,near⟩ := caps c hc hc₀'
  obtain ⟨R₂,N₂,hR₂,hR₂one,hasSymbol⟩ := exists_analyticNearOriginalSymbol_of_signedCapProfiles ϑ
    hϑ.continuous hCut hFlat B tube outer enlarged hB hTube (hIn.trans hIO.le) hOE hκ hκsmall hb
  refine ⟨max R₁ R₂,max N₁ N₂,C₃,Cang,Cnear,hR₁.trans_le (le_max_left _ _),max_lt hR₁one hR₂one,
    hC₃,hCang,hCnear,?_⟩
  intro metric hm δ hδ₀
  obtain ⟨hδ,S,Pplus,chart,fwd,inv,angular,estimate⟩ :=
    near metric hm δ ⟨hδ₀.1,hδ₀.2.trans (min_le_left _ _)⟩
  refine ⟨hδ,S,Pplus,chart,fwd,inv,angular,?_⟩
  have hSmall : 4*B*(5*δ) ≤ 1 := by
    have e := (le_div_iff₀ hB₀).mp (hδ₀.2.trans (min_le_right Δ (1/(20*B))))
    nlinarith only [e]
  intro pStar m hom adj A hA profiles
  have prof₂ := profiles.restrict ϑ κ (le_max_right _ _) (le_max_right _ _) hδ.1.ne' S chart m
  have sym := hasSymbol hδ.1 hSmall hIO.le S chart inv m hom adj A hA prof₂
  exact estimate pStar m sym adj A hA
    (profiles.restrict ϑ κ (le_max_left _ _) (le_max_left _ _) hδ.1.ne' S chart m)

end Burnett.A05

#print axioms Burnett.A05.AnalyticNearSignedCapProfiles.restrict
#print axioms Burnett.A05.exists_analyticNear_original_allScale_of_atlases
