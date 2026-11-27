import Burnett.Analysis.AllScaleTransfer.OriginalBranchRegularity

set_option autoImplicit false
set_option maxRecDepth 8500
set_option maxHeartbeats 10000000

noncomputable section

namespace Burnett.A05

open Burnett.A02.FrequencySplit Burnett.C02
open scoped ContDiff

/-- A box budget on a larger interval restricts to all smaller intervals
with the same extensions and bound. -/
theorem AnalyticNearComparableBudget.restrict {N M : ℕ} {A : ℝ} {f : Joint → ℂ} (hNM : N ≤ M)
    (boxes : AnalyticNearComparableBudget M A f) : AnalyticNearComparableBudget N A f := by
  obtain ⟨G,hSmooth,hJets,hPoint⟩ := boxes
  have hSub : Finset.Icc (-(N : ℤ)) (N : ℤ) ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
    intro k hk
    obtain ⟨low,high⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  exact ⟨G,fun k hk => hSmooth k (hSub hk),fun k hk => hJets k (hSub hk),fun k hk => hPoint k (hSub hk)⟩

/-- The original unscaled symbol may be supplied by its homogeneous law,
positive-ratio atlas and comparable boxes. The finite window threshold is
chosen to cover both the actual branches and the existing form estimate. -/
theorem exists_analyticNear_original_unscaled_of_atlas
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (κ b : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16) (hb : 7*κ/4 < b)
    (windows : Fin 3 → Option AnalyticNearInfraredWindow) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (m : Joint → ℂ),
      (∀ t : ℝ, 0 < t → ∀ p ∈ nonzeroSignedTriads, m (t • p) = m p) → ∀ A ≥ 0,
      AnalyticNearPositiveAtlas ϑ κ b A m →
      AnalyticNearComparableBudget N A (radianFourBranchSymbol ϑ κ m 3) →
      AnalyticNearFormBound windows m (C*A) := by
  obtain ⟨N₀,C,hC,forms⟩ := exists_wardUnscaledTrilinearForm_full_truncated_bound
    ϑ hϑ hRange hCut hFlat κ b hκ hκsmall hb
  obtain ⟨Ncov,hCover⟩ := exists_analyticNearComparableCoverage hCut hFlat hκ hκsmall
  obtain ⟨W,hW,windowBound⟩ := exists_analyticNear_window_bound windows
  have estimate (m : Joint → ℂ) (sym : AnalyticNearSymbol m) (A : ℝ) (hA : 0 ≤ A)
      (lo : AnalyticNearUnscaledLowBudget ϑ κ b A m)
      (co : AnalyticNearComparableBudget N₀ A (radianFourBranchSymbol ϑ κ m 3)) :
      AnalyticNearFormBound windows m ((W*C)*A) := by
    obtain ⟨B,hB,hNorm⟩ := sym.bounded
    have base : AnalyticNearFormBound (fun _ => none) m (C*A) :=
      forms m B hB sym.measurable hNorm sym.homogeneous A hA lo co
    simpa only [mul_assoc] using windowBound m (C*A) (mul_nonneg hC hA) base
  refine ⟨max N₀ Ncov,W*C,mul_nonneg hW hC,?_⟩
  intro m hom A hA atlas boxes
  have sym := analyticNearOriginalSymbol_of_positiveAtlas_boxes ϑ hϑ.continuous hCut hκ hκsmall
    hb hA m hom atlas hCover (boxes.restrict (le_max_right _ _))
  have hb₀ : 0 < b := (by positivity : 0 < 7*κ/4).trans hb
  exact analyticNear_unscaled_originalFormBound ϑ hCut hFlat κ b hκ hκsmall hb₀ windows N₀ (W*C)
    estimate m sym A hA atlas (boxes.restrict (le_max_left _ _))

end Burnett.A05

#print axioms Burnett.A05.AnalyticNearComparableBudget.restrict
#print axioms Burnett.A05.exists_analyticNear_original_unscaled_of_atlas
