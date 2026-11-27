import Burnett.Analysis.CubicEnergy.AngularCorrection.CorrectionLipschitzGradientNorm

set_option autoImplicit false

noncomputable section

namespace Burnett.A08

open MeasureTheory Metric Set Burnett.A06 Burnett.A07 Burnett.A02.FrequencySplit Burnett.Fourier
open scoped ComplexConjugate ContDiff ENNReal NNReal

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The original scalar correction estimates with the essential supremum
of the coefficient gradient in the rough commutator bound. -/
structure PaperAnalyticCorrectionBounds (b : Joint → ℂ) (C : ℝ)
    extends OriginalAnalyticCorrectionBounds b C where
  rough_gradient (d : E → ℝ) {L : ℝ≥0} (_ : LipschitzWith L d) (H v : SchwartzMap E ℂ) :
    ∃ U V : FirstOrderLp 2,
      ‖U‖ ≤ C * lipschitzGradientLInfty d * ‖H.toLp 4 volume‖ * ‖v.toLp 4 volume‖ ∧
      ‖V‖ ≤ C * lipschitzGradientLInfty d * ‖H.toLp 4 volume‖ * ‖v.toLp 4 volume‖ ∧
      ∀ w : SchwartzMap E ℂ,
        inner ℂ (w.toLp 2 volume) U = -radianHighCommutatorPair b d H v w ∧
        inner ℂ (w.toLp 2 volume) V =
          -radianHighCommutatorPair (highAdjointSymbol b) d (fun x => conj (H x)) v w

/-- Manuscript `lem:analytic-correction-bounds` for a smooth independent-variable
profile. The forward and adjoint estimates share the cutoff, derivative
threshold and constant. -/
theorem exists_paperAnalyticCorrectionBounds
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1/2) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
    ∃ (K : ℕ) (C : ℝ), 27 ≤ K ∧ 0 ≤ C ∧
      ∀ {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)}, IsOpen W →
      Q ×ˢ sphere (0 : RotationSpace) 1 ⊆ W → ContDiffOn ℝ ∞ F W →
      ∀ M : ℝ, 0 ≤ M →
      (∀ n ≤ K, ∀ p ∈ Q, ∀ x : RoundSphere3, ‖iteratedFDeriv ℝ n F (p, (x : RotationSpace))‖ ≤ M) →
      Nonempty (PaperAnalyticCorrectionBounds (originalRegularizedAngularSymbol η χ F) (C * M)) := by
  intro Q
  obtain ⟨K,C,hK,hC,bounds⟩ := exists_originalAnalyticCorrectionBounds
    η χ hr hρ hsmall hR hη hzero hone hχ hcut
  refine ⟨K,C,hK,hC,?_⟩
  intro F W hW hQ hF M hM hjet
  obtain ⟨P⟩ := bounds hW hQ hF M hM hjet
  exact ⟨⟨P, fun d {L} hd H v => P.lipschitz_commutator_gradientLInfty d (L := L) hd H v⟩⟩

end Burnett.A08
