import Burnett.Analysis.CubicEnergy.AngularCorrection.LipschitzWeakQuarticBound

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section

namespace Burnett.A08

open MeasureTheory Metric Set Burnett.A06 Burnett.A07 Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal NNReal

local instance lipschitzWeakQuarticOneLeFour : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The paper's quartic estimate for the same original regularized
correction and arbitrary bounded real symmetric Lipschitz coefficients.
The constants are chosen before the symbol profile and all input fields. -/
theorem exists_paperAnalyticLipschitzQuarticBound
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
      ∃ P : PaperAnalyticCorrectionBounds (originalRegularizedAngularSymbol η χ F) (C*M),
        ∀ (d : Fin 4 → Fin 4 → E → ℝ) (D G : ℝ) (hD : 0 ≤ D), 0 ≤ G →
        ∀ (hbounded : ∀ i j x, |d i j x| ≤ D)
          (L : ℝ≥0) (hLip : ∀ i j, LipschitzWith L (d i j)),
        (∀ i j, d i j = d j i) → (∀ i j, lipschitzGradientLInfty (d i j) ≤ G) →
        ∀ H u : SchwartzMap E ℂ,
          let e (i j : Fin 4) := boundedRealCoefficient (d i j) D hD
            (hLip i j).continuous.measurable (hbounded i j)
          ‖Complex.I * boundedWeakDivergenceCommutatorPair P.toOriginalAnalyticCorrectionBounds e H u u‖ ≤
            32*C*M *
              (D * schwartzGradientNorm 2 u * schwartzGradientNorm 4 H * schwartzGradientNorm 4 u +
               G * schwartzGradientNorm 2 u * ‖H.toLp 4 volume‖ * schwartzGradientNorm 4 u) := by
  intro Q
  obtain ⟨K,C,hK,hC,bounds⟩ := exists_paperAnalyticCorrectionBounds
    η χ hr hρ hsmall hR hη hzero hone hχ hcut
  refine ⟨K,C,hK,hC,?_⟩
  intro F W hW hQ hF M hM hJet
  obtain ⟨P⟩ := bounds hW hQ hF M hM hJet
  have hZ : ∀ z ∈ Q ×ˢ sphere (0 : RotationSpace) 1, ‖F z‖ ≤ M := by
    rintro ⟨p,x⟩ ⟨hp,hx⟩
    simpa only [norm_iteratedFDeriv_zero] using hJet 0 (Nat.zero_le K) p hp ⟨x,hx⟩
  obtain ⟨b,B,hB,hb,hsize,hRep⟩ := exists_borelOriginalRegularizedAngularSymbol η χ hρ
    hη.continuous hone hχ.continuous hcut hQ hF.continuousOn M hM hZ
  refine ⟨P,?_⟩
  intro d D G hD hG hbounded L hLip hs hgrad H u e
  obtain ⟨_,_,_,_,_,hQuartic⟩ := P.boundedWeakDivergenceCommutator_bound (mul_nonneg hC hM)
    b hb B hB hsize hRep d D G hD hG hbounded L hLip hgrad H u hs
  simpa only [mul_assoc] using hQuartic

end Burnett.A08
