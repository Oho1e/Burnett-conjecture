import Burnett.Analysis.CubicEnergy.AngularCorrection.PaperAnalyticCorrectionBounds

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.A08

open Filter MeasureTheory Metric Set Burnett.A06 Burnett.A07 Burnett.A02.FrequencySplit Burnett.Fourier
open scoped ContDiff ENNReal NNReal Topology

local instance inhomogeneousRadialCorrectionOneLeTwo : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance inhomogeneousRadialCorrectionOneLeFour : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The original angular symbol with a fixed radial weight in its high slot. -/
def inhomogeneousRadialCorrectionSymbol (η χ weight : ℝ → ℝ)
    (F : Joint × RotationSpace → ℂ) (x : Joint) : ℂ :=
  (η ‖x.2‖ * weight ‖x.2‖) •
    (χ (‖(normalizedHighPair x).1‖ ^ 2) • F (normalizedHighPair x, roundSphereRadialNormalize x.1))

/-- The inhomogeneous coordinate Sobolev norm on the high test field. -/
def correctionHighW14Norm (u : SchwartzMap E ℂ) : ℝ :=
  ‖u.toLp 4 volume‖ + schwartzGradientNorm 4 u

private def effectiveHighCutoff (η weight : ℝ → ℝ) (x : ℝ) : ℝ :=
  η x * (weight x / x)

private theorem effectiveHighCutoff_contDiff (η weight : ℝ → ℝ) {r : ℝ}
    (hr : 0 < r) (hη : ContDiff ℝ ∞ η) (hw : ContDiff ℝ ∞ weight)
    (hzero : ∀ x ≤ r, η x = 0) :
    ContDiff ℝ ∞ (effectiveHighCutoff η weight) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hr] with y hy
    change η y * (weight y / y) = 0
    rw [hzero y hy.le, zero_mul]
  · exact hη.contDiffAt.mul (hw.contDiffAt.div contDiffAt_id hx)

private theorem effectiveHighCutoff_symbol_eq (η χ weight : ℝ → ℝ) {r : ℝ}
    (hr : 0 < r) (hzero : ∀ x ≤ r, η x = 0) (F : Joint × RotationSpace → ℂ) :
    originalRegularizedAngularSymbol (effectiveHighCutoff η weight) χ F =
      inhomogeneousRadialCorrectionSymbol η χ weight F := by
  funext x
  have hweight : effectiveHighCutoff η weight ‖x.2‖ * ‖x.2‖ = η ‖x.2‖ * weight ‖x.2‖ := by
    unfold effectiveHighCutoff
    by_cases hx : ‖x.2‖ = 0
    · simp [hx, hzero 0 hr.le]
    · rw [mul_assoc, div_mul_cancel₀ _ hx]
  unfold originalRegularizedAngularSymbol regularizedLowCartesianSymbol lowCartesianSymbol
    inhomogeneousRadialCorrectionSymbol
  rw [smul_smul, hweight]

/-- Replace the high radial weight by any fixed smooth weight that equals
the radius at large frequency. Both actual high slot actions retain the
rough bound and adjoint identities, with inhomogeneous high test norms
for their values and coordinate commutators. -/
theorem exists_paperRadialInhomogeneousAnalyticCorrectionBounds
    (η χ weight : ℝ → ℝ) {r ρ R Rw : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1 / 2) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0)
    (hw : ContDiff ℝ ∞ weight) (hwHigh : ∀ x ≥ Rw, weight x = x) :
    let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
    ∃ (K : ℕ) (C : ℝ), 27 ≤ K ∧ 0 ≤ C ∧
      ∀ {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)}, IsOpen W →
      Q ×ˢ sphere (0 : RotationSpace) 1 ⊆ W → ContDiffOn ℝ ∞ F W →
      ∀ M : ℝ, 0 ≤ M →
      (∀ n ≤ K, ∀ p ∈ Q, ∀ x : RoundSphere3, ‖iteratedFDeriv ℝ n F (p, (x : RotationSpace))‖ ≤ M) →
      ∃ P : PaperAnalyticCorrectionBounds (inhomogeneousRadialCorrectionSymbol η χ weight F) (C * M),
        (∀ H u : SchwartzMap E ℂ,
          ‖P.forward H u‖ ≤ C * M * ‖H.toLp 4 volume‖ * correctionHighW14Norm u ∧
          ‖P.adjoint H u‖ ≤ C * M * ‖H.toLp 4 volume‖ * correctionHighW14Norm u) ∧
        (∀ (i : Fin 4) (H u : SchwartzMap E ℂ),
          ‖P.forward (coordinateDerivative i H) u‖ ≤
            C * M * ‖(coordinateDerivative i H).toLp 4 volume‖ * correctionHighW14Norm u ∧
          ‖P.adjoint (coordinateDerivative i H) u‖ ≤
            C * M * ‖(coordinateDerivative i H).toLp 4 volume‖ * correctionHighW14Norm u) := by
  intro Q
  have hVanishing (x : ℝ) (hx : x ≤ r) : effectiveHighCutoff η weight x = 0 := by
    rw [effectiveHighCutoff, hzero x hx, zero_mul]
  have hHigh (x : ℝ) (hx : x ≥ max R Rw) : effectiveHighCutoff η weight x = 1 := by
    have hRx : R ≤ x := (le_max_left _ _).trans hx
    have hRwx : Rw ≤ x := (le_max_right _ _).trans hx
    have hxpos : 0 < x := (by norm_num : (0 : ℝ) < 1).trans_le (hR.trans hRx)
    rw [effectiveHighCutoff, hone x hRx, hwHigh x hRwx, div_self hxpos.ne', one_mul]
  obtain ⟨K, C, hK, hC, bounds⟩ := exists_paperAnalyticCorrectionBounds
    (effectiveHighCutoff η weight) χ hr hρ hsmall (hR.trans (le_max_left R Rw))
    (effectiveHighCutoff_contDiff η weight hr hη hw hzero) hVanishing hHigh hχ hcut
  refine ⟨K, C, hK, hC, ?_⟩
  intro F W hW hQ hF M hM hjet
  have estimate := bounds hW hQ hF M hM hjet
  rw [effectiveHighCutoff_symbol_eq η χ weight hr hzero F] at estimate
  obtain ⟨P⟩ := estimate
  have hNorm (u : SchwartzMap E ℂ) : schwartzGradientNorm 4 u ≤ correctionHighW14Norm u :=
    le_add_of_nonneg_left (norm_nonneg _)
  have weakBound (u : SchwartzMap E ℂ) (D : ℝ) (hD : 0 ≤ D) :
      D * schwartzGradientNorm 4 u ≤ D * correctionHighW14Norm u :=
    mul_le_mul_of_nonneg_left (hNorm u) hD
  refine ⟨P, ?_, ?_⟩
  · intro H u
    obtain ⟨forward, adjoint⟩ := P.first_order H u
    have hD : 0 ≤ C * M * ‖H.toLp 4 volume‖ := mul_nonneg (mul_nonneg hC hM) (norm_nonneg _)
    exact ⟨forward.trans (weakBound u _ hD), adjoint.trans (weakBound u _ hD)⟩
  · intro i H u
    obtain ⟨forward, adjoint⟩ := P.derivative_first_order i H u
    have hD : 0 ≤ C * M * ‖(coordinateDerivative i H).toLp 4 volume‖ :=
      mul_nonneg (mul_nonneg hC hM) (norm_nonneg _)
    exact ⟨forward.trans (weakBound u _ hD), adjoint.trans (weakBound u _ hD)⟩

/-- A Japanese bracket on the plateau of a fixed radial profile, with the
ordinary radius outside the profile's support. -/
def windowedJapaneseHighWeight (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  x + φ x * (Real.sqrt (1 + x ^ 2) - x)

theorem windowedJapaneseHighWeight_profile (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) {Rw : ℝ}
    (hHigh : ∀ x ≥ Rw, φ x = 0) :
    ContDiff ℝ ∞ (windowedJapaneseHighWeight φ) ∧
    (∀ x ≥ Rw, windowedJapaneseHighWeight φ x = x) ∧
    (∀ x, φ x = 1 → windowedJapaneseHighWeight φ x = Real.sqrt (1 + x ^ 2)) := by
  have hArg : ContDiff ℝ ∞ (fun x : ℝ => 1 + x ^ 2) := contDiff_const.add (contDiff_id.pow 2)
  have hBracket : ContDiff ℝ ∞ (fun x : ℝ => Real.sqrt (1 + x ^ 2)) :=
    hArg.sqrt (fun x => by positivity)
  refine ⟨contDiff_id.add (hφ.mul (hBracket.sub contDiff_id)), ?_, ?_⟩
  · intro x hx
    simp [windowedJapaneseHighWeight, hHigh x hx]
  · intro x hx
    rw [windowedJapaneseHighWeight, hx, one_mul]
    ring

end Burnett.A08
