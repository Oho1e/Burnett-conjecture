import Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderOriginalAngularPairing
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.RadianHighDerivativeCommutator

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section

namespace Burnett.A07

open Burnett.A06 Burnett.A02.FrequencySplit Burnett.Fourier MeasureTheory Metric Set
open scoped ContDiff ENNReal

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The tested derivative commutator for the original unexpanded angular symbol.
The three derivative placements use the same angular series and infrared cutoff. -/
theorem originalRegularizedAngularPair_coordinateDerivative_commutator
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0)
    {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)}
    (hW : IsOpen W)
    (hK : (closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1) ×ˢ sphere (0 : RotationSpace) 1 ⊆ W)
    (hF : ContDiffOn ℝ ∞ F W) {M : ℝ} (hM : 0 ≤ M)
    (hjet : ∀ n ≤ 27, ∀ z ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1, ∀ d : RoundSphere3,
      ‖iteratedFDeriv ℝ n F (z, (d : RotationSpace))‖ ≤ M)
    (a : Fin 4) (H u w : SchwartzMap E ℂ) :
    -radianHighPair (originalRegularizedAngularSymbol η χ F) H u (coordinateDerivative a w) -
      radianHighPair (originalRegularizedAngularSymbol η χ F) H (coordinateDerivative a u) w =
        radianHighPair (originalRegularizedAngularSymbol η χ F) (coordinateDerivative a H) u w := by
  obtain ⟨_, _, coefficients⟩ := exists_smoothComplexAngularCoefficient_jet15 (E := Joint)
  obtain ⟨S, hS, hKS, jets⟩ :=
    coefficients hW ((isCompact_closedBall _ _).prod (isCompact_sphere _ _)) hK hF M hM hjet
  obtain ⟨_, _, harmonics⟩ := exists_sphereHarmonicMultiplier_Lp_bound 4 (by norm_num)
  have mode (i : HarmonicMode) :
      -radianHighPair (angularModeSymbol η χ F i) H u (coordinateDerivative a w) -
        radianHighPair (angularModeSymbol η χ F i) H (coordinateDerivative a u) w =
          radianHighPair (angularModeSymbol η χ F i) (coordinateDerivative a H) u w := by
    let b : OrderOneSymbol ℂ :=
      ⟨regularizedLowCartesianSymbol η χ (jointSphereHarmonicCoefficientComplex F i),
        regularizedLowCartesianSymbol_mem_orderOneSymbolSubmodule η χ _ hr hρ hR hη hzero hone
          hχ hcut hS hKS (jets i).1⟩
    obtain ⟨m, _, hm, _, _, _⟩ := harmonics i.1 i.2
    have hAngular : Measurable (sphereHarmonicMultiplierSymbol i.1 i.2 : E → ℝ) :=
      measurable_of_continuousOn_compl_singleton 0 (sphereHarmonicRadialSymbol_contDiffOn _ _).continuousOn
    have hMode : Measurable (angularModeSymbol η χ F i) :=
      (Complex.continuous_ofReal.measurable.comp (hAngular.comp measurable_fst)).mul b.measurable_symbol
    let P := orderOneWeightedSeminorm ℂ 0 b
    apply radianHighPair_coordinateDerivative_commutator a (angularModeSymbol η χ F i) hMode (m.bound * P)
      (mul_nonneg m.bound_nonneg (apply_nonneg _ _))
    intro p
    change ‖(sphereHarmonicMultiplierSymbol i.1 i.2 p.1 : ℂ) * (b : Joint → ℂ) p‖ ≤ _
    rw [norm_mul, ← hm p.1, mul_assoc]
    exact mul_le_mul (m.norm_le _) (b.norm_apply_le_weightedSeminorm_zero p) (norm_nonneg _) m.bound_nonneg
  have pairSum := originalRegularizedAngularPair_hasSum_of_smoothProfile
    η χ hr hρ hR hη hzero hone hχ hcut hW hK hF hM hjet
  have summed := (pairSum H u (coordinateDerivative a w)).neg.sub (pairSum H (coordinateDerivative a u) w)
  have differentiated :
      HasSum (fun i => radianHighPair (angularModeSymbol η χ F i) (coordinateDerivative a H) u w)
        (-radianHighPair (originalRegularizedAngularSymbol η χ F) H u (coordinateDerivative a w) -
          radianHighPair (originalRegularizedAngularSymbol η χ F) H (coordinateDerivative a u) w) := by
    convert summed using 1
    funext i
    exact (mode i).symm
  exact differentiated.unique (pairSum (coordinateDerivative a H) u w)

/-- The derivative commutator as an L² representative on the actual fixed-index
Schwartz fields. The same first-order output realizes the original Fourier pairings
and bounds the differentiated low field. -/
theorem exists_originalAngular_coordinateDerivative_commutator
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    let K := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)},
      IsOpen W → K ×ˢ sphere (0 : RotationSpace) 1 ⊆ W → ContDiffOn ℝ ∞ F W →
      ∀ M : ℝ, 0 ≤ M →
      (∀ n ≤ 27, ∀ p ∈ K, ∀ x : RoundSphere3, ‖iteratedFDeriv ℝ n F (p, (x : RotationSpace))‖ ≤ M) →
      ∃ T : SchwartzMap E ℂ → (FirstOrderLp 4 →L[ℂ] FirstOrderLp 2),
        (∀ u : SchwartzMap E ℂ, ∀ H : FirstOrderLp 4, ‖T u H‖ ≤ C * M * ‖H‖ * highDerivativeLp4Sum u) ∧
        (∀ H u w : SchwartzMap E ℂ,
          inner ℂ (w.toLp 2 volume) (T u (H.toLp 4 volume)) =
            radianHighPair (originalRegularizedAngularSymbol η χ F) H u w) ∧
        ∀ (a : Fin 4) (H u w : SchwartzMap E ℂ),
          -inner ℂ ((coordinateDerivative a w).toLp 2 volume) (T u (H.toLp 4 volume)) -
            inner ℂ (w.toLp 2 volume) (T (coordinateDerivative a u) (H.toLp 4 volume)) =
              inner ℂ (w.toLp 2 volume) (T u ((coordinateDerivative a H).toLp 4 volume)) := by
  obtain ⟨C, hC, firstOrder⟩ :=
    exists_originalAngular_firstOrder_L4_L2_bound η χ hr hρ hsmall hR hη hzero hone hχ hcut
  refine ⟨C, hC, ?_⟩
  intro F W hW hK hF M hM hjet
  choose T hNorm hPair using firstOrder hW hK hF M hM hjet
  refine ⟨T, hNorm, fun H u w => hPair u H w, ?_⟩
  intro a H u w
  rw [hPair, hPair, hPair]
  exact originalRegularizedAngularPair_coordinateDerivative_commutator
    η χ hr hρ hR hη hzero hone hχ hcut hW hK hF hM hjet a H u w

end Burnett.A07
