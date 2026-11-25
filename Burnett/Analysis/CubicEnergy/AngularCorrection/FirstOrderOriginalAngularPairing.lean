import Burnett.Analysis.CubicEnergy.AngularCorrection.ActualAngularFirstOrderBound
import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalAngularPairing
import Burnett.Analysis.CubicEnergy.AngularCorrection.PhysicalAngularMultiplierPairing

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section

namespace Burnett.A07

open Burnett.A06 Burnett.A02.FrequencySplit MeasureTheory Metric Set
open scoped ContDiff ENNReal

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The first-order bound on the whole low `L⁴` space realizes the unexpanded
original regularized angular symbol on the original Schwartz inputs. -/
theorem exists_originalAngular_firstOrder_L4_L2_bound
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    let K := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)},
      IsOpen W → K ×ˢ sphere (0 : RotationSpace) 1 ⊆ W → ContDiffOn ℝ ∞ F W →
      ∀ M : ℝ, 0 ≤ M →
      (∀ n ≤ 27, ∀ p ∈ K, ∀ x : RoundSphere3, ‖iteratedFDeriv ℝ n F (p,(x : RotationSpace))‖ ≤ M) →
      ∀ u : SchwartzMap E ℂ, ∃ T : FirstOrderLp 4 →L[ℂ] FirstOrderLp 2,
        (∀ H, ‖T H‖ ≤ C * M * ‖H‖ * highDerivativeLp4Sum u) ∧
        (∀ H w : SchwartzMap E ℂ,
          inner ℂ (w.toLp 2 volume) (T (H.toLp 4 volume)) =
            radianHighPair (originalRegularizedAngularSymbol η χ F) H u w) := by
  obtain ⟨C,hC,m,Y,hMsymbol,hY,assemble⟩ := exists_actualAngular_firstOrder_L4_L2_bound
    η χ hr hρ hsmall hR hη hzero hone hχ hcut
  refine ⟨C,hC,?_⟩
  intro F W hW hKW hF M hM hjet u
  obtain ⟨B,T,hB,hSeries⟩ := assemble hW hKW hF M hM hjet u
  refine ⟨T,fun H => (hSeries H).2.2.1.trans (hSeries H).2.2.2,?_⟩
  obtain ⟨_,_,coeff⟩ := exists_smoothComplexAngularCoefficient_jet15 (E := Joint)
  obtain ⟨V,hV,hKV,jet⟩ := coeff hW ((isCompact_closedBall _ _).prod (isCompact_sphere _ _)) hKW hF M hM hjet
  let b (i : HarmonicMode) : OrderOneSymbol ℂ :=
    ⟨regularizedLowCartesianSymbol η χ (jointSphereHarmonicCoefficientComplex F i),
      regularizedLowCartesianSymbol_mem_orderOneSymbolSubmodule η χ _ hr hρ hR hη hzero hone hχ hcut hV hKV (jet i).1⟩
  intro H w
  have mode (i : HarmonicMode) : inner ℂ (w.toLp 2 volume) (B i (Y i (H.toLp 4 volume))) =
      radianHighPair (angularModeSymbol η χ F i) H u w :=
    physicalAngularMultiplier_pair_eq (b i) u H w i (m i) (hMsymbol i) (Y i)
      (hY i H (H.memLp 2 volume) (H.memLp 4 volume)) (B i) (hB i)
  have hSum := (innerSL ℂ (w.toLp 2 volume)).hasSum (hSeries (H.toLp 4 volume)).1
  have hPhysical : HasSum (fun i => radianHighPair (angularModeSymbol η χ F i) H u w)
      (inner ℂ (w.toLp 2 volume) (T (H.toLp 4 volume))) := by
    convert hSum using 1
    funext i
    exact (mode i).symm
  exact hPhysical.unique (originalRegularizedAngularPair_hasSum_of_smoothProfile
    η χ hr hρ hR hη hzero hone hχ hcut hW hKW hF hM hjet H u w)

end Burnett.A07
