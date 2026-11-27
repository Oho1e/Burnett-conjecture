import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalAngularCutoff

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.A08.OriginalAngularCutoff

open Filter MeasureTheory Burnett.A08 Burnett.A07 Burnett.A06 Burnett.A02.FrequencySplit
open scoped ComplexConjugate ENNReal NNReal Topology

open private forwardBounds adjointBounds
  from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalAngularCutoff

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private abbrev Test := SchwartzMap E ℂ

variable {η χ : ℝ → ℝ} {F : Joint × RotationSpace → ℂ} {M C₀ C₁ : ℝ}

theorem full_firstOrder_norms (P : OriginalAngularCutoff η χ F M C₀ C₁) (H u : Test) :
    let B := 2 * (C₀ * M * ‖H.toLp 4 volume‖ * highDerivativeLp4Sum u)
    ‖P.fullForward H u‖ ≤ B ∧ ‖P.fullAdjoint H u‖ ≤ B :=
  ⟨(forwardBounds P H u).fullBound, (adjointBounds P H u).fullBound⟩

/-- The two finite-exponent bounds sum the same spherical series of the
original Fourier commutator. The first two high slots remain distinct. -/
theorem full_realSchwartz_rough_bounds (P : OriginalAngularCutoff η χ F M C₀ C₁)
    (d : SchwartzMap E ℝ) (L : ℝ≥0) (hL : LipschitzWith L d) (H u w : Test) :
    let C := 2 * (C₁ * M * (L : ℝ) * ‖H.toLp 4 volume‖)
    let pairing := radianHighCommutatorPair (originalRegularizedAngularSymbol η χ F) d H u w
    ‖pairing‖ ≤ C * ‖u.toLp 4 volume‖ * ‖w.toLp 2 volume‖ ∧
      ‖pairing‖ ≤ C * ‖u.toLp 2 volume‖ * ‖w.toLp 4 volume‖ := by
  let term (i : HarmonicMode) := radianHighCommutatorPair (angularModeSymbol η χ F i) d H u w
  have mul_eq (v : Test) :
      (realSchwartzMultiply d v : E → ℂ) = fun x => (d x : ℂ) * v x :=
    funext (realSchwartzMultiply_apply d v)
  have series : HasSum term
      (radianHighCommutatorPair (originalRegularizedAngularSymbol η χ F) d H u w) := by
    simpa only [term, radianHighCommutatorPair, mul_eq] using
      (P.originalSeries H (realSchwartzMultiply d u) w).sub (P.originalSeries H u (realSchwartzMultiply d w))
  have hC := P.nonnegRough
  have hM := P.nonnegM
  let A := C₁ * M * (L : ℝ) * ‖H.toLp 4 volume‖ * ‖u.toLp 4 volume‖ * ‖w.toLp 2 volume‖
  let B := C₁ * M * (L : ℝ) * ‖H.toLp 4 volume‖ * ‖u.toLp 2 volume‖ * ‖w.toLp 4 volume‖
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have a := (harmonic_series_estimate term hA (fun i => P.data.roughForward i d L hL H u w)).fullBound
  have b := (harmonic_series_estimate term hB (fun i => P.data.roughAdjoint i d L hL H u w)).fullBound
  rw [series.tsum_eq] at a b
  exact ⟨by simpa only [A, mul_assoc] using a, by simpa only [B, mul_assoc] using b⟩

theorem fullForward_derivative_pair (P : OriginalAngularCutoff η χ F M C₀ C₁)
    (a : Fin 4) (H u w : Test) :
    -inner ℂ ((coordinateDerivative a w).toLp 2 volume) (P.fullForward H u) -
      inner ℂ (w.toLp 2 volume) (P.fullForward H (coordinateDerivative a u)) =
        inner ℂ (w.toLp 2 volume) (P.fullForward (coordinateDerivative a H) u) := by
  rw [(P.fullPairs H u (coordinateDerivative a w)).1,
    (P.fullPairs H (coordinateDerivative a u) w).1, (P.fullPairs (coordinateDerivative a H) u w).1]
  have summed := (P.originalSeries H u (coordinateDerivative a w)).neg.sub
    (P.originalSeries H (coordinateDerivative a u) w)
  have differentiated :
      HasSum (fun i => radianHighPair (angularModeSymbol η χ F i) (coordinateDerivative a H) u w)
        (-radianHighPair (originalRegularizedAngularSymbol η χ F) H u (coordinateDerivative a w) -
          radianHighPair (originalRegularizedAngularSymbol η χ F) H (coordinateDerivative a u) w) := by
    convert summed using 1
    funext i
    exact (P.data.derivativePair i a H u w).symm
  exact differentiated.unique (P.originalSeries (coordinateDerivative a H) u w)

theorem fullAdjoint_derivative_pair (P : OriginalAngularCutoff η χ F M C₀ C₁)
    (a : Fin 4) (H u w : Test) :
    -inner ℂ ((coordinateDerivative a w).toLp 2 volume) (P.fullAdjoint H u) -
      inner ℂ (w.toLp 2 volume) (P.fullAdjoint H (coordinateDerivative a u)) =
        inner ℂ (w.toLp 2 volume) (P.fullAdjoint (coordinateDerivative a H) u) := by
  have dual (G v t : Test) :
      inner ℂ (t.toLp 2 volume) (P.fullAdjoint G v) =
        conj (inner ℂ (v.toLp 2 volume) (P.fullForward G t)) := by
    rw [(P.fullPairs G v t).2, (P.fullPairs G t v).1, radianHighPair_highAdjoint]
  rw [dual H u (coordinateDerivative a w), dual H (coordinateDerivative a u) w,
    dual (coordinateDerivative a H) u w]
  have h := congrArg (conj : ℂ → ℂ) (P.fullForward_derivative_pair a H w u)
  simp only [map_neg, map_sub] at h
  simpa only [sub_eq_add_neg, add_comm] using h

end Burnett.A08.OriginalAngularCutoff
