import Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension
import Burnett.Analysis.CubicEnergy.AngularHarmonics.SmoothAngularCoefficient
import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicActualMultiplier
import Burnett.Analysis.CubicEnergy.AngularHarmonics.HarmonicOperatorSum

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

namespace Burnett.A07

open Burnett.A06 Burnett.A02.FrequencySplit Burnett.Fourier MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private theorem exists_actualHarmonicLp4_multiplier :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : HarmonicMode,
      ∃ (m : BoundedSymbol E) (Y : FirstOrderLp 4 →L[ℂ] FirstOrderLp 4),
        (∀ ξ, m ξ = (sphereHarmonicMultiplierSymbol i.1 i.2 ξ : ℂ)) ∧
        ‖Y‖ ≤ C * ((i.1 : ℝ) + 1)^7 ∧
        ∀ (f : E → ℂ) (h₂ : MemLp f 2 volume) (h₄ : MemLp f 4 volume),
          (Y (h₄.toLp f) : E → ℂ) =ᵐ[volume]
            (fourierMultiplier m (h₂.toLp f) : E → ℂ) := by
  obtain ⟨C, hC, haveMode⟩ := exists_sphereHarmonicMultiplier_Lp_bound 4 (by norm_num)
  refine ⟨C, hC, fun i => ?_⟩
  let HasMultiplier (p : ℝ≥0∞) : Prop :=
    ∃ hp : Fact (1 ≤ p), letI := hp
      ∃ (m : BoundedSymbol E) (Y : FirstOrderLp p →L[ℂ] FirstOrderLp p),
        (∀ ξ, m ξ = (sphereHarmonicMultiplierSymbol i.1 i.2 ξ : ℂ)) ∧
        (∀ f, ‖Y f‖ ≤ C * ((i.1 : ℝ) + 1)^7 * ‖f‖) ∧
        ∀ (f : E → ℂ) (h₂ : MemLp f 2 volume) (hf : MemLp f p volume),
          (Y (hf.toLp f) : E → ℂ) =ᵐ[volume] (fourierMultiplier m (h₂.toLp f) : E → ℂ)
  have h : HasMultiplier (ENNReal.ofReal 4) := by
    letI : Fact (1 ≤ ENNReal.ofReal (4 : ℝ)) := ⟨by norm_num⟩
    obtain ⟨m, Y, hm, hY, compatibility, _⟩ := haveMode i.1 i.2
    exact ⟨inferInstance, m, Y, hm, hY, compatibility⟩
  have h4 : HasMultiplier 4 := (show ENNReal.ofReal (4 : ℝ) = 4 by norm_num) ▸ h
  obtain ⟨_, m, Y, hm, hY, compatibility⟩ := h4
  have hYnorm : ‖Y‖ ≤ C * ((i.1 : ℝ) + 1)^7 :=
    ContinuousLinearMap.opNorm_le_bound Y (by positivity) hY
  exact ⟨m, Y, hm, hYnorm, compatibility⟩

/-- The actual spherical modes, with their unmodified `L⁴` low input, give a
strong `L²` operator sum with the first-order bound of manuscript line 1385. -/
theorem exists_actualAngular_firstOrder_L4_L2_bound
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    let K := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ (m : HarmonicMode → BoundedSymbol E)
        (Y : HarmonicMode → FirstOrderLp 4 →L[ℂ] FirstOrderLp 4),
      (∀ i ξ, m i ξ = (sphereHarmonicMultiplierSymbol i.1 i.2 ξ : ℂ)) ∧
      (∀ i (f : E → ℂ) (h₂ : MemLp f 2 volume) (h₄ : MemLp f 4 volume),
        (Y i (h₄.toLp f) : E → ℂ) =ᵐ[volume] (fourierMultiplier (m i) (h₂.toLp f) : E → ℂ)) ∧
      ∀ {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)}, IsOpen W →
      K ×ˢ sphere (0 : RotationSpace) 1 ⊆ W → ContDiffOn ℝ ∞ F W →
      ∀ M : ℝ, 0 ≤ M →
      (∀ n ≤ 27, ∀ p ∈ K, ∀ x : RoundSphere3,
        ‖iteratedFDeriv ℝ n F (p,(x : RotationSpace))‖ ≤ M) →
      ∀ u : SchwartzMap E ℂ,
        ∃ (B : HarmonicMode → FirstOrderLp 4 →L[ℂ] FirstOrderLp 2)
          (T : FirstOrderLp 4 →L[ℂ] FirstOrderLp 2),
        (∀ i (f w : SchwartzMap E ℂ), inner ℂ (w.toLp 2 volume) (B i (f.toLp 4 volume)) =
          radianHighPair (regularizedLowCartesianSymbol η χ (jointSphereHarmonicCoefficientComplex F i)) f u w) ∧
        (∀ H : FirstOrderLp 4, HasSum (fun i => B i (Y i H)) (T H) ∧
          Summable (fun i => ‖B i (Y i H)‖) ∧
            ‖T H‖ ≤ (∑' i, ‖B i (Y i H)‖) ∧
            (∑' i, ‖B i (Y i H)‖) ≤ C * M * ‖H‖ * highDerivativeLp4Sum u) := by
  obtain ⟨Cm,hm,multiplier⟩ := exists_actualHarmonicLp4_multiplier
  obtain ⟨Cb,hb,cartesian⟩ := exists_regularizedLowCartesian_L4_to_L2
    η χ hr hρ hsmall hR hη hzero hone hχ hcut
  obtain ⟨Cc,hc,coefficient⟩ := exists_smoothComplexAngularCoefficient_jet15 (E := Joint)
  choose m Y symbol boundY physY using multiplier
  let C := Cb*Cc*Cm
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hb hc) hm
  refine ⟨2*C, mul_nonneg (by norm_num) hC, m, Y, symbol, physY, ?_⟩
  intro F W hW hKW hF M hM hjet u
  let K := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  obtain ⟨V,hV,hKV,jet⟩ := coefficient hW hK hKW hF M hM hjet
  let J (i : HarmonicMode) := Cc * (((i.1 : ℝ) + 1)^12)⁻¹ * M
  have mode (i : HarmonicMode) := cartesian hV hKV (jointSphereHarmonicCoefficientComplex F i)
    (J i) (by dsimp [J]; positivity) (jet i).1 (jet i).2 u
  choose B boundB pairing using mode
  let term (i : HarmonicMode) := (B i).comp (Y i)
  let A := C*M*highDerivativeLp4Sum u
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hC hM) (highDerivativeLp4Sum_nonneg u)
  have hTerm (i : HarmonicMode) : ‖term i‖ ≤ A / ((i.1 : ℝ) + 1)^5 := by
    have hpos : 0 < (i.1 : ℝ) + 1 := by positivity
    calc
      _ ≤ ‖B i‖ * ‖Y i‖ := (B i).opNorm_comp_le (Y i)
      _ ≤ (Cb * J i * highDerivativeLp4Sum u) * (Cm * ((i.1 : ℝ) + 1)^7) :=
        mul_le_mul (boundB i) (boundY i) (norm_nonneg _) (by
          exact mul_nonneg (mul_nonneg hb (by dsimp [J]; positivity)) (highDerivativeLp4Sum_nonneg u))
      _ = _ := by
        dsimp [J, A, C]
        field_simp [hpos.ne']
  have series := harmonic_series_estimate term hA hTerm
  refine ⟨B, ∑' i, term i, pairing, fun H => ?_⟩
  have hSum : HasSum (fun i => B i (Y i H)) ((∑' i, term i) H) :=
    (ContinuousLinearMap.apply ℂ (FirstOrderLp 2) H).hasSum series.summable.hasSum
  have hUpper := series.absoluteSummable.mul_right ‖H‖
  have hLe (i : HarmonicMode) : ‖B i (Y i H)‖ ≤ ‖term i‖*‖H‖ := (term i).le_opNorm H
  have hNorm : Summable (fun i => ‖B i (Y i H)‖) :=
    hUpper.of_nonneg_of_le (fun _ => norm_nonneg _) hLe
  refine ⟨hSum, hNorm, ?_, ?_⟩
  · rw [← hSum.tsum_eq]
    exact norm_tsum_le_tsum_norm hNorm
  · calc
      _ ≤ ∑' i, ‖term i‖ * ‖H‖ := hNorm.tsum_le_tsum hLe hUpper
      _ ≤ (2*A) * ‖H‖ := by
        rw [tsum_mul_right]
        exact mul_le_mul_of_nonneg_right series.absoluteSumBound (norm_nonneg _)
      _ = _ := by dsimp [A]; ring

end Burnett.A07
