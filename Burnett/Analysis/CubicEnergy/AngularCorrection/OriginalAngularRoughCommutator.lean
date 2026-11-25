import Burnett.Analysis.CubicEnergy.AngularCorrection.SchwartzHighSlotCommutator
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CartesianHighSlotAngularJets
import Burnett.Analysis.CubicEnergy.AngularCorrection.ActualAngularFirstOrderBound
import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalAngularPairing
import Burnett.Analysis.CubicEnergy.AngularCorrection.PhysicalAngularMultiplierPairing
import Burnett.Analysis.Fourier.SharpProjection

set_option autoImplicit false
set_option maxHeartbeats 10000000

noncomputable section

namespace Burnett.A07

open Burnett.A06 Burnett.A02.FrequencySplit Burnett.Fourier MeasureTheory Metric Set Filter
open scoped BigOperators ContDiff ENNReal NNReal

open private exists_actualHarmonicLp4_multiplier from Burnett.Analysis.CubicEnergy.AngularCorrection.ActualAngularFirstOrderBound

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private theorem exists_norm_bound_for_compatible_angularLp4 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : HarmonicMode) (m : BoundedSymbol E)
      (Y : FirstOrderLp 4 →L[ℂ] FirstOrderLp 4),
      (∀ ξ, m ξ = (sphereHarmonicMultiplierSymbol i.1 i.2 ξ : ℂ)) →
      (∀ (f : E → ℂ) (h₂ : MemLp f 2 volume) (h₄ : MemLp f 4 volume),
        (Y (h₄.toLp f) : E → ℂ) =ᵐ[volume] (fourierMultiplier m (h₂.toLp f) : E → ℂ)) →
      ‖Y‖ ≤ C * ((i.1 : ℝ) + 1)^7 := by
  obtain ⟨C,hC,mode⟩ := exists_actualHarmonicLp4_multiplier
  refine ⟨C,hC,?_⟩
  intro i m Y hm hy
  obtain ⟨m',Y',hm',norm',hy'⟩ := mode i
  have hSame : fourierMultiplier m = fourierMultiplier m' :=
    fourierMultiplier_congr_ae m m' (Eventually.of_forall fun ξ => (hm ξ).trans (hm' ξ).symm)
  have eqY : Y = Y' := by
    apply ContinuousLinearMap.ext
    intro H
    refine (CMBilinearDual.schwartz_toLp_denseRange 4 (by norm_num)).induction_on H
      (isClosed_eq Y.continuous Y'.continuous) ?_
    intro f
    have h := hy (f : E → ℂ) (f.memLp 2 volume) (f.memLp 4 volume)
    rw [hSame] at h
    exact Lp.ext (h.trans (hy' (f : E → ℂ) (f.memLp 2 volume) (f.memLp 4 volume)).symm)
  rw [eqY]
  exact norm'

private theorem norm_le_of_triLpMass_442 (f v w : SchwartzMap E ℂ) (z : ℂ)
    {A : ℝ} (hA : 0 ≤ A) (L : ℝ≥0)
    (h : ‖z‖ₑ ≤ (L : ℝ≥0∞) * ENNReal.ofReal A * triLpMass f v w 4 4 2) :
    ‖z‖ ≤ ((L : ℝ) * A * ‖v.toLp 4 volume‖) * ‖f.toLp 4 volume‖ * ‖w.toLp 2 volume‖ := by
  simp only [triLpMass, ENNReal.ofReal_ofNat, ← mul_assoc] at h
  have finite : (L : ℝ≥0∞) * ENNReal.ofReal A * eLpNorm (f : E → ℂ) 4 volume *
      eLpNorm (v : E → ℂ) 4 volume * eLpNorm (w : E → ℂ) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) (f.memLp 4 volume).2.ne)
      (v.memLp 4 volume).2.ne) (w.memLp 2 volume).2.ne
  have result := ENNReal.toReal_mono finite h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA, ← SchwartzMap.norm_toLp] at result
  simpa only [mul_assoc, mul_comm, mul_left_comm] using result

/-- The actual forward rough-coefficient commutator for the original angular
symbol on the physical Schwartz high fields used at a fixed manuscript index. -/
theorem exists_originalAngular_realSchwartz_roughCommutator
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1/2) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
    ∃ (K : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)},
      IsOpen W → Q ×ˢ sphere (0 : RotationSpace) 1 ⊆ W → ContDiffOn ℝ ∞ F W →
      ∀ M : ℝ, 0 ≤ M →
      (∀ n ≤ K, ∀ p ∈ Q, ∀ x : RoundSphere3, ‖iteratedFDeriv ℝ n F (p,(x : RotationSpace))‖ ≤ M) →
      ∀ (d : SchwartzMap E ℝ) (L : ℝ≥0), LipschitzWith L d → ∀ v : SchwartzMap E ℂ,
        ∃ (T Td : FirstOrderLp 4 →L[ℂ] FirstOrderLp 2),
        (∀ H w : SchwartzMap E ℂ,
          inner ℂ (w.toLp 2 volume) (T (H.toLp 4 volume)) =
            radianHighPair (originalRegularizedAngularSymbol η χ F) H v w ∧
          inner ℂ (w.toLp 2 volume) (Td (H.toLp 4 volume)) =
            radianHighPair (originalRegularizedAngularSymbol η χ F) H (realSchwartzMultiply d v) w) ∧
        (∀ H : FirstOrderLp 4, ‖symbolCLM (realSchwartzCoefficient d) (T H) - Td H‖ ≤
          C * M * (L : ℝ) * ‖H‖ * ‖v.toLp 4 volume‖) ∧
        ∀ H w : SchwartzMap E ℂ,
          inner ℂ (w.toLp 2 volume)
            (symbolCLM (realSchwartzCoefficient d) (T (H.toLp 4 volume)) - Td (H.toLp 4 volume)) =
            -radianHighCommutatorPair (originalRegularizedAngularSymbol η χ F) d H v w := by
  have hρ₁ : ρ < 1 := hsmall.trans (by norm_num)
  obtain ⟨K,Cb,hCb,modeBound⟩ := exists_regularizedLowCartesian_highSlot_angularJetBound
    η χ hρ hsmall hr hR hη hzero hone hχ hcut
  obtain ⟨Cc,hCc,coefficient⟩ := exists_jointSphereHarmonicCoefficientComplex_on_open_neighborhood (E := Joint)
  obtain ⟨_,_,smoothCoefficient⟩ := exists_smoothComplexAngularCoefficient_jet15 (E := Joint)
  obtain ⟨Cm,hCm,normY⟩ := exists_norm_bound_for_compatible_angularLp4
  obtain ⟨_,_,m,Y,hm,hY,make⟩ := exists_actualAngular_firstOrder_L4_L2_bound
    η χ hr hρ hρ₁ hR hη hzero hone hχ hcut
  let C := Cb*Cc*Cm
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hCb hCc) hCm
  refine ⟨max K 15 + 12, 2*C, mul_nonneg (by norm_num) hC, ?_⟩
  intro F W hW hContains hF M hM hjet d L hL v
  let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have jet27 : ∀ n ≤ 27, ∀ p ∈ Q, ∀ x : RoundSphere3,
      ‖iteratedFDeriv ℝ n F (p,(x : RotationSpace))‖ ≤ M := by
    intro n hn p hp x
    exact hjet n (hn.trans (by have h := Nat.le_max_right K 15; omega)) p hp x
  obtain ⟨V₀,hV₀,hQV₀,coefficientSmooth⟩ := smoothCoefficient hW hQ hContains hF M hM jet27
  obtain ⟨V₁,hV₁,hQV₁,jet⟩ := coefficient hW hQ hContains K
    (hF.of_le (WithTop.coe_le_coe.mpr le_top)) M hM
    (fun n hn p hp x => hjet n (hn.trans (Nat.add_le_add_right (Nat.le_max_left K 15) 12)) p hp x)
  let V := V₀ ∩ V₁
  have hV : IsOpen V := hV₀.inter hV₁
  have hQV : Q ⊆ V := fun _ hp => ⟨hQV₀ hp,hQV₁ hp⟩
  let coefficientSymbol (i : HarmonicMode) := jointSphereHarmonicCoefficientComplex F i
  have csmooth (i : HarmonicMode) : ContDiffOn ℝ ∞ (coefficientSymbol i) V :=
    (coefficientSmooth i).1.mono inter_subset_left
  let cBound (i : HarmonicMode) := Cc * (((i.1 : ℝ) + 1)^12)⁻¹ * M
  have hc (i : HarmonicMode) : 0 ≤ cBound i := by dsimp [cBound]; positivity
  let symbol (i : HarmonicMode) : OrderOneSymbol ℂ :=
    ⟨regularizedLowCartesianSymbol η χ (coefficientSymbol i),
      regularizedLowCartesianSymbol_mem_orderOneSymbolSubmodule η χ _ hr hρ hR hη hzero hone hχ hcut
        hV hQV (csmooth i)⟩
  let dv := realSchwartzMultiply d v
  obtain ⟨B,T,hB,hSeries⟩ := make hW hContains hF M hM jet27 v
  obtain ⟨Bd,Td,hBd,hSeriesd⟩ := make hW hContains hF M hM jet27 dv
  have original (u : SchwartzMap E ℂ) (D : HarmonicMode → FirstOrderLp 4 →L[ℂ] FirstOrderLp 2)
      (S : FirstOrderLp 4 →L[ℂ] FirstOrderLp 2)
      (pair : ∀ i (f w : SchwartzMap E ℂ), inner ℂ (w.toLp 2 volume) (D i (f.toLp 4 volume)) =
        radianHighPair (symbol i) f u w)
      (series : ∀ H : FirstOrderLp 4, HasSum (fun i => D i (Y i H)) (S H))
      (H w : SchwartzMap E ℂ) : inner ℂ (w.toLp 2 volume) (S (H.toLp 4 volume)) =
        radianHighPair (originalRegularizedAngularSymbol η χ F) H u w := by
    have mode (i : HarmonicMode) : inner ℂ (w.toLp 2 volume) (D i (Y i (H.toLp 4 volume))) =
        radianHighPair (angularModeSymbol η χ F i) H u w :=
      physicalAngularMultiplier_pair_eq (symbol i) u H w i (m i) (hm i) (Y i)
        (hY i H (H.memLp 2 volume) (H.memLp 4 volume)) (D i) (pair i)
    have hs := (innerSL ℂ (w.toLp 2 volume)).hasSum (series (H.toLp 4 volume))
    have hPhysical : HasSum (fun i => radianHighPair (angularModeSymbol η χ F i) H u w)
        (inner ℂ (w.toLp 2 volume) (S (H.toLp 4 volume))) := by
      convert hs using 1
      funext i
      exact (mode i).symm
    exact hPhysical.unique (originalRegularizedAngularPair_hasSum_of_smoothProfile
      η χ hr hρ hR hη hzero hone hχ hcut hW hContains hF hM jet27 H u w)
  have forward := original v B T hB (fun H => (hSeries H).1)
  have afterMultiply := original dv Bd Td hBd (fun H => (hSeriesd H).1)
  let multiplication := symbolCLM (realSchwartzCoefficient d)
  let oneMode (i : HarmonicMode) (H : FirstOrderLp 4) := multiplication (B i H) - Bd i H
  have hfactor (i : HarmonicMode) : 0 ≤ (L : ℝ) * (Cb*cBound i) * ‖v.toLp 4 volume‖ :=
    mul_nonneg (mul_nonneg L.coe_nonneg (mul_nonneg hCb (hc i))) (norm_nonneg _)
  have oneModeBound (i : HarmonicMode) (H : FirstOrderLp 4) :
      ‖oneMode i H‖ ≤ ((L : ℝ) * (Cb*cBound i) * ‖v.toLp 4 volume‖) * ‖H‖ := by
    apply schwartzHighSlotCommutator_L4_to_L2_norm_le (symbol i) d v (B i) (Bd i) (hB i) (hBd i)
      (hfactor i)
    intro f w
    apply norm_le_of_triLpMass_442 f v w _ (mul_nonneg hCb (hc i)) L
    exact modeBound hV hQV (coefficientSymbol i) (cBound i) (hc i) (csmooth i) (jet i).2 d L hL f v w
  refine ⟨T,Td,fun H w => ⟨forward H w,afterMultiply H w⟩, ?_, ?_⟩
  · intro H
    let A := C*M*(L : ℝ)*‖H‖*‖v.toLp 4 volume‖
    have hA : 0 ≤ A :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hM) L.coe_nonneg) (norm_nonneg _)) (norm_nonneg _)
    have mode_norm (i : HarmonicMode) : ‖oneMode i (Y i H)‖ ≤ A / ((i.1 : ℝ) + 1)^5 := by
      have hi : 0 < (i.1 : ℝ) + 1 := by positivity
      have hYnorm := ((Y i).le_opNorm H).trans
        (mul_le_mul_of_nonneg_right (normY i (m i) (Y i) (hm i) (hY i)) (norm_nonneg _))
      calc
        _ ≤ ((L : ℝ) * (Cb*cBound i) * ‖v.toLp 4 volume‖) * ‖Y i H‖ := oneModeBound i _
        _ ≤ ((L : ℝ) * (Cb*cBound i) * ‖v.toLp 4 volume‖) *
            (Cm * ((i.1 : ℝ) + 1)^7 * ‖H‖) := mul_le_mul_of_nonneg_left hYnorm (hfactor i)
        _ = _ := by
          dsimp [A, C, cBound]
          field_simp [hi.ne']
    have bound := (harmonic_series_estimate (fun i => oneMode i (Y i H)) hA mode_norm).fullBound
    have hs : HasSum (fun i => oneMode i (Y i H)) (multiplication (T H) - Td H) :=
      (multiplication.hasSum (hSeries H).1).sub (hSeriesd H).1
    rw [← hs.tsum_eq]
    exact bound.trans_eq (by dsimp [A]; ring)
  · intro H w
    exact schwartzHighSlotCommutator_pair_eq (originalRegularizedAngularSymbol η χ F) d v T Td
      forward afterMultiply H w

end Burnett.A07
