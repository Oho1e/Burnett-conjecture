import Burnett.Analysis.CubicEnergy.AngularCorrection.RadianCoordinateQuotient
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualBound

set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable section

namespace Burnett.A07

open Filter Set Metric MeasureTheory
open Burnett.A02.FrequencySplit (E Joint jointBilinear joint_bilinear_bound)
open Burnett.A06
open scoped ContDiff Topology ENNReal ComplexConjugate

private theorem second_ne_zero_or_first_ne_zero {x : Joint}
    (hx : x ≠ 0) (hξ : x.2 = 0) : x.1 ≠ 0 :=
  fun hp => hx (Prod.ext hp hξ)

private theorem smul_highAdjointFrequencies (t : ℝ) (x : Joint) :
    highAdjointFrequencies (t • x) = t • highAdjointFrequencies x := by
  change (-(t • x.1), t • x.2 + t • x.1) = (t • -x.1, t • (x.2 + x.1))
  rw [smul_neg, smul_add]

private theorem coordinateQuotient_scale
    (b : Joint → ℂ) (hb : ∀ t : ℝ, 0 < t → ∀ y, b (t • y) = t • b y)
    (j : Fin 4) (t : ℝ) (ht : 0 < t) (x : Joint) :
    coordinateQuotient b j (t • x) = coordinateQuotient b j x := by
  have haxis : (t • x).2 j = t * x.2 j := rfl
  have hcancel : ((t * x.2 j) / ((t * ‖x.2‖) ^ 2)) * t = x.2 j / ‖x.2‖ ^ 2 := by
    by_cases hz : ‖x.2‖ = 0
    · simp [hz]
    · field_simp [ht.ne', hz]
  rw [coordinateQuotient, coordinateQuotient, haxis, Prod.smul_snd, norm_smul,
    Real.norm_of_nonneg ht.le, hb t ht, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    hcancel]

private theorem coordinateQuotient_contDiffAt {b : Joint → ℂ} {x : Joint}
    (hb : ContDiffAt ℝ ∞ b x) (hx : x.2 ≠ 0) (j : Fin 4) :
    ContDiffAt ℝ ∞ (coordinateQuotient b j) x := by
  have hnum : ContDiffAt ℝ ∞ (fun y : Joint => y.2 j) x :=
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp contDiff_snd).contDiffAt
  have hden : ContDiffAt ℝ ∞ (fun y : Joint => ‖y.2‖ ^ 2) x :=
    (contDiff_norm_sq ℝ).contDiffAt.comp x contDiffAt_snd
  have hq := hnum.div hden (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))
  exact ((Complex.ofRealCLM.contDiff.contDiffAt).comp x hq).mul hb

private theorem lowCartesianSymbol_contDiffAt_of_ne_zero
    (χ : ℝ → ℝ) (c : Joint → ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ s ≥ ρ ^ 2, χ s = 0)
    {V : Set Joint} (hV : IsOpen V)
    (hContains : closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 ⊆ V)
    (hc : ContDiffOn ℝ ∞ c V) {x : Joint} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (lowCartesianSymbol χ c) x := by
  by_cases hξ : x.2 = 0
  · have hp := second_ne_zero_or_first_ne_zero hx hξ
    have hsep : ρ * ‖x.2‖ < ‖x.1‖ := by simpa [hξ] using norm_pos_iff.mpr hp
    have near := (isOpen_lt (continuous_const.mul continuous_snd.norm)
      continuous_fst.norm).mem_nhds hsep
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [near] with y hy
    exact lowCartesianSymbol_eq_zero_outside χ c hρ hcut hy.le
  · exact lowCartesianSymbol_contDiffAt χ c hρ hχ hcut hV hContains hc hξ

/-- The actual unregularized forward quotient is smooth away from the joint
origin and homogeneous of degree zero. At the high axis it is locally zero. -/
theorem coordinateQuotient_lowCartesianSymbol_regular
    (χ : ℝ → ℝ) (c : Joint → ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ s ≥ ρ ^ 2, χ s = 0)
    {V : Set Joint} (hV : IsOpen V)
    (hContains : closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 ⊆ V)
    (hc : ContDiffOn ℝ ∞ c V) (j : Fin 4) :
    ContDiffOn ℝ ∞ (coordinateQuotient (lowCartesianSymbol χ c) j) {x | x ≠ 0} ∧
      ∀ t : ℝ, 0 < t → ∀ x,
        coordinateQuotient (lowCartesianSymbol χ c) j (t • x) =
          coordinateQuotient (lowCartesianSymbol χ c) j x := by
  refine ⟨?_, coordinateQuotient_scale _ (lowCartesianSymbol_smul χ c) j⟩
  intro x hx
  have hx' : x ≠ 0 := hx
  apply ContDiffAt.contDiffWithinAt
  by_cases hξ : x.2 = 0
  · have hp := second_ne_zero_or_first_ne_zero hx' hξ
    have hsep : ρ * ‖x.2‖ < ‖x.1‖ := by simpa [hξ] using norm_pos_iff.mpr hp
    have near := (isOpen_lt (continuous_const.mul continuous_snd.norm)
      continuous_fst.norm).mem_nhds hsep
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [near] with y hy
    rw [coordinateQuotient, lowCartesianSymbol_eq_zero_outside χ c hρ hcut hy.le, mul_zero]
  · exact coordinateQuotient_contDiffAt
      (lowCartesianSymbol_contDiffAt χ c hρ hχ hcut hV hContains hc hξ) hξ j

/-- The actual unregularized adjoint quotient has the same joint symbol
regularity. The low/high separation excludes the new high axis even after
the high input and output have been interchanged. -/
theorem coordinateQuotient_highAdjoint_lowCartesianSymbol_regular
    (χ : ℝ → ℝ) (c : Joint → ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hsmall : ρ < 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ s ≥ ρ ^ 2, χ s = 0)
    {V : Set Joint} (hV : IsOpen V)
    (hContains : closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 ⊆ V)
    (hc : ContDiffOn ℝ ∞ c V) (j : Fin 4) :
    ContDiffOn ℝ ∞ (coordinateQuotient (highAdjointSymbol (lowCartesianSymbol χ c)) j)
      {x | x ≠ 0} ∧
      ∀ t : ℝ, 0 < t → ∀ x,
        coordinateQuotient (highAdjointSymbol (lowCartesianSymbol χ c)) j (t • x) =
          coordinateQuotient (highAdjointSymbol (lowCartesianSymbol χ c)) j x := by
  have hscale (t : ℝ) (ht : 0 < t) (x : Joint) :
      highAdjointSymbol (lowCartesianSymbol χ c) (t • x) =
        t • highAdjointSymbol (lowCartesianSymbol χ c) x := by
    simp only [highAdjointSymbol, smul_highAdjointFrequencies, lowCartesianSymbol_smul χ c t ht,
      Complex.real_smul, map_mul, Complex.conj_ofReal]
  refine ⟨?_, coordinateQuotient_scale _ hscale j⟩
  intro x hx
  have hx' : x ≠ 0 := hx
  apply ContDiffAt.contDiffWithinAt
  by_cases hξ : x.2 = 0
  · have hp := second_ne_zero_or_first_ne_zero hx' hξ
    have hsep : ρ * ‖x.2 + x.1‖ < ‖x.1‖ := by
      simpa only [hξ, zero_add, one_mul] using mul_lt_mul_of_pos_right hsmall
        (norm_pos_iff.mpr hp)
    have near := (isOpen_lt (continuous_const.mul (continuous_snd.add continuous_fst).norm)
      continuous_fst.norm).mem_nhds hsep
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [near] with y hy
    have hzero := lowCartesianSymbol_eq_zero_outside χ c hρ hcut (x := highAdjointFrequencies y)
      (by simpa [highAdjointFrequencies] using hy.le)
    simp only [coordinateQuotient, highAdjointSymbol, hzero, map_zero, mul_zero]
  · have hmap0 : highAdjointFrequencies (0 : Joint) = 0 := by
      change (-(0 : E), (0 : E) + 0) = 0
      simp
    have hmap : highAdjointFrequencies x ≠ 0 :=
      fun hm => hx' (highAdjointFrequencies.injective (hm.trans hmap0.symm))
    have hshift : ContDiff ℝ ∞ (highAdjointFrequencies : Joint → Joint) := by
      change ContDiff ℝ ∞ (fun y : Joint => (-y.1, y.2+y.1))
      exact contDiff_fst.neg.prodMk (contDiff_snd.add contDiff_fst)
    have hcore := lowCartesianSymbol_contDiffAt_of_ne_zero χ c hρ hχ hcut hV hContains hc hmap
    have hdag : ContDiffAt ℝ ∞ (highAdjointSymbol (lowCartesianSymbol χ c)) x :=
      Complex.conjCLE.toContinuousLinearMap.contDiff.contDiffAt.comp x
        (hcore.comp x hshift.contDiffAt)
    exact coordinateQuotient_contDiffAt hdag hξ j

/-- Apply the existing Schwartz Coifman–Meyer estimate at (4,4,2) to a real
projection of a smooth homogeneous complex symbol. For the actual coordinate
quotients the two hypotheses are supplied by the two regularity lemmas above. -/
theorem jointBilinear_bound_four_four_two_of_regular
    (q : Joint → ℂ)
    (hq : ContDiffOn ℝ ∞ q {x | x ≠ 0})
    (hscale : ∀ t : ℝ, 0 < t → ∀ x, q (t • x) = q x)
    (part : ℂ →L[ℝ] ℝ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f u : SchwartzMap E ℂ,
      MemLp (jointBilinear (fun p => part (q p)) f u) (ENNReal.ofReal 2) volume ∧
      eLpNorm (jointBilinear (fun p => part (q p)) f u) (ENNReal.ofReal 2) volume ≤
        C * (eLpNorm (f : E → ℂ) (ENNReal.ofReal 4) volume *
          eLpNorm (u : E → ℂ) (ENNReal.ofReal 4) volume) :=
  joint_bilinear_bound 4 4 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _
    (part.contDiff.comp_contDiffOn hq)
    (fun t ht x => congrArg part (hscale t ht x))

end Burnett.A07
