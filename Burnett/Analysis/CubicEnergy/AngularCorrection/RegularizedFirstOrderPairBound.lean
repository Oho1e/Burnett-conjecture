import Burnett.Analysis.CubicEnergy.AngularCorrection.CoordinateQuotientProfileJets
import Burnett.Analysis.CubicEnergy.AngularCorrection.FixedInfraredSchwartzPairing
import Burnett.Analysis.CubicEnergy.AngularCorrection.RadianHighPairCM
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.OrderOneSymbolPairing

set_option autoImplicit false
set_option maxHeartbeats 7200000

noncomputable section

namespace Burnett.A07

open MeasureTheory Filter Set Metric
open Burnett.A02.FrequencySplit (E Joint triLpMass)
open Burnett.A06
open scoped BigOperators ContDiff ENNReal ComplexConjugate

private theorem realProjection_opNorm_le_one : ‖Complex.reCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x.re‖ ≤ 1 * ‖x‖
  rw [Real.norm_eq_abs, one_mul]
  exact Complex.abs_re_le_norm x

private theorem imaginaryProjection_opNorm_le_one : ‖Complex.imCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x.im‖ ≤ 1 * ‖x‖
  rw [Real.norm_eq_abs, one_mul]
  exact Complex.abs_im_le_norm x

private def conjSchwartzLow (f : SchwartzMap E ℂ) : SchwartzMap E ℂ where
  toFun := Complex.conjLIE ∘ (f : E → ℂ)
  smooth' := Complex.conjCLE.contDiff.comp f.smooth'
  decay' k n := by
    obtain ⟨C, _, hC⟩ := f.decay k n
    refine ⟨C, fun x => ?_⟩
    rw [Complex.conjLIE.norm_iteratedFDeriv_comp_left]
    exact hC x

private theorem conjSchwartzLow_eLpNorm (f : SchwartzMap E ℂ) (q : ℝ≥0∞) :
    eLpNorm (conjSchwartzLow f : E → ℂ) q volume =
      eLpNorm (f : E → ℂ) q volume := by
  apply eLpNorm_congr_enorm_ae
  filter_upwards with x
  change ‖conj (f x)‖ₑ = ‖f x‖ₑ
  simp only [← ofReal_norm_eq_enorm, Complex.norm_conj]

private theorem highAdjointSymbol_orderOne_bound
    (b : Joint → ℂ) (P : ℝ) (P0 : 0 ≤ P)
    (bound : ∀ p : Joint, ‖b p‖ ≤ P * (1+‖p.1‖+‖p.2‖)) (p : Joint) :
    ‖highAdjointSymbol b p‖ ≤ (2*P) * (1+‖p.1‖+‖p.2‖) := by
  have hfreq : 1 + ‖p.1‖ + ‖p.2+p.1‖ ≤ 2*(1+‖p.1‖+‖p.2‖) := by
    linarith [norm_add_le p.2 p.1, norm_nonneg p.2]
  rw [highAdjointSymbol, Complex.norm_conj]
  calc
    _ ≤ P * (1+‖p.1‖+‖p.2+p.1‖) := by
      have h := bound (highAdjointFrequencies p)
      change ‖b (highAdjointFrequencies p)‖ ≤ P * (1+‖-p.1‖+‖p.2+p.1‖) at h
      simpa only [norm_neg] using h
    _ ≤ P * (2*(1+‖p.1‖+‖p.2‖)) := mul_le_mul_of_nonneg_left hfreq P0
    _ = _ := by ring

private theorem assemble_coordinate_pair_bound
    (b : Joint → ℂ) (hb : Measurable b) {P r : ℝ} (P0 : 0 ≤ P) (hr : 0 < r)
    (growth : ∀ p : Joint, ‖b p‖ ≤ P * (1+‖p.1‖+‖p.2‖))
    (gap : ∀ p : Joint, ‖p.2‖ ≤ r → b p = 0)
    (f u w : SchwartzMap E ℂ) (K : ℝ≥0∞)
    (estimate : ∀ j : Fin 4,
      ‖radianHighPair (coordinateQuotient b j) f (coordinateDerivative j u) w‖ₑ ≤
        K * eLpNorm (coordinateDerivative j u : E → ℂ) (ENNReal.ofReal 4) volume) :
    ‖radianHighPair b f u w‖ₑ ≤
      K * ∑ j : Fin 4, eLpNorm (coordinateDerivative j u : E → ℂ) (ENNReal.ofReal 4) volume := by
  rw [radianHighPair_eq_sum_coordinateDerivative b hb P0 hr growth gap]
  calc
    _ ≤ ∑ j : Fin 4, ‖(-Complex.I) *
        radianHighPair (coordinateQuotient b j) f (coordinateDerivative j u) w‖ₑ :=
      enorm_sum_le Finset.univ _
    _ ≤ ∑ j : Fin 4, K * eLpNorm (coordinateDerivative j u : E → ℂ) (ENNReal.ofReal 4) volume := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [← ofReal_norm_eq_enorm, norm_mul, norm_neg, Complex.norm_I, one_mul]
        using estimate j
    _ = _ := by rw [Finset.mul_sum]

/-- One profile budget controls the original regularized Cartesian term and
its actual high adjoint, with the same four high-coordinate L⁴ derivatives. -/
theorem exists_regularizedLowCartesian_highPair_firstOrderBound
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {V : Set Joint}, IsOpen V →
      closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 ⊆ V →
      ∀ (c : Joint → ℂ) (B : ℝ), 0 ≤ B → ContDiffOn ℝ ∞ c V →
      (∀ n ≤ 15, ∀ z ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1,
        ‖iteratedFDeriv ℝ n c z‖ ≤ B) →
      ∀ f u w : SchwartzMap E ℂ,
        ‖radianHighPair (regularizedLowCartesianSymbol η χ c) f u w‖ₑ ≤
          C * ENNReal.ofReal B * eLpNorm (f : E → ℂ) (ENNReal.ofReal 4) volume *
            (∑ j : Fin 4, eLpNorm (coordinateDerivative j u : E → ℂ) (ENNReal.ofReal 4) volume) *
              eLpNorm (w : E → ℂ) (ENNReal.ofReal 2) volume ∧
        ‖radianHighPair (highAdjointSymbol (regularizedLowCartesianSymbol η χ c))
            (fun x => conj (f x)) u w‖ₑ ≤
          C * ENNReal.ofReal B * eLpNorm (f : E → ℂ) (ENNReal.ofReal 4) volume *
            (∑ j : Fin 4, eLpNorm (coordinateDerivative j u : E → ℂ) (ENNReal.ofReal 4) volume) *
              eLpNorm (w : E → ℂ) (ENNReal.ofReal 2) volume := by
  obtain ⟨J, J0, jets⟩ :=
    exists_coordinateQuotient_profile_sphereJet_bound η χ hr hρ hsmall hR hη hzero hone hχ hcut
  obtain ⟨K, Kfin, cm⟩ := exists_radianHighPair_CM_four_four_two_bound
  obtain ⟨H4, H4fin, cut4⟩ :=
    exists_fixedInfraredSchwartz_Lp_bound η hη r R hr hzero hone 4 (by norm_num)
  obtain ⟨H2, H2fin, cut2⟩ :=
    exists_fixedInfraredSchwartz_Lp_bound η hη r R hr hzero hone 2 (by norm_num)
  let H := H4 + H2
  let C := K * ENNReal.ofReal J * H
  have Hfin : H < ⊤ := ENNReal.add_lt_top.mpr ⟨H4fin, H2fin⟩
  refine ⟨C, ENNReal.mul_lt_top (ENNReal.mul_lt_top Kfin ENNReal.ofReal_lt_top) Hfin, ?_⟩
  intro V hV hContains c B B0 hc hjet f u w
  let b : OrderOneSymbol ℂ := ⟨regularizedLowCartesianSymbol η χ c,
    regularizedLowCartesianSymbol_mem_orderOneSymbolSubmodule η χ c hr hρ hR
      hη hzero hone hχ hcut hV hContains hc⟩
  let P := orderOneWeightedSeminorm ℂ 0 b
  let fAdj := conjSchwartzLow f
  let hfReg := fixedInfraredSchwartz η hη r R hr hzero hone
  let f4 (v : SchwartzMap E ℂ) := eLpNorm (v : E → ℂ) (ENNReal.ofReal 4) volume
  let f2 (v : SchwartzMap E ℂ) := eLpNorm (v : E → ℂ) (ENNReal.ofReal 2) volume
  let CC := C * ENNReal.ofReal B
  have P0 : 0 ≤ P := apply_nonneg _ _
  have hcut4 (v : SchwartzMap E ℂ) : f4 (hfReg v) ≤ H * f4 v :=
    (cut4 v).trans (mul_le_mul_right' (le_add_of_nonneg_right (zero_le H2)) _)
  have hcut2 (v : SchwartzMap E ℂ) : f2 (hfReg v) ≤ H * f2 v :=
    (cut2 v).trans (mul_le_mul_right' (le_add_of_nonneg_left (zero_le H4)) _)
  have hbGrowth : ∀ p : Joint, ‖(b : Joint → ℂ) p‖ ≤ P * (1+‖p.1‖+‖p.2‖) :=
    b.norm_apply_le_weightedSeminorm_zero
  have hgap (p : Joint) (hp : ‖p.2‖ ≤ r) : (b : Joint → ℂ) p = 0 :=
    regularizedLowCartesianSymbol_eq_zero_on_highGap η χ c hzero p hp
  have hAdjGap (p : Joint) (hp : ‖p.2‖ ≤ (1-ρ)*r) :
      highAdjointSymbol (b : Joint → ℂ) p = 0 :=
    highAdjoint_regularizedLowCartesianSymbol_eq_zero_on_highGap η χ c hzero hρ hsmall hcut p hp
  have hAdjMeas : Measurable (highAdjointSymbol (b : Joint → ℂ)) :=
    Complex.continuous_conj.measurable.comp
      (b.measurable_symbol.comp highAdjointFrequencies.measurable)
  have hbAdj := highAdjointSymbol_orderOne_bound (b : Joint → ℂ) P P0 hbGrowth
  have jetRe := jets hV hContains c B B0 hc hjet Complex.reCLM realProjection_opNorm_le_one
  have jetIm := jets hV hContains c B B0 hc hjet Complex.imCLM imaginaryProjection_opNorm_le_one
  have original (j : Fin 4) :
      ‖radianHighPair (coordinateQuotient (b : Joint → ℂ) j) f (coordinateDerivative j u) w‖ₑ ≤
        (CC * f4 f * f2 w) * f4 (coordinateDerivative j u) := by
    let q := coordinateQuotient (lowCartesianSymbol χ c) j
    obtain ⟨hq, hscale⟩ :=
      coordinateQuotient_lowCartesianSymbol_regular χ c hρ hχ hcut hV hContains hc j
    have bound := cm q hq hscale (J*B) (mul_nonneg J0 B0)
      (fun i hi x hx => (jetRe j i hi x hx).1) (fun i hi x hx => (jetIm j i hi x hx).1)
      f (hfReg (coordinateDerivative j u)) w
    have hsym : coordinateQuotient (b : Joint → ℂ) j = fun p => η ‖p.2‖ • q p :=
      funext (coordinateQuotient_regularizedLowCartesianSymbol η χ c j)
    rw [hsym, radianHighPair_fixedInfrared_on_input η hη r R hr hzero hone]
    refine bound.trans ?_
    change K * ENNReal.ofReal (J*B) * (f4 f * f4 (hfReg (coordinateDerivative j u)) * f2 w) ≤ _
    calc
      _ ≤ K * ENNReal.ofReal (J*B) * (f4 f * (H * f4 (coordinateDerivative j u)) * f2 w) := by
        gcongr
        exact hcut4 (coordinateDerivative j u)
      _ = _ := by
        rw [ENNReal.ofReal_mul J0]
        dsimp [CC, C]
        ac_rfl
  have adjoint (j : Fin 4) :
      ‖radianHighPair (coordinateQuotient (highAdjointSymbol (b : Joint → ℂ)) j)
          fAdj (coordinateDerivative j u) w‖ₑ ≤
        (CC * f4 f * f2 w) * f4 (coordinateDerivative j u) := by
    let q := coordinateQuotient (highAdjointSymbol (lowCartesianSymbol χ c)) j
    obtain ⟨hq, hscale⟩ :=
      coordinateQuotient_highAdjoint_lowCartesianSymbol_regular χ c hρ hsmall hχ hcut
        hV hContains hc j
    have bound := cm q hq hscale (J*B) (mul_nonneg J0 B0)
      (fun i hi x hx => (jetRe j i hi x hx).2) (fun i hi x hx => (jetIm j i hi x hx).2)
      fAdj (coordinateDerivative j u) (hfReg w)
    have hsym : coordinateQuotient (highAdjointSymbol (b : Joint → ℂ)) j =
        fun p => η ‖p.2+p.1‖ • q p :=
      funext (coordinateQuotient_highAdjoint_regularizedLowCartesianSymbol η χ c j)
    rw [hsym, radianHighPair_fixedInfrared_on_output η hη r R hr hzero hone]
    refine bound.trans ?_
    change K * ENNReal.ofReal (J*B) *
      (f4 fAdj * f4 (coordinateDerivative j u) * f2 (hfReg w)) ≤ _
    have hconj : f4 fAdj = f4 f := conjSchwartzLow_eLpNorm f (ENNReal.ofReal 4)
    rw [hconj]
    calc
      _ ≤ K * ENNReal.ofReal (J*B) * (f4 f * f4 (coordinateDerivative j u) * (H * f2 w)) := by
        gcongr
        exact hcut2 w
      _ = _ := by
        rw [ENNReal.ofReal_mul J0]
        dsimp [CC, C]
        ac_rfl
  have rearrange : (CC * f4 f * f2 w) * (∑ j : Fin 4, f4 (coordinateDerivative j u)) =
      CC * f4 f * (∑ j : Fin 4, f4 (coordinateDerivative j u)) * f2 w := by ac_rfl
  constructor
  · change ‖radianHighPair (b : Joint → ℂ) f u w‖ₑ ≤
      CC * f4 f * (∑ j : Fin 4, f4 (coordinateDerivative j u)) * f2 w
    rw [← rearrange]
    exact assemble_coordinate_pair_bound (b : Joint → ℂ) b.measurable_symbol P0 hr hbGrowth
      hgap f u w _ original
  · change ‖radianHighPair (highAdjointSymbol (b : Joint → ℂ)) fAdj u w‖ₑ ≤
      CC * f4 f * (∑ j : Fin 4, f4 (coordinateDerivative j u)) * f2 w
    rw [← rearrange]
    exact assemble_coordinate_pair_bound (highAdjointSymbol (b : Joint → ℂ)) hAdjMeas
      (mul_nonneg (by positivity) P0) (mul_pos (sub_pos.mpr hsmall) hr) hbAdj hAdjGap
      fAdj u w _ adjoint

end Burnett.A07
