import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWeightedSummation

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Burnett.A06

open MeasureTheory
open Burnett.A02.FrequencySplit
open scoped ENNReal NNReal ContDiff BigOperators

private abbrev pairMeasure : Measure (Joint × E) :=
  (volume : Measure Joint).prod (volume : Measure E)

def highCoefficientGapDensity (A : Joint → ℂ) (a b d : SchwartzMap E ℂ)
    (u v w r t : ℝ) (YH YL : Joint → E) (c : E → ℂ) (f g h : SchwartzMap E ℂ)
    (j : ℕ) (yx : Joint × E) : ℂ :=
  ((dyadicScale t j)⁻¹ : ℝ) • c yx.2 *
    (blockKernel A yx.1 * (shiftedTest a f (u*r) t j 0 yx.2 *
      shiftedTest b g v t j (YH yx.1) yx.2 * shiftedTest d h w t j (YL yx.1) yx.2))

/-- The top frequency is kept at its original physical point after translating
the tested integral. Only the lower annular input and the low-pass input move. -/
def highCoefficientGapBlock (A : Joint → ℂ) (a b d : SchwartzMap E ℂ)
    (u v w r t : ℝ) (YH YL : Joint → E) (c : E → ℂ) (f g h : SchwartzMap E ℂ)
    (j : ℕ) : ℂ :=
  ∫ yx, highCoefficientGapDensity A a b d u v w r t YH YL c f g h j yx ∂pairMeasure

private theorem shiftBound (c : ℝ) (y : E) :
    1+‖(-c) • y‖ ≤ (1+‖c‖)*(1+‖y‖) := by
  rw [norm_smul,norm_neg]
  nlinarith only [norm_nonneg c,norm_nonneg y]

private theorem gapShiftWeight_le (v w : ℝ) (YH YL : Joint → E) (y : Joint)
    (hbH : ‖YH y‖ ≤ ‖y.2‖) (hbL : ‖YL y‖ ≤ ‖y.1‖+‖y.2‖) :
    (1+‖(-v⁻¹) • YH y‖)*(1+‖(-w⁻¹) • YL y‖)^5 ≤
      ((1+‖v⁻¹‖)*(1+‖w⁻¹‖)^5) * ((1+‖y.1‖)^5*(1+‖y.2‖)^6) := by
  have low : 1+‖YL y‖ ≤ (1+‖y.1‖)*(1+‖y.2‖) := by
    nlinarith only [hbL,mul_nonneg (norm_nonneg y.1) (norm_nonneg y.2)]
  have hH := (shiftBound (v⁻¹) (YH y)).trans
    (mul_le_mul_of_nonneg_left (add_le_add_left hbH 1) (by positivity))
  have hL := (shiftBound (w⁻¹) (YL y)).trans (mul_le_mul_of_nonneg_left low (by positivity))
  calc
    _ ≤ ((1+‖v⁻¹‖)*(1+‖y.2‖))*(((1+‖w⁻¹‖)*(1+‖y.1‖)*(1+‖y.2‖))^5) := by
      apply mul_le_mul hH (pow_le_pow_left₀ (by positivity) _ 5) (by positivity) (by positivity)
      simpa only [mul_assoc] using hL
    _ = _ := by ring

/-- A positive separation ratio costs exactly one factor of the ratio from the
coefficient amplitude. In particular the constant stays uniform as that ratio
tends to zero. Each top annulus, lower annulus, and low-pass is a Fourier window
of its original test function. -/
theorem exists_highCoefficientGapBlock_sum_bound
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    (a b d : SchwartzMap E ℂ)
    (hca : HasCompactSupport (a : E → ℂ)) (hcb : HasCompactSupport (b : E → ℂ))
    (ca : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (cb : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (p q z : ℝ) (hp : 1<p) (hq : 1<q) (hz : 1<z) (bal : triBalance p q z)
    {u v w : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {r t : ℝ}, 0<r → 0<t →
      ∀ (YH YL : Joint → E), Continuous YH → Continuous YL →
      (∀ y, ‖YH y‖ ≤ ‖y.2‖) → (∀ y, ‖YL y‖ ≤ ‖y.1‖+‖y.2‖) →
      ∀ (n : ℕ) (L : ℝ≥0) (c : Fin n → E → ℂ), (∀ i, Continuous (c i)) →
      (∀ i x, ‖c i x‖ ≤ (L : ℝ)*r*dyadicScale t i) →
      ∀ (f g h : SchwartzMap E ℂ),
      (∑ i : Fin n, ‖highCoefficientGapBlock A a b d u v w r t YH YL (c i) f g h i‖ₑ) ≤
        (L : ℝ≥0∞)*ENNReal.ofReal r*C*triLpMass f g h p q z := by
  obtain ⟨D,hD,windows⟩ := dyadic_two_high_one_low a b d hca hcb ca cb p q z hp hq hz bal
  let Cshift := ENNReal.ofReal ((1+‖v⁻¹‖)*(1+‖w⁻¹‖)^5)
  refine ⟨D*Cshift*kernelMoment A 5 6, ?_, ?_⟩
  · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hD ENNReal.ofReal_lt_top)
      (kernelMoment_lt_top A ha hA 5 6)
  intro r t hr ht YH YL hYH hYL hbH hbL n L c hc hcbound f g h
  let l := (L : ℝ≥0∞)*ENNReal.ofReal r
  let U (i : Fin n) := highCoefficientGapDensity A a b d u v w r t YH YL (c i) f g h i
  let entry (i : Fin n) (y : Joint) (x : E) := shiftedTest a f (u*r) t i 0 x *
    shiftedTest b g v t i (YH y) x * shiftedTest d h w t i (YL y) x
  let W (y : Joint) := ENNReal.ofReal (1+‖(-v⁻¹) • YH y‖) *
    ENNReal.ofReal ((1+‖(-w⁻¹) • YL y‖)^5)
  have hK := (blockKernel_integrable A ha hA).2
  have measurableU (i : Fin n) : Measurable (fun yx => ‖U i yx‖ₑ) := by
    have hcont : Continuous (U i) := by
      let F := windowTest a f ((u*r)*dyadicScale t i)
      let G := windowTest b g (v*dyadicScale t i)
      let H := windowTest d h (w*dyadicScale t i)
      change Continuous (fun yx : Joint × E =>
        ((dyadicScale t i)⁻¹ : ℝ) • c i yx.2 *
        (blockKernel A yx.1 *
          (F (yx.2-dyadicScale t i • (0 : E)) * G (yx.2-dyadicScale t i • YH yx.1) *
            H (yx.2-dyadicScale t i • YL yx.1))))
      have hF := F.continuous
      have hG := G.continuous
      have hH := H.continuous
      have hci := hc i
      fun_prop
    exact hcont.enorm.measurable
  have point_bound (i : Fin n) (y : Joint) (x : E) :
      ‖U i (y,x)‖ₑ ≤ (l*‖blockKernel A y‖ₑ)*‖entry i y x‖ₑ := by
    have hs : 0 < dyadicScale t i := by unfold dyadicScale; positivity
    have hnorm : ‖(dyadicScale t i)⁻¹ • c i x‖ ≤ (L : ℝ)*r := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
      exact (mul_le_mul_of_nonneg_left (hcbound i x) (inv_nonneg.mpr hs.le)).trans_eq
        (by field_simp [hs.ne'])
    have en := ENNReal.ofReal_le_ofReal hnorm
    rw [ENNReal.ofReal_mul (show 0 ≤ (L : ℝ) from L.2)] at en
    simp only [ofReal_norm_eq_enorm,ENNReal.ofReal_coe_nnreal] at en
    change ‖(((dyadicScale t i)⁻¹ : ℝ) • c i x) * (blockKernel A y * entry i y x)‖ₑ ≤ _
    simp only [enorm_mul]
    exact (mul_le_mul_right' en _).trans_eq (by unfold l; ac_rfl)
  have sum_bound (y : Joint) :
      (∫⁻ x : E, ∑ i : Fin n, ‖entry i y x‖ₑ) ≤ D*W y*triLpMass f g h p q z := by
    have bound := windows (u*r) v w t (mul_pos hu hr) hv hw ht 0 (YH y) (YL y) n f g h
    simpa only [entry,W,smul_zero,norm_zero,add_zero,ENNReal.ofReal_one,mul_one,mul_assoc] using bound
  have weight_bound (y : Joint) :
      ‖blockKernel A y‖ₑ * W y ≤
        Cshift * ENNReal.ofReal ((1+‖y.1‖)^5*(1+‖y.2‖)^6*‖blockKernel A y‖) := by
    have ht' := ENNReal.ofReal_le_ofReal (gapShiftWeight_le v w YH YL y (hbH y) (hbL y))
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity)] at ht'
    rw [ENNReal.ofReal_mul (by positivity),ofReal_norm_eq_enorm]
    exact (mul_le_mul_left' ht' _).trans_eq (by unfold Cshift; ac_rfl)
  have hL : l ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  calc
    _ ≤ ∑ i : Fin n, ∫⁻ yx, ‖U i yx‖ₑ ∂pairMeasure :=
      Finset.sum_le_sum fun _ _ => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ yx, ∑ i : Fin n, ‖U i yx‖ₑ ∂pairMeasure :=
      (lintegral_finset_sum _ (fun i _ => measurableU i)).symm
    _ = ∫⁻ y : Joint, ∫⁻ x : E, ∑ i : Fin n, ‖U i (y,x)‖ₑ :=
      lintegral_prod _ ((Finset.measurable_sum _ (fun i _ => measurableU i)).aemeasurable)
    _ ≤ ∫⁻ y : Joint, ∫⁻ x : E, (l*‖blockKernel A y‖ₑ)*∑ i : Fin n, ‖entry i y x‖ₑ := by
      refine lintegral_mono fun y => lintegral_mono fun x => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => point_bound i y x
    _ = ∫⁻ y : Joint, (l*‖blockKernel A y‖ₑ)*∫⁻ x : E, ∑ i : Fin n, ‖entry i y x‖ₑ :=
      lintegral_congr fun y => lintegral_const_mul' _ _ (ENNReal.mul_ne_top hL (by finiteness))
    _ ≤ ∫⁻ y : Joint, (l*‖blockKernel A y‖ₑ)*(D*W y*triLpMass f g h p q z) :=
      lintegral_mono fun y => mul_le_mul_left' (sum_bound y) _
    _ ≤ ∫⁻ y : Joint, (l*D*Cshift*triLpMass f g h p q z) *
         ENNReal.ofReal ((1+‖y.1‖)^5*(1+‖y.2‖)^6*‖blockKernel A y‖) := by
      refine lintegral_mono fun y => ?_
      calc
        _ = (l*D*triLpMass f g h p q z)*(‖blockKernel A y‖ₑ*W y) := by ac_rfl
        _ ≤ _ := (mul_le_mul_left' (weight_bound y) _).trans_eq (by ac_rfl)
    _ = _ := by
      have hm : triLpMass f g h p q z ≠ ⊤ := by
        unfold triLpMass
        exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (f.eLpNorm_lt_top _ volume).ne
          (g.eLpNorm_lt_top _ volume).ne) (h.eLpNorm_lt_top _ volume).ne
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top hL hD.ne) ENNReal.ofReal_ne_top) hm)]
      change l*D*Cshift*triLpMass f g h p q z*kernelMoment A 5 6 = _
      unfold l
      ac_rfl

end Burnett.A06
