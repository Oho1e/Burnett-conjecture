import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotPaperExponents
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotLipschitzBlock

set_option autoImplicit false
set_option maxHeartbeats 4800000

noncomputable section

namespace Burnett.A06

open MeasureTheory
open Burnett.A02.FrequencySplit
open scoped ENNReal NNReal ContDiff ComplexConjugate BigOperators

private abbrev pairMeasure : Measure (Joint × E) :=
  (volume : Measure Joint).prod (volume : Measure E)

private def highSlotShiftMoment (A : Joint → ℂ) (u v : ℝ) : ℝ≥0∞ :=
  ∫⁻ y : Joint, (‖y.2‖ₑ * ‖blockKernel A y‖ₑ) *
    (ENNReal.ofReal (1+‖(-v⁻¹) • y.2‖) * ENNReal.ofReal ((1+‖(-u⁻¹) • y.1‖)^5))

private theorem shifted_moment_lt_top (A : Joint → ℂ) (ha : HasCompactSupport A)
    (hA : ContDiff ℝ ∞ A) (u v : ℝ) : highSlotShiftMoment A u v < ⊤ := by
  let W := fun y : Joint => (‖y.2‖ * ‖blockKernel A y‖) *
    ((1+‖(-v⁻¹) • y.2‖) * (1+‖(-u⁻¹) • y.1‖)^5)
  have hK := (blockKernel_integrable A ha hA).2
  have hW : Integrable W := by
    let C := (1+‖v⁻¹‖) * (1+‖u⁻¹‖)^5
    have hC : 0 ≤ C := by dsimp [C]; positivity
    refine ((blockKernel_mixed_moment A ha hA 5 2).const_mul C).mono' ?_ ?_
    · unfold W
      fun_prop
    · filter_upwards with y
      have shift (c : ℝ) (z : E) : 1+‖(-c) • z‖ ≤ (1+‖c‖)*(1+‖z‖) := by
        rw [norm_smul,norm_neg]
        nlinarith only [norm_nonneg c,norm_nonneg z]
      have hn (z : E) : 0 ≤ 1+‖z‖ := by positivity
      have square : ‖y.2‖ * (1+‖y.2‖) ≤ (1+‖y.2‖)^2 := by
        nlinarith only [norm_nonneg y.2]
      change ‖W y‖ ≤ C * ((1+‖y.1‖)^5 * (1+‖y.2‖)^2 * ‖blockKernel A y‖)
      rw [Real.norm_of_nonneg (show 0 ≤ W y by dsimp [W]; positivity)]
      unfold W
      calc
        _ ≤ (‖y.2‖ * ‖blockKernel A y‖) *
            (((1+‖v⁻¹‖)*(1+‖y.2‖)) * ((1+‖u⁻¹‖)*(1+‖y.1‖))^5) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul (shift _ _)
            (pow_le_pow_left₀ (hn _) (shift _ _) _) (by positivity) (by positivity)
        _ = C * ((1+‖y.1‖)^5 * (‖y.2‖*(1+‖y.2‖)) * ‖blockKernel A y‖) := by
          dsimp [C]
          rw [mul_pow]
          ring
        _ ≤ _ := by gcongr
  have eq (y : Joint) : ‖W y‖ₑ = (‖y.2‖ₑ * ‖blockKernel A y‖ₑ) *
      (ENNReal.ofReal (1+‖(-v⁻¹) • y.2‖) * ENNReal.ofReal ((1+‖(-u⁻¹) • y.1‖)^5)) := by
    unfold W
    rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (by positivity)]
    simp only [ofReal_norm_eq_enorm]
  unfold highSlotShiftMoment
  simp_rw [← eq]
  exact hW.hasFiniteIntegral

/-- Each Schwartz field uses an actual fixed Fourier window on the same dyadic
scale. The coefficient sequence is left in the physical high slot. -/
def highSlotWindowedBlock (A : Joint → ℂ) (a b d : SchwartzMap E ℂ) (u v w t : ℝ)
    (coeff : E → ℝ) (f g h : SchwartzMap E ℂ) (j : ℕ) : ℂ :=
  highSlotBlockPair A (dyadicScale t j) coeff
    (windowTest d f (u*dyadicScale t j))
    (windowTest a g (v*dyadicScale t j))
    (windowTest b h (w*dyadicScale t j))

private theorem coefficient_diff_enorm {c : E → ℝ} {L : ℝ≥0}
    (hc : LipschitzWith L c) {s : ℝ} (hs : 0 < s) (x y : E) :
    ‖((s⁻¹ * (c (x-s • y) - c x) : ℝ) : ℂ)‖ₑ ≤ (L : ℝ≥0∞) * ‖y‖ₑ := by
  have hdiff := hc.dist_le_mul (x-s • y) x
  have shift : x-s • y-x = -(s • y) := by abel
  rw [Real.dist_eq,dist_eq_norm,shift,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hs] at hdiff
  have hnorm : ‖((s⁻¹ * (c (x-s • y) - c x) : ℝ) : ℂ)‖ ≤ (L : ℝ)*‖y‖ := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_inv,abs_of_pos hs]
    exact (mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hs.le)).trans_eq
      (by field_simp [hs.ne'])
  have en := ENNReal.ofReal_le_ofReal hnorm
  rw [ENNReal.ofReal_mul (show 0 ≤ (L : ℝ) from L.2)] at en
  simpa only [ofReal_norm_eq_enorm,ENNReal.ofReal_coe_nnreal] using en

/-- The two actual annular windows and the one actual low-pass window give a
uniform sum of the high-slot commutator blocks. The same bound works for
every finite number of consecutive scales and every positive initial scale. -/
theorem exists_highSlotWindowedBlock_sum_bound_paper
    (inputL2 : Bool)
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    (a b d : SchwartzMap E ℂ)
    (hca : HasCompactSupport (a : E → ℂ)) (hcb : HasCompactSupport (b : E → ℂ))
    (ca : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (cb : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    {u v w : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {t : ℝ}, 0<t → ∀ (n : ℕ) (L : ℝ≥0)
      (c : Fin n → E → ℝ), (∀ i, LipschitzWith L (c i)) → ∀ (f g h : SchwartzMap E ℂ),
      ‖∑ i : Fin n, highSlotWindowedBlock A a b d u v w t (c i) f g h i‖ₑ ≤
        (L : ℝ≥0∞) * C * triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  obtain ⟨D,hD,windows⟩ := dyadic_two_high_one_low a b d hca hcb ca cb
    (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) 4
    (one_lt_highSlotInputExponent inputL2) (one_lt_highSlotTestExponent inputL2) (by norm_num)
    (highSlotInputTestBalance inputL2)
  refine ⟨D * highSlotShiftMoment A u v,ENNReal.mul_lt_top hD
    (shifted_moment_lt_top A ha hA u v),?_⟩
  intro t ht n L c hc f g h
  let s (i : Fin n) := dyadicScale t (i : ℕ)
  let F (i : Fin n) := windowTest d f (u*s i)
  let G (i : Fin n) := windowTest a g (v*s i)
  let H (i : Fin n) := windowTest b h (w*s i)
  let U (i : Fin n) (yx : Joint × E) :=
    highSlotBlockDensity A (s i) (c i) (F i) (G i) (H i) yx.1 yx.2
  let entry (i : Fin n) (y : Joint) (x : E) :=
    shiftedTest a g v t i y.2 x * shiftedTest b h w t i 0 x * shiftedTest d f u t i y.1 x
  let summand (yx : Joint × E) := ∑ i : Fin n, U i yx
  have hpos (i : Fin n) : 0 < s i := by dsimp [s,dyadicScale]; positivity
  have hU (i : Fin n) : Integrable (U i) pairMeasure :=
    highSlotBlockDensity_integrable A ha hA (hpos i) (hc i) _ _ _
  have hsum : Integrable summand pairMeasure := integrable_finset_sum _ fun i _ => hU i
  have eq : (∑ i : Fin n, highSlotWindowedBlock A a b d u v w t (c i) f g h i) =
      ∫ yx, summand yx ∂pairMeasure := by
    dsimp only [highSlotWindowedBlock, highSlotBlockPair]
    exact (integral_finset_sum _ (fun i _ => hU i)).symm
  have point_bound (i : Fin n) (y : Joint) (x : E) :
      ‖U i (y,x)‖ₑ ≤ ((L : ℝ≥0∞) * (‖y.2‖ₑ * ‖blockKernel A y‖ₑ)) * ‖entry i y x‖ₑ := by
    simp only [U,highSlotBlockDensity,entry,shiftedTest,smul_zero,sub_zero,enorm_mul,
      RCLike.enorm_conj,F,G,H,s]
    exact (mul_le_mul_right' (coefficient_diff_enorm (hc i) (hpos i) x y.2) _).trans_eq
      (by ring)
  have sum_bound (y : Joint) :
      (∫⁻ x : E, ∑ i : Fin n, ‖entry i y x‖ₑ) ≤
        D * (ENNReal.ofReal (1+‖(-v⁻¹) • y.2‖) * ENNReal.ofReal ((1+‖(-u⁻¹) • y.1‖)^5)) *
          triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
    have bound := windows v w u t hv hw hu ht y.2 0 y.1 n g h f
    simp only [entry,smul_zero,norm_zero,add_zero,ENNReal.ofReal_one,mul_one] at bound ⊢
    exact bound.trans_eq (by unfold triLpMass; ac_rfl)
  have hcu : (L : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hck (y : Joint) : ‖y.2‖ₑ * ‖blockKernel A y‖ₑ ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by finiteness) (by finiteness)
  rw [eq]
  calc
    _ ≤ ∫⁻ yx, ‖summand yx‖ₑ ∂pairMeasure := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y : Joint, ∫⁻ x : E, ‖summand (y,x)‖ₑ :=
      lintegral_prod _ hsum.aestronglyMeasurable.enorm
    _ ≤ ∫⁻ y : Joint, ∫⁻ x : E,
        ((L : ℝ≥0∞) * (‖y.2‖ₑ * ‖blockKernel A y‖ₑ)) * ∑ i : Fin n, ‖entry i y x‖ₑ := by
      refine lintegral_mono fun y => lintegral_mono fun x => ?_
      rw [Finset.mul_sum]
      exact (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => point_bound i y x)
    _ = ∫⁻ y : Joint,
        ((L : ℝ≥0∞) * (‖y.2‖ₑ * ‖blockKernel A y‖ₑ)) * ∫⁻ x : E, ∑ i : Fin n, ‖entry i y x‖ₑ :=
      lintegral_congr fun y => lintegral_const_mul' _ _ (ENNReal.mul_ne_top hcu (hck y))
    _ ≤ ∫⁻ y : Joint,
        ((L : ℝ≥0∞) * (‖y.2‖ₑ * ‖blockKernel A y‖ₑ)) *
        (D * (ENNReal.ofReal (1+‖(-v⁻¹) • y.2‖) * ENNReal.ofReal ((1+‖(-u⁻¹) • y.1‖)^5)) *
          triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2)) :=
      lintegral_mono fun y => mul_le_mul_left' (sum_bound y) _
    _ = _ := by
      let M := fun y : Joint => (‖y.2‖ₑ * ‖blockKernel A y‖ₑ) *
        (ENNReal.ofReal (1+‖(-v⁻¹) • y.2‖) * ENNReal.ofReal ((1+‖(-u⁻¹) • y.1‖)^5))
      let C := (L : ℝ≥0∞) * D * triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2)
      have hC : C ≠ ⊤ := by
        unfold C triLpMass
        exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hcu hD.ne)
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top (f.eLpNorm_lt_top _ volume).ne
            (g.eLpNorm_lt_top _ volume).ne) (h.eLpNorm_lt_top _ volume).ne)
      calc
        _ = ∫⁻ y : Joint, C * M y := lintegral_congr fun y => by dsimp [C,M]; ac_rfl
        _ = C * highSlotShiftMoment A u v := lintegral_const_mul' _ _ hC
        _ = _ := by dsimp [C]; ac_rfl

theorem exists_highSlotWindowedBlock_sum_bound
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    (a b d : SchwartzMap E ℂ)
    (hca : HasCompactSupport (a : E → ℂ)) (hcb : HasCompactSupport (b : E → ℂ))
    (ca : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (cb : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    {u v w : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {t : ℝ}, 0<t → ∀ (n : ℕ) (L : ℝ≥0)
      (c : Fin n → E → ℝ), (∀ i, LipschitzWith L (c i)) → ∀ (f g h : SchwartzMap E ℂ),
      ‖∑ i : Fin n, highSlotWindowedBlock A a b d u v w t (c i) f g h i‖ₑ ≤
        (L : ℝ≥0∞) * C * triLpMass f g h 4 4 2 :=
  exists_highSlotWindowedBlock_sum_bound_paper false A ha hA a b d hca hcb ca cb hu hv hw

end Burnett.A06
