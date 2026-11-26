import Burnett.Analysis.CubicEnergy.JointMultiplier.JointKernelMoment
import Burnett.Analysis.CubicEnergy.JointMultiplier.JointDyadicWindows

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.A06

open MeasureTheory
open Burnett.A02.FrequencySplit
open scoped ENNReal NNReal ContDiff ComplexConjugate

/-- The high-slot first moment of the actual joint inverse Fourier kernel. -/
def highSlotBlockMoment (a : Joint → ℂ) : ℝ≥0∞ :=
  ∫⁻ y : Joint, ‖(‖y.2‖ : ℂ) * blockKernel a y‖ₑ

theorem highSlotBlockMoment_lt_top (a : Joint → ℂ) (ha : HasCompactSupport a)
    (hs : ContDiff ℝ ∞ a) : highSlotBlockMoment a < ⊤ := by
  have hK := (blockKernel_integrable a ha hs).2
  have hI : Integrable (fun y : Joint => (‖y.2‖ : ℂ) * blockKernel a y) := by
    apply (blockKernel_mixed_moment a ha hs 0 1).mono'
    · exact ((Complex.continuous_ofReal.comp (continuous_snd.norm)).mul hK).aestronglyMeasurable
    · filter_upwards with y
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg y.2), pow_zero,
        one_mul, pow_one]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg _)
  exact hI.hasFiniteIntegral

/-- One physical order-one Fourier block of the high-input commutator.
The reference kernel acts on the two translations at scale s. -/
def highSlotBlockDensity (a : Joint → ℂ) (s : ℝ) (d : E → ℝ)
    (f g h : SchwartzMap E ℂ) (y : Joint) (x : E) : ℂ :=
  ((s⁻¹ * (d (x - s • y.2) - d x) : ℝ) : ℂ) *
    (blockKernel a y * (f (x - s • y.1) * g (x - s • y.2) * conj (h x)))

/-- The actual Lebesgue pairing of one high-slot commutator block. -/
def highSlotBlockPair (a : Joint → ℂ) (s : ℝ) (d : E → ℝ)
    (f g h : SchwartzMap E ℂ) : ℂ :=
  ∫ yx : Joint × E, highSlotBlockDensity a s d f g h yx.1 yx.2
    ∂((volume : Measure Joint).prod (volume : Measure E))

private theorem normalized_coefficient_difference {d : E → ℝ} {L : ℝ≥0}
    (hd : LipschitzWith L d) {s : ℝ} (hs : 0 < s) (x y : E) :
    ‖s⁻¹ * (d (x - s • y) - d x)‖ ≤ (L : ℝ) * ‖y‖ := by
  have hdiff := hd.dist_le_mul (x - s • y) x
  have shift : x - s • y - x = -(s • y) := by abel
  rw [Real.dist_eq, dist_eq_norm, shift, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hs] at hdiff
  rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hs]
  exact (mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hs.le)).trans_eq
    (by field_simp [hs.ne'])

private theorem highSlotBlock_lintegral_le
    (a : Joint → ℂ) (ha : HasCompactSupport a) (hsmooth : ContDiff ℝ ∞ a)
    {s : ℝ} (hs : 0 < s) {d : E → ℝ} {L : ℝ≥0} (hd : LipschitzWith L d)
    (p q r : ℝ) (hbalance : triBalance p q r) (f g h : SchwartzMap E ℂ) :
    (∫⁻ yx : Joint × E, ‖highSlotBlockDensity a s d f g h yx.1 yx.2‖ₑ
        ∂((volume : Measure Joint).prod (volume : Measure E))) ≤
      (L : ℝ≥0∞) * highSlotBlockMoment a * triLpMass f g h p q r := by
  let K := fun y : Joint => (‖y.2‖ : ℂ) * blockKernel a y
  have hK₀ := (blockKernel_integrable a ha hsmooth).2
  have hK : Continuous K := (Complex.continuous_ofReal.comp continuous_snd.norm).mul hK₀
  have hD : Continuous d := hd.continuous
  have hF : Continuous (fun yx : Joint × E => highSlotBlockDensity a s d f g h yx.1 yx.2) := by
    unfold highSlotBlockDensity
    fun_prop
  have point (y : Joint) (x : E) :
      ‖highSlotBlockDensity a s d f g h y x‖ₑ ≤
        (L : ℝ≥0∞) * ‖K y * (f (x - s • y.1) * g (x - s • y.2) * h x)‖ₑ := by
    have real :
        ‖highSlotBlockDensity a s d f g h y x‖ ≤
          (L : ℝ) * ‖K y * (f (x - s • y.1) * g (x - s • y.2) * h x)‖ := by
      calc
        _ = ‖s⁻¹ * (d (x - s • y.2) - d x)‖ *
              (‖blockKernel a y‖ * (‖f (x - s • y.1)‖ * ‖g (x - s • y.2)‖ * ‖h x‖)) := by
          simp only [highSlotBlockDensity, norm_mul, Complex.norm_real, Complex.norm_conj]
        _ ≤ ((L : ℝ) * ‖y.2‖) *
              (‖blockKernel a y‖ * (‖f (x - s • y.1)‖ * ‖g (x - s • y.2)‖ * ‖h x‖)) :=
          mul_le_mul_of_nonneg_right (normalized_coefficient_difference hd hs x y.2) (by positivity)
        _ = _ := by
          simp only [K, norm_mul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg y.2)]
          ring
    have en := ENNReal.ofReal_le_ofReal real
    rw [ENNReal.ofReal_mul (show 0 ≤ (L : ℝ) from L.2)] at en
    simpa only [ofReal_norm_eq_enorm, ENNReal.ofReal_coe_nnreal] using en
  let P := ENNReal.ofReal p
  let Q := ENNReal.ofReal q
  let R := ENNReal.ofReal r
  let S := (P⁻¹ + Q⁻¹)⁻¹
  letI : ENNReal.HolderTriple P Q S := ENNReal.HolderTriple.of P Q
  letI : ENNReal.HolderTriple S R 1 := ⟨by simpa only [S, inv_inv, inv_one] using hbalance⟩
  rw [lintegral_prod _ hF.enorm.aemeasurable]
  calc
    _ ≤ ∫⁻ y : Joint, ∫⁻ x : E,
        (L : ℝ≥0∞) * ‖K y * (f (x - s • y.1) * g (x - s • y.2) * h x)‖ₑ :=
      lintegral_mono fun y => lintegral_mono (point y)
    _ = (L : ℝ≥0∞) *
        (∫⁻ y : Joint, ∫⁻ x : E, ‖K y * (f (x - s • y.1) * g (x - s • y.2) * h x)‖ₑ) := by
      calc
        _ = ∫⁻ y : Joint, (L : ℝ≥0∞) *
            (∫⁻ x : E, ‖K y * (f (x - s • y.1) * g (x - s • y.2) * h x)‖ₑ) :=
          lintegral_congr fun _ => lintegral_const_mul' _ _ ENNReal.coe_ne_top
        _ = _ := lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_left' (dilated_kernel_trilinear_bound
        (p := P) (s := Q) (r := S) (t := R) K hK.measurable f g h s) _

private theorem highSlotBlockPair_bound
    (a : Joint → ℂ) (ha : HasCompactSupport a) (hsmooth : ContDiff ℝ ∞ a)
    {s : ℝ} (hs : 0 < s) {d : E → ℝ} {L : ℝ≥0} (hd : LipschitzWith L d)
    (p q r : ℝ) (hbalance : triBalance p q r) (f g h : SchwartzMap E ℂ) :
    ‖highSlotBlockPair a s d f g h‖ₑ ≤
      (L : ℝ≥0∞) * highSlotBlockMoment a * triLpMass f g h p q r :=
  (enorm_integral_le_lintegral_enorm _).trans
    (highSlotBlock_lintegral_le a ha hsmooth hs hd p q r hbalance f g h)

private theorem triBalance_four_four_two : triBalance 4 4 2 := by
  rw [triBalance, ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4),
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  norm_num

/-- The physical kernel pairing is an ordinary absolutely convergent integral. -/
theorem highSlotBlockDensity_integrable (a : Joint → ℂ) (ha : HasCompactSupport a)
    (hsmooth : ContDiff ℝ ∞ a) {s : ℝ} (hs : 0 < s)
    {d : E → ℝ} {L : ℝ≥0} (hd : LipschitzWith L d) (f g h : SchwartzMap E ℂ) :
    Integrable (fun yx : Joint × E => highSlotBlockDensity a s d f g h yx.1 yx.2)
      ((volume : Measure Joint).prod (volume : Measure E)) := by
  have hK := (blockKernel_integrable a ha hsmooth).2
  have hD := hd.continuous
  have hC : Continuous (fun yx : Joint × E => highSlotBlockDensity a s d f g h yx.1 yx.2) := by
    unfold highSlotBlockDensity
    fun_prop
  refine ⟨hC.aestronglyMeasurable, ?_⟩
  apply (highSlotBlock_lintegral_le a ha hsmooth hs hd 4 4 2 triBalance_four_four_two f g h).trans_lt
  refine ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (highSlotBlockMoment_lt_top a ha hsmooth)) ?_
  unfold triLpMass
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (f.eLpNorm_lt_top _ volume) (g.eLpNorm_lt_top _ volume))
    (h.eLpNorm_lt_top _ volume)

/-- Both manuscript exponents for one actual smooth joint Fourier block.
The same Lipschitz first-moment constant works at every positive scale. -/
theorem highSlotBlockPair_two_paper_bounds (a : Joint → ℂ) (ha : HasCompactSupport a)
    (hsmooth : ContDiff ℝ ∞ a) {s : ℝ} (hs : 0 < s)
    {d : E → ℝ} {L : ℝ≥0} (hd : LipschitzWith L d) (f g h : SchwartzMap E ℂ) :
    ‖highSlotBlockPair a s d f g h‖ₑ ≤
      (L : ℝ≥0∞) * highSlotBlockMoment a * triLpMass f g h 4 4 2 ∧
    ‖highSlotBlockPair a s d f g h‖ₑ ≤
      (L : ℝ≥0∞) * highSlotBlockMoment a * triLpMass f g h 4 2 4 := by
  refine ⟨highSlotBlockPair_bound a ha hsmooth hs hd 4 4 2 triBalance_four_four_two f g h, ?_⟩
  have hb : triBalance 4 2 4 := by
    simpa only [triBalance, add_assoc, add_comm, add_left_comm] using triBalance_four_four_two
  exact highSlotBlockPair_bound a ha hsmooth hs hd 4 2 4 hb f g h

end Burnett.A06
