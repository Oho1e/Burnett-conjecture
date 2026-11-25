import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CoefficientWindowUniformLimit
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CoefficientWindowTelescoping
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighCoefficientGapRadian

set_option autoImplicit false
set_option maxHeartbeats 4300000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open MeasureTheory Filter Finset
open scoped ENNReal ContDiff ComplexConjugate Topology BigOperators

private abbrev pairMeasure : Measure (Joint × E) :=
  (volume : Measure Joint).prod (volume : Measure E)

def coefficientRealPart (D : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  (2⁻¹ : ℂ) • (D+gapConjugate D)

theorem coefficientRealPart_apply (D : SchwartzMap E ℂ) (x : E) :
    coefficientRealPart D x = ((D x).re : ℂ) := by
  change (2⁻¹ : ℂ)*(D x + conj (D x)) = ((D x).re : ℂ)
  have h : (2⁻¹ : ℂ) = ((1/2 : ℝ) : ℂ) := by norm_num
  rw [h]
  apply Complex.ext
  · simp [Complex.mul_re,Complex.add_re]
    ring
  · simp [Complex.mul_im,Complex.add_im]

private theorem actual_pair_eq_coefficientRealPart {A : Joint → ℂ}
    (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A) (s : ℝ) (D f g h : SchwartzMap E ℂ) :
    highSlotBlockPair A s (fun x => (D x).re) f g h =
      radianHighCommutatorPair (radianHighReferenceBlock A s) (fun x => (D x).re) f g h :=
  highSlotBlockPair_eq_radianHighCommutatorPair A ha hA s _ f g h
    (gapSchwartzProduct (coefficientRealPart D) g) (gapSchwartzProduct (coefficientRealPart D) h)
    (fun x => by rw [gapSchwartzProduct_apply,coefficientRealPart_apply])
    (fun x => by rw [gapSchwartzProduct_apply,coefficientRealPart_apply])

private def coefficientTestWeight (A : Joint → ℂ) (s : ℝ)
    (f g h : SchwartzMap E ℂ) (yx : Joint × E) : ℂ :=
  blockKernel A yx.1 * (f (yx.2-s • yx.1.1)*g (yx.2-s • yx.1.2)*conj (h yx.2))

private theorem coefficientTestWeight_integrable {A : Joint → ℂ} (ha : HasCompactSupport A)
    (hA : ContDiff ℝ ∞ A) (s : ℝ) (f g h : SchwartzMap E ℂ) :
    Integrable (coefficientTestWeight A s f g h) pairMeasure := by
  obtain ⟨hK,hKC⟩ := blockKernel_integrable A ha hA
  have hC : Continuous (coefficientTestWeight A s f g h) := by unfold coefficientTestWeight; fun_prop
  refine ⟨hC.aestronglyMeasurable,?_⟩
  change (∫⁻ yx, ‖coefficientTestWeight A s f g h yx‖ₑ ∂pairMeasure) < ⊤
  rw [lintegral_prod _ hC.enorm.aemeasurable]
  letI : ENNReal.HolderTriple 4 4 2 := by
    have h : (4:ℝ).HolderTriple 4 2 := ⟨by norm_num,by norm_num,by norm_num⟩
    simpa using h.ennrealOfReal
  simp only [coefficientTestWeight,enorm_mul,RCLike.enorm_conj]
  have hf := dilated_kernel_trilinear_bound (p := 4) (s := 4) (r := 2) (t := 2) (blockKernel A)
    hKC.measurable f g h s
  simp only [enorm_mul] at hf
  exact hf.trans_lt (ENNReal.mul_lt_top hK.hasFiniteIntegral
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (f.eLpNorm_lt_top _ volume) (g.eLpNorm_lt_top _ volume))
      (h.eLpNorm_lt_top _ volume)))

private theorem coefficientDensity_integrable {A : Joint → ℂ} (ha : HasCompactSupport A)
    (hA : ContDiff ℝ ∞ A) (s : ℝ) (D f g h : SchwartzMap E ℂ) :
    Integrable (fun yx : Joint × E => highSlotBlockDensity A s (fun x => (D x).re) f g h yx.1 yx.2)
      pairMeasure := by
  let B := SchwartzMap.seminorm ℝ 0 0 D
  have cB (x : E) : ‖(D x).re‖≤B := by
    simpa only [Real.norm_eq_abs,B] using (Complex.abs_re_le_norm (D x)).trans (D.norm_le_seminorm ℝ x)
  have hK := (blockKernel_integrable A ha hA).2
  have hDC : Continuous (fun x : E => (D x).re) := Complex.continuous_re.comp D.continuous
  have hC : Continuous (fun yx : Joint × E =>
      highSlotBlockDensity A s (fun x => (D x).re) f g h yx.1 yx.2) := by
    unfold highSlotBlockDensity
    fun_prop
  refine ((coefficientTestWeight_integrable ha hA s f g h).norm.const_mul (‖s⁻¹‖*(2*B))).mono'
    hC.aestronglyMeasurable ?_
  filter_upwards with yx
  have hcoef : ‖(D (yx.2-s • yx.1.2)).re-(D yx.2).re‖≤2*B := by
    linarith only [norm_sub_le (D (yx.2-s • yx.1.2)).re (D yx.2).re,
      cB (yx.2-s • yx.1.2),cB yx.2]
  change ‖((s⁻¹*((D (yx.2-s • yx.1.2)).re-(D yx.2).re) : ℝ):ℂ)*coefficientTestWeight A s f g h yx‖ ≤
    (‖s⁻¹‖*(2*B))*‖coefficientTestWeight A s f g h yx‖
  rw [norm_mul,Complex.norm_real,norm_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef (norm_nonneg _)) (norm_nonneg _)

private def coefficientRadianAddHom {A : Joint → ℂ} (ha : HasCompactSupport A)
    (hA : ContDiff ℝ ∞ A) (s : ℝ) (f g h : SchwartzMap E ℂ) : SchwartzMap E ℂ →+ ℂ where
  toFun D := radianHighCommutatorPair (radianHighReferenceBlock A s) (fun x => (D x).re) f g h
  map_zero' := by
    rw [← actual_pair_eq_coefficientRealPart ha hA s,highSlotBlockPair]
    simp only [highSlotBlockDensity,SchwartzMap.zero_apply,Complex.zero_re,sub_zero,mul_zero,
      Complex.ofReal_zero,zero_mul,integral_zero]
  map_add' D C := by
    simp_rw [← actual_pair_eq_coefficientRealPart ha hA s,highSlotBlockPair]
    rw [← integral_add (coefficientDensity_integrable ha hA s D f g h)
      (coefficientDensity_integrable ha hA s C f g h)]
    apply integral_congr_ae
    filter_upwards with yx
    simp only [highSlotBlockDensity,SchwartzMap.add_apply,Complex.add_re,Complex.ofReal_mul,
      Complex.ofReal_sub,Complex.ofReal_add]
    ring

/-- The same low-pass/annular telescoping is an exact equality of the
original radian commutator pairings, at every finite cutoff. -/
theorem radianHighCommutatorPair_coefficient_telescoping
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    (χ D f g h : SchwartzMap E ℂ) (s S : ℝ) (N : ℕ) :
    radianHighCommutatorPair (radianHighReferenceBlock A s)
      (fun x => (windowTest χ D S x).re) f g h +
      (∑ j ∈ range N, radianHighCommutatorPair (radianHighReferenceBlock A s)
        (fun x => (windowTest (coefficientDyadicBandpass χ) D (dyadicCoefficientScale S (j+1)) x).re) f g h) =
      radianHighCommutatorPair (radianHighReferenceBlock A s)
        (fun x => (windowTest χ D (dyadicCoefficientScale S N) x).re) f g h := by
  let P := coefficientRadianAddHom ha hA s f g h
  change P (windowTest χ D S) +
      (∑ j ∈ range N, P (windowTest (coefficientDyadicBandpass χ) D (dyadicCoefficientScale S (j+1)))) =
      P (windowTest χ D (dyadicCoefficientScale S N))
  rw [← map_sum,← map_add,windowTest_coefficient_telescoping]

/-- At a fixed true reference operator scale, the exact radian tested
commutator with the low-pass coefficient converges to the pairing with
the original real part of the coefficient. -/
theorem tendsto_radianHighCommutatorPair_lowpass_coefficient
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    (χ D f g h : SchwartzMap E ℂ) (hχ : χ 0=1)
    (s : ℝ) (S : ℕ → ℝ) (hS : Tendsto S atTop (𝓝 0)) :
    Tendsto (fun n => radianHighCommutatorPair (radianHighReferenceBlock A s)
      (fun x => (windowTest χ D (S n) x).re) f g h) atTop
        (𝓝 (radianHighCommutatorPair (radianHighReferenceBlock A s) (fun x => (D x).re) f g h)) := by
  obtain ⟨ε,hε,hLim,hWindow⟩ := exists_windowTest_uniform_small_scale_error χ D hχ S hS
  let d (x : E) := (D x).re
  let dN (n : ℕ) (x : E) := (windowTest χ D (S n) x).re
  let F (yx : Joint × E) := highSlotBlockDensity A s d f g h yx.1 yx.2
  let Fₙ (n : ℕ) (yx : Joint × E) := highSlotBlockDensity A s (dN n) f g h yx.1 yx.2
  let B := SchwartzMap.seminorm ℝ 0 0 D+1
  let w (yx : Joint × E) := (‖s⁻¹‖*2*B)*‖coefficientTestWeight A s f g h yx‖
  have hK := (blockKernel_integrable A ha hA).2
  have hdc : ∀ n, Continuous (dN n) := fun n => Complex.continuous_re.comp (windowTest χ D (S n)).continuous
  have hF (n : ℕ) : Continuous (Fₙ n) := by
    have hd := hdc n
    unfold Fₙ highSlotBlockDensity
    fun_prop
  have hDiff (n : ℕ) (x : E) : ‖dN n x-d x‖ ≤ ε n := by
    rw [Real.norm_eq_abs]
    change |(windowTest χ D (S n) x).re-(D x).re| ≤ _
    rw [← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans (hWindow n x)
  have hdlim (x : E) : Tendsto (fun n => dN n x) atTop (𝓝 (d x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => hDiff n x) hLim
  have hEventually : ∀ᶠ n in atTop, ε n < 1 := hLim.eventually (gt_mem_nhds zero_lt_one)
  have hbound : ∀ᶠ n in atTop, ∀ᵐ yx ∂pairMeasure, ‖Fₙ n yx‖≤w yx := by
    filter_upwards [hEventually] with n hn
    refine .of_forall fun yx => ?_
    have hD (x : E) : ‖dN n x‖ ≤ B := by
      have z' : ‖dN n x‖ ≤ ‖d x‖+‖dN n x-d x‖ := by
        simpa only [sub_add_cancel,add_comm ‖dN n x-d x‖ ‖d x‖] using
          norm_add_le (dN n x-d x) (d x)
      have dz : ‖d x‖ ≤ SchwartzMap.seminorm ℝ 0 0 D := by
        simpa only [d,Real.norm_eq_abs] using
          (Complex.abs_re_le_norm (D x)).trans (D.norm_le_seminorm ℝ x)
      dsimp only [B]
      linarith only [z',dz,hDiff n x,hn]
    have hcoef : ‖dN n (yx.2-s • yx.1.2)-dN n yx.2‖ ≤ 2*B := by
      linarith only [norm_sub_le (dN n (yx.2-s • yx.1.2)) (dN n yx.2),hD (yx.2-s • yx.1.2),hD yx.2]
    change ‖((s⁻¹*(dN n (yx.2-s • yx.1.2)-dN n yx.2) : ℝ):ℂ)*coefficientTestWeight A s f g h yx‖ ≤
      (‖s⁻¹‖*2*B)*‖coefficientTestWeight A s f g h yx‖
    rw [norm_mul,Complex.norm_real,norm_mul,mul_assoc ‖s⁻¹‖ 2 B]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef (norm_nonneg _)) (norm_nonneg _)
  have hpoint : ∀ᵐ yx ∂pairMeasure, Tendsto (fun n => Fₙ n yx) atTop (𝓝 (F yx)) := by
    refine .of_forall fun yx => ?_
    have hdiff := (hdlim (yx.2-s • yx.1.2)).sub (hdlim yx.2)
    have hprod := hdiff.const_mul (s⁻¹)
    have hcc := Complex.continuous_ofReal.continuousAt.tendsto.comp hprod
    exact hcc.mul_const (coefficientTestWeight A s f g h yx)
  have hI := tendsto_integral_filter_of_dominated_convergence w
    (.of_forall (fun n => (hF n).aestronglyMeasurable)) hbound
    ((coefficientTestWeight_integrable ha hA s f g h).norm.const_mul _) hpoint
  simp_rw [← actual_pair_eq_coefficientRealPart ha hA s]
  exact hI

end Burnett.A06
