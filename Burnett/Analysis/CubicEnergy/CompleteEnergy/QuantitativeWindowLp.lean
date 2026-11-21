import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeWindowHormander
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.MikhlinFinite
import Burnett.Analysis.SignedFourierWindow.SignWindowSum
import Burnett.Analysis.SignedFourierWindow.CalderonWeakType
import Burnett.Analysis.SignedFourierWindow.InterpolationMoment
import Burnett.Analysis.SignedFourierWindow.KernelBilinearDual

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Burnett.Fourier
open scoped NNReal ENNReal

private def interpolationCoefficient (B H : ℝ) (p : ℝ) : ℝ≥0∞ :=
  let W : ℝ≥0∞ := 2*(4096+768*(ENNReal.ofReal B)^2+2*ENNReal.ofReal H)
  (ENNReal.ofReal ((2:ℝ)^p*p) *
    (W*ENNReal.ofReal (p-1)⁻¹ + (ENNReal.ofReal B)^2*ENNReal.ofReal (2-p)⁻¹))^(1/p)

private theorem interpolationCoefficient_lt_top (B H : ℝ) (p : ℝ) (hp : 1<p) :
    interpolationCoefficient B H p < ⊤ := by
  have hp0 : 0 < p := by linarith
  apply ENNReal.rpow_lt_top_of_nonneg (by positivity : 0 ≤ 1/p)
  dsimp only [interpolationCoefficient]
  finiteness

private theorem convolution_weak_one (K : E → ℂ) (hK : Continuous K) (h2 : MemLp K 2 volume)
    (D : ℝ) (hD : ∀ z, ‖K z‖ ≤ D) (B : ℝ) (hB : 0 ≤ B)
    (test : ∀ f : SchwartzMap E ℂ, ∃ u : ComplexL2 E,
      (u : E → ℂ) =ᵐ[volume] kernelApply K f ∧ ‖u‖ ≤ B*‖f.toLp 2 volume‖)
    (H : ℝ) (hH : ∀ h : E, (∫⁻ z in {z : E | 2*‖h‖ ≤ ‖z‖}, ‖K (z-h)-K z‖ₑ) ≤ ENNReal.ofReal H)
    (f : E → ℂ) (hf : Integrable f) (level : ℝ) (hl : 0 < level) :
    ENNReal.ofReal level * volume {x | level < ‖kernelApply K f x‖} ≤
      (2*(4096+768*(ENNReal.ofReal B)^2+2*ENNReal.ofReal H))*∫⁻ y, ‖f y‖ₑ := by
  let g := hf.1.mk f
  have hg : Measurable g := hf.1.stronglyMeasurable_mk.measurable
  have eq : f =ᵐ[volume] g := hf.1.ae_eq_mk
  have val (x : E) : kernelApply K f x = kernelApply K g x :=
    integral_congr_ae (eq.mono fun y hy => congrArg (fun z => K (x-y)*z) hy)
  have mass : (∫⁻ y, ‖g y‖ₑ) = ∫⁻ y, ‖f y‖ₑ :=
    lintegral_congr_ae (eq.symm.fun_comp (fun z => ‖z‖ₑ))
  have weak := kernel_weak_type K hK h2 D hD B hB test _ hH g hg (hf.congr eq)
    level.toNNReal (Real.toNNReal_pos.mpr hl)
  change ENNReal.ofReal level * volume {x | ENNReal.ofReal level < ‖kernelApply K g x‖ₑ} ≤ _ at weak
  have sets : {x | ENNReal.ofReal level < ‖kernelApply K g x‖ₑ} = {x | level < ‖kernelApply K g x‖} := by
    ext x
    simp only [Set.mem_setOf_eq,← ofReal_norm_eq_enorm,ENNReal.ofReal_lt_ofReal_iff_of_nonneg hl.le]
  rw [mass, sets] at weak
  simp_rw [val]
  exact weak

private theorem convolution_lower_Lp (K : E → ℂ) (hK : Continuous K) (hI : Integrable K)
    (h2 : MemLp K 2 volume) (D : ℝ) (hD : ∀ z, ‖K z‖ ≤ D) (B : ℝ) (hB : 0 ≤ B)
    (test : ∀ f : SchwartzMap E ℂ, ∃ u : ComplexL2 E,
      (u : E → ℂ) =ᵐ[volume] kernelApply K f ∧ ‖u‖ ≤ B*‖f.toLp 2 volume‖)
    (H : ℝ) (hH : ∀ h : E, (∫⁻ z in {z : E | 2*‖h‖ ≤ ‖z‖}, ‖K (z-h)-K z‖ₑ) ≤ ENNReal.ofReal H)
    (p : ℝ) (hp : 1<p) (hp2 : p<2) (f : E → ℂ) (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (kernelApply K f) (ENNReal.ofReal p) volume ≤
      interpolationCoefficient B H p * eLpNorm f (ENNReal.ofReal p) volume := by
  have strong := kernelApply_L2_extension K h2 B hB test
  have weak := convolution_weak_one K hK h2 D hD B hB test H hH
  apply kernelLp_exhaustion K hK hI D hD p hp.le _ _ f hf
  intro g hg hgi
  have result := kernel_interpolation_moment K hK D hD _ (ENNReal.ofReal B) weak strong g hg hgi p hp hp2
  have hp0 : 0<p := by linarith
  have ip : 0 ≤ 1/p := by positivity
  have r := ENNReal.rpow_le_rpow result ip
  rw [ENNReal.mul_rpow_of_nonneg _ _ ip] at r
  have nonzero := (ENNReal.ofReal_pos.mpr hp0).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm nonzero ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm nonzero ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal hp0.le]
  exact r

private theorem convolution_reflection (K : E → ℂ) (f : E → ℂ) :
    kernelApply (fun x => K (-x)) f = (kernelApply K (f ∘ Neg.neg)) ∘ Neg.neg := by
  funext x
  unfold kernelApply
  let g := fun y : E => K (-x-y)*f (-y)
  change (∫ y, K (-(x-y))*f y) = ∫ y, g y
  have point (y : E) : K (-(x-y))*f y = g (-y) := by
    have eq : -(x-y) = -x - -y := by abel
    simp only [g,eq,neg_neg]
  simp_rw [point]
  exact (Measure.measurePreserving_neg (volume : Measure E)).integral_comp
    (LinearIsometryEquiv.neg ℝ (E := E)).toHomeomorph.measurableEmbedding g

private theorem reflected_norm_bound (K : E → ℂ) (hK : Continuous K) (p C : ℝ≥0∞)
    (est : ∀ f : E → ℂ, MemLp f p volume → eLpNorm (kernelApply K f) p volume ≤ C * eLpNorm f p volume)
    (f : E → ℂ) (hf : MemLp f p volume) :
    eLpNorm (kernelApply (fun x => K (-x)) f) p volume ≤ C * eLpNorm f p volume := by
  have neg := Measure.measurePreserving_neg (volume : Measure E)
  have hm := hf.comp_measurePreserving neg
  have hout := kernelApply_measurable_ae K hK (f ∘ Neg.neg) hm.1
  rw [convolution_reflection, eLpNorm_comp_measurePreserving hout.aestronglyMeasurable neg]
  exact (est _ hm).trans_eq (congrArg (C * ·) (eLpNorm_comp_measurePreserving hf.1 neg))

private theorem mikhlinBands_L2_test (a : SchwartzMap E ℂ) (ac : HasCompactSupport (a : E → ℂ))
    (cut : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) (A : ℝ) (hA : 0 ≤ A) (sup : ∀ ξ, ‖a ξ‖ ≤ A)
    (t : ℝ) (ht : 0<t) (I : Finset ℕ) (f : SchwartzMap E ℂ) :
    let K := finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) t 0 I (fun _ => 1)
    ∃ u : ComplexL2 E, (u : E → ℂ) =ᵐ[volume] kernelApply K f ∧ ‖u‖ ≤ (2*A)*‖f.toLp 2 volume‖ := by
  intro K
  refine ⟨fourierMultiplier (mikhlinBands a cut t ht I) (f.toLp 2 volume),
    mikhlinBands_test a ac cut t ht I f, ?_⟩
  have hsem : SchwartzMap.seminorm ℝ 0 0 a ≤ A :=
    SchwartzMap.seminorm_le_bound ℝ 0 0 a hA
      (by simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using sup)
  exact (fourierMultiplier_norm_le _ _).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsem (by norm_num)) (norm_nonneg _))

/-- Every finite unmodulated Mikhlin sum obeys the same Lᵖ bound when the window
supremum, the kernel moment and the weighted derivative are bounded by A. -/
theorem unmodulated_window_all_Lp (A : ℝ) (hA : 0 ≤ A) (p : ℝ) (hp : 1<p) :
    ∃ V : ℝ≥0∞, V < ⊤ ∧ ∀ (a : SchwartzMap E ℂ), HasCompactSupport (a : E → ℂ) →
      (∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) → (∀ ξ, ‖a ξ‖ ≤ A) →
      let φ := (SchwartzMap.fourierTransformCLE ℂ).symm a
      ((∫ z, ‖z‖ * ‖φ z‖) ≤ A) →
      (∀ z, (1+‖z‖)^5 * ‖fderiv ℝ φ z‖ ≤ A) →
      ∀ (t : ℝ), 0<t → ∀ (I : Finset ℕ) (f : E → ℂ), MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (kernelApply (finiteWindowKernel φ t 0 I (fun _ => 1)) f) (ENNReal.ofReal p) volume ≤
          V * eLpNorm f (ENNReal.ofReal p) volume := by
  let B := 2*A
  have hB : 0 ≤ B := by unfold B; positivity
  let H := annularHormanderBound A
  have low (r : ℝ) (hr : 1<r) (hr2 : r<2) (a : SchwartzMap E ℂ)
      (ac : HasCompactSupport (a : E → ℂ)) (cut : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
      (sup : ∀ ξ, ‖a ξ‖ ≤ A) :
      let φ := (SchwartzMap.fourierTransformCLE ℂ).symm a
      ((∫ z, ‖z‖ * ‖φ z‖) ≤ A) → (∀ z, (1+‖z‖)^5 * ‖fderiv ℝ φ z‖ ≤ A) →
      ∀ (t : ℝ), 0<t → ∀ (I : Finset ℕ) (f : E → ℂ), MemLp f (ENNReal.ofReal r) volume →
      eLpNorm (kernelApply (finiteWindowKernel φ t 0 I (fun _ => 1)) f) (ENNReal.ofReal r) volume ≤
        interpolationCoefficient B H r * eLpNorm f (ENNReal.ofReal r) volume := by
    intro φ moment deriv t ht I f hf
    let K := finiteWindowKernel φ t 0 I (fun _ => 1)
    obtain ⟨hK,hI,h2,D,hD⟩ := finite_kernel_regular φ t ht 0 I (fun _ => 1)
    exact convolution_lower_Lp K hK hI h2 D hD B hB (mikhlinBands_L2_test a ac cut A hA sup t ht I)
      H (kernel_hormander_enorm K hI H (unmodulated_window_hormander φ A hA moment deriv t ht I))
      r hr hr2 f hf
  rcases lt_trichotomy p 2 with hp2 | rfl | hp2
  · exact ⟨interpolationCoefficient B H p, interpolationCoefficient_lt_top B H p hp, low p hp hp2⟩
  · refine ⟨ENNReal.ofReal B, ENNReal.ofReal_lt_top, ?_⟩
    intro a ac cut sup φ _ _ t ht I f hf
    let K := finiteWindowKernel φ t 0 I (fun _ => 1)
    obtain ⟨_,_,h2,_,_⟩ := finite_kernel_regular φ t ht 0 I (fun _ => 1)
    simpa using kernelApply_L2_extension K h2 B hB
      (mikhlinBands_L2_test a ac cut A hA sup t ht I) f (by simpa using hf)
  · let r := p/(p-1)
    have den : 0<p-1 := by linarith
    have hr : 1<r := (lt_div_iff₀ den).mpr (by linarith)
    have hr2 : r<2 := (div_lt_iff₀ den).mpr (by linarith)
    refine ⟨interpolationCoefficient B H r, interpolationCoefficient_lt_top B H r hr, ?_⟩
    intro a ac cut sup φ moment deriv t ht I f hf
    let K := finiteWindowKernel φ t 0 I (fun _ => 1)
    obtain ⟨hK,hI,_,D,hD⟩ := finite_kernel_regular φ t ht 0 I (fun _ => 1)
    exact kernelLp_of_reflected_conjugate K hK hI D hD p hp2 _
      (reflected_norm_bound K hK _ _ (low r hr hr2 a ac cut sup moment deriv t ht I)) f hf

end Burnett.A02.FrequencySplit
