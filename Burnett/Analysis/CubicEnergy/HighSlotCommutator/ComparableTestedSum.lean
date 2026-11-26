import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotPaperExponents
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.ComparablePhysicalIntegration
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighAnnularCoefficient
import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWeightedSummation

set_option autoImplicit false
set_option maxHeartbeats 5500000
noncomputable section
namespace Burnett.A06

open MeasureTheory Finset
open Burnett.A02.FrequencySplit
open scoped ENNReal NNReal ContDiff FourierTransform BigOperators

private def comparableKernelConstant (A : Joint → ℂ) (l v : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1+‖l⁻¹‖)^5*(1+‖v⁻¹‖))*kernelMoment A 5 6

private theorem comparableKernelConstant_finite {A : Joint → ℂ} (ha : HasCompactSupport A)
    (hA : ContDiff ℝ ∞ A) (l v : ℝ) : comparableKernelConstant A l v < ⊤ :=
  ENNReal.mul_lt_top ENNReal.ofReal_lt_top (kernelMoment_lt_top A ha hA 5 6)

private theorem comparable_weight_bounded (A : Joint → ℂ) {l : ℝ} (hl : 0<l) (v : ℝ)
    (y : Joint) (Y Q : E) (hY : ‖Y‖≤‖y.1‖+‖y.2‖) (hQ : ‖Q‖≤‖y.2‖) :
    ‖blockKernel A y‖ₑ*(coefficientWindowShiftCost l Y*ENNReal.ofReal (1+‖(-v⁻¹) • Q‖)) ≤
      ENNReal.ofReal ((1+‖l⁻¹‖)^5*(1+‖v⁻¹‖)) *
        ENNReal.ofReal ((1+‖y.1‖)^5*(1+‖y.2‖)^6*‖blockKernel A y‖) := by
  have ha : 1+‖Y‖ ≤ (1+‖y.1‖)*(1+‖y.2‖) := by
    nlinarith only [hY,mul_nonneg (norm_nonneg y.1) (norm_nonneg y.2)]
  have low : 1+l⁻¹*(‖Y‖+1) ≤ (1+‖l⁻¹‖)*((1+‖y.1‖)*(1+‖y.2‖)) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left ha (by positivity))
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hl.le)]
    nlinarith only [norm_nonneg Y]
  have high : 1+‖(-v⁻¹) • Q‖ ≤ (1+‖v⁻¹‖)*(1+‖y.2‖) := by
    rw [norm_smul,norm_neg]
    have h := mul_le_mul_of_nonneg_left hQ (norm_nonneg (v⁻¹))
    nlinarith only [h,norm_nonneg (v⁻¹),norm_nonneg y.2]
  have eL := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀
    (show 0 ≤ 1+l⁻¹*(‖Y‖+1) by positivity) low 5)
  have eH := ENNReal.ofReal_le_ofReal high
  refine (mul_le_mul_left' (mul_le_mul' eL eH) _).trans_eq ?_
  have hr :
      ((1+‖l⁻¹‖)*((1+‖y.1‖)*(1+‖y.2‖)))^5 * ((1+‖v⁻¹‖)*(1+‖y.2‖)) =
        ((1+‖l⁻¹‖)^5*(1+‖v⁻¹‖))*((1+‖y.1‖)^5*(1+‖y.2‖)^6) := by ring
  rw [← ENNReal.ofReal_mul (by positivity),hr,
    ENNReal.ofReal_mul (p := (1+‖l⁻¹‖)^5*(1+‖v⁻¹‖)) (by positivity),
    ENNReal.ofReal_mul (p := (1+‖y.1‖)^5*(1+‖y.2‖)^6) (q := ‖blockKernel A y‖) (by positivity),
    ofReal_norm_eq_enorm]
  ac_rfl

private theorem sum_kernel_comparable_bound (A : Joint → ℂ) {l : ℝ} (hl : 0<l) (v : ℝ)
    (Y Q : Joint → E)
    (hY : ∀ y, ‖Y y‖≤‖y.1‖+‖y.2‖) (hQ : ∀ y, ‖Q y‖≤‖y.2‖)
    (J : Finset ℕ) (V : ℕ → Joint → E → ℝ≥0∞)
    (hv : ∀ j, Measurable (Function.uncurry (V j))) (hK : Continuous (blockKernel A))
    {M : ℝ≥0∞} (hM : M≠⊤)
    (bound : ∀ y, (∑ j ∈ J, ∫⁻ x : E, V j y x) ≤
      M*(coefficientWindowShiftCost l (Y y)*ENNReal.ofReal (1+‖(-v⁻¹) • Q y‖))) :
    (∑ j ∈ J, ∫⁻ y : Joint, ‖blockKernel A y‖ₑ*(∫⁻ x : E, V j y x)) ≤
      M*comparableKernelConstant A l v := by
  let cost (y : Joint) := coefficientWindowShiftCost l (Y y)*ENNReal.ofReal (1+‖(-v⁻¹) • Q y‖)
  calc
    _ = ∫⁻ y : Joint, ‖blockKernel A y‖ₑ * ∑ j ∈ J, ∫⁻ x : E, V j y x := by
      rw [← lintegral_finset_sum _ (fun j _ => hK.measurable.enorm.mul (hv j).lintegral_prod_right)]
      simp only [mul_sum]
    _ ≤ ∫⁻ y : Joint, ‖blockKernel A y‖ₑ*(M*cost y) :=
      lintegral_mono fun y => mul_le_mul_left' (bound y) _
    _ ≤ ∫⁻ y : Joint, M*(ENNReal.ofReal ((1+‖l⁻¹‖)^5*(1+‖v⁻¹‖)) *
        ENNReal.ofReal ((1+‖y.1‖)^5*(1+‖y.2‖)^6*‖blockKernel A y‖)) := by
      refine lintegral_mono fun y => ?_
      rw [mul_left_comm]
      exact mul_le_mul_left' (comparable_weight_bounded A hl v y (Y y) (Q y) (hY y) (hQ y)) _
    _ = _ := by
      rw [lintegral_const_mul' _ _ hM,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl

private theorem measurable_shifted_enorm (a f : SchwartzMap E ℂ) (u t : ℝ) (j : ℕ)
    (Y : Joint → E) (hY : Continuous Y) :
    Measurable (fun yx : Joint × E => ‖shiftedTest a f u t j (Y yx.1) yx.2‖ₑ) := by
  let F := windowTest a f (u*dyadicScale t j)
  have hF := F.continuous
  have h : Continuous (fun yx : Joint × E => F (yx.2-dyadicScale t j • Y yx.1)) := by fun_prop
  exact h.enorm.measurable

private theorem measurable_coeff_amplitude (profile D : SchwartzMap E ℂ) (t : ℝ) (j : ℕ) :
    Measurable (fun yx : Joint × E => normalizedRealCoefficientAmplitude profile D t j yx.2) := by
  let F := windowTest profile D (dyadicScale t j)
  have h : Continuous (fun yx : Joint × E => (dyadicScale t j)⁻¹*(F yx.2).re) :=
    continuous_const.mul (Complex.continuous_re.comp (F.continuous.comp continuous_snd))
  exact h.enorm.measurable

/-- Moving the exponent two to the other slot exchanges the two available
Carleson estimates for the absolute products of the same windows. -/
private theorem exists_comparableCoefficient_low_low_high_sum_paper (inputL2 : Bool) (profile a b e : SchwartzMap E ℂ)
    (hc : HasCompactSupport (profile : E → ℂ)) (he : HasCompactSupport (e : E → ℂ))
    (hprofile : ∀ z, profile z≠0 → 1/2<‖z‖ ∧ ‖z‖<2)
    (heAnn : ∀ z, e z≠0 → 1/2<‖z‖ ∧ ‖z‖<2) :
    ∃ C : ℝ≥0∞, C<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {t T : ℝ}, 0<t → ∀ (J : Finset ℕ), (∀ j ∈ J, dyadicScale t j≤T) →
      ∀ (f g h : SchwartzMap E ℂ) {u v w : ℝ}, 0<u → 0<v → 0<w → ∀ Y Z Q : E,
      (∑ j ∈ J, ∫⁻ x : E, normalizedRealCoefficientAmplitude profile D t j x *
        (‖shiftedTest a f u t j Y x‖ₑ*‖shiftedTest b g v t j Z x‖ₑ*‖shiftedTest e h w t j Q x‖ₑ)) ≤
        C*(L : ℝ≥0∞)*coefficientWindowShiftCost u Y*coefficientWindowShiftCost v Z*
          ENNReal.ofReal (1+‖(-w⁻¹) • Q‖)*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  cases inputL2
  · exact exists_comparableCoefficient_low_low_high_sum profile a b e hc he hprofile heAnn
  · obtain ⟨C,hC,bound⟩ := exists_comparableCoefficient_low_high_low_sum profile a e b hc he hprofile heAnn
    refine ⟨C,hC,?_⟩
    intro D L hD t T ht J hJ f g h u v w hu hv hw Y Z Q
    have H := bound D L hD ht J hJ f h g hu hw hv Y Q Z
    simpa [triLpMass,highSlotInputExponent,highSlotTestExponent,
      mul_comm,mul_left_comm,mul_assoc] using H

private theorem exists_comparableCoefficient_low_high_low_sum_paper (inputL2 : Bool) (profile a b e : SchwartzMap E ℂ)
    (hc : HasCompactSupport (profile : E → ℂ)) (hb : HasCompactSupport (b : E → ℂ))
    (hprofile : ∀ z, profile z≠0 → 1/2<‖z‖ ∧ ‖z‖<2)
    (hbAnn : ∀ z, b z≠0 → 1/2<‖z‖ ∧ ‖z‖<2) :
    ∃ C : ℝ≥0∞, C<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {t T : ℝ}, 0<t → ∀ (J : Finset ℕ), (∀ j ∈ J, dyadicScale t j≤T) →
      ∀ (f g h : SchwartzMap E ℂ) {u v w : ℝ}, 0<u → 0<v → 0<w → ∀ Y Z Q : E,
      (∑ j ∈ J, ∫⁻ x : E, normalizedRealCoefficientAmplitude profile D t j x *
        (‖shiftedTest a f u t j Y x‖ₑ*‖shiftedTest b g v t j Z x‖ₑ*‖shiftedTest e h w t j Q x‖ₑ)) ≤
        C*(L : ℝ≥0∞)*coefficientWindowShiftCost u Y*ENNReal.ofReal (1+‖(-v⁻¹) • Z‖)*
          coefficientWindowShiftCost w Q*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  cases inputL2
  · exact exists_comparableCoefficient_low_high_low_sum profile a b e hc hb hprofile hbAnn
  · obtain ⟨C,hC,bound⟩ := exists_comparableCoefficient_low_low_high_sum profile a e b hc hb hprofile hbAnn
    refine ⟨C,hC,?_⟩
    intro D L hD t T ht J hJ f g h u v w hu hv hw Y Z Q
    have H := bound D L hD ht J hJ f h g hu hw hv Y Q Z
    simpa [triLpMass,highSlotInputExponent,highSlotTestExponent,
      mul_comm,mul_left_comm,mul_assoc] using H

/-- The actual two tested Fourier terms for the real comparable-frequency
coefficient, summed over any finite dyadic selection and fully integrated
against the original reference symbol kernel. -/
theorem exists_comparableCoefficient_tested_sum_bound_paper
    (inputL2 : Bool)
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    {lo hi ρ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ < 1)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖)
    (a b e d profile : SchwartzMap E ℂ) {u v w l : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w) (hl : 0<l)
    (hprofile : HasCompactSupport (profile : E → ℂ))
    (hb : HasCompactSupport (b : E → ℂ)) (he : HasCompactSupport (e : E → ℂ))
    (hProfileAnn : ∀ ξ, profile ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnB : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnE : ∀ ξ, e ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hShift : ∀ z : E, ‖z‖ ≤ 2+(1+ρ)*hi → a (u • z) = 1)
    (hIn : ∀ z : E, lo ≤ ‖z‖ → ‖z‖ ≤ hi → b (v • z) = 1)
    (hOut : ∀ z : E, (1-ρ)*lo ≤ ‖z‖ → ‖z‖ ≤ (1+ρ)*hi → e (w • z) = 1)
    (hLow : ∀ z : E, ‖z‖ ≤ ρ*hi → d (l • z) = 1) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {t : ℝ}, 0<t → ∀ (J : Finset ℕ) (C : ℕ → SchwartzMap E ℂ),
      (∀ j x, C j x = ((windowTest profile D (dyadicScale t j) x).re : ℂ)) →
      (∀ j z, 𝓕 (C j : E → ℂ) z ≠ 0 → ‖dyadicScale t j • z‖ ≤ 2) →
      ∀ f g h : SchwartzMap E ℂ,
      (∑ j ∈ J, ‖(dyadicScale t j)⁻¹ •
        (testedBlock A (dyadicScale t j) f (gapSchwartzProduct (C j) g) h -
         testedBlock A (dyadicScale t j) f g (gapSchwartzProduct (C j) h))‖ₑ) ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  obtain ⟨P,hP,leftBound⟩ := exists_comparableCoefficient_low_low_high_sum_paper inputL2
    profile d a e hprofile he hProfileAnn hAnnE
  obtain ⟨S,hS,rightBound⟩ := exists_comparableCoefficient_low_high_low_sum_paper inputL2
    profile d b a hprofile hb hProfileAnn hAnnB
  let W₀ := coefficientWindowShiftCost u 0
  let K₁ := comparableKernelConstant A l w
  let K₂ := comparableKernelConstant A l v
  have hW₀ : W₀<⊤ := ENNReal.ofReal_lt_top
  have hK₁ : K₁<⊤ := comparableKernelConstant_finite ha hA l w
  have hK₂ : K₂<⊤ := comparableKernelConstant_finite ha hA l v
  refine ⟨W₀*(P*K₁+S*K₂),ENNReal.mul_lt_top hW₀ (ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top hP hK₁,ENNReal.mul_lt_top hS hK₂⟩),?_⟩
  intro D L hD t ht J C realC suppC f g h
  let T := ∑ j ∈ J, dyadicScale t j
  have hJ (j : ℕ) (hj : j∈J) : dyadicScale t j≤T :=
    single_le_sum (f := dyadicScale t) (fun j _ => by unfold dyadicScale; positivity) hj
  let low (j : ℕ) := windowTest d f (l*dyadicScale t j)
  let G (j : ℕ) := windowTest b g (v*dyadicScale t j)
  let H (j : ℕ) := windowTest e h (w*dyadicScale t j)
  let U₁ (j : ℕ) (y : Joint) (x : E) := normalizedRealCoefficientAmplitude profile D t j x *
      (‖shiftedTest d f l t j (y.1-y.2) x‖ₑ*‖shiftedTest a g u t j 0 x‖ₑ*
        ‖shiftedTest e h w t j (-y.2) x‖ₑ)
  let U₂ (j : ℕ) (y : Joint) (x : E) := normalizedRealCoefficientAmplitude profile D t j x *
      (‖shiftedTest d f l t j y.1 x‖ₑ*‖shiftedTest b g v t j y.2 x‖ₑ*
        ‖shiftedTest a h u t j 0 x‖ₑ)
  let mass := triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2)
  have hMass : mass≠⊤ := by
    unfold mass triLpMass
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (f.eLpNorm_lt_top _ volume).ne (g.eLpNorm_lt_top _ volume).ne)
      (h.eLpNorm_lt_top _ volume).ne
  have hU₁ (j : ℕ) : Measurable (Function.uncurry (U₁ j)) := by
    exact (measurable_coeff_amplitude profile D t j).mul
      (((measurable_shifted_enorm d f l t j (fun y => y.1-y.2) (by fun_prop)).mul
        (measurable_shifted_enorm a g u t j (fun _ => 0) continuous_const)).mul
        (measurable_shifted_enorm e h w t j (fun y => -y.2) (by fun_prop)))
  have hU₂ (j : ℕ) : Measurable (Function.uncurry (U₂ j)) := by
    exact (measurable_coeff_amplitude profile D t j).mul
      (((measurable_shifted_enorm d f l t j Prod.fst continuous_fst).mul
        (measurable_shifted_enorm b g v t j Prod.snd continuous_snd)).mul
        (measurable_shifted_enorm a h u t j (fun _ => 0) continuous_const))
  have Kcont := (blockKernel_integrable A ha hA).2
  let B₁ := P*(L : ℝ≥0∞)*W₀*mass
  let B₂ := S*(L : ℝ≥0∞)*W₀*mass
  have f₁ : B₁≠⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hP.ne ENNReal.coe_ne_top) hW₀.ne) hMass
  have f₂ : B₂≠⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hS.ne ENNReal.coe_ne_top) hW₀.ne) hMass
  have BLeft := sum_kernel_comparable_bound A hl w (fun y => y.1-y.2) (fun y => -y.2)
    (fun y => norm_sub_le y.1 y.2) (fun y => by rw [norm_neg]) J U₁ hU₁ Kcont f₁
    (fun y => (leftBound D L hD ht J hJ f g h hl hu hw (y.1-y.2) 0 (-y.2)).trans_eq (by
      unfold B₁ W₀ mass
      ring))
  have BRight := sum_kernel_comparable_bound A hl v Prod.fst Prod.snd
    (fun y => le_add_of_nonneg_right (norm_nonneg y.2)) (fun _ => le_rfl) J U₂ hU₂ Kcont f₂
    (fun y => (rightBound D L hD ht J hJ f g h hl hv hu y.1 y.2 0).trans_eq (by
      unfold B₂ W₀ mass
      ring))
  calc
    _ ≤ ∑ j ∈ J, ((∫⁻ y, ‖blockKernel A y‖ₑ*(∫⁻ x, U₁ j y x)) +
        (∫⁻ y, ‖blockKernel A y‖ₑ*(∫⁻ x, U₂ j y x))) := by
      refine sum_le_sum fun j _ => ?_
      obtain ⟨eqI,eqO⟩ := comparableCoefficient_insert_tested_windows A ha hA hρ hρ'
        hBand a b e d u v w l hShift hIn hOut hLow (dyadicScale t j) (C j) f g h (suppC j)
      rw [smul_sub,eqI,eqO]
      let X := (dyadicScale t j)⁻¹ • testedBlock A (dyadicScale t j) (low j)
        (gapSchwartzProduct (C j) (windowTest a g (u*dyadicScale t j))) (H j)
      let Y := (dyadicScale t j)⁻¹ • testedBlock A (dyadicScale t j) (low j) (G j)
        (gapSchwartzProduct (C j) (windowTest a h (u*dyadicScale t j)))
      have hsum : ‖X-Y‖ₑ ≤ ‖X‖ₑ+‖Y‖ₑ := by
        simpa only [sub_eq_add_neg,enorm_neg] using enorm_add_le X (-Y)
      exact hsum.trans
        (add_le_add (comparable_tested_input_integral_le ha hA profile D (C j) a e d f g h t l u w j (realC j))
          (comparable_tested_output_integral_le ha hA profile D (C j) a b d f g h t l v u j (realC j)))
    _ ≤ B₁*K₁+B₂*K₂ := by
      rw [sum_add_distrib]
      exact add_le_add BLeft BRight
    _ = _ := by unfold B₁ B₂ W₀ mass; ring

theorem exists_comparableCoefficient_tested_sum_bound
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    {lo hi ρ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ < 1)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖)
    (a b e d profile : SchwartzMap E ℂ) {u v w l : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w) (hl : 0<l)
    (hprofile : HasCompactSupport (profile : E → ℂ))
    (hb : HasCompactSupport (b : E → ℂ)) (he : HasCompactSupport (e : E → ℂ))
    (hProfileAnn : ∀ ξ, profile ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnB : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnE : ∀ ξ, e ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hShift : ∀ z : E, ‖z‖ ≤ 2+(1+ρ)*hi → a (u • z) = 1)
    (hIn : ∀ z : E, lo ≤ ‖z‖ → ‖z‖ ≤ hi → b (v • z) = 1)
    (hOut : ∀ z : E, (1-ρ)*lo ≤ ‖z‖ → ‖z‖ ≤ (1+ρ)*hi → e (w • z) = 1)
    (hLow : ∀ z : E, ‖z‖ ≤ ρ*hi → d (l • z) = 1) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {t : ℝ}, 0<t → ∀ (J : Finset ℕ) (C : ℕ → SchwartzMap E ℂ),
      (∀ j x, C j x = ((windowTest profile D (dyadicScale t j) x).re : ℂ)) →
      (∀ j z, 𝓕 (C j : E → ℂ) z ≠ 0 → ‖dyadicScale t j • z‖ ≤ 2) →
      ∀ f g h : SchwartzMap E ℂ,
      (∑ j ∈ J, ‖(dyadicScale t j)⁻¹ •
        (testedBlock A (dyadicScale t j) f (gapSchwartzProduct (C j) g) h -
         testedBlock A (dyadicScale t j) f g (gapSchwartzProduct (C j) h))‖ₑ) ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 4 2 :=
  exists_comparableCoefficient_tested_sum_bound_paper false A ha hA hρ hρ' hBand a b e d profile hu hv hw hl
    hprofile hb he hProfileAnn hAnnB hAnnE hShift hIn hOut hLow

end Burnett.A06
