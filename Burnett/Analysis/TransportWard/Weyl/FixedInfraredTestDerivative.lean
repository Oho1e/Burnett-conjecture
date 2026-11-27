import Burnett.Analysis.FrozenTransport.FrozenCubicOddTest
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false
set_option maxHeartbeats 3800000

noncomputable section

namespace Burnett.V03.Palatini

open MeasureTheory Filter Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped BigOperators ComplexConjugate ContDiff FourierTransform RealInnerProductSpace

open private fixedInfraredSymbol_spectrum_integrable from Burnett.Analysis.FrozenTransport.FrozenCubicActionPairing

private theorem radianSpectrum_partial (β : E → ℝ) (u : SchwartzMap E ℂ) (a : Index) (ξ : E) :
    radianActionSpectrum β (energyPartial a u) ξ =
      ((tau * ξ a : ℝ) : ℂ) * Complex.I * radianActionSpectrum β u ξ := by
  simp only [radianActionSpectrum, energyPartial_fourier]
  ring

private theorem radian_spectrum_first_moment_of_integrable (β : E → ℝ)
    (hβ : ∀ u : SchwartzMap E ℂ, Integrable (radianActionSpectrum β u)) (u : SchwartzMap E ℂ) :
    Integrable (fun ξ : E => ‖ξ‖ * ‖radianActionSpectrum β u ξ‖) := by
  let F := radianActionSpectrum β u
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  let P (a : Index) (ξ : E) := ‖ξ a‖ * ‖F ξ‖
  have hP (a : Index) : Integrable (P a) := by
    refine ((hβ (energyPartial a u)).norm.const_mul tau⁻¹).congr (.of_forall fun ξ => ?_)
    change tau⁻¹ * ‖radianActionSpectrum β (energyPartial a u) ξ‖ = ‖ξ a‖ * ‖F ξ‖
    simp only [radianSpectrum_partial, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hτ.le, ← mul_assoc, inv_mul_cancel₀ hτ.ne', one_mul, F]
  have hBound (ξ : E) : ‖ξ‖ ≤ ∑ a : Index, ‖ξ a‖ := by
    have hRep : (∑ a : Index, ξ a • EuclideanSpace.single a (1 : ℝ)) = ξ := by
      simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
        (EuclideanSpace.basisFun Index ℝ).sum_repr ξ
    calc
      _ = ‖∑ a : Index, ξ a • EuclideanSpace.single a (1 : ℝ)‖ := congrArg norm hRep.symm
      _ ≤ _ := by
        simpa only [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one] using
          norm_sum_le (s := Finset.univ) (fun a : Index => ξ a • EuclideanSpace.single a (1 : ℝ))
  apply (integrable_finset_sum Finset.univ (fun a _ => hP a)).mono'
    (continuous_norm.aestronglyMeasurable.mul (hβ u).aestronglyMeasurable.norm)
  exact .of_forall fun ξ => by
    change ‖‖ξ‖ * ‖F ξ‖‖ ≤ ∑ a : Index, P a ξ
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    simp only [P, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hBound ξ) (norm_nonneg _)

/-- The original inverse Fourier derivative, in the same radian convention,
applies to a fixed infrared test whenever its spectra against Schwartz
inputs are integrable. -/
theorem radianTest_coordinateDerivative_of_integrable (β : E → ℝ)
    (hβ : ∀ u : SchwartzMap E ℂ, Integrable (radianActionSpectrum β u)) (u : SchwartzMap E ℂ) (x : E) :
    DifferentiableAt ℝ (fun y => (-Complex.I) * radianAction β u y) x ∧
    ∀ a : Index, fderiv ℝ (fun y => (-Complex.I) * radianAction β u y) x (EuclideanSpace.single a 1) =
      (-Complex.I) * radianAction β (energyPartial a u) x := by
  let F := radianActionSpectrum β u
  let L := VectorFourier.fourierSMulRight (innerSL ℝ) F
  let Neg : E →L[ℝ] E := -ContinuousLinearMap.id ℝ E
  have hF : Integrable F := hβ u
  have hM : Integrable (fun ξ => ‖ξ‖ * ‖F ξ‖) := radian_spectrum_first_moment_of_integrable β hβ u
  have hL : Integrable L := by
    apply (hM.const_mul (2 * Real.pi * ‖(innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)‖)).mono'
      hF.aestronglyMeasurable.fourierSMulRight
    filter_upwards with ξ
    simpa only [L, mul_assoc] using VectorFourier.norm_fourierSMulRight_le (innerSL ℝ) F ξ
  have hInv : radianAction β u = (𝓕 F) ∘ Neg :=
    (radianActionSpectrum_inverse β u).symm.trans
      (funext fun y => Real.fourierIntegralInv_eq_fourierIntegral_neg F y)
  have hD : HasFDerivAt (radianAction β u) ((𝓕 L (Neg x)).comp Neg) x := by
    rw [hInv]
    exact (Real.hasFDerivAt_fourierIntegral hF hM (Neg x)).comp x Neg.hasFDerivAt
  have hDA := hD.const_mul (-Complex.I)
  refine ⟨hDA.differentiableAt, fun a => ?_⟩
  rw [hDA.fderiv]
  change (-Complex.I) * 𝓕 L (-x) (-(EuclideanSpace.single a 1)) = _
  congr 1
  rw [Real.fourierIntegral_continuousLinearMap_apply hL,
    ← radianActionSpectrum_inverse, Real.fourierIntegralInv_eq_fourierIntegral_neg]
  congr 1
  funext ξ
  have hc : (innerSL ℝ) ξ (-(EuclideanSpace.single a 1)) = -ξ a := by
    change inner ℝ ξ (-(EuclideanSpace.single a 1)) = -ξ a
    simp [EuclideanSpace.inner_single_right]
  simp only [L, F, VectorFourier.fourierSMulRight_apply, hc, Complex.real_smul, smul_eq_mul,
    radianSpectrum_partial, tau]
  push_cast
  ring

theorem fixedInfraredTest_coordinateDerivative
    (cut : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (u : SchwartzMap E ℂ) (x : E) :
    let β := fixedInfraredSymbol cut 0 b
    DifferentiableAt ℝ (fun y => (-Complex.I) * radianAction β u y) x ∧
    ∀ a : Index, fderiv ℝ (fun y => (-Complex.I) * radianAction β u y) x (EuclideanSpace.single a 1) =
      (-Complex.I) * radianAction β (energyPartial a u) x := by
  exact radianTest_coordinateDerivative_of_integrable _ (fixedInfraredSymbol_spectrum_integrable
    cut 0 hcut (fun _ => by simp) b hb hom) u x

/-- Each Schwartz input to the regularized frozen test has bounded output
and bounded first coordinate derivatives in the physical chart. -/
theorem fixedInfraredTest_global_coordinateBounds
    (cut : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (u : SchwartzMap E ℂ) :
    let β := fixedInfraredSymbol cut 0 b
    let Q (x : E) := (-Complex.I) * radianAction β u x
    Differentiable ℝ Q ∧ (∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖Q x‖ ≤ M) ∧
    ∀ a : Index, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ Q x (EuclideanSpace.single a 1)‖ ≤ M := by
  intro β Q
  have hD (x : E) := fixedInfraredTest_coordinateDerivative cut hcut b hb hom u x
  let M (f : SchwartzMap E ℂ) := ∫ ξ, ‖radianActionSpectrum β f ξ‖
  have hM (f : SchwartzMap E ℂ) : 0 ≤ M f := integral_nonneg fun _ => norm_nonneg _
  have hB (f : SchwartzMap E ℂ) (x : E) : ‖(-Complex.I) * radianAction β f x‖ ≤ M f := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, ← radianActionSpectrum_inverse, Real.fourierIntegralInv]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  refine ⟨fun x => (hD x).1, ⟨M u, hM u, hB u⟩, fun a =>
    ⟨M (energyPartial a u), hM (energyPartial a u), fun x => ?_⟩⟩
  have he : fderiv ℝ Q x (EuclideanSpace.single a 1) = (-Complex.I) * radianAction β (energyPartial a u) x :=
    (hD x).2 a
  rw [he]
  exact hB (energyPartial a u) x

end Burnett.V03.Palatini
