import Burnett.Analysis.PrincipalEnergy.Freezing.RealSkewTest
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Set Metric Burnett.RicciSymbol
open Burnett.Microlocal.AngularCommutator
open scoped ContDiff FourierTransform RealInnerProductSpace

/-- The actual spectrum of a degree-one multiplier has finite moments against
Schwartz data, including the moment needed to differentiate its inverse transform. -/
theorem radian_spectrum_norm_moment (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (u : SchwartzMap E ℂ) (n : ℕ) :
    Integrable (fun ξ : E => ‖ξ‖ ^ n * ‖radianActionSpectrum b u ξ‖) := by
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have hs : sphere (0 : E) 1 ⊆ {x | x ≠ 0} := by
    intro x hx
    have h : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
    exact norm_ne_zero_iff.mp (h.trans_ne one_ne_zero)
  obtain ⟨A,hA⟩ := (isCompact_sphere (0 : E) 1).bddAbove_image (hb.continuousOn.norm.mono hs)
  have hbnd (ξ : E) : ‖b (tau • ξ)‖ ≤ (max A 0 * tau) * ‖ξ‖ := by
    by_cases hξ : ξ = 0
    · simp [hξ, homogeneous_value_zero hom]
    let y := ‖ξ‖⁻¹ • ξ
    have hp := norm_pos_iff.mpr hξ
    have hy : y ∈ sphere (0 : E) 1 := by
      simpa only [mem_sphere, dist_zero_right, y] using norm_smul_inv_norm (𝕜 := ℝ) hξ
    have hscale : ‖ξ‖ • y = ξ := by simp [y, smul_smul, hp.ne']
    have hscaled : tau • ξ = (tau * ‖ξ‖) • y := by
      calc
        _ = tau • (‖ξ‖ • y) := congrArg (fun v : E => tau • v) hscale.symm
        _ = _ := (mul_smul tau ‖ξ‖ y).symm
    rw [hscaled, hom _ (mul_pos hτ hp), norm_mul,
      Real.norm_of_nonneg (mul_nonneg hτ.le hp.le)]
    calc
      _ ≤ (tau * ‖ξ‖) * max A 0 :=
        mul_le_mul_of_nonneg_left ((hA (mem_image_of_mem _ hy)).trans (le_max_left _ _))
          (mul_nonneg hτ.le hp.le)
      _ = _ := by ring
  let U := SchwartzMap.fourierTransformCLM ℂ u
  have hMeas : Measurable b :=
    measurable_of_continuousOn_compl_singleton 0 hb.continuousOn
  have hSpectrum : Measurable (radianActionSpectrum b u) := by
    change Measurable (fun ξ : E => (b (tau • ξ) : ℂ) * U ξ)
    exact (Complex.continuous_ofReal.measurable.comp
      (hMeas.comp (continuous_const.smul continuous_id).measurable)).mul U.continuous.measurable
  apply ((U.integrable_pow_mul volume (n + 1)).const_mul (max A 0 * tau)).mono'
    ((continuous_norm.measurable.pow_const n).mul hSpectrum.norm).aestronglyMeasurable
  filter_upwards with ξ
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
  change ‖ξ‖ ^ n * ‖(b (tau • ξ) : ℂ) * U ξ‖ ≤
    (max A 0 * tau) * (‖ξ‖ ^ (n + 1) * ‖U ξ‖)
  rw [norm_mul, Complex.norm_real, pow_succ]
  calc
    _ ≤ ‖ξ‖ ^ n * (((max A 0 * tau) * ‖ξ‖) * ‖U ξ‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hbnd ξ) (norm_nonneg _)) (pow_nonneg (norm_nonneg _) _)
    _ = _ := by ring

/-- The Fourier multiplier commutes pointwise with the actual first derivative
of its Schwartz input. Its output has a genuine real Fréchet derivative. -/
theorem radian_action_coordinate_derivative (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (u : SchwartzMap E ℂ) (x : E) :
    DifferentiableAt ℝ (radianAction b u) x ∧
      ∀ j : Index, fderiv ℝ (radianAction b u) x (EuclideanSpace.single j 1) =
        radianAction b (energyPartial j u) x := by
  let F := radianActionSpectrum b u
  let L := VectorFourier.fourierSMulRight (innerSL ℝ) F
  let Neg : E →L[ℝ] E := -ContinuousLinearMap.id ℝ E
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  let β : E → ℝ := fun z => b (tau • z)
  have hβ : ContDiffOn ℝ ∞ β {y | y ≠ 0} :=
    hb.comp (contDiff_const.smul contDiff_id).contDiffOn (fun _ hy => smul_ne_zero hτ.ne' hy)
  have hβhom (t : ℝ) (ht : 0 < t) (y : E) : β (t • y) = t * β y := by
    change b (tau • t • y) = t * b (tau • y)
    rw [smul_comm tau t y, hom t ht]
  have hF : Integrable F := orderOne_spectrum_integrable β hβ hβhom u
  have hM : Integrable (fun ξ => ‖ξ‖ * ‖F ξ‖) := by
    simpa only [F, pow_one] using radian_spectrum_norm_moment b hb hom u 1
  have hL : Integrable L := by
    apply (hM.const_mul (2 * Real.pi * ‖(innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)‖)).mono'
      hF.aestronglyMeasurable.fourierSMulRight
    filter_upwards with ξ
    simpa only [L, mul_assoc] using VectorFourier.norm_fourierSMulRight_le (innerSL ℝ) F ξ
  have inverse : radianAction b u = (𝓕 F) ∘ Neg :=
    (radianActionSpectrum_inverse b u).symm.trans
      (funext fun y => Real.fourierIntegralInv_eq_fourierIntegral_neg F y)
  have hD : HasFDerivAt (radianAction b u) ((𝓕 L (Neg x)).comp Neg) x := by
    rw [inverse]
    exact (Real.hasFDerivAt_fourierIntegral hF hM (Neg x)).comp x Neg.hasFDerivAt
  refine ⟨hD.differentiableAt, fun j => ?_⟩
  rw [hD.fderiv]
  change 𝓕 L (-x) (-(EuclideanSpace.single j 1)) =
    radianAction b (energyPartial j u) x
  rw [Real.fourierIntegral_continuousLinearMap_apply hL,
    ← radianActionSpectrum_inverse, Real.fourierIntegralInv_eq_fourierIntegral_neg]
  congr 1
  funext ξ
  have hcoord : (innerSL ℝ) ξ (-(EuclideanSpace.single j 1)) = -ξ j := by
    change inner ℝ ξ (-(EuclideanSpace.single j 1)) = -ξ j
    simp [EuclideanSpace.inner_single_right]
  simp only [L, F, VectorFourier.fourierSMulRight_apply, hcoord, Complex.real_smul,
    smul_eq_mul, radianActionSpectrum, energyPartial_fourier, tau]
  push_cast
  ring

/-- The same derivative identity with the real skew normalization used in the
freezing proof. -/
theorem radian_skew_coordinate_derivative (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (u : SchwartzMap E ℂ) (x : E) :
    DifferentiableAt ℝ (radianSkewAction b u) x ∧
      ∀ j : Index, fderiv ℝ (radianSkewAction b u) x (EuclideanSpace.single j 1) =
        radianSkewAction b (energyPartial j u) x := by
  obtain ⟨hD, hCoord⟩ := radian_action_coordinate_derivative b hb hom u x
  have h := hD.hasFDerivAt.const_mul (-Complex.I)
  refine ⟨h.differentiableAt, fun j => ?_⟩
  change fderiv ℝ (fun y => -Complex.I * radianAction b u y) x (EuclideanSpace.single j 1) = _
  rw [h.fderiv]
  change -Complex.I * fderiv ℝ (radianAction b u) x (EuclideanSpace.single j 1) = _
  rw [hCoord j]
  rfl

end Burnett.A02.FrequencySplit
