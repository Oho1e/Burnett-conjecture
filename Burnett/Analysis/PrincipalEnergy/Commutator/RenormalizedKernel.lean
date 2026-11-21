import Burnett.Analysis.PrincipalEnergy.Commutator.VanishingInput

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Filter MeasureTheory Burnett.Microlocal.AngularDyadicKernel
open scoped BigOperators FourierTransform Topology

private def highFrequencyIntegrand (a : E → E → ℂ) (x : E) (f : SchwartzMap E ℂ) (ξ : E) : ℂ :=
  (Real.fourierChar (inner ℝ ξ x)) •
    (firstOrderHighSymbol a x ξ * (SchwartzMap.fourierTransformCLM ℂ f) ξ)

private theorem highFrequency_integrable (a : E → E → ℂ) (ha : FrequencyOrderOne a) (x : E)
    (f : SchwartzMap E ℂ) : Integrable (highFrequencyIntegrand a x f) (volume : Measure E) := by
  obtain ⟨M,hM,hA⟩ := ha.order 0
  have hOrder (ξ : E) : ‖a x ξ‖ ≤ M * (1 + ‖ξ‖) := by
    simpa only [pow_zero, mul_one, norm_iteratedFDeriv_zero] using hA x ξ
  let F := SchwartzMap.fourierTransformCLM ℂ f
  have hM₁ := F.integrable.norm.add (F.integrable_pow_mul (volume : Measure E) 1)
  have hM₂ : Integrable (fun ξ : E => M * ((1 + ‖ξ‖) * ‖F ξ‖)) (volume : Measure E) := by
    simpa only [add_mul, one_mul, pow_one] using hM₁.const_mul M
  have hSym : Continuous (firstOrderHighSymbol a x) :=
    (Complex.continuous_ofReal.comp (continuous_const.sub radialCore_contDiff.continuous)).mul (ha.smooth x).continuous
  have hChar : Continuous (fun ξ : E => Real.fourierChar (inner ℝ ξ x)) :=
    Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)
  apply hM₂.mono' (hChar.smul (hSym.mul F.continuous)).aestronglyMeasurable
  filter_upwards with ξ
  have hc : ‖((1 - radialCore ξ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr (radialCore_le_one ξ))]
    linarith [radialCore_nonneg ξ]
  change ‖Real.fourierChar (inner ℝ ξ x) •
    ((((1 - radialCore ξ : ℝ) : ℂ) * a x ξ) * F ξ)‖ ≤ _
  rw [Circle.norm_smul, norm_mul, norm_mul, ← mul_assoc M]
  exact mul_le_mul_of_nonneg_right ((mul_le_of_le_one_left (norm_nonneg _) hc).trans (hOrder ξ)) (norm_nonneg _)

theorem firstOrderHighAction_sub_smul (a : E → E → ℂ) (ha : FrequencyOrderOne a) (x : E)
    (f g : SchwartzMap E ℂ) (c : ℂ) :
    firstOrderHighAction a (f - c • g : SchwartzMap E ℂ) x =
      firstOrderHighAction a f x - c * firstOrderHighAction a g x := by
  have h : highFrequencyIntegrand a x (f - c • g) =
      fun ξ => highFrequencyIntegrand a x f ξ - c • highFrequencyIntegrand a x g ξ := by
    funext ξ
    simp only [highFrequencyIntegrand, map_sub, map_smul, SchwartzMap.sub_apply, SchwartzMap.smul_apply,
      mul_sub, mul_smul_comm, smul_sub, smul_comm (Real.fourierChar _)]
  have heq (u : SchwartzMap E ℂ) : firstOrderHighAction a u x = ∫ ξ, highFrequencyIntegrand a x u ξ := by
    rw [firstOrderHighAction, Real.fourierIntegralInv_eq]
    rfl
  rw [heq, h]
  change (∫ ξ, highFrequencyIntegrand a x f ξ - (c • highFrequencyIntegrand a x g) ξ) = _
  rw [integral_sub (highFrequency_integrable a ha x f) ((highFrequency_integrable a ha x g).smul c)]
  change (∫ ξ, highFrequencyIntegrand a x f ξ) - (∫ ξ, c • highFrequencyIntegrand a x g ξ) = _
  rw [integral_smul, ← heq, ← heq, smul_eq_mul]

def scalarSchwartzProduct (r f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) f.hasTemperateGrowth r

@[simp] theorem scalarSchwartzProduct_apply (r f : SchwartzMap E ℂ) (x : E) :
    scalarSchwartzProduct r f x = r x * f x := rfl

def highCoefficientCommutator (a : E → E → ℂ) (r f : SchwartzMap E ℂ) (x : E) : ℂ :=
  r x * firstOrderHighAction a f x - firstOrderHighAction a (scalarSchwartzProduct r f) x

/-- At an arbitrary point the counterterm carries the action on a local
function of value one. The centered input has an absolutely integrable
diagonal remainder for the original nonhomogeneous Fourier operator. -/
theorem highCoefficientCommutator_centered_kernel (a : E → E → ℂ) (ha : FrequencyOrderOne a)
    (r f χ : SchwartzMap E ℂ) (L F H : NNReal)
    (hr : LipschitzWith L r) (hf : LipschitzWith F f) (hχ : LipschitzWith H χ)
    (hfC : HasCompactSupport (f : E → ℂ)) (hχC : HasCompactSupport (χ : E → ℂ)) (x : E) (hx : χ x = 1) :
    Integrable (fun y => coefficientKernel r (firstOrderKernel a) x y * (f y - f x * χ y)) (volume : Measure E) ∧
      highCoefficientCommutator a r f x - f x * highCoefficientCommutator a r χ x =
        ∫ y, coefficientKernel r (firstOrderKernel a) x y * (f y - f x * χ y) := by
  let g := f - f x • χ
  have hScaled : HasCompactSupport ((fun _ : E => f x) • (χ : E → ℂ)) := hχC.smul_left
  have hgC : HasCompactSupport (g : E → ℂ) := hfC.sub hScaled
  have hg0 : g x = 0 := by simp [g, hx]
  have hg : LipschitzWith (F + ‖f x‖₊ * H) (g : E → ℂ) := by
    change LipschitzWith (F + ‖f x‖₊ * H) (fun y => f y - f x • χ y)
    exact hf.sub ((lipschitzWith_smul (β := ℂ) (f x)).comp hχ)
  have hP : scalarSchwartzProduct r g = scalarSchwartzProduct r f - f x • scalarSchwartzProduct r χ := by
    ext y
    simp only [scalarSchwartzProduct_apply, g, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul]
    ring
  have hgA : highCoefficientCommutator a r g x =
      highCoefficientCommutator a r f x - f x * highCoefficientCommutator a r χ x := by
    unfold highCoefficientCommutator
    have hAct : firstOrderHighAction a g x = firstOrderHighAction a f x - f x * firstOrderHighAction a χ x :=
      firstOrderHighAction_sub_smul a ha x f χ (f x)
    rw [hAct, hP, firstOrderHighAction_sub_smul a ha x]
    ring
  have h := firstOrderHighCoefficientCommutator_vanishingInput a ha r g (scalarSchwartzProduct r g)
    (scalarSchwartzProduct_apply r g) L _ hr hg hgC x hg0
  have hgValue (y : E) : g y = f y - f x * χ y := rfl
  rcases h with ⟨hi,he⟩
  change highCoefficientCommutator a r g x = _ at he
  rw [hgA] at he
  simpa only [hgValue] using And.intro hi he

end Burnett.Analysis.FirstOrderDyadic
