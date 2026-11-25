import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotAdjoint
import Burnett.Analysis.Fourier.RadianCoordinateDerivative
import Burnett.Analysis.H1FourierEnergy

set_option autoImplicit false
set_option maxHeartbeats 3600000

noncomputable section

namespace Burnett.A07

open MeasureTheory Filter
open Burnett.A02.FrequencySplit (E Joint radianFourier radianFourier_scaled tau)
open Burnett.A06
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

private theorem tau_positive : 0 < tau := mul_pos (by norm_num) Real.pi_pos

private theorem tau_smul_inv_smul (p : E) : tau • (tau⁻¹ • p) = p := by
  rw [smul_smul, mul_inv_cancel₀ tau_positive.ne', one_smul]

private def scaledFourierSchwartz (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  let factor := Units.mk0 (tau⁻¹) (inv_ne_zero tau_positive.ne')
  let scale : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (G := ℝˣ) factor
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scale (SchwartzMap.fourierTransformCLM ℂ f)

private theorem scaledFourierSchwartz_apply (f : SchwartzMap E ℂ) (p : E) :
    scaledFourierSchwartz f p = radianFourier f p := by
  change 𝓕 (f : E → ℂ) (tau⁻¹ • p) = radianFourier f p
  rw [← radianFourier_scaled, tau_smul_inv_smul]

private theorem weighted_scaledFourierSchwartz_integrable (f : SchwartzMap E ℂ) :
    Integrable (fun p : E => (1 + ‖p‖) * ‖scaledFourierSchwartz f p‖) := by
  have h := (scaledFourierSchwartz f).integrable_pow_mul volume 1
  simpa only [pow_one, add_mul, one_mul] using (scaledFourierSchwartz f).integrable.norm.add h

/-- The actual sesquilinear Fourier weight is absolutely integrable under the
zeroth order-one symbol bound and Schwartz assumptions on the three fields. -/
theorem integrable_radianHighPairWeight_of_orderOne
    (b : Joint → ℂ) (hb : Measurable b) (B : ℝ) (hB : 0 ≤ B)
    (bound : ∀ p : Joint, ‖b p‖ ≤ B * (1 + ‖p.1‖ + ‖p.2‖))
    (f u w : SchwartzMap E ℂ) :
    Integrable (radianHighPairWeight b f u w) := by
  let F := scaledFourierSchwartz f
  let U := scaledFourierSchwartz u
  let W := scaledFourierSchwartz w
  let M := SchwartzMap.seminorm ℝ 0 0 W
  have hM : 0 ≤ M := apply_nonneg _ _
  have majorant : Integrable (fun p : Joint => (B * M) *
      (((1 + ‖p.1‖) * ‖F p.1‖) * ((1 + ‖p.2‖) * ‖U p.2‖))) := by
    rw [Measure.volume_eq_prod E E]
    exact ((weighted_scaledFourierSchwartz_integrable f).mul_prod
      (weighted_scaledFourierSchwartz_integrable u)).const_mul _
  have hformula : radianHighPairWeight b f u w =
      fun p : Joint => b p * F p.1 * U p.2 * conj (W (p.2 + p.1)) := by
    funext p
    simp only [radianHighPairWeight, F, U, W, scaledFourierSchwartz_apply]
  rw [hformula]
  apply majorant.mono'
  · exact (((hb.mul (F.continuous.measurable.comp measurable_fst)).mul
      (U.continuous.measurable.comp measurable_snd)).mul
      (Complex.continuous_conj.measurable.comp
        (W.continuous.measurable.comp (measurable_snd.add measurable_fst)))).aestronglyMeasurable
  · apply Eventually.of_forall
    intro p
    have hfreq : 1 + ‖p.1‖ + ‖p.2‖ ≤ (1 + ‖p.1‖) * (1 + ‖p.2‖) := by
      nlinarith [mul_nonneg (norm_nonneg p.1) (norm_nonneg p.2)]
    simp only [norm_mul, Complex.norm_conj]
    calc
      _ ≤ (B * ((1 + ‖p.1‖) * (1 + ‖p.2‖))) * ‖F p.1‖ * ‖U p.2‖ * M := by
        gcongr
        · exact (bound p).trans (mul_le_mul_of_nonneg_left hfreq hB)
        · exact W.norm_le_seminorm ℝ _
      _ = _ := by ring

private theorem radianHighPairWeight_coordinateDerivative
    (a : Fin 4) (b : Joint → ℂ) (f u w : SchwartzMap E ℂ) (p : Joint) :
    radianHighPairWeight b (coordinateDerivative a f) u w p =
      -radianHighPairWeight b f u (coordinateDerivative a w) p -
        radianHighPairWeight b f (coordinateDerivative a u) w p := by
  simp only [radianHighPairWeight, radianFourier_coordinateDerivative, map_mul,
    map_add, Complex.conj_I, Complex.conj_ofReal, PiLp.add_apply, Complex.ofReal_add]
  ring

/-- The tested identity for `[∂ₐ,B_b(f,·)]`. The minus sign on differentiation
of the test comes from the distributional derivative of the output. -/
theorem radianHighPair_coordinateDerivative_commutator
    (a : Fin 4) (b : Joint → ℂ) (hb : Measurable b) (B : ℝ) (hB : 0 ≤ B)
    (bound : ∀ p : Joint, ‖b p‖ ≤ B * (1 + ‖p.1‖ + ‖p.2‖))
    (f u w : SchwartzMap E ℂ) :
    -radianHighPair b f u (coordinateDerivative a w) -
        radianHighPair b f (coordinateDerivative a u) w =
      radianHighPair b (coordinateDerivative a f) u w := by
  have htest := integrable_radianHighPairWeight_of_orderOne b hb B hB bound f u
    (coordinateDerivative a w)
  have hinput := integrable_radianHighPairWeight_of_orderOne b hb B hB bound f
    (coordinateDerivative a u) w
  have hsplit :
      (∫ p, -radianHighPairWeight b f u (coordinateDerivative a w) p -
        radianHighPairWeight b f (coordinateDerivative a u) w p) =
      -(∫ p, radianHighPairWeight b f u (coordinateDerivative a w) p) -
        ∫ p, radianHighPairWeight b f (coordinateDerivative a u) w p := by
    calc
      _ = (∫ p, -radianHighPairWeight b f u (coordinateDerivative a w) p) -
          ∫ p, radianHighPairWeight b f (coordinateDerivative a u) w p :=
        integral_sub (μ := volume)
          (f := fun p => -radianHighPairWeight b f u (coordinateDerivative a w) p)
          (g := radianHighPairWeight b f (coordinateDerivative a u) w) htest.neg hinput
      _ = _ := by rw [integral_neg]
  unfold radianHighPair
  rw [funext (radianHighPairWeight_coordinateDerivative a b f u w), hsplit, smul_sub, smul_neg]

private theorem radianHighPairWeight_highAdjoint
    (b : Joint → ℂ) (f u w : E → ℂ) (p : Joint) :
    radianHighPairWeight (highAdjointSymbol b) (fun x => conj (f x)) u w p =
      conj (radianHighPairWeight b f w u (highAdjointFrequencies p)) := by
  have hf := radianFourier_conj_neg f (-p.1)
  rw [neg_neg] at hf
  have hfreq : (p.2 + p.1) + -p.1 = p.2 := by abel
  simp only [radianHighPairWeight, highAdjointSymbol, map_mul, starRingEnd_self_apply]
  change conj (b (highAdjointFrequencies p)) * radianFourier (fun x => conj (f x)) p.1 *
    radianFourier u p.2 * conj (radianFourier w (p.2 + p.1)) =
      conj (b (highAdjointFrequencies p)) * conj (radianFourier f (-p.1)) *
        conj (radianFourier w (p.2 + p.1)) * radianFourier u ((p.2 + p.1) + -p.1)
  rw [hf, hfreq]
  ring

/-- The same high-frequency change of variables proves absolute integrability
for the actual adjoint pairing. -/
theorem integrable_radianHighPairWeight_highAdjoint_of_orderOne
    (b : Joint → ℂ) (hb : Measurable b) (B : ℝ) (hB : 0 ≤ B)
    (bound : ∀ p : Joint, ‖b p‖ ≤ B * (1 + ‖p.1‖ + ‖p.2‖))
    (f u w : SchwartzMap E ℂ) :
    Integrable (radianHighPairWeight (highAdjointSymbol b) (fun x => conj (f x)) u w) := by
  have hi := integrable_radianHighPairWeight_of_orderOne b hb B hB bound f w u
  have hc := Complex.conjCLE.toContinuousLinearMap.integrable_comp hi
  change Integrable (fun p => conj (radianHighPairWeight b f w u p)) at hc
  rw [funext (radianHighPairWeight_highAdjoint b f u w)]
  exact measurePreserving_highAdjointFrequencies.integrable_comp_of_integrable hc

/-- Differentiating the high-slot adjoint gives precisely the high-slot
adjoint of the differentiated low-field pairing. -/
theorem radianHighPair_coordinateDerivative_commutator_highAdjoint
    (a : Fin 4) (b : Joint → ℂ) (hb : Measurable b) (B : ℝ) (hB : 0 ≤ B)
    (bound : ∀ p : Joint, ‖b p‖ ≤ B * (1 + ‖p.1‖ + ‖p.2‖))
    (f u w : SchwartzMap E ℂ) :
    -radianHighPair (highAdjointSymbol b) (fun x => conj (f x)) u (coordinateDerivative a w) -
        radianHighPair (highAdjointSymbol b) (fun x => conj (f x)) (coordinateDerivative a u) w =
      radianHighPair (highAdjointSymbol b) (fun x => conj (coordinateDerivative a f x)) u w := by
  rw [radianHighPair_highAdjoint, radianHighPair_highAdjoint, radianHighPair_highAdjoint]
  have h := congrArg (conj : ℂ → ℂ)
    (radianHighPair_coordinateDerivative_commutator a b hb B hB bound f w u)
  simp only [map_neg, map_sub] at h
  calc
    _ = -conj (radianHighPair b f w (coordinateDerivative a u)) -
          conj (radianHighPair b f (coordinateDerivative a w) u) := by abel
    _ = _ := h

/-- Real coordinate differentiation commutes with complex conjugation, so the
adjoint commutator differentiates its actual conjugated low coefficient. -/
theorem fderiv_conj_apply_coordinate (a : Fin 4) (f : SchwartzMap E ℂ) (x : E) :
    fderiv ℝ (fun y => conj (f y)) x (EuclideanSpace.single a 1) =
      conj (coordinateDerivative a f x) := by
  have hd := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x
    (f.differentiable x).hasFDerivAt
  change fderiv ℝ (((Complex.conjCLE : ℂ →L[ℝ] ℂ) : ℂ → ℂ) ∘ (f : E → ℂ)) x
    (EuclideanSpace.single a 1) = _
  rw [hd.fderiv, coordinateDerivative, SchwartzMap.pderivCLM_apply]
  rfl

end Burnett.A07
