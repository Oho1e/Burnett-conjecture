import Burnett.Analysis.FrozenTransport.Ward.WardLowTransfer
import Burnett.Analysis.Fourier.RadianCoordinateDerivative

set_option autoImplicit false
set_option maxRecDepth 6600
set_option maxHeartbeats 12500000
noncomputable section

namespace Burnett.C02

open Set MeasureTheory Burnett.A02.FrequencySplit Burnett.A05
open Burnett.Analysis.CapFourier
open Burnett.A07 (coordinateDerivative radianFourier_coordinateDerivative)
open Burnett.Analysis.ProjectiveNullCaps (lowSlotWeight)
open scoped ContDiff

abbrev WardDerivativeAxes := Fin 4 × Fin 4 × Fin 4

private def directionDerivativeCoefficient (dir : E) (i : Fin 4) : ℂ :=
  Complex.I⁻¹ * (dir i : ℂ)

private theorem directionDerivativeCoefficient_smooth (i : Fin 4) :
    ContDiff ℝ ∞ (fun dir : E => directionDerivativeCoefficient dir i) :=
  contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff)

private theorem sum_sq_coordinate (p : E) : ∑ i : Fin 4, (p i)^2 = ‖p‖^2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq p).symm

/-- The radial factor in one slot is exactly the sum of four ordinary
coordinate derivatives with directional coefficients. -/
theorem ward_radialFourier_eq_sum_coordinateDerivative (f : SchwartzMap E ℂ) (p : E) :
    (‖p‖ : ℂ) * radianFourier f p = ∑ i,
      directionDerivativeCoefficient (endpointDirection p) i * radianFourier (coordinateDerivative i f) p := by
  have hTerm (i : Fin 4) : directionDerivativeCoefficient (endpointDirection p) i *
      radianFourier (coordinateDerivative i f) p =
        ((‖p‖⁻¹ * (p i)^2 : ℝ) : ℂ) * radianFourier f p := by
    rw [radianFourier_coordinateDerivative]
    simp only [directionDerivativeCoefficient, endpointDirection, PiLp.smul_apply, smul_eq_mul,
      Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
    calc
      _ = (Complex.I⁻¹ * Complex.I) * ((‖p‖ : ℂ)⁻¹ * (p i : ℂ)^2) * radianFourier f p := by ring
      _ = _ := by rw [inv_mul_cancel₀ Complex.I_ne_zero, one_mul]
  simp_rw [hTerm]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.mul_sum, sum_sq_coordinate]
  congr 1
  apply congrArg Complex.ofReal
  by_cases h : ‖p‖ = 0
  · simp [h]
  · field_simp

private def wardThirdDirection (x : WardLowPoint) : E :=
  endpointDirection (-(x.2.1 + x.2.2 • x.1))

private theorem wardThirdDirection_smooth : ContDiffOn ℝ ∞ wardThirdDirection wardLowProfileDomain := by
  apply endpointDirection_contDiffOn.comp
    (contDiff_snd.fst.add (contDiff_snd.snd.smul contDiff_fst)).neg.contDiffOn
  intro x hx
  apply neg_ne_zero.mpr
  intro h
  have he := eq_neg_of_add_eq_zero_left h
  have hn := hx.2.2
  rw [he, norm_neg] at hn
  linarith only [hn, hx.2.1]

private theorem unit_mem_wardLowProfileDomain (x : WardLowPoint) (h₁ : ‖x.1‖ = 1)
    (h₂ : ‖x.2.1‖ = 1) (hρ : |x.2.2| < 1 / 3) : x ∈ wardLowProfileDomain := by
  refine ⟨by rw [h₁]; norm_num, ?_, by rw [h₂]; norm_num⟩
  rw [norm_smul, h₁, mul_one, Real.norm_eq_abs]
  exact hρ.trans (by norm_num)

/-- The normalized symbol associated to one exact product of three ordinary
derivatives, in the actual signed low, high and third Fourier slots. -/
def wardLowCoordinateProfile (F : WardLowPoint → ℂ) (i : WardDerivativeAxes) (x : WardLowPoint) : ℂ :=
  F x * (directionDerivativeCoefficient x.1 i.1 *
    directionDerivativeCoefficient x.2.1 i.2.1 * directionDerivativeCoefficient (wardThirdDirection x) i.2.2)

private theorem wardLowCoordinateProfile_smooth (F : WardLowPoint → ℂ)
    (hF : ContDiffOn ℝ ∞ F wardLowProfileDomain) (i : WardDerivativeAxes) :
    ContDiffOn ℝ ∞ (wardLowCoordinateProfile F i) wardLowProfileDomain :=
  hF.mul ((((directionDerivativeCoefficient_smooth i.1).comp contDiff_fst).contDiffOn.mul
    ((directionDerivativeCoefficient_smooth i.2.1).comp contDiff_snd.fst).contDiffOn).mul
    ((directionDerivativeCoefficient_smooth i.2.2).comp_contDiffOn wardThirdDirection_smooth))

/-- The exact, unscaled coefficient in the original Fourier pairing. -/
def wardLowRadialSymbol (ϑ : ℝ → ℝ) (κ : ℝ) (F : WardLowPoint → ℂ) (x : Joint) : ℂ :=
  wardLowSlotSymbol ϑ κ F x * ((‖x.1‖ * ‖x.2‖ * ‖-(x.1+x.2)‖ : ℝ) : ℂ)

private theorem sum_mul_three {R : Type*} [CommSemiring R] (f g h : Fin 4 → R) :
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) =
      ∑ i : WardDerivativeAxes, f i.1 * g i.2.1 * h i.2.2 := by
  calc
    _ = ∑ i, f i * ((∑ j, g j) * (∑ k, h k)) := by rw [mul_assoc, Finset.sum_mul]
    _ = ∑ i, ∑ j, f i * (g j * (∑ k, h k)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul, Finset.mul_sum]
    _ = _ := by simp only [Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

private theorem wardLowRadialWeight_eq_coordinate_sum (ϑ : ℝ → ℝ) (κ : ℝ)
    (F : WardLowPoint → ℂ) (f g h : SchwartzMap E ℂ) (x : Joint) :
    radianTrilinearWeight (wardLowRadialSymbol ϑ κ F) f g h x =
      ∑ i : WardDerivativeAxes, radianTrilinearWeight (wardLowSlotSymbol ϑ κ (wardLowCoordinateProfile F i))
        (coordinateDerivative i.1 f) (coordinateDerivative i.2.1 g) (coordinateDerivative i.2.2 h) x := by
  classical
  by_cases hx : x ∈ wardLowActive
  · let r := -(x.1+x.2)
    have hr : wardThirdDirection (wardLowInput x) = endpointDirection r := by
      change endpointDirection (-(endpointDirection x.2 + (‖x.1‖ / ‖x.2‖) • endpointDirection x.1)) = _
      dsimp [r]
      rw [wardLowSignedThird_eq x.1 x.2 hx.1 hx.2.1,
        endpointDirection_pos_smul ‖x.2‖ (norm_pos_iff.mpr hx.2.1)]
    let w := (lowSlotWeight ϑ κ x.1 x.2 r : ℂ) * F (wardLowInput x)
    let f₁ := fun i => directionDerivativeCoefficient (endpointDirection x.1) i * radianFourier (coordinateDerivative i f) x.1
    let g₁ := fun i => directionDerivativeCoefficient (endpointDirection x.2) i * radianFourier (coordinateDerivative i g) x.2
    let h₁ := fun i => directionDerivativeCoefficient (endpointDirection r) i * radianFourier (coordinateDerivative i h) r
    have hp : wardLowSlotSymbol ϑ κ F x = w := by
      rw [wardLowSlotSymbol, piecewise_eq_of_mem _ _ _ hx]
    have hcoord (i : WardDerivativeAxes) :
        radianTrilinearWeight (wardLowSlotSymbol ϑ κ (wardLowCoordinateProfile F i))
          (coordinateDerivative i.1 f) (coordinateDerivative i.2.1 g) (coordinateDerivative i.2.2 h) x =
          w * (f₁ i.1 * g₁ i.2.1 * h₁ i.2.2) := by
      simp only [radianTrilinearWeight, radianWeight, Complex.ofReal_one, one_mul,
        wardLowSlotSymbol, piecewise_eq_of_mem _ _ _ hx, wardLowCoordinateProfile, hr]
      unfold w f₁ g₁ h₁ r wardLowInput
      ring
    calc
      _ = w * (((‖x.1‖ : ℂ) * radianFourier f x.1) * ((‖x.2‖ : ℂ) * radianFourier g x.2) *
          ((‖r‖ : ℂ) * radianFourier h r)) := by
        simp only [radianTrilinearWeight, radianWeight, Complex.ofReal_one, one_mul, wardLowRadialSymbol,
          hp, Complex.ofReal_mul, r]
        ring
      _ = w * ((∑ i, f₁ i) * (∑ i, g₁ i) * (∑ i, h₁ i)) := by
        rw [ward_radialFourier_eq_sum_coordinateDerivative f x.1,
          ward_radialFourier_eq_sum_coordinateDerivative g x.2,
          ward_radialFourier_eq_sum_coordinateDerivative h r]
      _ = _ := by
        rw [sum_mul_three, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => (hcoord i).symm)
  · simp only [radianTrilinearWeight, wardLowRadialSymbol, wardLowSlotSymbol,
      piecewise_eq_of_notMem _ _ _ hx, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-- Sum of the four actual coordinate gradient L³ norms of a scalar slot. -/
def wardCoordinateGradientL3 (f : SchwartzMap E ℂ) : ℝ :=
  ∑ i, (eLpNorm (coordinateDerivative i f : E → ℂ) 3 volume).toReal

/-- The actual first-low trilinear Fourier integral, with no radial
truncation and with all its radial factors restored. -/
theorem exists_wardLowRadialForm_bound (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16)
    (F : WardLowPoint → ℂ) (hF : ContDiffOn ℝ ∞ F wardLowProfileDomain) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g h : SchwartzMap E ℂ,
      Integrable (radianTrilinearWeight (wardLowRadialSymbol ϑ κ F) f g h) ∧
      ‖radianTrilinearForm (wardLowRadialSymbol ϑ κ F) f g h‖ ≤
        C * (wardCoordinateGradientL3 f * wardCoordinateGradientL3 g * wardCoordinateGradientL3 h) := by
  let m := fun i => wardLowSlotSymbol ϑ κ (wardLowCoordinateProfile F i)
  have hEach (i : WardDerivativeAxes) := exists_wardLowSlotForm_bound ϑ hϑ hCut κ hκ hSmall
    (wardLowCoordinateProfile F i) wardLowProfileDomain (wardLowCoordinateProfile_smooth F hF i)
    unit_mem_wardLowProfileDomain
  have hm (i : WardDerivativeAxes) : Measurable (m i) := (hEach i).1
  choose B hB using (fun i => (hEach i).2.1)
  choose C hC hEst using (fun i => (hEach i).2.2)
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro f g h
  let w := fun i => radianTrilinearWeight (m i) (coordinateDerivative i.1 f)
    (coordinateDerivative i.2.1 g) (coordinateDerivative i.2.2 h)
  let T := fun i => radianTrilinearForm (m i) (coordinateDerivative i.1 f)
    (coordinateDerivative i.2.1 g) (coordinateDerivative i.2.2 h)
  have hInt (i : WardDerivativeAxes) : Integrable (w i) :=
    integrable_radianTrilinearWeight_of_bounded (m i) (hm i).aestronglyMeasurable (B i) (hB i)
      (coordinateDerivative i.1 f) (coordinateDerivative i.2.1 g) (coordinateDerivative i.2.2 h)
  have hWeight : radianTrilinearWeight (wardLowRadialSymbol ϑ κ F) f g h = fun x => ∑ i, w i x :=
    funext (wardLowRadialWeight_eq_coordinate_sum ϑ κ F f g h)
  refine ⟨hWeight.symm ▸ integrable_finset_sum Finset.univ (fun i _ => hInt i), ?_⟩
  have hForm : radianTrilinearForm (wardLowRadialSymbol ϑ κ F) f g h = ∑ i, T i := by
    change (tau^8)⁻¹ • (∫ x, radianTrilinearWeight (wardLowRadialSymbol ϑ κ F) f g h x) =
      ∑ i : WardDerivativeAxes, (tau^8)⁻¹ • (∫ x, w i x)
    rw [hWeight, ← Finset.smul_sum, ← integral_finset_sum Finset.univ (fun i _ => hInt i)]
  rw [hForm]
  have hTerm (f₀ : SchwartzMap E ℂ) (j : Fin 4) :
      (eLpNorm (coordinateDerivative j f₀ : E → ℂ) 3 volume).toReal ≤ wardCoordinateGradientL3 f₀ := by
    unfold wardCoordinateGradientL3
    exact Finset.single_le_sum (f := fun i => (eLpNorm (coordinateDerivative i f₀ : E → ℂ) 3 volume).toReal)
      (fun (_ : Fin 4) _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)
  have hNonneg (f₀ : SchwartzMap E ℂ) : 0 ≤ wardCoordinateGradientL3 f₀ :=
    Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  calc
    _ ≤ ∑ i, ‖T i‖ := norm_sum_le _ _
    _ ≤ ∑ i, C i * (wardCoordinateGradientL3 f * wardCoordinateGradientL3 g * wardCoordinateGradientL3 h) := by
      apply Finset.sum_le_sum
      intro i _
      refine (hEst i _ _ _).trans (mul_le_mul_of_nonneg_left ?_ (hC i))
      simp only [triLpMass, ENNReal.toReal_mul, ENNReal.ofReal_ofNat]
      exact mul_le_mul (mul_le_mul (hTerm f i.1) (hTerm g i.2.1) ENNReal.toReal_nonneg (hNonneg f))
        (hTerm h i.2.2) ENNReal.toReal_nonneg (mul_nonneg (hNonneg f) (hNonneg g))
    _ = _ := (Finset.sum_mul _ _ _).symm

end Burnett.C02
