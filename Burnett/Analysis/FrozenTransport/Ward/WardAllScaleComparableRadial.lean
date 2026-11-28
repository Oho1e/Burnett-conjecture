import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleSignedPartition
import Burnett.Analysis.FrozenTransport.Ward.WardLowTransferDerivatives
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer

set_option autoImplicit false
set_option maxRecDepth 6500
set_option maxHeartbeats 12400000
noncomputable section

namespace Burnett.C02

open Set MeasureTheory Burnett.A05 Burnett.A02.FrequencySplit Burnett.Analysis.CapFourier
open Burnett.A07 (coordinateDerivative)
open scoped ContDiff

open private wardComparableSymbol_eq wardExtendedTriadSymbol wardSignedThird_smooth from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer
open private wardComparableSymbol_bounded from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleSignedPartition
open private directionDerivativeCoefficient directionDerivativeCoefficient_smooth sum_mul_three from Burnett.Analysis.FrozenTransport.Ward.WardLowTransferDerivatives

/-- The paper's three unscaled radial factors on its comparable branch. -/
def wardComparableRadialSymbol (ϑ : ℝ → ℝ) (κ : ℝ) (F : Joint → ℂ) (x : Joint) : ℂ :=
  wardComparableSymbol ϑ κ F x * ((‖x.1‖ * ‖x.2‖ * ‖wardSignedThird x‖ : ℝ) : ℂ)

private def wardComparableCoordinateProfile (F : Joint → ℂ) (i : WardDerivativeAxes) (x : Joint) : ℂ :=
  F x * (directionDerivativeCoefficient (endpointDirection x.1) i.1 *
    directionDerivativeCoefficient (endpointDirection x.2) i.2.1 *
      directionDerivativeCoefficient (endpointDirection (wardSignedThird x)) i.2.2)

private theorem wardComparableCoordinateProfile_smooth (F : Joint → ℂ)
    (hF : ContDiffOn ℝ ∞ F wardTriadDomain) (i : WardDerivativeAxes) :
    ContDiffOn ℝ ∞ (wardComparableCoordinateProfile F i) wardTriadDomain := by
  have hp : ContDiffOn ℝ ∞ (fun x : Joint => endpointDirection x.1) wardTriadDomain :=
    endpointDirection_contDiffOn.comp contDiff_fst.contDiffOn (fun _ hx => hx.1)
  have hq : ContDiffOn ℝ ∞ (fun x : Joint => endpointDirection x.2) wardTriadDomain :=
    endpointDirection_contDiffOn.comp contDiff_snd.contDiffOn (fun _ hx => hx.2.1)
  have hr : ContDiffOn ℝ ∞ (fun x : Joint => endpointDirection (wardSignedThird x)) wardTriadDomain :=
    endpointDirection_contDiffOn.comp wardSignedThird_smooth.contDiffOn (fun _ hx => hx.2.2)
  exact hF.mul ((((directionDerivativeCoefficient_smooth i.1).comp_contDiffOn hp).mul
    ((directionDerivativeCoefficient_smooth i.2.1).comp_contDiffOn hq)).mul
    ((directionDerivativeCoefficient_smooth i.2.2).comp_contDiffOn hr))

private theorem wardComparableCoordinateProfile_hom (F : Joint → ℂ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ x ∈ wardTriadDomain, F (t • x) = F x) (i : WardDerivativeAxes) :
    ∀ t : ℝ, 0 < t → ∀ x ∈ wardTriadDomain,
      wardComparableCoordinateProfile F i (t • x) = wardComparableCoordinateProfile F i x := by
  intro t ht x hx
  have hr : wardSignedThird (t • x) = t • wardSignedThird x := by
    simp only [wardSignedThird, Prod.smul_fst, Prod.smul_snd, smul_neg, smul_add]
  simp only [wardComparableCoordinateProfile, hHom t ht x hx, Prod.smul_fst, Prod.smul_snd, hr,
    endpointDirection_pos_smul t ht]

private theorem wardComparableCoordinateSymbol_eq (ϑ : ℝ → ℝ) (κ : ℝ) (F : Joint → ℂ)
    (i : WardDerivativeAxes) (x : Joint) :
    wardComparableSymbol ϑ κ (wardComparableCoordinateProfile F i) x =
      wardComparableSymbol ϑ κ F x * (directionDerivativeCoefficient (endpointDirection x.1) i.1 *
        directionDerivativeCoefficient (endpointDirection x.2) i.2.1 *
          directionDerivativeCoefficient (endpointDirection (wardSignedThird x)) i.2.2) := by
  classical
  rw [wardComparableSymbol_eq, wardComparableSymbol_eq]
  by_cases hx : x ∈ wardTriadDomain
  · have h₁ : wardExtendedTriadSymbol F x = F x := piecewise_eq_of_mem _ _ _ hx
    have h₂ : wardExtendedTriadSymbol (wardComparableCoordinateProfile F i) x = wardComparableCoordinateProfile F i x :=
      piecewise_eq_of_mem _ _ _ hx
    rw [h₁, h₂, wardComparableCoordinateProfile]
    exact (mul_assoc _ _ _).symm
  · have h₁ : wardExtendedTriadSymbol F x = 0 := piecewise_eq_of_notMem _ _ _ hx
    have h₂ : wardExtendedTriadSymbol (wardComparableCoordinateProfile F i) x = 0 := piecewise_eq_of_notMem _ _ _ hx
    rw [h₁, h₂, mul_zero, zero_mul]

private theorem wardComparableRadialWeight_eq_coordinate_sum (ϑ : ℝ → ℝ) (κ : ℝ)
    (F : Joint → ℂ) (f g h : SchwartzMap E ℂ) (x : Joint) :
    radianTrilinearWeight (wardComparableRadialSymbol ϑ κ F) f g h x =
      ∑ i : WardDerivativeAxes, radianTrilinearWeight (wardComparableSymbol ϑ κ (wardComparableCoordinateProfile F i))
        (coordinateDerivative i.1 f) (coordinateDerivative i.2.1 g) (coordinateDerivative i.2.2 h) x := by
  let r := wardSignedThird x
  let B := wardComparableSymbol ϑ κ F x
  let f₁ := fun i => directionDerivativeCoefficient (endpointDirection x.1) i * radianFourier (coordinateDerivative i f) x.1
  let g₁ := fun i => directionDerivativeCoefficient (endpointDirection x.2) i * radianFourier (coordinateDerivative i g) x.2
  let h₁ := fun i => directionDerivativeCoefficient (endpointDirection r) i * radianFourier (coordinateDerivative i h) r
  have hCoord (i : WardDerivativeAxes) :
      radianTrilinearWeight (wardComparableSymbol ϑ κ (wardComparableCoordinateProfile F i))
        (coordinateDerivative i.1 f) (coordinateDerivative i.2.1 g) (coordinateDerivative i.2.2 h) x =
        B * (f₁ i.1 * g₁ i.2.1 * h₁ i.2.2) := by
    simp only [radianTrilinearWeight, radianWeight, Complex.ofReal_one, one_mul, wardComparableCoordinateSymbol_eq]
    dsimp only [r, B, f₁, g₁, h₁, wardSignedThird]
    ring
  calc
    _ = B * (((‖x.1‖ : ℂ) * radianFourier f x.1) * ((‖x.2‖ : ℂ) * radianFourier g x.2) *
        ((‖r‖ : ℂ) * radianFourier h r)) := by
      simp only [radianTrilinearWeight, radianWeight, Complex.ofReal_one, one_mul, wardComparableRadialSymbol,
        Complex.ofReal_mul, r, B, wardSignedThird]
      ring
    _ = B * ((∑ i, f₁ i) * (∑ i, g₁ i) * (∑ i, h₁ i)) := by
      rw [ward_radialFourier_eq_sum_coordinateDerivative f x.1, ward_radialFourier_eq_sum_coordinateDerivative g x.2,
        ward_radialFourier_eq_sum_coordinateDerivative h r]
    _ = _ := by
      rw [sum_mul_three, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => (hCoord i).symm

/-- The actual comparable Fourier integral is absolutely integrable and
obeys the three gradient norms without any radial upper cutoff. -/
theorem exists_wardComparableRadialForm_bound (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) (F : Joint → ℂ)
    (hF : ContDiffOn ℝ ∞ F wardTriadDomain)
    (hHom : ∀ t : ℝ, 0 < t → ∀ x ∈ wardTriadDomain, F (t • x) = F x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g h : SchwartzMap E ℂ,
      Integrable (radianTrilinearWeight (wardComparableRadialSymbol ϑ κ F) f g h) ∧
      ‖radianTrilinearForm (wardComparableRadialSymbol ϑ κ F) f g h‖ ≤
        C * (wardCoordinateGradientL3 f * wardCoordinateGradientL3 g * wardCoordinateGradientL3 h) := by
  classical
  let G i := wardComparableCoordinateProfile F i
  let m i := wardComparableSymbol ϑ κ (G i)
  have hGh (i : WardDerivativeAxes) := wardComparableCoordinateProfile_hom F hHom i
  have hGs (i : WardDerivativeAxes) := wardComparableCoordinateProfile_smooth F hF i
  choose C hC hEst using fun i => exists_wardComparableForm_bound ϑ hϑ hCut hFlat κ hκ hSmall (G i) (hGs i) (hGh i)
  choose B _hB hBound using fun i => wardComparableSymbol_bounded ϑ hϑ hCut hFlat κ hκ hSmall (G i) (hGs i) (hGh i)
  have hm (i : WardDerivativeAxes) : Measurable (m i) := measurable_radianFourBranchSymbol ϑ hϑ.continuous.measurable κ _
    ((hGs i).continuousOn.measurable_piecewise continuousOn_const wardTriadDomain_open.measurableSet) 3
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro f g h
  let W := fun i => radianTrilinearWeight (m i) (coordinateDerivative i.1 f)
    (coordinateDerivative i.2.1 g) (coordinateDerivative i.2.2 h)
  let T := fun i => radianTrilinearForm (m i) (coordinateDerivative i.1 f)
    (coordinateDerivative i.2.1 g) (coordinateDerivative i.2.2 h)
  have hInt (i : WardDerivativeAxes) : Integrable (W i) :=
    integrable_radianTrilinearWeight_of_bounded (m i) (hm i).aestronglyMeasurable (B i) (hBound i) _ _ _
  have hWeight : radianTrilinearWeight (wardComparableRadialSymbol ϑ κ F) f g h = fun x => ∑ i, W i x :=
    funext (wardComparableRadialWeight_eq_coordinate_sum ϑ κ F f g h)
  refine ⟨hWeight.symm ▸ integrable_finset_sum Finset.univ (fun i _ => hInt i), ?_⟩
  have hForm : radianTrilinearForm (wardComparableRadialSymbol ϑ κ F) f g h = ∑ i, T i := by
    change (tau^8)⁻¹ • (∫ x, radianTrilinearWeight (wardComparableRadialSymbol ϑ κ F) f g h x) =
      ∑ i : WardDerivativeAxes, (tau^8)⁻¹ • (∫ x, W i x)
    rw [hWeight, ← Finset.smul_sum, ← integral_finset_sum Finset.univ (fun i _ => hInt i)]
  rw [hForm]
  have hTerm (u : SchwartzMap E ℂ) (j : Fin 4) :
      (eLpNorm (coordinateDerivative j u : E → ℂ) 3 volume).toReal ≤ wardCoordinateGradientL3 u := by
    unfold wardCoordinateGradientL3
    exact Finset.single_le_sum (f := fun i => (eLpNorm (coordinateDerivative i u : E → ℂ) 3 volume).toReal)
      (fun (_ : Fin 4) _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)
  have hNonneg (u : SchwartzMap E ℂ) : 0 ≤ wardCoordinateGradientL3 u :=
    Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
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
