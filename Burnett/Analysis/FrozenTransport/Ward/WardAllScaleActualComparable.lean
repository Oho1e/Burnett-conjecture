import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableBrackets
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableRadial
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualLowFields
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableFactors
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugePatch

set_option autoImplicit false
set_option maxRecDepth 6700
set_option maxHeartbeats 12500000
noncomputable section

namespace Burnett.C02

open Set MeasureTheory Burnett.A05 Burnett.A02.FrequencySplit Burnett.Analysis.CapFourier
open Burnett.RicciSymbol (Tensor2)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.C03 (projectedGaugeComplement)
open scoped ContDiff

open private wardComparableSymbol_eq wardExtendedTriadSymbol from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer
open private wardComparableDenominator from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableFactors
open private wardGradientPhaseProduct_bound from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualLowFields
open private ward_coordinate_gradient_bound from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugePatch

private theorem wardComparableCut_eq_sum_phases {ι : Type*} [Fintype ι] (ϑ : ℝ → ℝ) (κ : ℝ)
    (m : Tensor2) (A : Joint → ℂ) (F : ι → Joint → ℂ) (j : ι → Fin 3)
    (hA : ∀ x ∈ wardTriadDomain, A x = wardComparableDenominator x *
      ∑ s, F s x * (normalizedFrozenPhase m (wardPhaseCovector x (j s)) : ℂ)) (x : Joint) :
    wardComparableSymbol ϑ κ A x = ∑ s, wardComparableRadialSymbol ϑ κ (F s) x *
      (normalizedFrozenPhase m (wardPhaseCovector x (j s)) : ℂ) := by
  classical
  rw [wardComparableSymbol_eq]
  by_cases hx : x ∈ wardTriadDomain
  · have hS (B : Joint → ℂ) : wardExtendedTriadSymbol B x = B x := piecewise_eq_of_mem _ _ _ hx
    rw [hS, hA x hx]
    simp only [wardComparableRadialSymbol, wardComparableSymbol_eq, hS]
    rw [← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    let D : ℂ := ((‖x.1‖ * ‖x.2‖ * ‖wardSignedThird x‖ : ℝ) : ℂ)
    let W : ℂ := Burnett.Analysis.ProjectiveNullCaps.comparableSlotWeight ϑ κ x.1 x.2 (wardSignedThird x)
    let P : ℂ := normalizedFrozenPhase m (wardPhaseCovector x (j s))
    change W * D * (F s x * P) = W * F s x * D * P
    ring
  · have hS (B : Joint → ℂ) : wardExtendedTriadSymbol B x = 0 := piecewise_eq_of_notMem _ _ _ hx
    simp only [wardComparableRadialSymbol, wardComparableSymbol_eq, hS, mul_zero, zero_mul, Finset.sum_const_zero]

/-- Actual comparable integral in the common C02 phase-gradient bound. The
phase lies on its own thin field and the unchanged C03 gauge occupies its
original slot. This uses the exact comparable part of the four-branch sum. -/
theorem exists_wardActualComparableComponent_bound {ι : Type*} [Fintype ι]
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (hCut : ∀ t, 1 ≤ t → ϑ t = 0)
    (hFlat : ∀ t, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) (m : Tensor2)
    (A : Joint → ℂ) (F : ι → Joint → ℂ) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) wardTriadDomain)
    (hHom : ∀ i (t : ℝ), 0 < t → ∀ x ∈ wardTriadDomain, F i (t • x) = F i x)
    (j : ι → Fin 3) (physical : Fin 3 → Bool) (k : Fin 3 → OrderedPair) (hj : ∀ i, physical (j i) = true)
    (hA : ∀ x ∈ wardTriadDomain, A x = wardComparableDenominator x *
      ∑ s, F s x * (normalizedFrozenPhase m (wardPhaseCovector x (j s)) : ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ WardActualLowComponentBound m physical k (wardComparableSymbol ϑ κ A) C := by
  classical
  choose C hC hEst using fun i => exists_wardComparableRadialForm_bound ϑ hϑ hCut hFlat κ hκ hSmall (F i) (hF i) (hHom i)
  refine ⟨64 * ∑ i, C i, mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => hC i), ?_⟩
  intro wi wo hm η hη i o z V G P f
  let B s := wardComparableRadialSymbol ϑ κ (F s)
  let f' s := Function.update f (j s) (P (k (j s)))
  let W s := radianTrilinearWeight (B s) (f' s 0) (f' s 1) (f' s 2)
  let T s := radianTrilinearForm (B s) (f' s 0) (f' s 1) (f' s 2)
  have hg (s : ι) (ξ : E) : radianFourier (P (k (j s))) ξ =
      (normalizedFrozenPhase m ξ : ℂ) * radianFourier (f (j s)) ξ := by
    have he : f (j s) = V (k (j s)) := by simp [f, wardActualLowSlots, hj, V]
    rw [he]
    exact actualWardPhaseSchwartz_radianFourier m wi wo hm hη i o z (k (j s)) ξ
  have hInt (s : ι) : Integrable (W s) := (hEst s _ _ _).1
  have hW : radianTrilinearWeight (wardComparableSymbol ϑ κ A) (f 0) (f 1) (f 2) = fun x => ∑ s, W s x := by
    funext x
    have he (s : ι) : W s x =
        radianTrilinearWeight (fun y => B s y * (normalizedFrozenPhase m (wardPhaseCovector y (j s)) : ℂ))
          (f 0) (f 1) (f 2) x :=
      congrFun (wardRadianWeight_phase_transfer (B s) (fun ξ => (normalizedFrozenPhase m ξ : ℂ)) f (P (k (j s))) (j s)
        (hg s)).symm x
    change wardComparableSymbol ϑ κ A x * _ = _
    rw [wardComparableCut_eq_sum_phases ϑ κ m A F j hA x, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => (he s).symm
  refine ⟨hW.symm ▸ integrable_finset_sum Finset.univ (fun s _ => hInt s),?_⟩
  have hSum : radianTrilinearForm (wardComparableSymbol ϑ κ A) (f 0) (f 1) (f 2) = ∑ s, T s := by
    change (tau^8)⁻¹ • (∫ x, radianTrilinearWeight (wardComparableSymbol ϑ κ A) (f 0) (f 1) (f 2) x) =
      ∑ s : ι, (tau^8)⁻¹ • (∫ x, W s x)
    rw [hW, ← Finset.smul_sum, ← integral_finset_sum Finset.univ (fun s _ => hInt s)]
  rw [hSum]
  let a := euclideanFieldGradientL3 P
  let b := euclideanFieldGradientL3 G + euclideanFieldGradientL3 V
  have hn (u : OrderedPair → SchwartzMap E ℂ) : 0 ≤ euclideanFieldGradientL3 u := ENNReal.toReal_nonneg
  have hfn (s : Fin 3) : wardCoordinateGradientL3 (f s) ≤ 4 * b := by
    by_cases hs : physical s = true
    · have he : f s = V (k s) := by simp [f, wardActualLowSlots, hs, V]
      rw [he]
      exact (ward_coordinate_gradient_bound V (k s)).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hn G)) (by norm_num))
    · have he : f s = G (k s) := by simp [f, wardActualLowSlots, hs, G]
      rw [he]
      exact (ward_coordinate_gradient_bound G (k s)).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hn V)) (by norm_num))
  calc
    _ ≤ ∑ s, ‖T s‖ := norm_sum_le _ _
    _ ≤ ∑ s, C s * (64 * a * b^2) := by
      apply Finset.sum_le_sum
      intro s _
      exact (hEst s _ _ _).2.trans (mul_le_mul_of_nonneg_left (wardGradientPhaseProduct_bound f (P (k (j s)))
        (j s) a b (hn P) (add_nonneg (hn G) (hn V)) (ward_coordinate_gradient_bound P _) hfn) (hC s))
    _ = _ := by rw [← Finset.sum_mul]; unfold a b; ring

theorem exists_wardActualComparableGaugeComponent_bounds (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16)
    (m : Tensor2) (w : ℝ) (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ) (k : Fin 3 → OrderedPair) :
    let H₀ := wardTensorBasis (k 0)
    let H₁ := wardTensorBasis (k 1)
    let H₂ := wardTensorBasis (k 2)
    (∃ C : ℝ, 0 ≤ C ∧ WardActualLowComponentBound m ![true,true,false] k
      (wardComparableSymbol ϑ κ (wardOneHighGaugeRaw m w a H₂ H₀ H₁)) C) ∧
    (∃ C : ℝ, 0 ≤ C ∧ WardActualLowComponentBound m ![true,false,false] k
      (wardComparableSymbol ϑ κ (wardTwoGaugePhysicalLowRaw m w a H₁ H₂ H₀)) C) := by
  intro H₀ H₁ H₂
  have hOne j := wardComparableOneGaugeProfiles_smooth_hom m w a H₂ H₀ H₁ ha hHom j
  have hTwo := wardComparableTwoGaugeProfile_smooth_hom m w a H₁ H₂ H₀ ha hHom
  constructor
  · exact exists_wardActualComparableComponent_bound ϑ hϑ hCut hFlat κ hκ hSmall m _
      (wardComparableOneGaugeProfiles m w a H₂ H₀ H₁) (fun j => (hOne j).1) (fun j => (hOne j).2)
      ![0,1] ![true,true,false] k (by intro j; fin_cases j <;> rfl)
      (wardComparableOneGaugeRaw_normalized m w a H₂ H₀ H₁)
  · refine exists_wardActualComparableComponent_bound (ι := Fin 1) ϑ hϑ hCut hFlat κ hκ hSmall m _
      (fun _ => wardComparableTwoGaugeProfile m w a H₁ H₂ H₀) (fun _ => hTwo.1) (fun _ => hTwo.2)
      (fun _ => 0) ![true,false,false] k (fun _ => rfl) ?_
    intro x hx
    simpa only [Fin.sum_univ_one, wardPhaseCovector, Matrix.cons_val_zero] using
      wardComparableTwoGaugeRaw_normalized m w a H₁ H₂ H₀ x hx

end Burnett.C02
