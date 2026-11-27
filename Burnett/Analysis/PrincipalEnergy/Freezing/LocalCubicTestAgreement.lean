import Burnett.Analysis.PrincipalEnergy.Freezing.OriginalCubicFreezing

set_option autoImplicit false
set_option maxHeartbeats 6900000

noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped Topology

open private lowerValueTest lowerDerivativeTest from Burnett.Analysis.PrincipalEnergy.Freezing.GeneralLowerCubicAction

private theorem weightedCubicIntegral_of_local_test (c u v w w' : SchwartzMap E ℂ) {U : Set E}
    (hZero : ∀ x ∉ U, u x = 0) (hEq : EqOn (fun x => w x) (fun x => w' x) U) :
    weightedCubicIntegral c w u v = weightedCubicIntegral c w' u v ∧
    weightedCubicIntegral c u w v = weightedCubicIntegral c u w' v ∧
    weightedCubicIntegral c u v w = weightedCubicIntegral c u v w' := by
  refine ⟨?_,?_,?_⟩
  all_goals
    unfold weightedCubicIntegral
    apply integral_congr_ae
    apply ae_of_all
    intro x
    by_cases hx : x ∈ U
    · simp only [hEq hx]
    · simp only [hZero x hx, mul_zero, zero_mul]

/-- The complete cubic variation depends only on the germ of the test
output along the support of the original field, in all three placements. -/
theorem realCompleteCubicTest_eq_of_local_test_agreement {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℝ)
    (C₀ : J × J × J → SchwartzMap E ℂ) (C₁ : Index × J × J × J → SchwartzMap E ℂ)
    (z w w' : J → SchwartzMap E ℂ) {U : Set E} (hU : IsOpen U)
    (hSupport : ∀ i, tsupport (z i : E → ℂ) ⊆ U)
    (hEq : ∀ i, EqOn (fun x => w i x) (fun x => w' i x) U) :
    realCompleteCubicTest C C₀ C₁ z w = realCompleteCubicTest C C₀ C₁ z w' := by
  have zeroOutside (i : J) (x : E) (hx : x ∉ U) : z i x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => hx (hSupport i hs))
  have derivativeZero (i : J) (a : Index) (x : E) (hx : x ∉ U) : energyPartial a (z i) x = 0 := by
    change fderiv ℝ (z i : E → ℂ) x (EuclideanSpace.single a 1) = 0
    rw [fderiv_of_notMem_tsupport ℝ (fun hs => hx (hSupport i hs)), ContinuousLinearMap.zero_apply]
  have derivativeEq (i : J) (x : E) (hx : x ∈ U) :
      fderiv ℝ (w i : E → ℂ) x = fderiv ℝ (w' i : E → ℂ) x := by
    have equalNear : (w i : E → ℂ) =ᶠ[𝓝 x] (w' i : E → ℂ) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hEq i hy
    exact equalNear.fderiv_eq
  have partialEq (i : J) (a : Index) : EqOn (fun x => energyPartial a (w i) x)
      (fun x => energyPartial a (w' i) x) U := by
    intro x hx
    change fderiv ℝ (w i : E → ℂ) x (EuclideanSpace.single a 1) =
      fderiv ℝ (w' i : E → ℂ) x (EuclideanSpace.single a 1)
    rw [derivativeEq i x hx]
  have principal : realPrincipalVariation C z (fun i => w i) = realPrincipalVariation C z (fun i => w' i) := by
    unfold realPrincipalVariation
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ U
    · simp only [principalVariationDensity, fun i => hEq i hx, fun i => derivativeEq i x hx]
    · simp only [principalVariationDensity, fun i => zeroOutside i x hx, fun i a => derivativeZero i a x hx,
        mul_zero, zero_mul, add_zero, Finset.sum_const_zero]
  have lower : realLowerCubicVariation C₀ C₁ z w = realLowerCubicVariation C₀ C₁ z w' := by
    unfold realLowerCubicVariation
    apply congrArg Complex.re
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i _
      have e₁ := (weightedCubicIntegral_of_local_test (C₀ i) (z i.2.1) (z i.2.2)
        (w i.1) (w' i.1) (zeroOutside i.2.1) (hEq i.1)).1
      have e₂ := (weightedCubicIntegral_of_local_test (C₀ i) (z i.1) (z i.2.2)
        (w i.2.1) (w' i.2.1) (zeroOutside i.1) (hEq i.2.1)).2.1
      have e₃ := (weightedCubicIntegral_of_local_test (C₀ i) (z i.1) (z i.2.1)
        (w i.2.2) (w' i.2.2) (zeroOutside i.1) (hEq i.2.2)).2.2
      simp only [lowerValueTest,e₁,e₂,e₃]
    · apply Finset.sum_congr rfl
      intro i _
      have e₁ := (weightedCubicIntegral_of_local_test (C₁ i) (z i.2.2.1) (energyPartial i.1 (z i.2.2.2))
        (w i.2.1) (w' i.2.1) (zeroOutside i.2.2.1) (hEq i.2.1)).1
      have e₂ := (weightedCubicIntegral_of_local_test (C₁ i) (z i.2.1) (energyPartial i.1 (z i.2.2.2))
        (w i.2.2.1) (w' i.2.2.1) (zeroOutside i.2.1) (hEq i.2.2.1)).2.1
      have e₃ := (weightedCubicIntegral_of_local_test (C₁ i) (z i.2.1) (z i.2.2.1)
        (energyPartial i.1 (w i.2.2.2)) (energyPartial i.1 (w' i.2.2.2))
        (zeroOutside i.2.1) (partialEq i.2.2.2 i.1)).2.2
      simp only [lowerDerivativeTest,lowerValueTest,e₁,e₂,e₃]
  simp only [realCompleteCubicTest,principal,lower]

end Burnett.A03
