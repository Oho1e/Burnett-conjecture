import Burnett.Analysis.PrincipalEnergy.Freezing.CubicEnergyLpContinuity
import Burnett.Analysis.PrincipalEnergy.Freezing.LeftRemainderCompatibility

set_option autoImplicit false
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.A03

open MeasureTheory Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal BigOperators Burnett.A03

open private patchValueComponent patchDerivativeComponent from Burnett.Analysis.PrincipalEnergy.Freezing.CubicEnergyLpContinuity

/-- A differentiable physical output with the indicated finite L³ jets
represents exactly its distributional coordinate derivative. -/
theorem classical_patchLpJet_is_weak_derivative
    (u : E → ℂ) (hDiff : Differentiable ℝ u)
    (hV : MemLp u (ENNReal.ofReal 3) volume) (a : Index)
    (hD : MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single a 1)) (ENNReal.ofReal 3) volume) :
    HasWeakCoordinateDerivative3 (hV.toLp u)
      (hD.toLp (fun x => fderiv ℝ u x (EuclideanSpace.single a 1))) a := by
  intro φ
  let p := ENNReal.ofReal (3 / 2)
  have hLeft := (energy_integral_three_three_halves hV ((energyPartial a φ).memLp p volume)).1
  have hRight := (energy_integral_three_three_halves hD (φ.memLp p volume)).1
  have hProd := (energy_integral_three_three_halves hV (φ.memLp p volume)).1
  rw [patch_lp_pair_toLp, patch_lp_pair_toLp]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := u) (g := (φ : E → ℂ)) (v := EuclideanSpace.single a 1) hRight hLeft hProd hDiff φ.differentiable

/-- For the actual three placements, two weak jets with the same physical
test value have exactly the same principal cubic energy. -/
theorem principal_cubic_Lp_functional_eq_of_same_weak_value {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (U V : PatchFieldLpJet J) (hValue : U.1 = V.1)
    (hU : ∀ p : Index × J, HasWeakCoordinateDerivative3 (U.1 p.2) (U.2 p) p.1)
    (hV : ∀ p : Index × J, HasWeakCoordinateDerivative3 (V.1 p.2) (V.2 p) p.1) :
    principalCubicLpFunctional C z U = principalCubicLpFunctional C z V := by
  have hDeriv (p : Index × J) (φ : SchwartzMap E ℂ) : patchLpPair φ (U.2 p) = patchLpPair φ (V.2 p) := by
    have h := hU p φ
    rw [hValue, hV p φ] at h
    exact neg_injective h.symm
  simp only [principalCubicLpFunctional, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, patchValueComponent, patchDerivativeComponent,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.proj_apply, hValue, hDeriv]

/-- The decomposed real test action uses one physical input and its genuine
derivative. The Fourier symmetrization and Weyl comparison remainders enter
with their algebraic signs before taking any norms. -/
theorem principal_cubic_freezing_eq_mode_sub_remainder_add_remainder {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (w : J → E → ℂ) (hJet : ∀ i, BoundedCoordinateJet (w i))
    (hDiff : ∀ i, Differentiable ℝ (w i))
    (hW : ∀ i, MemLp (w i) (ENNReal.ofReal 3) volume)
    (hDW : ∀ p : Index × J,
      MemLp (fun x => fderiv ℝ (w p.2) x (EuclideanSpace.single p.1 1)) (ENNReal.ofReal 3) volume)
    (mode symmResidual testResidual : PatchFieldLpJet J)
    (hMode : ∀ p : Index × J, HasWeakCoordinateDerivative3 (mode.1 p.2) (mode.2 p) p.1)
    (hSymm : ∀ p : Index × J, HasWeakCoordinateDerivative3 (symmResidual.1 p.2) (symmResidual.2 p) p.1)
    (hTest : ∀ p : Index × J, HasWeakCoordinateDerivative3 (testResidual.1 p.2) (testResidual.2 p) p.1)
    (hValue : ∀ i : J, (mode.1 i - symmResidual.1 i + testResidual.1 i : PatchLp3) =
      (hW i).toLp (w i)) :
    principalPatchTestEnergy C z w = principalCubicLpFunctional C z mode -
      principalCubicLpFunctional C z symmResidual + principalCubicLpFunctional C z testResidual := by
  let U : PatchFieldLpJet J := (fun i => (hW i).toLp _, fun p => (hDW p).toLp _)
  let V := mode - symmResidual + testResidual
  have hU (p : Index × J) : HasWeakCoordinateDerivative3 (U.1 p.2) (U.2 p) p.1 :=
    classical_patchLpJet_is_weak_derivative _ (hDiff p.2) (hW p.2) p.1 (hDW p)
  have hV (p : Index × J) : HasWeakCoordinateDerivative3 (V.1 p.2) (V.2 p) p.1 := by
    have hSub := left_weak_coordinate_of_symmetrization_remainder _ _ _ _ p.1 (hMode p) (hSymm p)
    intro φ
    change patchLpPair (energyPartial p.1 φ) ((mode.1 p.2 - symmResidual.1 p.2) + testResidual.1 p.2) =
      -patchLpPair φ ((mode.2 p - symmResidual.2 p) + testResidual.2 p)
    rw [map_add, map_add, hSub φ, hTest p φ]
    abel
  have hEq : U.1 = V.1 := funext fun i => (hValue i).symm
  calc
    _ = principalCubicLpFunctional C z U := (principal_cubic_Lp_functional_eq_action C z w hJet hW hDW).symm
    _ = principalCubicLpFunctional C z V := principal_cubic_Lp_functional_eq_of_same_weak_value C z U V hEq hU hV
    _ = _ := by simp only [V, map_add, map_sub]

end Burnett.A03
