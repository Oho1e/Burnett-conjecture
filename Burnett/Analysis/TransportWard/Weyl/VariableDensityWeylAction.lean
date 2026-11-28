import Burnett.Analysis.TransportWard.Weyl.CoefficientCommutatorTaylor
import Burnett.Analysis.TransportWard.Weyl.RadianWeylDerivative
import Burnett.Analysis.TransportWard.Weyl.FrozenHessianMatrixCommutator

/-! Exact pointwise variable-coefficient commutator of the genuine finite
differential principal field and the same compact scalar Weyl test. -/

set_option autoImplicit false
set_option maxHeartbeats 6900000
set_option maxRecDepth 4700

noncomputable section

namespace Burnett.V03.Palatini

open Function Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic Burnett.Analysis.CarlesonEmbedding
open scoped BigOperators ContDiff

open private actualFirstOrderAction_smul from Burnett.Analysis.PrincipalEnergy.Energy.CompactActualFourier

local notation "J" => Fin 4 × Fin 4
local notation "D" => frozenSchwartzCoordinatePartial

/-- A matrix of real density coefficients is complexified component by
component on the same coordinate Schwartz domain. -/
def variableDensityPrincipalSchwartzField {ι : Type*} [Fintype ι]
    (c : ι → ι → J → SchwartzMap E ℂ) (u : ι → SchwartzMap E ℂ) (i : ι) : SchwartzMap E ℂ :=
  ∑ d : J, ∑ j, (-1 : ℂ) • scalarSchwartzProduct (c i j d) (D d.1 (D d.2 (u j)))

/-- The genuine variable principal expression, acting on smooth output of
the actual Fourier operator. -/
def variableDensityPrincipalField {ι : Type*} [Fintype ι]
    (c : ι → ι → J → SchwartzMap E ℂ) (u : ι → E → ℂ) (i : ι) (x : E) : ℂ :=
  ∑ d : J, ∑ j, -(c i j d x) * physicalCoordinatePartial d.1 (physicalCoordinatePartial d.2 (u j)) x

theorem variableDensityPrincipalSchwartzField_apply {ι : Type*} [Fintype ι]
    (c : ι → ι → J → SchwartzMap E ℂ) (u : ι → SchwartzMap E ℂ) (i : ι) (x : E) :
    variableDensityPrincipalSchwartzField c u i x =
      variableDensityPrincipalField c (fun j => (u j : E → ℂ)) i x := by
  change SchwartzMap.delta ℂ ℂ x (variableDensityPrincipalSchwartzField c u i) = _
  simp only [variableDensityPrincipalSchwartzField, variableDensityPrincipalField, map_sum, map_smul,
    SchwartzMap.delta_apply, scalarSchwartzProduct_apply, frozenSchwartzCoordinatePartial,
    SchwartzMap.pderivCLM_apply, physicalCoordinatePartial, smul_eq_mul, neg_mul, one_mul]
  rfl

/-- The literal operator commutator with the sign convention in the
variational pairing. -/
def variableDensityWeylCommutator {ι : Type*} [Fintype ι]
    (c : ι → ι → J → SchwartzMap E ℂ) (a : E → E → ℂ)
    (u : ι → SchwartzMap E ℂ) (i : ι) (x : E) : ℂ :=
  Complex.I * (variableDensityPrincipalField c (fun j => firstOrderAction a (u j)) i x -
    firstOrderAction a (variableDensityPrincipalSchwartzField c u i) x)

/-- The exact second-jet contribution of the input-side multiplication
commutator. The two radian coordinates come from that same input. -/
def variableCoefficientSecondSymbol (a : E → E → ℂ) (c : SchwartzMap E ℂ)
    (d : J) (x ξ : E) : ℂ :=
  -((physicalRadianCovector ξ d.1 : ℂ) * (physicalRadianCovector ξ d.2 : ℂ)) *
    coefficientCommutatorSymbol a c x ξ

theorem variableDensityWeylCommutator_eq_exact_leftActions {ι : Type*} [Fintype ι]
    (c : ι → ι → J → SchwartzMap E ℂ) {a : E → E → ℂ} (ha : ScaledJointOrderOne a)
    (u : ι → SchwartzMap E ℂ) (i : ι) (x : E) :
    variableDensityWeylCommutator c a u i x =
      ∑ d : J, ∑ j, (
        c i j d x * firstOrderAction (frozenSecondCommutatorSymbol a d.1 d.2) (u j) x +
          firstOrderAction (variableCoefficientSecondSymbol a (c i j d) d) (u j) x) := by
  let hf := ha.firstBaseFrequency.frequency
  simp only [variableDensityWeylCommutator, variableDensityPrincipalField, variableDensityPrincipalSchwartzField,
    firstOrderAction_finset_sum hf, actualFirstOrderAction_smul hf, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [← frozenSecondCommutator_eq_leftAction ha d.1 d.2 (u j) x]
  unfold variableCoefficientSecondSymbol
  rw [← firstOrderAction_input_secondCoordinateDerivative (coefficientCommutatorSymbol a (c i j d)) d.1 d.2,
    firstOrderAction_coefficientCommutatorSymbol hf]
  ring

/-- Specialization to the same genuine two-window Weyl action, after the
already proved exact left reduction. -/
theorem variableDensityCompactWeylCommutator_eq_exact_leftActions {ι : Type*} [Fintype ι]
    (c : ι → ι → J → SchwartzMap E ℂ) (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1) (hβ : ScaledJointOrderOne (normalizedWeylSymbol β))
    (u : ι → SchwartzMap E ℂ) (i : ι) (x : E) :
    let a := windowedWeylLeftSymbol θ β R h
    variableDensityWeylCommutator c a u i x =
      ∑ d : J, ∑ j, (
        c i j d x * firstOrderAction (frozenSecondCommutatorSymbol a d.1 d.2) (u j) x +
          firstOrderAction (variableCoefficientSecondSymbol a (c i j d) d) (u j) x) := by
  intro a
  exact variableDensityWeylCommutator_eq_exact_leftActions c
    (windowedWeyl_leftSymbol_scaled_order_one θ β R h hAmp hPlateau hβ) u i x

end Burnett.V03.Palatini
