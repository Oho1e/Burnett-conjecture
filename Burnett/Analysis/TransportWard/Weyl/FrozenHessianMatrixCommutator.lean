import Burnett.Analysis.TransportWard.Weyl.FrozenScalarCommutator
import Burnett.Analysis.FrozenTransport.V03MetricActionCoefficient
import Burnett.Analysis.TransportWard.Weyl.WindowedWeylFullSymbol
import Burnett.Analysis.PrincipalEnergy.Energy.CompactActualFourier
import Burnett.Analysis.PrincipalEnergy.Localization.GlobalFiniteMatrixCoefficient

/-! The actual frozen differential principal field with the same scalar
Weyl test on each Hessian row and column. -/

set_option autoImplicit false
set_option maxHeartbeats 6200000
set_option maxRecDepth 4500

noncomputable section

namespace Burnett.V03.Palatini

open Function MeasureTheory Filter Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.CarlesonEmbedding Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped BigOperators ComplexConjugate ContDiff

open private actualFirstOrderAction_smul from Burnett.Analysis.PrincipalEnergy.Energy.CompactActualFourier

local notation "D" => frozenSchwartzCoordinatePartial
local notation "J" => Fin 4 × Fin 4

/-- The second-order part of the actual coordinate density Euler
linearization, with the background matrix frozen at `G`. -/
def frozenDensityPrincipalSchwartzField {ι : Type*} [Fintype ι] (S : ι → Mat) (G : Mat)
    (u : ι → SchwartzMap E ℂ) (i : ι) : SchwartzMap E ℂ :=
  ∑ d : J, ∑ j, (-(metricActionCoefficient S (d.1,i) (d.2,j) G : ℂ)) • D d.1 (D d.2 (u j))

/-- The frozen principal Euler expression on the actual smooth output
of the same scalar Fourier test. -/
def frozenDensityPrincipalField {ι : Type*} [Fintype ι] (S : ι → Mat) (G : Mat)
    (u : ι → E → ℂ) (i : ι) (x : E) : ℂ :=
  ∑ d : J, ∑ j, (-(metricActionCoefficient S (d.1,i) (d.2,j) G : ℂ)) *
    physicalCoordinatePartial d.1 (physicalCoordinatePartial d.2 (u j)) x

theorem frozenDensityPrincipalSchwartzField_apply {ι : Type*} [Fintype ι] (S : ι → Mat) (G : Mat)
    (u : ι → SchwartzMap E ℂ) (i : ι) (x : E) :
    frozenDensityPrincipalSchwartzField S G u i x =
      frozenDensityPrincipalField S G (fun j => (u j : E → ℂ)) i x := by
  change (SchwartzMap.delta ℂ ℂ x) (frozenDensityPrincipalSchwartzField S G u i) = _
  simp only [frozenDensityPrincipalSchwartzField, frozenDensityPrincipalField, map_sum, map_smul,
    smul_eq_mul, SchwartzMap.delta_apply]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro j _
  simp only [frozenSchwartzCoordinatePartial, SchwartzMap.pderivCLM_apply, physicalCoordinatePartial]
  rfl

/-- The literal frozen scalar/matrix commutator, with the paper's sign `i[L,B]`. -/
def frozenDensityWeylCommutator {ι : Type*} [Fintype ι] (S : ι → Mat) (G : Mat)
    (a : E → E → ℂ) (u : ι → SchwartzMap E ℂ) (i : ι) (x : E) : ℂ :=
  Complex.I * (frozenDensityPrincipalField S G (fun j => firstOrderAction a (u j)) i x -
    firstOrderAction a (frozenDensityPrincipalSchwartzField S G u i) x)

theorem frozenDensityWeylCommutator_eq_leftActions {ι : Type*} [Fintype ι]
    (S : ι → Mat) (G : Mat) {a : E → E → ℂ} (h : ScaledJointOrderOne a)
    (u : ι → SchwartzMap E ℂ) (i : ι) (x : E) :
    frozenDensityWeylCommutator S G a u i x =
      ∑ d : J, ∑ j, (metricActionCoefficient S (d.1,i) (d.2,j) G : ℂ) *
        firstOrderAction (frozenSecondCommutatorSymbol a d.1 d.2) (u j) x := by
  let ha := h.firstBaseFrequency.frequency
  simp only [frozenDensityWeylCommutator, frozenDensityPrincipalField, frozenDensityPrincipalSchwartzField,
    firstOrderAction_finset_sum ha, actualFirstOrderAction_smul ha, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro j _
  rw [← frozenSecondCommutator_eq_leftAction h d.1 d.2 (u j) x]
  ring

/-- The concrete double-cutoff Weyl test from the native A03–A01 replay.
Here the only frozen object is the matrix in the Hessian coefficient. -/
theorem frozenDensityCompactWeylCommutator_eq_leftActions
    {ι : Type*} [Fintype ι] (S : ι → Mat) (G : Mat) (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1) (hβ : ScaledJointOrderOne (normalizedWeylSymbol β))
    (u : ι → SchwartzMap E ℂ) (i : ι) (x : E) :
    let a := windowedWeylLeftSymbol θ β R h
    frozenDensityWeylCommutator S G a u i x =
      ∑ d : J, ∑ j, (metricActionCoefficient S (d.1,i) (d.2,j) G : ℂ) *
        firstOrderAction (frozenSecondCommutatorSymbol a d.1 d.2) (u j) x := by
  intro a
  exact frozenDensityWeylCommutator_eq_leftActions S G
    (windowedWeyl_leftSymbol_scaled_order_one θ β R h hAmp hPlateau hβ) u i x

end Burnett.V03.Palatini
