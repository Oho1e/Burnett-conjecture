import Burnett.Analysis.PrincipalEnergy.Energy.SchwartzLeibniz

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.Analysis.SymmetricEnergy

open MeasureTheory
open scoped BigOperators InnerProductSpace SchwartzMap ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

def coordinateDirection (a : Fin 4) : Space := EuclideanSpace.single a 1

def coordinatePartial (a : Fin 4) : Op (SchwartzTest F) :=
  schwartzDerivative (coordinateDirection a)

def coordinateH1 (f : 𝓢(Space, F)) : ℝ :=
  Real.sqrt (‖f.toLp 2 volume‖ ^ 2 +
    ∑ a : Fin 4, ‖(SchwartzMap.pderivCLM ℂ (coordinateDirection a) f).toLp 2 volume‖ ^ 2)

theorem firstOrderEnergy_eq_coordinateH1 (f : 𝓢(Space, F)) :
    firstOrderEnergy coordinatePartial (schwartzTestEquiv f) = coordinateH1 f := by
  unfold firstOrderEnergy coordinateH1
  simp only [coordinatePartial, schwartzDerivative, transportSchwartzOp_on_equiv,
    ContinuousLinearMap.coe_coe]
  rfl

def schwartzCoordinatePrincipal (r : Fin 4 → Fin 4 → 𝓢(Space, F →L[ℂ] F))
    (f : 𝓢(Space, F)) : 𝓢(Space, F) :=
  ∑ a, ∑ b, schwartzMultiplication (r a b)
    (SchwartzMap.pderivCLM ℂ (coordinateDirection a) (SchwartzMap.pderivCLM ℂ (coordinateDirection b) f))

theorem schwartzCoordinatePrincipal_apply (r : Fin 4 → Fin 4 → 𝓢(Space, F →L[ℂ] F))
    (f : 𝓢(Space, F)) (x : Space) :
    schwartzCoordinatePrincipal r f x = ∑ a, ∑ b,
      r a b x (fderiv ℝ (fun y => fderiv ℝ (⇑f) y (coordinateDirection b)) x (coordinateDirection a)) := by
  change SchwartzMap.delta ℂ F x (schwartzCoordinatePrincipal r f) = _
  simp only [schwartzCoordinatePrincipal, map_sum, SchwartzMap.delta_apply,
    schwartzMultiplication_apply, SchwartzMap.pderivCLM_apply]
  rfl

theorem coordinate_principal_energy_bound (r : Fin 4 → Fin 4 → 𝓢(Space, F →L[ℂ] F))
    (f : 𝓢(Space, F)) (B : 𝓢(Space, F) →ₗ[ℂ] 𝓢(Space, F))
    (hB : (transportSchwartzOp B).IsSymmetric)
    (hR : ∀ a b x u v, ⟪r a b x u, v⟫_ℂ = ⟪u, r b a x v⟫_ℂ)
    (A K : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hr : ∀ a b x, ‖r a b x‖ ≤ A)
    (hdR : ∀ a b x, ‖fderiv ℝ (⇑(r a b)) x (coordinateDirection a)‖ ≤ A)
    (hlip : ∀ a b v, ‖comm (schwartzCoefficient (r a b)) (transportSchwartzOp B) v‖ ≤ K * A * ‖v‖)
    (hDB : ∀ a, ‖comm (coordinatePartial a) (transportSchwartzOp B) (schwartzTestEquiv f)‖ ≤ K * coordinateH1 f)
    (hBu : ‖(B f).toLp 2 volume‖ ≤ K * coordinateH1 f) :
    |2 * (∫ x, ⟪B f x, schwartzCoordinatePrincipal r f x⟫_ℂ).im| ≤ 80 * K * A * coordinateH1 f ^ 2 := by
  let D (i : Fin 4) : Op (SchwartzTest F) := coordinatePartial i
  let R (a b : Fin 4) : Op (SchwartzTest F) := schwartzCoefficient (r a b)
  let dR (a b : Fin 4) : Op (SchwartzTest F) :=
    schwartzCoefficient (SchwartzMap.pderivCLM ℂ (coordinateDirection a) (r a b))
  let u := schwartzTestEquiv f
  have hD (a : Fin 4) : IsSkew (D a) := schwartz_derivative_isSkew (coordinateDirection a)
  have hsym (a b : Fin 4) (v w : SchwartzTest F) : ⟪R a b v, w⟫_ℂ = ⟪v, R b a w⟫_ℂ :=
    schwartz_coefficient_adjoint (r a b) (r b a) (hR a b) v w
  have hLeibniz (a b : Fin 4) : D a * R a b = R a b * D a + dR a b :=
    schwartz_coefficient_leibniz (coordinateDirection a) (r a b)
  have hm (a b : Fin 4) (v : SchwartzTest F) : ‖R a b v‖ ≤ A * ‖v‖ :=
    schwartz_coefficient_norm_bound (r a b) A hA (hr a b) v
  have hdm (a b : Fin 4) (v : SchwartzTest F) : ‖dR a b v‖ ≤ A * ‖v‖ :=
    schwartz_coefficient_norm_bound _ A hA
      (fun x => by simpa only [SchwartzMap.pderivCLM_apply] using hdR a b x) v
  have hE : firstOrderEnergy D u = coordinateH1 f := firstOrderEnergy_eq_coordinateH1 f
  have hdb (a : Fin 4) : ‖comm (D a) (transportSchwartzOp B) u‖ ≤ K * firstOrderEnergy D u := by
    rw [hE]
    exact hDB a
  have hBnorm : ‖transportSchwartzOp B u‖ ≤ K * firstOrderEnergy D u := by
    rw [hE]
    change ‖transportSchwartzOp B (schwartzTestEquiv f)‖ ≤ _
    rw [transportSchwartzOp_on_equiv]
    exact hBu
  have hP : principal D R u = schwartzTestEquiv (schwartzCoordinatePrincipal r f) := by
    simp only [principal, D, R, u, schwartzCoordinatePrincipal, coordinatePartial,
      schwartzDerivative, schwartzCoefficient, LinearMap.sum_apply, Module.End.mul_apply,
      transportSchwartzOp_on_equiv, ContinuousLinearMap.coe_coe, map_sum]
  have hpair : ⟪transportSchwartzOp B u, principal D R u⟫_ℂ =
      ∫ x, ⟪B f x, schwartzCoordinatePrincipal r f x⟫_ℂ := by
    rw [hP]
    change ⟪transportSchwartzOp B (schwartzTestEquiv f), _⟫_ℂ = _
    rw [transportSchwartzOp_on_equiv, schwartzTestEquiv_inner]
  have h := principal_energy_bound D R dR (transportSchwartzOp B) hD hB hsym hLeibniz u A K
    hA hK hm hdm hlip hdb hBnorm
  have hCard : (Fintype.card (Fin 4) : ℝ) = 4 := by simp
  have hScale : 5 * (4 : ℝ) ^ 2 = 80 := by norm_num
  simpa only [hE, hpair, hCard, hScale] using h

end Burnett.Analysis.SymmetricEnergy
