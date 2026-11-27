import Burnett.Analysis.PrincipalEnergy.Freezing.RadianSkewDifferentiation
import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianActionLinearity
import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedSpatialSkew

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.RicciSymbol
open scoped ContDiff

/-- The coordinate commutator of the actual separated skew test. Only the
spatial profile is differentiated in the remaining separated action. -/
theorem separated_skew_coordinate_commutator (f : SchwartzMap E ℂ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (u : SchwartzMap E ℂ) (x : E) (j : Index) :
    DifferentiableAt ℝ (separatedSkewAction f b u) x ∧
      fderiv ℝ (separatedSkewAction f b u) x (EuclideanSpace.single j 1) -
          separatedSkewAction f b (energyPartial j u) x =
        separatedSkewAction (energyPartial j f) b u x := by
  obtain ⟨hU, hUCoord⟩ := radian_skew_coordinate_derivative b hb hom u x
  obtain ⟨hProd, hProdCoord⟩ := radian_skew_coordinate_derivative b hb hom (energyProduct f u) x
  have hD := (((f.differentiable x).hasFDerivAt.mul hU.hasFDerivAt).add
    hProd.hasFDerivAt).mul_const (2 : ℂ)⁻¹
  have form : separatedSkewAction f b u = fun y =>
      ((f : E → ℂ) * radianSkewAction b u + radianSkewAction b (energyProduct f u)) y * (2 : ℂ)⁻¹ := by
    funext y
    simp only [separatedSkewAction, Pi.add_apply, Pi.mul_apply, div_eq_mul_inv]
  have product : energyPartial j (energyProduct f u) =
      energyProduct (energyPartial j f) u + energyProduct f (energyPartial j u) := by
    ext y
    simp only [energyPartial_product, SchwartzMap.add_apply, energyProduct_apply]
  constructor
  · rw [form]
    exact hD.differentiableAt
  rw [form, hD.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    hUCoord, hProdCoord]
  change (2 : ℂ)⁻¹ * (f x * radianSkewAction b (energyPartial j u) x +
    radianSkewAction b u x * energyPartial j f x +
    radianSkewAction b (energyPartial j (energyProduct f u)) x) -
    separatedSkewAction f b (energyPartial j u) x =
    separatedSkewAction (energyPartial j f) b u x
  rw [product]
  unfold separatedSkewAction radianSkewAction
  rw [radian_action_add b hb hom]
  simp only [Pi.add_apply]
  ring

end Burnett.A02.FrequencySplit
