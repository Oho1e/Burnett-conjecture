import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section

namespace Burnett.Analysis.CapFourier

open MeasureTheory
open Burnett.A02.FrequencySplit (radianFourier radianAction tau)
open scoped RealInnerProductSpace FourierTransform ENNReal

abbrev Space := Burnett.A02.FrequencySplit.E

def linearJacobian (A : Space ≃L[ℝ] Space) : ℝ := |A.toContinuousLinearMap.det|

theorem linearJacobian_pos (A : Space ≃L[ℝ] Space) : 0 < linearJacobian A :=
  abs_pos.mpr (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero

theorem linearJacobian_symm (A : Space ≃L[ℝ] Space) :
    linearJacobian A.symm = (linearJacobian A)⁻¹ := by
  change |LinearMap.det (A.toLinearEquiv.symm : Space →ₗ[ℝ] Space)| =
    |LinearMap.det (A.toLinearEquiv : Space →ₗ[ℝ] Space)|⁻¹
  rw [LinearEquiv.det_coe_symm,abs_inv]

theorem det_adjoint_eq (A : Space →L[ℝ] Space) : A.adjoint.det = A.det := by
  change LinearMap.det A.adjoint.toLinearMap = LinearMap.det A.toLinearMap
  let b : OrthonormalBasis (Fin 4) ℝ Space := EuclideanSpace.basisFun (Fin 4) ℝ
  have hh := LinearMap.toMatrix_adjoint b b A.toLinearMap
  change LinearMap.toMatrix b.toBasis b.toBasis A.adjoint.toLinearMap =
    (LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap).conjTranspose at hh
  rw [← LinearMap.det_toMatrix b.toBasis A.adjoint.toLinearMap,
    ← LinearMap.det_toMatrix b.toBasis A.toLinearMap,hh,Matrix.det_conjTranspose]
  simp

/-- For the linear frequency change `A`, the physical coordinate change
is the genuine real adjoint of `A`. -/
def physicalDualEquiv (A : Space ≃L[ℝ] Space) : Space ≃L[ℝ] Space :=
  A.toContinuousLinearMap.adjoint.toContinuousLinearEquivOfDetNeZero
    ((det_adjoint_eq A.toContinuousLinearMap).symm ▸ (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero)

theorem physicalDualEquiv_apply (A : Space ≃L[ℝ] Space) (x : Space) :
    physicalDualEquiv A x = A.toContinuousLinearMap.adjoint x := by
  simp [physicalDualEquiv]

theorem inner_physicalDualEquiv (A : Space ≃L[ℝ] Space) (ξ x : Space) :
    ⟪ξ,physicalDualEquiv A x⟫ = ⟪A ξ,x⟫ := by
  rw [physicalDualEquiv_apply]
  exact ContinuousLinearMap.adjoint_inner_right A.toContinuousLinearMap ξ x

theorem linearJacobian_physicalDualEquiv (A : Space ≃L[ℝ] Space) :
    linearJacobian (physicalDualEquiv A) = linearJacobian A := by
  unfold linearJacobian physicalDualEquiv
  simp only [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero,det_adjoint_eq]

theorem map_linear_volume (A : Space ≃L[ℝ] Space) :
    Measure.map A (volume : Measure Space) = ENNReal.ofReal ((linearJacobian A)⁻¹) • volume := by
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure Space)
    (f := A.toLinearEquiv.toLinearMap) (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero
  simpa only [linearJacobian,abs_inv] using h

theorem integral_comp_linearEquiv (A : Space ≃L[ℝ] Space) (f : Space → ℂ) :
    (∫ x, f (A x)) = (linearJacobian A)⁻¹ • (∫ x, f x) := by
  have h := A.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map (μ := (volume : Measure Space)) f
  change (∫ x, f x ∂Measure.map A volume) = (∫ x, f (A x)) at h
  rw [map_linear_volume,integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (linearJacobian_pos A).le)] at h
  exact h.symm

def pullbackSchwartz (A : Space ≃L[ℝ] Space) (f : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A f

@[simp] theorem pullbackSchwartz_apply (A : Space ≃L[ℝ] Space) (f : SchwartzMap Space ℂ) (x : Space) :
    pullbackSchwartz A f x = f (A x) := rfl

/-- Exact determinant and signed phase for the manuscript's radian Fourier
transform of the spatial pullback. -/
theorem radianFourier_comp_inverseDual (A : Space ≃L[ℝ] Space) (f : Space → ℂ) (ζ : Space) :
    radianFourier (f ∘ (physicalDualEquiv A).symm) ζ =
      linearJacobian A • radianFourier f (A ζ) := by
  let D := physicalDualEquiv A
  let g (x : Space) := Complex.exp ((- (inner ℝ x (A ζ) : ℝ) : ℂ)*Complex.I) * f x
  calc
    _ = ∫ y, g (D.symm y) := by
      unfold radianFourier
      apply integral_congr_ae
      filter_upwards with y
      have hp : inner ℝ y ζ = inner ℝ (D.symm y) (A ζ) := by
        calc
          _ = inner ℝ ζ y := real_inner_comm ζ y
          _ = inner ℝ ζ (D (D.symm y)) := by rw [D.apply_symm_apply]
          _ = inner ℝ (A ζ) (D.symm y) := inner_physicalDualEquiv A ζ (D.symm y)
          _ = _ := real_inner_comm _ _
      simp only [g,Function.comp_apply,hp,D]
    _ = _ := by
      rw [integral_comp_linearEquiv D.symm g,linearJacobian_symm,inv_inv]
      change linearJacobian (physicalDualEquiv A) • _ = _
      rw [linearJacobian_physicalDualEquiv]
      rfl

/-- The `(2π)^(-4)` radian inverse normalization is preserved. The real
Jacobian from the spatial pullback cancels the inverse frequency Jacobian. -/
theorem radianAction_linear_conjugation (A : Space ≃L[ℝ] Space) (b : Space → ℝ)
    (f : SchwartzMap Space ℂ) (x : Space) :
    radianAction (b ∘ A) (pullbackSchwartz (physicalDualEquiv A).symm f) (physicalDualEquiv A x) =
      radianAction b f x := by
  let D := physicalDualEquiv A
  let h (ξ : Space) := Complex.exp ((inner ℝ ξ x : ℂ)*Complex.I) * ((b ξ : ℂ)*radianFourier f ξ)
  have hi : (∫ ζ, Complex.exp ((inner ℝ ζ (D x) : ℂ)*Complex.I) *
      (((b ∘ A) ζ : ℂ)*radianFourier (pullbackSchwartz D.symm f) ζ)) =
      ∫ ζ, linearJacobian A • h (A ζ) := by
    apply integral_congr_ae
    filter_upwards with ζ
    have hF : radianFourier (pullbackSchwartz D.symm f) ζ =
        linearJacobian A • radianFourier f (A ζ) :=
      radianFourier_comp_inverseDual A f ζ
    rw [hF,show inner ℝ ζ (D x) = inner ℝ (A ζ) x from inner_physicalDualEquiv A ζ x]
    simp only [Function.comp_apply,h,mul_smul_comm]
  unfold radianAction
  rw [hi,integral_smul,integral_comp_linearEquiv A h,smul_smul (linearJacobian A) ((linearJacobian A)⁻¹),
    mul_inv_cancel₀ (linearJacobian_pos A).ne',one_smul]

end Burnett.Analysis.CapFourier
