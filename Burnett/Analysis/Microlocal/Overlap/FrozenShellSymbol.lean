import Burnett.Analysis.Microlocal.Overlap.HalfDensityKernelTransport
import Burnett.Analysis.AngularCaps.LinearFourierChange

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Burnett.Microlocal.OverlapKernel

open MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.CapFourier
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel Burnett.Microlocal.OverlapGradient
open scoped ContDiff FourierTransform Manifold

/-- The spatial kernel of a pulled-back inverse Fourier symbol includes
the matching absolute determinant in the original Fourier normalization. -/
theorem inverseFourier_comp_inverseAdjoint (A : E ≃L[ℝ] E) (p : E → ℂ) (z : E) :
    (𝓕⁻ (p ∘ (physicalDualEquiv A).symm)) z = linearJacobian A • (𝓕⁻ p) (A z) := by
  let D := physicalDualEquiv A
  let g (u : E) := Real.fourierChar (inner ℝ u (A z)) • p u
  have hPhase (ξ : E) : inner ℝ ξ z = inner ℝ (D.symm ξ) (A z) := by
    calc
      _ = inner ℝ z ξ := real_inner_comm _ _
      _ = inner ℝ z (D (D.symm ξ)) := by rw [D.apply_symm_apply]
      _ = inner ℝ (A z) (D.symm ξ) := inner_physicalDualEquiv A z (D.symm ξ)
      _ = _ := real_inner_comm _ _
  rw [Real.fourierIntegralInv_eq (p ∘ D.symm) z, Real.fourierIntegralInv_eq p (A z)]
  calc
    _ = ∫ ξ, g (D.symm ξ) := by
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [Function.comp_apply, g, hPhase, D]
    _ = _ := by
      rw [integral_comp_linearEquiv D.symm g, linearJacobian_symm, inv_inv]
      simp only [D, linearJacobian_physicalDualEquiv, g]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The invertible chart derivative at the output point of the kernel. -/
def frozenChartDerivative (c d : M) {x : E}
    (hx : x ∈ (chartTransition c d).source) : E ≃L[ℝ] E :=
  (fderiv ℝ (overlapTransition c d) x).toContinuousLinearEquivOfDetNeZero
    (overlapTransition_fderiv_det_ne_zero c d hx)

/-- The frequency transformation associated to the same frozen
spatial derivative. -/
def frozenChartFrequency (c d : M) {x : E}
    (hx : x ∈ (chartTransition c d).source) : E ≃L[ℝ] E :=
  (physicalDualEquiv (frozenChartDerivative c d hx)).symm

theorem frozenChartFrequency_inverse_adjoint (c d : M) {x : E}
    (hx : x ∈ (chartTransition c d).source) (ξ : E) :
    (fderiv ℝ (overlapTransition c d) x).adjoint (frozenChartFrequency c d hx ξ) = ξ := by
  let A := frozenChartDerivative c d hx
  have hA : A.toContinuousLinearMap = fderiv ℝ (overlapTransition c d) x :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
  rw [← hA, ← physicalDualEquiv_apply]
  exact (physicalDualEquiv A).apply_symm_apply ξ

theorem inverseFourier_frozenChartFrequency (c d : M) {x : E}
    (hx : x ∈ (chartTransition c d).source) (p : E → ℂ) (z : E) :
    (𝓕⁻ (p ∘ frozenChartFrequency c d hx)) z =
      (overlapJacobianWeight c d x)^2 •
        (𝓕⁻ p) (fderiv ℝ (overlapTransition c d) x z) := by
  let A := frozenChartDerivative c d hx
  have hA : A.toContinuousLinearMap = fderiv ℝ (overlapTransition c d) x :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
  have hJ : linearJacobian A = (overlapJacobianWeight c d x)^2 := by
    rw [linearJacobian, hA, overlapTransition_fderiv c d hx, overlapJacobianWeight_sq_on_source c d hx]
  change (𝓕⁻ (p ∘ (physicalDualEquiv A).symm)) z = _
  rw [inverseFourier_comp_inverseAdjoint, hJ]
  rfl

/-- The actual annular shell uses the inverse adjoint on its full
frequency symbol, including its radial cutoff. -/
theorem overlap_frozen_shellKernel_symbol (c d : M) {x : E}
    (hx : x ∈ (chartTransition c d).source) (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) (z : E) :
    (overlapJacobianWeight c d x)^2 •
        shellKernel m hm j (fderiv ℝ (overlapTransition c d) x z) =
      (𝓕⁻ (fun ξ => annularSymbol m ((dyadicScale j)⁻¹ • frozenChartFrequency c d hx ξ))) z := by
  rw [shellKernel_eq_inverseFourier]
  exact (inverseFourier_frozenChartFrequency c d hx
    (fun ξ => annularSymbol m ((dyadicScale j)⁻¹ • ξ)) z).symm

/-- The same exact identity holds for the finite partial angular multiplier
at every cutoff index. -/
theorem overlap_frozen_partialAngularKernel_symbol (c d : M) {x : E}
    (hx : x ∈ (chartTransition c d).source) (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (N : ℕ) (z : E) :
    (overlapJacobianWeight c d x)^2 •
        partialAngularKernel m hm N (fderiv ℝ (overlapTransition c d) x z) =
      (𝓕⁻ (fun ξ => partialAngularSymbol m N (frozenChartFrequency c d hx ξ))) z := by
  unfold partialAngularKernel
  rw [← inverseFourier_partialAngular_eq_sum m hm hd]
  exact (inverseFourier_frozenChartFrequency c d hx (partialAngularSymbol m N) z).symm

end Burnett.Microlocal.OverlapKernel
