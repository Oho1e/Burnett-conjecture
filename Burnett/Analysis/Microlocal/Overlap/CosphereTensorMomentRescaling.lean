import Burnett.Analysis.Microlocal.Overlap.CosphereEinsteinMoments
import Burnett.Analysis.Microlocal.Overlap.CosphereAuxiliaryMeasureChange

set_option autoImplicit false

noncomputable section
namespace Burnett.Microlocal.Overlap

open MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear
open CotangentAngularExtension CotangentUnitNormalization ContravariantTensor UnitNullCompactness
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.Bianchi.NormChange
open scoped ContDiff Manifold ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem intrinsicTensorPhase_scale (Q : ContravariantTwoTensor M) (p : CotangentBundle M)
    (c : ℝ) : intrinsicTensorPhase Q (cotangentScale c p) = c^2 * intrinsicTensorPhase Q p := by
  change Q p.1 (c • p.2.toLinearMap) (c • p.2.toLinearMap) =
    c^2 * Q p.1 p.2.toLinearMap p.2.toLinearMap
  rw [(Q p.1).map_smul, LinearMap.smul_apply, ((Q p.1) p.2.toLinearMap).map_smul]
  simp only [smul_eq_mul, pow_two, mul_assoc]

/-- The quadratic test at the normalized covector cancels the squared norm
used to reweight the measure. Both integrability and the signed integral pass
between the actual auxiliary unit sections. -/
theorem cosphereTensorPhase_of_auxiliaryRescaling
    (r r' : Metric (M := M)) (μ : Measure (Cosphere r)) (μ' : Measure (Cosphere r'))
    (hμ : μ' = (μ.withDensity (fun p : Cosphere r => cotangentAuxiliaryWeight r' p.val)).map
      (renormalizeUnitCosphere r r'))
    (Q : ContravariantTwoTensor M) :
    (Integrable (fun p : Cosphere r' => intrinsicTensorPhase Q p.val) μ' ↔
      Integrable (fun p : Cosphere r => intrinsicTensorPhase Q p.val) μ) ∧
    (∫ p : Cosphere r', intrinsicTensorPhase Q p.val ∂μ') =
      ∫ p : Cosphere r, intrinsicTensorPhase Q p.val ∂μ := by
  let F : Cosphere r ≃ₜ Cosphere r' := unitShellHomeomorph r r'
  let s : Cosphere r → ℝ := shellScale r r'
  have hWeight : (fun p : Cosphere r => cotangentAuxiliaryWeight r' p.val) =
      squareDensity s := by
    funext p
    change ENNReal.ofReal (dualEnergy r'.inner (GlobalLeviCivita.inner_nondegenerate r') p.val) =
      ENNReal.ofReal ((cotangentNorm r' p.val)^2)
    rw [cotangentNorm_sq r' (unitShell_punctured r p.property)]
  have hRescaled : μ' = rescaled μ F s := by
    rw [hμ, hWeight]
    rfl
  rw [hRescaled]
  apply divided_quadratic_test_preserved μ F s (shellScale_continuous r r') (shellScale_pos r r')
  intro p
  change intrinsicTensorPhase Q (unitShellHomeomorph r r' p).val =
    intrinsicTensorPhase Q p.val / (shellScale r r' p)^2
  rw [unitShellHomeomorph_value, intrinsicTensorPhase_scale, inv_pow, div_eq_inv_mul]

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- A physical auxiliary change preserves the same Einstein tensor moments
against every compact smooth symmetric test. -/
theorem cosphereEinsteinMoments_of_auxiliaryRescaling
    (r r' : Metric (M := M)) (B : Field (M := M)) (hn : IsNondegenerate B)
    (μ : Measure (Cosphere r)) (μ' : Measure (Cosphere r'))
    (hμ : μ' = (μ.withDensity (fun p : Cosphere r => cotangentAuxiliaryWeight r' p.val)).map
      (renormalizeUnitCosphere r r'))
    (hMoment : HasCosphereEinsteinMoments r B hn μ) : HasCosphereEinsteinMoments r' B hn μ' := by
  intro Q hQ
  obtain ⟨hBase, hPhase, hEq⟩ := hMoment Q hQ
  obtain ⟨hIff, hPhaseEq⟩ := cosphereTensorPhase_of_auxiliaryRescaling r r' μ μ' hμ Q
  exact ⟨hBase, hIff.mpr hPhase, hEq.trans hPhaseEq.symm⟩

end Burnett.Microlocal.Overlap
