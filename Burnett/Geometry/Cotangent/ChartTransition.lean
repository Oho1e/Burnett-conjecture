import Burnett.Geometry.Cotangent.Core

/-!
# Covectors in two preferred charts

The dual of the actual tangent frame change acts on a cotangent fiber.
The same fiberwise inverse quadratic form gives both coordinate expressions.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.UnitNullCompactness

open Matrix
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ChartVolume Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.InverseField (matrixInverse)
open scoped BigOperators ContDiff Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The matrix carrying covector components from chart c to chart d at m. -/
def cotangentTransitionMatrix (c d m : M) : Matrix Index Index ℝ :=
  (derivativeMatrix (fderiv ℝ (chartTransition d c) (chartAt CoordinateSpace d m)))ᵀ

theorem cotangentTransitionMatrix_eq_inv_transpose (c d m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source) (hd : m ∈ (chartAt CoordinateSpace d).source) :
    cotangentTransitionMatrix c d m =
      ((derivativeMatrix (fderiv ℝ (chartTransition c d) (chartAt CoordinateSpace c m)))⁻¹)ᵀ := by
  let D := fderiv ℝ (chartTransition c d) (chartAt CoordinateSpace c m)
  let E := fderiv ℝ (chartTransition d c) (chartAt CoordinateSpace d m)
  have hId : E.toLinearMap.comp D.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro v
    change E (D v) = v
    apply tangentFrame_injective c m hc
    exact (tangentFrame_change d c m hd hc (D v)).symm.trans
      (tangentFrame_change c d m hc hd v).symm
  have hMul : derivativeMatrix E * derivativeMatrix D = 1 := by
    unfold derivativeMatrix
    rw [← LinearMap.toMatrix_comp, hId, LinearMap.toMatrix_id]
  change (derivativeMatrix E)ᵀ = ((derivativeMatrix D)⁻¹)ᵀ
  rw [Matrix.inv_eq_left_inv hMul]

theorem cotangentCoords_change (c d : M) (p : CotangentBundle M)
    (hc : p.1 ∈ (chartAt CoordinateSpace c).source)
    (hd : p.1 ∈ (chartAt CoordinateSpace d).source) :
    cotangentCoords d p = cotangentTransitionMatrix c d p.1 *ᵥ cotangentCoords c p := by
  funext i
  let E := fderiv ℝ (chartTransition d c) (chartAt CoordinateSpace d p.1)
  let v := E (coordinateBasis i)
  have hrepr (j : Index) : coordinateBasis.repr v j = v j := rfl
  have hf := congrArg ((cotangentTrivialization c p).2) (coordinateBasis.sum_repr v)
  calc
    cotangentCoords d p i = (cotangentTrivialization c p).2 v := by
      rw [cotangentCoords, cotangentTrivialization_apply, cotangentTrivialization_apply]
      exact congrArg p.2 (tangentFrame_change d c p.1 hd hc (coordinateBasis i))
    _ = ∑ j, v j * cotangentCoords c p j := by
      simpa only [map_sum, map_smul, smul_eq_mul, hrepr, cotangentCoords] using hf.symm
    _ = (cotangentTransitionMatrix c d p.1 *ᵥ cotangentCoords c p) i := by
      simp only [cotangentTransitionMatrix, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [derivativeMatrix, LinearMap.toMatrix_apply]
      exact congrArg (fun a : ℝ => a * cotangentCoords c p j) (hrepr j).symm

theorem cotangentCoords_assemble_change (c d m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source) (hd : m ∈ (chartAt CoordinateSpace d).source)
    (ξ : Covector) :
    cotangentCoords d (cotangentAssemble c (m, ξ)) = cotangentTransitionMatrix c d m *ᵥ ξ := by
  rw [cotangentCoords_change c d _ hc hd, cotangentCoords_assemble c _ hc]
  rfl

/-- The two coordinate descriptions assemble to the same actual covector. -/
theorem cotangentAssemble_change (c d m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source) (hd : m ∈ (chartAt CoordinateSpace d).source)
    (ξ : Covector) :
    cotangentAssemble d (m, cotangentTransitionMatrix c d m *ᵥ ξ) =
      cotangentAssemble c (m, ξ) := by
  rw [← cotangentCoords_assemble_change c d m hc hd ξ]
  exact cotangentAssemble_coords d (cotangentAssemble c (m, ξ)) hd

theorem cotangentTransitionMatrix_comp_mulVec (c d e m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source) (hd : m ∈ (chartAt CoordinateSpace d).source)
    (he : m ∈ (chartAt CoordinateSpace e).source) (ξ : Covector) :
    cotangentTransitionMatrix d e m *ᵥ (cotangentTransitionMatrix c d m *ᵥ ξ) =
      cotangentTransitionMatrix c e m *ᵥ ξ := by
  rw [← cotangentCoords_assemble_change d e m hd he,
    cotangentAssemble_change c d m hc hd, cotangentCoords_assemble_change c e m hc he]

theorem cotangentTransitionMatrix_reverse_mulVec (c d m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source) (hd : m ∈ (chartAt CoordinateSpace d).source)
    (ξ : Covector) :
    cotangentTransitionMatrix d c m *ᵥ (cotangentTransitionMatrix c d m *ᵥ ξ) = ξ := by
  rw [← cotangentCoords_assemble_change d c m hd hc,
    cotangentAssemble_change c d m hc hd, cotangentCoords_assemble c _ hc]

theorem cotangentTransitionMatrix_mulVec_ne_zero (c d m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source) (hd : m ∈ (chartAt CoordinateSpace d).source)
    {ξ : Covector} (hξ : ξ ≠ 0) : cotangentTransitionMatrix c d m *ᵥ ξ ≠ 0 := by
  intro hz
  have h := cotangentTransitionMatrix_reverse_mulVec c d m hc hd ξ
  rw [hz, Matrix.mulVec_zero] at h
  exact hξ h.symm

/-- The true inverse metric evaluates equally in the two coordinate descriptions. -/
theorem symbolNorm_cotangentTransitionMatrix
    (g : ManifoldBilinear.Field (M := M)) (hn : ManifoldBilinear.IsNondegenerate g)
    (hs : ManifoldBilinear.IsSymmetric g) (c d m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source) (hd : m ∈ (chartAt CoordinateSpace d).source)
    (ξ : Covector) :
    symbolNorm (matrixInverse (metricComponents (coordinateBilinear g d) (chartAt CoordinateSpace d m)))
        (cotangentTransitionMatrix c d m *ᵥ ξ) =
      symbolNorm (matrixInverse (metricComponents (coordinateBilinear g c) (chartAt CoordinateSpace c m))) ξ := by
  let p := cotangentAssemble c (m, ξ)
  have hd' := dualEnergy_chart g hn hs d p hd
  have hc' := dualEnergy_chart g hn hs c p hc
  rw [show p.1 = m from rfl, cotangentCoords_assemble_change c d m hc hd ξ] at hd'
  rw [show p.1 = m from rfl, cotangentCoords_assemble c (m, ξ) hc] at hc'
  exact hd'.symm.trans hc'

end Burnett.Geometry.UnitNullCompactness
