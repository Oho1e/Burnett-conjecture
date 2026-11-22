import Burnett.Analysis.GaugeProjection.MatrixGeneralLipschitzBound

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter Set
open Burnett.A02.FrequencySplit (E)
open Burnett.A07 (coordinateDerivative)
open Burnett.Fourier
open scoped NNReal BigOperators

private def matrixSchwartzL2Linear : ProjectionSchwartzMatrix →ₗ[ℂ] ProjectionL2Matrix where
  toFun := projectionMatrixToL2
  map_add' u v := by
    funext i j
    exact map_add (schwartzLpMap (V := E)) (u i j) (v i j)
  map_smul' c u := by
    funext i j
    exact map_smul (schwartzLpMap (V := E)) c (u i j)

private theorem matrixSchwartzL2Linear_injective : Function.Injective matrixSchwartzL2Linear := by
  intro u v hv
  funext i j
  exact (SchwartzMap.injective_toLp 2 volume) (congrFun (congrFun hv i) j)

private abbrev matrixSchwartzL2Range : Submodule ℂ ProjectionL2Matrix :=
  LinearMap.range matrixSchwartzL2Linear

private theorem matrixSchwartzL2Range_dense : Dense (matrixSchwartzL2Range : Set ProjectionL2Matrix) := by
  let R : Set (ComplexL2 E) := Set.range (fun u : SchwartzMap E ℂ => u.toLp 2 volume)
  have hR : Dense R := schwartz_toLp_denseRange (V := E)
  have h : Dense (Set.pi Set.univ (fun _ : Fin 4 => Set.pi Set.univ (fun _ : Fin 4 => R))) :=
    dense_pi Set.univ fun _ _ => dense_pi Set.univ fun _ _ => hR
  apply h.mono
  intro v hv
  have e (i j : Fin 4) : ∃ u : SchwartzMap E ℂ, u.toLp 2 volume = v i j :=
    hv i (Set.mem_univ i) j (Set.mem_univ j)
  choose u hu using e
  exact ⟨u, funext fun i => funext fun j => hu i j⟩

private def matrixSchwartzRangeEquiv : ProjectionSchwartzMatrix ≃ₗ[ℂ] matrixSchwartzL2Range :=
  LinearEquiv.ofInjective matrixSchwartzL2Linear matrixSchwartzL2Linear_injective

private def coefficientProductLinear (f : E → ℂ) (L : ℝ≥0) (hL : LipschitzWith L f) :
    SchwartzMap E ℂ →ₗ[ℂ] ComplexL2 E where
  toFun := projectionLipschitzCoefficientProductL2 f L hL
  map_add' u v := by
    let P := projectionLipschitzCoefficientProductL2 f L hL
    apply Lp.ext
    filter_upwards [projectionLipschitzCoefficientProductL2_ae f L hL (u + v),
      projectionLipschitzCoefficientProductL2_ae f L hL u, projectionLipschitzCoefficientProductL2_ae f L hL v,
      Lp.coeFn_add (P u) (P v)] with x ha hu hv hs
    change P (u + v) x = _ at ha
    change P u x = _ at hu
    change P v x = _ at hv
    change P (u + v) x = (P u + P v) x
    rw [ha, hs, Pi.add_apply, hu, hv, SchwartzMap.add_apply, mul_add]
  map_smul' c u := by
    let P := projectionLipschitzCoefficientProductL2 f L hL
    apply Lp.ext
    filter_upwards [projectionLipschitzCoefficientProductL2_ae f L hL (c • u),
      projectionLipschitzCoefficientProductL2_ae f L hL u, Lp.coeFn_smul c (P u)] with x ha hu hs
    change P (c • u) x = _ at ha
    change P u x = _ at hu
    change P (c • u) x = (c • P u) x
    rw [ha, hs, Pi.smul_apply, hu, SchwartzMap.smul_apply, smul_eq_mul, smul_eq_mul]
    ring

private def matrixCoefficientProductLinear (f : E → ℂ) (L : ℝ≥0) (hL : LipschitzWith L f) :
    ProjectionSchwartzMatrix →ₗ[ℂ] ProjectionL2Matrix where
  toFun u i j := projectionLipschitzCoefficientProductL2 f L hL (u i j)
  map_add' u v := by
    funext i j
    exact map_add (coefficientProductLinear f L hL) (u i j) (v i j)
  map_smul' c u := by
    funext i j
    exact map_smul (coefficientProductLinear f L hL) c (u i j)

private def matrixSchwartzDerivativeLinear (b : Fin 4) : ProjectionSchwartzMatrix →ₗ[ℂ] ProjectionSchwartzMatrix where
  toFun := projectionMatrixDerivative b
  map_add' u v := by
    funext i j
    exact map_add (coordinateDerivative b) (u i j) (v i j)
  map_smul' c u := by
    funext i j
    exact map_smul (coordinateDerivative b) c (u i j)

private def matrixSchwartzProjectionLinear : ProjectionSchwartzMatrix →ₗ[ℂ] ProjectionSchwartzMatrix where
  toFun := projectionFullSchwartz
  map_add' u v := by
    funext i j
    simp only [projectionFullSchwartz, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c u := by
    funext i j
    simp only [projectionFullSchwartz, Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

private def matrixSchwartzCommutatorLinear (b : Fin 4) (f : E → ℂ) (L : ℝ≥0) (hL : LipschitzWith L f) :
    ProjectionSchwartzMatrix →ₗ[ℂ] ProjectionL2Matrix :=
  let A := matrixCoefficientProductLinear f L hL
  let D := matrixSchwartzDerivativeLinear b
  projectionFullL2.toLinearMap.comp (A.comp D) - A.comp (matrixSchwartzProjectionLinear.comp D)

/-- The actual differentiated commutator on Schwartz fields admits a bounded
extension to the entire physical matrix \(L^2\) space with the same estimate. -/
theorem exists_projectionLipschitzCommutatorL2_extension :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : Fin 4) (f : E → ℂ) (L : ℝ≥0) (hL : LipschitzWith L f),
        ∃ T : ProjectionL2Matrix →L[ℂ] ProjectionL2Matrix,
          (∀ w : ProjectionSchwartzMatrix, T (projectionMatrixToL2 w) = projectionLipschitzCommutatorL2 b f L hL w) ∧
          (∀ u : ProjectionL2Matrix, ‖T u‖ ≤ C * (L : ℝ) * ‖u‖) := by
  obtain ⟨C, hC, estimate⟩ := exists_projectionGeneralLipschitzCommutatorL2_bound
  refine ⟨C, hC, fun b f L hL => ?_⟩
  let A := matrixSchwartzCommutatorLinear b f L hL
  let V := matrixSchwartzL2Range
  let e := matrixSchwartzRangeEquiv
  let B : V →ₗ[ℂ] ProjectionL2Matrix := A.comp e.symm.toLinearMap
  have hB (v : V) : ‖B v‖ ≤ C * (L : ℝ) * ‖v‖ := by
    obtain ⟨w, rfl⟩ := e.surjective v
    have h := estimate b f L hL w
    change ‖A (e.symm (e w))‖ ≤ _
    rw [LinearEquiv.symm_apply_apply]
    exact h
  let B' : V →L[ℂ] ProjectionL2Matrix := B.mkContinuous (C * (L : ℝ)) hB
  have hD : DenseRange V.subtypeL := matrixSchwartzL2Range_dense.denseRange_val
  have hU := V.subtypeₗᵢ.isometry.isUniformInducing
  let T := B'.extend V.subtypeL hD hU
  have hT (v : V) : T v = B v :=
    ContinuousLinearMap.extend_eq B' V.subtypeL hD hU v
  have cover (w : ProjectionSchwartzMatrix) :
      T (projectionMatrixToL2 w) = projectionLipschitzCommutatorL2 b f L hL w := by
    change T (e w : ProjectionL2Matrix) = A w
    rw [hT]
    change A (e.symm (e w)) = A w
    rw [LinearEquiv.symm_apply_apply]
  refine ⟨T, cover, fun u => hD.induction_on u ?_ ?_⟩
  · exact isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)
  · intro v
    change ‖T v‖ ≤ _
    rw [hT]
    exact hB v

end Burnett.P01
