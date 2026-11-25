import Burnett.Analysis.TransportPatches.ProjectedRemainderScale
import Burnett.Analysis.GaugeProjection.LocalizedProjectedFiniteLp
import Burnett.Analysis.GaugeProjection.ProjectedDefectLocalizationError

set_option autoImplicit false
set_option maxRecDepth 3800
set_option maxHeartbeats 4400000

noncomputable section

namespace Burnett.C03

open Set MeasureTheory Burnett.P01 Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open scoped ContDiff ENNReal

open private norm_scalarPartial_le_first from Burnett.Analysis.TransportPatches.ProjectedRemainderScale
open private projectionMatrixLpNorm_le_of_support coordinateDerivative_zero_outside from
  Burnett.Analysis.GaugeProjection.LocalizedProjectedFiniteLp

/-- The original localized fluctuation and all four coordinate derivatives
have the same compact patch-volume factor at every finite exponent. -/
theorem localizedMetricSchwartz_patchLp
    (g g₀ : CoordinateSpace → Tensor2) (hg : SmoothCoordinateComponents g)
    (hg₀ : SmoothCoordinateComponents g₀)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hSupp : tsupport χ ⊆ K)
    (A B D e : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (he : 0 ≤ e)
    (hχ₀ : ∀ x ∈ tsupport χ, ‖χ x‖ ≤ A)
    (hχ₁ : ∀ x ∈ tsupport χ, ‖iteratedFDeriv ℝ 1 χ x‖ ≤ B)
    (hField : ∀ x ∈ tsupport χ, ‖g x - g₀ x‖ ≤ e ∧
      ‖coordinateJet g x - coordinateJet g₀ x‖ ≤ D)
    (p : ℝ) (hp : 0 < p) :
    let z := localizedMetricSchwartz g g₀ χ hχ hc hg hg₀
    projectionMatrixLpNorm p z ≤ ENNReal.ofReal (A * e) * volume K ^ (1 / p) ∧
      ∀ a : Index, projectionMatrixLpNorm p (projectionMatrixDerivative a z) ≤
        ENNReal.ofReal (A * D + B * e) * volume K ^ (1 / p) := by
  let z := localizedMetricSchwartz g g₀ χ hχ hc hg hg₀
  have hSupport (i j : Index) : tsupport (z i j : CoordinateSpace → ℂ) ⊆ K :=
    (localizedMetricSchwartz_tsupport_subset g g₀ χ hχ hc hg hg₀ i j).trans hSupp
  have hValue (x : CoordinateSpace) (hx : x ∈ tsupport χ) (i j : Index) :
      ‖g x i j - g₀ x i j‖ ≤ e :=
    ((norm_le_pi_norm ((g x - g₀ x) i) j).trans
      (norm_le_pi_norm (g x - g₀ x) i)).trans (hField x hx).1
  have hDerivative (x : CoordinateSpace) (hx : x ∈ tsupport χ) (a i j : Index) :
      ‖coordinateJet g x a i j - coordinateJet g₀ x a i j‖ ≤ D := by
    let d := coordinateJet g x - coordinateJet g₀ x
    exact ((norm_le_pi_norm (d a i) j).trans
      ((norm_le_pi_norm (d a) i).trans (norm_le_pi_norm d a))).trans (hField x hx).2
  have hZero (w : ProjectionSchwartzMatrix)
      (hw : ∀ x i j, x ∉ tsupport χ → w i j x = 0) :
      ∀ x i j, x ∉ K → w i j x = 0 :=
    fun x i j hx => hw x i j (fun hxχ => hx (hSupp hxχ))
  have hz (x : CoordinateSpace) (i j : Index) (hx : x ∉ tsupport χ) : z i j x = 0 := by
    have hχzero := image_eq_zero_of_notMem_tsupport hx
    change ((χ x * (g x i j - g₀ x i j) : ℝ) : ℂ) = 0
    simp [hχzero]
  refine ⟨projectionMatrixLpNorm_le_of_support z K hK.isClosed.measurableSet p hp
    (A * e) (mul_nonneg hA he) (hZero z hz) ?_, ?_⟩
  · intro x i j
    by_cases hx : x ∈ tsupport χ
    · change ‖((χ x * (g x i j - g₀ x i j) : ℝ) : ℂ)‖ ≤ _
      rw [Complex.norm_real, norm_mul]
      exact mul_le_mul (hχ₀ x hx) (hValue x hx i j) (norm_nonneg _) hA
    · rw [hz x i j hx, norm_zero]
      exact mul_nonneg hA he
  · intro a
    have hzD (x : CoordinateSpace) (i j : Index) (hx : x ∉ K) :
        projectionMatrixDerivative a z i j x = 0 :=
      coordinateDerivative_zero_outside (z i j) K (hSupport i j) a x hx
    apply projectionMatrixLpNorm_le_of_support (projectionMatrixDerivative a z) K
      hK.isClosed.measurableSet p hp _ (add_nonneg (mul_nonneg hA hD) (mul_nonneg hB he)) hzD
    intro x i j
    rw [projectionMatrixDerivative, localizedMetricSchwartz_coordinateDerivative_real, Complex.norm_real]
    by_cases hx : x ∈ tsupport χ
    · refine (norm_add_le _ _).trans ?_
      simp only [norm_mul]
      exact add_le_add (mul_le_mul (hχ₀ x hx) (hDerivative x hx a i j) (norm_nonneg _) hA)
        (mul_le_mul ((norm_scalarPartial_le_first χ x a).trans (hχ₁ x hx))
          (hValue x hx i j) (norm_nonneg _) hB)
    · have hχzero := image_eq_zero_of_notMem_tsupport hx
      have hχD : scalarPartial χ a x = 0 := by
        simp only [scalarPartial, fderiv_of_notMem_tsupport ℝ hx, ContinuousLinearMap.zero_apply]
      simp only [hχzero, hχD, zero_mul, add_zero, norm_zero]
      exact add_nonneg (mul_nonneg hA hD) (mul_nonneg hB he)

end Burnett.C03
