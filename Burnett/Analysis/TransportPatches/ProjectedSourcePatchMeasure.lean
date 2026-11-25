import Burnett.Analysis.GaugeProjection.ProjectedVacuumSourceOnChart

/-! Propagate an explicit pointwise remainder bound through the actual
whole-space projection, retaining the measure of the same patch. -/
set_option autoImplicit false
set_option maxRecDepth 3800
set_option maxHeartbeats 4300000

noncomputable section

namespace Burnett.C03

open Set MeasureTheory Burnett.P01 Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.A07 (coordinateDerivative)
open scoped ENNReal ContDiff BigOperators

open private partial_smooth partial_tsupport complexCompactSchwartz_partial smooth_gauge
  metricMixedJet_symmetric metricSecondJet_symmetric from
  Burnett.Analysis.GaugeProjection.ProjectedVacuumSourceOnChart

/-- A pointwise bound on the explicit localized vacuum remainder gives
the same volume factor for the actual projected full-space source. -/
theorem norm_projectedLocalizedSource_le_patch_measure
    (g inv g₀ : CoordinateSpace → Tensor2) (χ : CoordinateSpace → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hg : SmoothCoordinateComponents g) (hi : SmoothCoordinateComponents inv)
    (hg₀ : SmoothCoordinateComponents g₀)
    (hInvSym : ∀ x ∈ tsupport χ, IsSymmetricTensor (inv x))
    (hSym : ∀ x, IsSymmetricTensor (g x))
    (hVac : ∀ x ∈ tsupport χ, ∀ i j, coordinateRicci
      (fun y => christoffel (inv y) (coordinateJet g y)) x i j = 0)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hχK : tsupport χ ⊆ K)
    (M : ℝ) (hM : 0 ≤ M)
    (hR : ∀ x ∈ tsupport χ, ∀ i j, ‖localizedVacuumSourceRemainder inv g g₀ χ x i j‖ ≤ M) :
    ‖projectionFullL2 (projectionMatrixToL2
      (localizedWaveSourceSchwartz inv g g₀ χ hχ hc hi hg hg₀))‖ ≤
      ‖projectionFullL2‖ * (ENNReal.ofReal M * volume K ^ ((1 : ℝ) / 2)).toReal := by
  let Q := localizedWaveSourceSchwartz inv g g₀ χ hχ hc hi hg hg₀
  let V := localizedGaugeSchwartz inv g χ hχ hc hi hg
  let R : ProjectionSchwartzMatrix := fun i j =>
    Q i j - (coordinateDerivative i (V j) + coordinateDerivative j (V i))
  have hDecomp (i j : Index) (x : CoordinateSpace) :
      Q i j x = coordinateDerivative i (V j) x + coordinateDerivative j (V i) x + R i j x := by
    simp only [R, SchwartzMap.sub_apply, SchwartzMap.add_apply]
    ring
  have hMajorant (i j : Index) (x : CoordinateSpace) :
      ‖R i j x‖ ≤ K.indicator (fun _ => M) x := by
    have hv (a b : Index) : coordinateDerivative a (V b) x =
        (scalarPartial (fun y => χ y * coordinateGaugeCovector inv g y b) a x : ℂ) :=
      complexCompactSchwartz_partial _ _ _ a x
    change ‖Q i j x - (coordinateDerivative i (V j) x + coordinateDerivative j (V i) x)‖ ≤ _
    rw [hv, hv]
    by_cases hx : x ∈ tsupport χ
    · have hId := localizedVacuumSource_eq_symmetrizedGauge_add_remainder inv g g₀ χ x i j
        (hχ.differentiable (by simp)) (fun a => (partial_smooth χ a hχ).differentiable (by simp) x)
        (fun a b => (hg a b).differentiable (by simp))
        (fun a b => (hg₀ a b).differentiable (by simp))
        (fun d a b => (partial_smooth _ d (hg a b)).differentiable (by simp) x)
        (fun d a b => (partial_smooth _ d (hg₀ a b)).differentiable (by simp) x)
        (fun a b => (hi a b).differentiable (by simp) x) (hInvSym x hx)
        (metricMixedJet_symmetric g hg x) (metricSecondJet_symmetric g hSym x)
        (fun b => (smooth_gauge inv g hi hg b).differentiable (by simp) x) (hVac x hx i j)
      change ‖(scalarWaveAt (inv x) (fun y => χ y * (g y i j - g₀ y i j)) x : ℂ) - _‖ ≤ _
      rw [hId, Complex.ofReal_add, Complex.ofReal_add, add_sub_cancel_left, Complex.norm_real,
        indicator_of_mem (hχK hx)]
      exact hR x hx i j
    · let z (y : CoordinateSpace) := χ y * (g y i j - g₀ y i j)
      have hz : tsupport z ⊆ tsupport χ := tsupport_mul_subset_left
      have hZero (a b : Index) : scalarPartial (scalarPartial z b) a x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun h => hx (hz (partial_tsupport z b (partial_tsupport (scalarPartial z b) a h))))
      have hvZero (a b : Index) : scalarPartial (fun y => χ y * coordinateGaugeCovector inv g y b) a x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_mul_subset_left (partial_tsupport _ a h)))
      change ‖(scalarWaveAt (inv x) z x : ℂ) - _‖ ≤ _
      simp only [hvZero, scalarWaveAt, hZero, mul_zero, Finset.sum_const_zero, Complex.ofReal_zero,
        add_zero, sub_zero, norm_zero]
      by_cases hxK : x ∈ K
      · rwa [indicator_of_mem hxK]
      · rw [indicator_of_notMem hxK]
  calc
    _ ≤ ‖projectionFullL2‖ * (eLpNorm (K.indicator (fun _ => M)) 2 volume).toReal :=
      norm_projectionFullL2_localized_source_le Q R V hDecomp K hK M hMajorant
    _ = _ := by
      rw [eLpNorm_indicator_const hK.isClosed.measurableSet (by norm_num) (by simp),
        ← ofReal_norm, Real.norm_of_nonneg hM]
      norm_num

end Burnett.C03
