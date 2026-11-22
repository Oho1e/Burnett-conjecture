import Burnett.Analysis.GaugeProjection.IntrinsicChartProjectedSource
import Burnett.Analysis.GaugeProjection.IntrinsicChartProjectedNorms

set_option autoImplicit false

noncomputable section

namespace Burnett.P01

open Burnett.RicciSymbol
open Burnett.Geometry Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Geometry.ManifoldMetricTransition (coordinateBilinear)
open Set Filter MeasureTheory
open Burnett.A07 (coordinateDerivative)
open scoped ContDiff Manifold NNReal Topology

private theorem coordinateDerivative_tsupport_le (f : SchwartzMap CoordinateSpace ℂ) (a : Index) :
    tsupport (coordinateDerivative a f : CoordinateSpace → ℂ) ⊆
      tsupport (f : CoordinateSpace → ℂ) := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  apply support_fderiv_subset ℝ
  intro hzero
  apply hx
  change fderiv ℝ (f : CoordinateSpace → ℂ) x (EuclideanSpace.single a 1) = 0
  rw [hzero, ContinuousLinearMap.zero_apply]

/-- The unprojected nondivergence term only sees coefficient values on the support of its input. -/
private theorem projectedSourceQ_eq_of_agreement_on_support (K : Set CoordinateSpace)
    (z : ProjectionSchwartzMatrix) (hz : ∀ i j, tsupport (z i j : CoordinateSpace → ℂ) ⊆ K)
    (A B : ProjectedSourceCoefficients) (hAB : ∀ i j x, x ∈ K → A.entry i j x = B.entry i j x) :
    projectedSourceQ A z = projectedSourceQ B z := by
  funext i j
  apply Lp.ext
  filter_upwards [projectedSourceQ_ae A z i j, projectedSourceQ_ae B z i j] with x hA hB
  rw [hA, hB]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hx : x ∈ K
  · rw [hAB a b x hx]
  · have hzero : coordinateDerivative a (coordinateDerivative b (z i j)) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (hz i j
        (coordinateDerivative_tsupport_le _ b (coordinateDerivative_tsupport_le _ a h))))
    rw [hzero, mul_zero, mul_zero]

/-- A single near-maximizing selection controls all choices, provided each individual
index already admits a finite upper bound. -/
private theorem uniform_bound_of_bounded_selections {E : ℕ → Type*}
    (value : (n : ℕ) → E n → ℝ)
    (row : ∀ n, E n → BddAbove (range (value n)))
    (family : ∀ a : (n : ℕ) → E n, ∃ C : ℝ, 0 ≤ C ∧ ∀ n, value n (a n) ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : (n : ℕ) → E n, ∀ n, value n (a n) ≤ C := by
  classical
  by_cases hex : Nonempty ((n : ℕ) → E n)
  · let base := hex.some
    have near (n : ℕ) : ∃ a : E n, (⨆ b, value n b) - 1 < value n a := by
      letI : Nonempty (E n) := ⟨base n⟩
      exact exists_lt_of_lt_ciSup (sub_lt_self _ one_pos)
    choose a ha using near
    obtain ⟨C, hC, hBound⟩ := family a
    refine ⟨C + 1, by linarith, fun b n => ?_⟩
    have hb : value n (b n) ≤ ⨆ t, value n t := le_ciSup (row n (base n)) (b n)
    linarith [ha n, hBound n]
  · exact ⟨0, le_rfl, fun a => (hex ⟨a⟩).elim⟩

/-- At fixed slope, the source estimate for every extension family of a supported input
gives a single bound shared by all the families. -/
theorem projectedSource_uniform_extension_bound
    (K : Set CoordinateSpace) (G : ℕ → CoordinateSpace → Tensor2) (z : ℕ → ProjectionSchwartzMatrix)
    (hz : ∀ n i j, tsupport (z n i j : CoordinateSpace → ℂ) ⊆ K)
    (hSource : ∀ (a : ℕ → CoordinateSpace → Tensor2) (ha : ∀ n, SmoothCoordinateComponents (a n))
      (L : ℝ≥0) (hL : ∀ n i j, LipschitzWith L (fun x => a n x i j)),
      (∀ n, a n =ᶠ[𝓝ˢ K] G n) → ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
        ‖projectedSourceDivergenceL2 (ProjectedSourceCoefficients.ofReal
          (fun i j x => a n x i j) (ha n) L (hL n)) (projectionFullSchwartz (z n))‖ ≤ C) :
    ∀ L : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : ℕ → CoordinateSpace → Tensor2) (ha : ∀ n, SmoothCoordinateComponents (a n))
        (hL : ∀ n i j, LipschitzWith L (fun x => a n x i j)),
        (∀ n, a n =ᶠ[𝓝ˢ K] G n) → ∀ n,
          ‖projectedSourceDivergenceL2 (ProjectedSourceCoefficients.ofReal
            (fun i j x => a n x i j) (ha n) L (hL n)) (projectionFullSchwartz (z n))‖ ≤ C := by
  intro L
  let E (n : ℕ) := { a : CoordinateSpace → Tensor2 // SmoothCoordinateComponents a ∧
    (∀ i j, LipschitzWith L (fun x => a x i j)) ∧ a =ᶠ[𝓝ˢ K] G n }
  let coeff (n : ℕ) (a : E n) := ProjectedSourceCoefficients.ofReal (fun i j x => a.val x i j)
    a.property.1 L a.property.2.1
  let value (n : ℕ) (a : E n) := ‖projectedSourceDivergenceL2 (coeff n a) (projectionFullSchwartz (z n))‖
  obtain ⟨H, _, hEstimate⟩ := exists_projectedSourceDivergenceL2_bound
  have row (n : ℕ) (b : E n) : BddAbove (range (value n)) := by
    refine ⟨‖projectionFullL2 (projectedSourceQ (coeff n b) (z n))‖ +
      H * (L : ℝ) * projectedSourceGradientMass (z n), ?_⟩
    rintro _ ⟨a, rfl⟩
    have heq := projectedSourceQ_eq_of_agreement_on_support K (z n) (hz n) (coeff n a) (coeff n b)
      (by
        intro i j x hx
        have ha := (a.property.2.2.filter_mono (nhds_le_nhdsSet hx)).eq_of_nhds
        have hb := (b.property.2.2.filter_mono (nhds_le_nhdsSet hx)).eq_of_nhds
        change (a.val x i j : ℂ) = (b.val x i j : ℂ)
        rw [ha, hb])
    simpa only [value, heq] using hEstimate (coeff n a) (z n)
  obtain ⟨C, hC, hBound⟩ := uniform_bound_of_bounded_selections value row (fun a =>
    hSource (fun n => (a n).val) (fun n => (a n).property.1) L
      (fun n => (a n).property.2.1) (fun n => (a n).property.2.2))
  exact ⟨C, hC, fun a ha hL hInv => hBound (fun n => ⟨a n, ha n, hL n, hInv n⟩)⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- In the chart at `c`, the original cutoff fluctuation has all the projected norm limits.
For each Lipschitz bound, one whole-space divergence bound works for every smooth
extension that agrees with the chart inverse near the cutoff support. -/
theorem exists_intrinsicChartProjectedField_norms_and_uniform_source
    (r : ManifoldMetric.Metric (M := M))
    (g : ℕ → ManifoldBilinear.Field (M := M)) (g₀ : ManifoldBilinear.Field (M := M))
    (hg : ∀ n, ManifoldBilinear.IsSmooth (g n)) (hg₀ : ManifoldBilinear.IsSmooth g₀)
    (hs : ∀ n, ManifoldBilinear.IsSymmetric (g n))
    (hND : ∀ n, ManifoldBilinear.IsNondegenerate (g n)) (hND₀ : ManifoldBilinear.IsNondegenerate g₀)
    (hVac : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (hconv : ManifoldMetricSequence.LocallyUniformlyConverges r g g₀)
    (hDh : AuxiliaryAdmissibility.CompactDhBound r g₀ g)
    (c : M) (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχU : tsupport χ ⊆ (chartAt CoordinateSpace c).target) :
    let G n := metricComponents (coordinateBilinear (g n) c)
    let G₀ := metricComponents (coordinateBilinear g₀ c)
    ∃ z : ℕ → ProjectionSchwartzMatrix,
      (∀ n x i j, z n i j x = ((χ x * (G n x i j - G₀ x i j) : ℝ) : ℂ)) ∧
      ProjectedFieldNormLimits (fun n => projectionFullSchwartz (z n)) ∧
      ∀ L : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : ℕ → CoordinateSpace → Tensor2) (ha : ∀ n, SmoothCoordinateComponents (a n))
          (hL : ∀ n i j, LipschitzWith L (fun x => a n x i j)),
          (∀ n, a n =ᶠ[𝓝ˢ (tsupport χ)] projectedChartInverse (G n)) →
          ∀ n, ‖projectedSourceDivergenceL2 (ProjectedSourceCoefficients.ofReal
            (fun i j x => a n x i j) (ha n) L (hL n)) (projectionFullSchwartz (z n))‖ ≤ C := by
  dsimp only
  obtain ⟨z, hz, hNorm⟩ := exists_intrinsicChartProjectedField_norms r g g₀ hg hg₀ hND₀
    hconv hDh c χ hχ hc hχU
  refine ⟨z, hz, hNorm, projectedSource_uniform_extension_bound (tsupport χ) _ z ?_ ?_⟩
  · intro n i j
    apply closure_minimal _ isClosed_closure
    intro x hx
    apply subset_tsupport χ
    intro hzero
    apply hx
    rw [hz n x i j, hzero, zero_mul, Complex.ofReal_zero]
  intro a ha L hL hInv
  obtain ⟨R, hR, C, hC, hBound⟩ := exists_projectedVacuumDivergenceL2_of_intrinsic r g g₀
    hg hg₀ hs hND hND₀ hVac hconv hDh c χ hχ hc hχU a ha L hL hInv
  refine ⟨C, hC, fun n => ?_⟩
  have he : localizedMetricSchwartz (R.metric n) R.background χ hχ hc (R.metric_smooth n)
      R.background_smooth = z n := by
    funext i j
    ext x
    exact (hR n i j x).trans (hz n x i j).symm
  rw [← he]
  exact hBound n

end Burnett.P01
