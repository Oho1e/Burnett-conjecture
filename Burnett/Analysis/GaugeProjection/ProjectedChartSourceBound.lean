import Burnett.Analysis.GaugeProjection.ProjectedChartRepresentatives
import Burnett.Analysis.GaugeProjection.UniformLocalizedMetricJets

set_option autoImplicit false
set_option maxHeartbeats 3600000

noncomputable section

namespace Burnett.P01

open Set Filter MeasureTheory
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.CurvatureDifference
open scoped Topology ContDiff NNReal BigOperators Matrix.Norms.Elementwise

private theorem coordinateMetric_continuousOn {U : Set CoordinateSpace} {g : CoordinateSpace → Tensor2}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) U) : ContinuousOn g U :=
  continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => (hg i j).continuousOn

private theorem coordinateJet_continuous {g : CoordinateSpace → Tensor2}
    (hg : SmoothCoordinateComponents g) : Continuous (coordinateJet g) :=
  continuous_pi fun d => continuous_pi fun i => continuous_pi fun j =>
    ((hg i j).continuous_fderiv (by simp)).clm_apply continuous_const

private theorem coordinateSecondMetricJet_continuous {g : CoordinateSpace → Tensor2}
    (hg : SmoothCoordinateComponents g) : Continuous (coordinateSecondMetricJet g) := by
  refine continuous_pi fun d => continuous_pi fun a => continuous_pi fun i => continuous_pi fun j => ?_
  have h₁ : ContDiff ℝ ∞ (fun x => coordinateJet g x a i j) :=
    ((hg i j).fderiv_right (by simp)).clm_apply contDiff_const
  exact (h₁.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem exists_compact_uniform_coordinateDifference_bound
    (K : Set CoordinateSpace) (hK : IsCompact K) (g : ℕ → CoordinateSpace → Tensor2)
    (g₀ : CoordinateSpace → Tensor2) (hg : ∀ n, ContinuousOn (g n) K)
    (hg₀ : ContinuousOn g₀ K) (hConv : TendstoUniformlyOn g g₀ atTop K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ K → ‖g n x - g₀ x‖ ≤ C := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hConv 1 zero_lt_one)
  choose c hc using fun n => hK.exists_bound_of_continuousOn ((hg n).sub hg₀)
  let C := 1 + ∑ n ∈ Finset.range N, max (c n) 0
  have hsum : 0 ≤ ∑ n ∈ Finset.range N, max (c n) 0 :=
    Finset.sum_nonneg fun n _ => le_max_right _ _
  refine ⟨C, by positivity, fun n x hx => ?_⟩
  by_cases hn : N ≤ n
  · exact (by simpa only [dist_eq_norm] using (dist_comm _ _).trans_lt (hN n hn x hx) :
      ‖g n x - g₀ x‖ < 1).le.trans (le_add_of_nonneg_right hsum)
  · have hn' := Finset.mem_range.mpr (lt_of_not_ge hn)
    exact (hc n x hx).trans ((le_max_left _ _).trans
      ((Finset.single_le_sum (fun m _ => le_max_right (c m) 0) hn').trans
        (le_add_of_nonneg_left zero_le_one)))

private theorem exists_compact_uniform_projectedChartInverse_bound
    (K : Set CoordinateSpace) (hK : IsCompact K) (g : ℕ → CoordinateSpace → Tensor2)
    (g₀ : CoordinateSpace → Tensor2) (hg : ∀ n, ContinuousOn (g n) K)
    (hg₀ : ContinuousOn g₀ K) (hDet : ∀ n x, x ∈ K → (Matrix.of (g n x)).det ≠ 0)
    (hDet₀ : ∀ x ∈ K, (Matrix.of (g₀ x)).det ≠ 0)
    (hConv : TendstoUniformlyOn g g₀ atTop K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ K → ‖projectedChartInverse (g n) x‖ ≤ C := by
  let F : Tensor2 → Matrix Index Index ℝ := Matrix.of
  have hi : Isometry F := Isometry.of_dist_eq fun x y => rfl
  have hConv' : TendstoUniformlyOn (fun n x => F (g n x)) (fun x => F (g₀ x)) atTop K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hConv ε hε] with n hn x hx
    simpa only [hi.dist_eq] using hn x hx
  obtain ⟨C, hC, bound⟩ := exists_compact_uniform_metricInverse_bound K hK
    (fun n x => F (g n x)) (fun x => F (g₀ x)) (fun n => hi.continuous.comp_continuousOn (hg n))
    (hi.continuous.comp_continuousOn hg₀) hDet hDet₀ hConv'
  exact ⟨C, hC, fun n x hx => bound n x hx⟩

/-- The whole-space projected source from the original open-chart data.
The representatives agree on a neighborhood of the localization set, and the
Schwartz input is exactly the original zero-extended cutoff fluctuation. -/
theorem exists_projectedVacuumDivergenceL2_of_openChart
    (U : Set CoordinateSpace) (hU : IsOpen U)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ U)
    (g inv : ℕ → CoordinateSpace → Tensor2) (g₀ : CoordinateSpace → Tensor2)
    (hg : ∀ n i j, ContDiffOn ℝ ∞ (fun x => g n x i j) U)
    (hg₀ : ∀ i j, ContDiffOn ℝ ∞ (fun x => g₀ x i j) U)
    (hs : ∀ n x, x ∈ U → IsSymmetricTensor (g n x))
    (hDet : ∀ n x, x ∈ U → (Matrix.of (g n x)).det ≠ 0)
    (hDet₀ : ∀ x ∈ U, (Matrix.of (g₀ x)).det ≠ 0)
    (hi : ∀ n, SmoothCoordinateComponents (inv n)) (L : ℝ≥0)
    (hL : ∀ n a b, LipschitzWith L (fun x => inv n x a b))
    (hInv : ∀ n, inv n =ᶠ[𝓝ˢ (tsupport χ)] projectedChartInverse (g n))
    (hVac : ∀ n x, x ∈ tsupport χ → ∀ i j, coordinateRicci
      (fun y => christoffel (projectedChartInverse (g n) y) (coordinateJet (g n) y)) x i j = 0)
    (hConv : TendstoUniformlyOn g g₀ atTop (tsupport χ))
    (D : ℝ) (hD : ∀ n x, x ∈ tsupport χ → ‖coordinateJet (g n) x‖ ≤ D) :
    ∃ R : ProjectedChartRepresentatives g inv g₀ (tsupport χ),
      let z (n : ℕ) := localizedMetricSchwartz (R.metric n) R.background χ hχ hc
        (R.metric_smooth n) R.background_smooth
      (∀ n i j x, z n i j x = ((χ x * (g n x i j - g₀ x i j) : ℝ) : ℂ)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
        ‖projectedSourceDivergenceL2 (ProjectedSourceCoefficients.ofReal
          (fun a b x => inv n x a b) (hi n) L (hL n)) (projectionFullSchwartz (z n))‖ ≤ C := by
  let K := tsupport χ
  obtain ⟨R⟩ := exists_projectedChartRepresentatives hc hU hχU g inv g₀ hg hg₀ hs hDet hInv hVac
  have hG (n : ℕ) : ContinuousOn (g n) K := (coordinateMetric_continuousOn (hg n)).mono hχU
  have hG₀ : ContinuousOn g₀ K := (coordinateMetric_continuousOn hg₀).mono hχU
  have e (n : ℕ) (x : CoordinateSpace) (hx : x ∈ K) :
      R.metric n =ᶠ[𝓝 x] g n := (R.metric_agrees n).filter_mono (nhds_le_nhdsSet hx)
  have e₀ (x : CoordinateSpace) (hx : x ∈ K) :
      R.background x = g₀ x := ((R.background_agrees).filter_mono (nhds_le_nhdsSet hx)).eq_of_nhds
  obtain ⟨I, hI, hIB⟩ := exists_compact_uniform_projectedChartInverse_bound K hc g g₀ hG hG₀
    (fun n x hx => hDet n x (hχU hx)) (fun x hx => hDet₀ x (hχU hx)) hConv
  obtain ⟨G, hGnn, hGB⟩ := exists_compact_uniform_coordinateDifference_bound K hc g g₀ hG hG₀ hConv
  obtain ⟨G₁, hG₁⟩ := hc.exists_bound_of_continuousOn (coordinateJet_continuous R.background_smooth).continuousOn
  obtain ⟨G₂, hG₂⟩ := hc.exists_bound_of_continuousOn
    (coordinateSecondMetricJet_continuous R.background_smooth).continuousOn
  let M := I + G + max D 0 + max G₁ 0 + max G₂ 0
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hA (n : ℕ) (x : CoordinateSpace) (hx : x ∈ K) : ‖inv n x‖ ≤ M := by
    rw [((hInv n).filter_mono (nhds_le_nhdsSet hx)).eq_of_nhds]
    exact (hIB n x hx).trans (by dsimp [M]; linarith [le_max_right D 0, le_max_right G₁ 0, le_max_right G₂ 0])
  have hH (n : ℕ) (x : CoordinateSpace) (hx : x ∈ K) :
      ‖R.metric n x - R.background x‖ ≤ M := by
    rw [(e n x hx).eq_of_nhds, e₀ x hx]
    exact (hGB n x hx).trans (by dsimp [M]; linarith [le_max_right D 0, le_max_right G₁ 0, le_max_right G₂ 0])
  have hF (n : ℕ) (x : CoordinateSpace) (hx : x ∈ K) : ‖coordinateJet (R.metric n) x‖ ≤ M := by
    rw [projectedChart_coordinateJet_eq_of_eventuallyEq (e n x hx)]
    exact (hD n x hx).trans (by
      dsimp [M]
      linarith [le_max_left D 0, le_max_right G₁ 0, le_max_right G₂ 0])
  have hF₀ (x : CoordinateSpace) (hx : x ∈ K) : ‖coordinateJet R.background x‖ ≤ M :=
    (hG₁ x hx).trans (by dsimp [M]; linarith [le_max_right D 0, le_max_left G₁ 0, le_max_right G₂ 0])
  have hF₂ (x : CoordinateSpace) (hx : x ∈ K) : ‖coordinateSecondMetricJet R.background x‖ ≤ M :=
    (hG₂ x hx).trans (by dsimp [M]; linarith [le_max_right D 0, le_max_right G₁ 0, le_max_left G₂ 0])
  obtain ⟨B, _, hb⟩ := exists_compact_localizedSourceJets_bound K R.metric inv R.background M hM
    (fun n x _ i j => (R.metric_smooth n i j).differentiable (by simp) x)
    (fun n x _ i j => (hi n i j).differentiable (by simp) x)
    R.inverse_left R.inverse_right hA hH hF hF₀ hF₂
  have est := exists_wholeSpace_projectedVacuumDivergenceL2_bound inv R.metric R.background
    χ hχ hc hi R.metric_smooth R.background_smooth B L hL R.inverse_symmetric R.metric_symmetric R.vacuum hb
  refine ⟨R, ?_, est⟩
  intro n i j x
  change ((χ x * (R.metric n x i j - R.background x i j) : ℝ) : ℂ) = _
  by_cases hx : x ∈ K
  · rw [(e n x hx).eq_of_nhds, e₀ x hx]
  · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]

end Burnett.P01
