import Burnett.Geometry.MaximalChart.MetricCoordinates
import Burnett.Geometry.ManifoldMetricSequence

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Geometry.MaximalChart

open Set Filter Function LinearMap Burnett.RicciSymbol
open Burnett.Geometry ChartVolume ConnectionDifference ManifoldMetric ManifoldMetricTransition
open scoped Manifold ContDiff Topology Matrix
open ManifoldTensorNorm ManifoldMetricSequence ManifoldBilinear CovariantTensorNorm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

variable [SecondCountableTopology M]

omit [SecondCountableTopology M] in
theorem physicalNorm2_eq_fixed (r : Metric (M := M)) (B : Field (M := M))
    (c : AtlasChart M) {x : CoordinateSpace} (hx : x ∈ c.chart.target) :
    physicalNorm2 r B (c.chart.symm x) =
      norm2 (metricComponents (fixedForm r.inner c) x) (metricComponents (fixedForm B c) x) := by
  let q := c.chart.symm x
  let d := AtlasChart.atPoint q
  have he : x ∈ (c.transition d).source := ⟨hx, mem_chart_source CoordinateSpace q⟩
  let e := c.transition d
  let A := derivativeMatrix (fderiv ℝ e x)
  have ht : e x ∈ (chartAt CoordinateSpace q).target := (e.mapsTo he).1
  have hinv : (chartAt CoordinateSpace q).symm (e x) = c.chart.symm x :=
    d.chart.left_inv he.2
  rw [fixedForm_matrix_change r.inner c d he,fixedForm_matrix_change B c d he,
      ← pullback2_eq_pullbackMetric A (metricComponents (fixedForm B d) (e x)),
      TensorCoordinateChange.norm2_pullback _ _ (fixedDerivativeMatrix_isUnit c d he),
      fixedForm_eq_preferred_components r.inner q ht,fixedForm_eq_preferred_components B q ht]
  rw [←hinv]
  exact physicalNorm2_eq_coordinate r B q ht

omit [SecondCountableTopology M] in
theorem fixedRiemannian_posDef (r : Metric (M := M)) (c : AtlasChart M)
    {x : CoordinateSpace} (hx : x ∈ c.chart.target) :
    Matrix.PosDef (metricComponents (fixedForm r.inner c) x : Matrix Index Index ℝ) := by
  let q := c.chart.symm x
  let d := AtlasChart.atPoint q
  have he : x ∈ (c.transition d).source := ⟨hx, mem_chart_source CoordinateSpace q⟩
  have ht : c.transition d x ∈ (chartAt CoordinateSpace q).target := ((c.transition d).mapsTo he).1
  rw [fixedForm_matrix_change r.inner c d he,fixedForm_eq_preferred_components r.inner q ht]
  exact TensorCoordinateChange.pullbackMetric_posDef _ _ (ManifoldMetric.coordinateMetric_posDef r q ht)
    (fixedDerivativeMatrix_isUnit c d he)

theorem fixed_components_uniform_of_physical_C0loc (r : Metric (M := M))
    (B : ℕ → Field (M := M)) (B₀ : Field (M := M)) (hconv : LocallyUniformlyConverges r B B₀)
    (c : AtlasChart M) (K : Set CoordinateSpace) (hK : IsCompact K) (hKU : K ⊆ c.chart.target) :
    TendstoUniformlyOn (fun n => metricComponents (fixedForm (B n) c)) (metricComponents (fixedForm B₀ c)) atTop K := by
  let R : CoordinateSpace → Matrix Index Index ℝ := metricComponents (fixedForm r.inner c)
  obtain ⟨C,hC,hbound⟩ := exists_uniform_norm2_control R K hK
    (fun i => (fixedForm_components_smooth r.inner (isSmooth_inner r) c i i).continuousOn.mono hKU)
    (fun x hx => fixedRiemannian_posDef r c (hKU hx))
  have hbase : IsCompact (c.chart.symm '' K) := hK.image_of_continuousOn (c.chart.continuousOn_symm.mono hKU)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hconv _ hbase) (ε/C) (div_pos hε hC)] with n hn
  intro y hy
  have hsmall : physicalNorm2 r (B n - B₀) (c.chart.symm y) < ε/C := by
    simpa only [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg (physicalNorm2_nonneg r (B n - B₀) _)] using
      hn _ (mem_image_of_mem _ hy)
  rw [dist_comm,dist_eq_norm]
  have h := hbound y hy (metricComponents (fixedForm (B n) c) y - metricComponents (fixedForm B₀ c) y)
  have heq := physicalNorm2_eq_fixed r (B n - B₀) c (hKU hy)
  change _ = norm2 (R y) (metricComponents (fixedForm (B n) c) y - metricComponents (fixedForm B₀ c) y) at heq
  rw [← heq] at h
  apply h.trans_lt
  calc
    _ < C * (ε / C) := mul_lt_mul_of_pos_left hsmall hC
    _ = ε := by field_simp

end Burnett.Geometry.MaximalChart
