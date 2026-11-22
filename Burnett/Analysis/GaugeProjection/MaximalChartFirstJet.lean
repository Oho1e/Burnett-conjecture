import Burnett.Geometry.MaximalChart.MetricJet
import Burnett.Geometry.MaximalChart.UniformMetric
import Burnett.Analysis.GaugeProjection.IntrinsicChartProjectedSource

set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable section

namespace Burnett.Geometry.MaximalChart

open Set Filter MeasureTheory Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ChartVolume ManifoldMetric ManifoldMetricTransition
open ManifoldBilinear ManifoldMetricSequence ConnectionCoordinateChange
open scoped Manifold ContDiff Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem transformedJet_continuous :
    Continuous (fun z : Matrix Index Index ℝ × Tensor2 × FirstJet × Connection =>
      transformedJet z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  apply continuous_pi
  intro b
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [transformedJet, transformedMetricDerivative, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.sum_apply, Pi.smul_apply, smul_eq_mul, connectionMatrix]
  fun_prop

omit [IsManifold Model ∞ M] in
private theorem transform_continuousOn (c d : AtlasChart M) :
    ContinuousOn (fun z : CoordinateSpace × Tensor2 × FirstJet =>
      transformedJet (derivativeMatrix (fderiv ℝ (c.transition d) z.1)) z.2.1 z.2.2 (fixedHessian c d z.1))
      ((c.transition d).source ×ˢ univ) := by
  let e := c.transition d
  have hA : ContinuousOn (fun x => derivativeMatrix (fderiv ℝ e x)) e.source := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    exact fun j => (fixedJacobian_entry_smooth c d i j).continuousOn
  have hH : ContinuousOn (fixedHessian c d) e.source := by
    have hF : ContDiffOn ℝ ∞ (fderiv ℝ e) e.source :=
      (c.smooth_transition d).fderiv_of_isOpen e.open_source (by simp)
    have hF₂ : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ e)) e.source :=
      hF.fderiv_of_isOpen e.open_source (by simp)
    apply continuousOn_pi.mpr
    intro a
    apply continuousOn_pi.mpr
    intro b
    apply continuousOn_pi.mpr
    intro k
    exact (PiLp.continuous_apply 2 (fun _ : Index => ℝ) a).comp_continuousOn
      ((hF₂.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const)
  let U := e.source ×ˢ (univ : Set (Tensor2 × FirstJet))
  have hp : MapsTo (Prod.fst : CoordinateSpace × Tensor2 × FirstJet → _) U e.source := fun _ hz => hz.1
  have hArgs : ContinuousOn (fun z : CoordinateSpace × Tensor2 × FirstJet =>
      (derivativeMatrix (fderiv ℝ e z.1), z.2.1, z.2.2, fixedHessian c d z.1)) U :=
    (hA.comp continuous_fst.continuousOn hp).prodMk ((continuous_fst.comp continuous_snd).continuousOn.prodMk
      (((continuous_snd.comp continuous_snd).continuousOn).prodMk (hH.comp continuous_fst.continuousOn hp)))
  exact Continuous.comp_continuousOn' (s := U)
    (g := fun z : Matrix Index Index ℝ × Tensor2 × FirstJet × Connection =>
      transformedJet z.1 z.2.1 z.2.2.1 z.2.2.2)
    (f := fun z : CoordinateSpace × Tensor2 × FirstJet =>
      (derivativeMatrix (fderiv ℝ e z.1), z.2.1, z.2.2, fixedHessian c d z.1))
    transformedJet_continuous hArgs

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

private theorem uniform_values_on_compact {T : Type*} [NormedAddCommGroup T]
    (g : ℕ → CoordinateSpace → T) (g₀ : CoordinateSpace → T) {K : Set CoordinateSpace}
    (hK : IsCompact K) (hg : ∀ n, ContinuousOn (g n) K) (hg₀ : ContinuousOn g₀ K)
    (hu : TendstoUniformlyOn g g₀ atTop K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ K → ‖g n x‖ ≤ C := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hg₀
  obtain ⟨N,hN⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hu 1 zero_lt_one)
  choose b hb hbound using fun n => (hK.image_of_continuousOn (hg n)).isBounded.exists_pos_norm_le
  have hsum : 0 ≤ ∑ n ∈ Finset.range N, b n := Finset.sum_nonneg (fun n _ => (hb n).le)
  refine ⟨1 + max B 0 + ∑ n ∈ Finset.range N, b n, by positivity, fun n x hx => ?_⟩
  by_cases hn : N ≤ n
  · apply le_trans _ (le_add_of_nonneg_right hsum)
    apply (norm_le_norm_sub_add (g n x) (g₀ x)).trans
    apply add_le_add _ ((hB x hx).trans (le_max_left _ _))
    simpa only [← dist_eq_norm, dist_comm] using (hN n hn x hx).le
  · have hbmax := Finset.single_le_sum (fun i (_ : i ∈ Finset.range N) => (hb i).le)
        (Finset.mem_range.mpr (not_le.mp hn))
    exact (hbound n _ (mem_image_of_mem _ hx)).trans (hbmax.trans (le_add_of_nonneg_left (by positivity)))

omit [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
private theorem fixedForm_preferredJet (B : Field (M := M)) (p : M) {x : CoordinateSpace}
    (hx : x ∈ (chartAt CoordinateSpace p).target) :
    coordinateJet (metricComponents (fixedForm B (.atPoint p))) x =
      coordinateJet (metricComponents (coordinateBilinear B p)) x := by
  funext b i j
  have he : (fun y => metricComponents (fixedForm B (.atPoint p)) y i j) =ᶠ[𝓝 x]
      (fun y => metricComponents (coordinateBilinear B p) y i j) := by
    filter_upwards [(chartAt CoordinateSpace p).open_target.mem_nhds hx] with y hy
    exact congrFun (congrFun (fixedForm_eq_preferred_components B p hy) i) j
  exact congrArg (fun f : CoordinateSpace →L[ℝ] ℝ => f _) he.fderiv_eq

private theorem fixedForm_firstJet_bound_on_overlap
    (r : Metric (M := M)) (g : ℕ → Field (M := M)) (B : Field (M := M))
    (hg : ∀ n, IsSmooth (g n)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (p : M) {K : Set CoordinateSpace} (hK : IsCompact K)
    (hKU : K ⊆ (c.transition (.atPoint p)).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ K → ‖coordinateJet (metricComponents (fixedForm (g n) c)) x‖ ≤ C := by
  let d := AtlasChart.atPoint p
  let e := c.transition d
  let G n := metricComponents (coordinateBilinear (g n) p)
  let G₀ := metricComponents (coordinateBilinear B p)
  have hI : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKU)
  have hIt : e '' K ⊆ (chartAt CoordinateSpace p).target :=
    image_subset_iff.mpr (fun _ hx => (e.mapsTo (hKU hx)).1)
  obtain ⟨J, _, hJ⟩ := Burnett.P01.exists_coordinateMetricFirstJet_bound_of_intrinsic
    r g B hg hB hn hconv hb p (e '' K) hI hIt
  have hCon (F : Field (M := M)) (hF : IsSmooth F) :
      ContinuousOn (metricComponents (coordinateBilinear F p)) (e '' K) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    exact fun j => ((contDiffOn_metricComponents F hF p i j).continuousOn.mono hIt)
  obtain ⟨D, _, hD⟩ := uniform_values_on_compact G G₀ hI (fun n => hCon (g n) (hg n)) (hCon B hB)
    (components_uniform_of_physical_C0loc r g B hconv p _ hI hIt)
  let T (z : CoordinateSpace × Tensor2 × FirstJet) :=
    transformedJet (derivativeMatrix (fderiv ℝ e z.1)) z.2.1 z.2.2 (fixedHessian c d z.1)
  let V : Set (CoordinateSpace × Tensor2 × FirstJet) :=
    K ×ˢ Metric.closedBall 0 D ×ˢ Metric.closedBall 0 J
  have hV : IsCompact V := hK.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hT : ContinuousOn T V := (transform_continuousOn c d).mono (fun _ hz => ⟨hKU hz.1, mem_univ _⟩)
  obtain ⟨H, hH, hh⟩ := (hV.image_of_continuousOn hT).isBounded.exists_pos_norm_le
  refine ⟨H, hH.le, fun n x hx => ?_⟩
  have he : x ∈ e.source := hKU hx
  have hy : e x ∈ (chartAt CoordinateSpace p).target := (e.mapsTo he).1
  have hxI := mem_image_of_mem e hx
  have hv : (x, G n (e x), coordinateJet (G n) (e x)) ∈ V :=
    ⟨hx, Metric.mem_closedBall.mpr ((dist_zero_right _).trans_le (hD n _ hxI)),
      Metric.mem_closedBall.mpr ((dist_zero_right _).trans_le (hJ n _ hxI))⟩
  have hEq := fixedForm_jet_change (g n) (hg n) c d x he
  rw [fixedForm_eq_preferred_components (g n) p hy, fixedForm_preferredJet (g n) p hy] at hEq
  exact (congrArg norm hEq).le.trans (hh (T (x, G n (e x), coordinateJet (G n) (e x))) (mem_image_of_mem T hv))

/-- The actual first component jet is uniformly bounded on each compact subset of a maximal chart. -/
theorem fixedForm_firstJet_uniform_bound_on_compact
    (r : Metric (M := M)) (g : ℕ → Field (M := M)) (B : Field (M := M))
    (hg : ∀ n, IsSmooth (g n)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) {K : Set CoordinateSpace} (hK : IsCompact K) (hU : K ⊆ c.chart.target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ K → ‖coordinateJet (metricComponents (fixedForm (g n) c)) x‖ ≤ C := by
  classical
  let J n := coordinateJet (metricComponents (fixedForm (g n) c))
  have hgerm (x : K) : ∃ (U : Set CoordinateSpace) (A : ℝ),
      U ∈ 𝓝 (x : CoordinateSpace) ∧ 0 ≤ A ∧ ∀ n y, y ∈ U → ‖J n y‖ ≤ A := by
    let p := c.chart.symm x
    let e := c.transition (.atPoint p)
    have he : (x : CoordinateSpace) ∈ e.source := ⟨hU x.2, mem_chart_source CoordinateSpace p⟩
    obtain ⟨U, hUc, hx, hUe⟩ := exists_compact_subset e.open_source he
    obtain ⟨A, hA, hj⟩ := fixedForm_firstJet_bound_on_overlap r g B hg hB hn hconv hb c p hUc hUe
    exact ⟨U, A, mem_interior_iff_mem_nhds.mp hx, hA, hj⟩
  choose U A hu ha hj using hgerm
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx => U ⟨x,hx⟩) (fun x hx => hu ⟨x,hx⟩)
  refine ⟨∑ z ∈ t, A z, Finset.sum_nonneg (fun z _ => ha z), ?_⟩
  intro n y hy
  obtain ⟨x, hxt, hxy⟩ := mem_iUnion₂.mp (ht hy)
  exact (hj x n y hxy).trans (Finset.single_le_sum (fun z _ => ha z) hxt)

/-- Compact first-jet control for the perturbation itself, in the selected maximal chart. -/
theorem fixedJet_uniform_bound_on_compact
    (r : Metric (M := M)) (g : ℕ → Field (M := M)) (B : Field (M := M))
    (hg : ∀ n, IsSmooth (g n)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) {K : Set CoordinateSpace} (hK : IsCompact K) (hU : K ⊆ c.chart.target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ K → ‖coordinateJet
      (fun y => metricComponents (fixedForm (g n) c) y - metricComponents (fixedForm B c) y) x‖ ≤ C := by
  obtain ⟨C,hC,hJ⟩ := fixedForm_firstJet_uniform_bound_on_compact r g B hg hB hn hconv hb c hK hU
  have hBG := BackgroundConnection.continuousOn_coordinateJet (metricComponents (fixedForm B c)) c.chart.target
    c.chart.open_target (fun i j => (fixedForm_components_smooth B hB c i j).of_le (by simp))
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn (hBG.mono hU)
  refine ⟨C + max D 0, add_nonneg hC (le_max_right _ _), fun n x hx => ?_⟩
  have hmem := c.chart.open_target.mem_nhds (hU hx)
  rw [coordinateJet_sub _ _ x
    (fun i j => ((fixedForm_components_smooth (g n) (hg n) c i j).contDiffAt hmem).differentiableAt (by simp))
    (fun i j => ((fixedForm_components_smooth B hB c i j).contDiffAt hmem).differentiableAt (by simp))]
  exact (norm_sub_le _ _).trans (add_le_add (hJ n x hx) ((hD x hx).trans (le_max_left _ _)))

end Burnett.Geometry.MaximalChart
