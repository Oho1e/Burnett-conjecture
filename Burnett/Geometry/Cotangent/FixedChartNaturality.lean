import Burnett.Geometry.Cotangent.Core
import Burnett.Geometry.MaximalChart.MetricCoordinates
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-! Actual cotangent lifts and restricted scalar pushforwards in maximal-atlas charts. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Burnett.Geometry.FixedCotangentChart

open Bundle Filter MeasureTheory Set Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldMetric MaximalChart UnitNullCompactness
open scoped ContDiff Manifold Topology

abbrev Phase := CoordinateSpace × Covector

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The differential of the inverse fixed chart, in the tangent fiber at the represented point. -/
def inverseFrame (c : AtlasChart M) (x : M) : CoordinateSpace →L[ℝ] TangentSpace Model x :=
  mfderiv Model Model (c.chart.symm : CoordinateSpace → M) (c.chart x)

theorem inverseFrame_change (c d : AtlasChart M) (x : M)
    (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source) :
    inverseFrame d x = (inverseFrame c x).comp (fderiv ℝ (d.transition c) (d.chart x)) := by
  let y := d.chart x
  let e := d.transition c
  have hy : y ∈ e.source := by
    refine ⟨d.chart.mapsTo hd, ?_⟩
    change d.chart.symm (d.chart x) ∈ c.chart.source
    rwa [d.chart.left_inv hd]
  have hbase : e y = c.chart x := by
    change c.chart (d.chart.symm (d.chart x)) = c.chart x
    rw [d.chart.left_inv hd]
  have he : (c.chart.symm : CoordinateSpace → M) ∘ e =ᶠ[𝓝 y]
      (d.chart.symm : CoordinateSpace → M) := by
    filter_upwards [e.open_source.mem_nhds hy] with w hw
    exact c.chart.left_inv hw.2
  have hc' : MDifferentiableAt Model Model (c.chart.symm : CoordinateSpace → M) (e y) :=
    (contMDiffAt_symm_of_mem_maximalAtlas c.compatible (e.mapsTo hy).1).mdifferentiableAt (by simp)
  have he' : MDifferentiableAt Model Model e y :=
    ((d.smooth_transition c).contDiffAt (e.open_source.mem_nhds hy)).differentiableAt
      (by simp) |>.mdifferentiableAt
  change mfderiv Model Model (d.chart.symm : CoordinateSpace → M) y =
    (mfderiv Model Model (c.chart.symm : CoordinateSpace → M) (c.chart x)).comp (fderiv ℝ e y)
  calc
    _ = mfderiv Model Model ((c.chart.symm : CoordinateSpace → M) ∘ e) y :=
      (he.mfderiv_eq (I := Model) (I' := Model)).symm
    _ = (mfderiv Model Model (c.chart.symm : CoordinateSpace → M) (e y)).comp
        (mfderiv Model Model e y) := mfderiv_comp y hc' he'
    _ = _ := by rw [mfderiv_eq_fderiv, hbase]

/-- The actual covector expressed in the fixed chart, as a linear form on chart vectors. -/
def fixedCovector (c : AtlasChart M) (p : CotangentBundle M) : CotangentModel :=
  p.2.comp (inverseFrame c p.proj)

/-- Coordinates of the same actual cotangent point on the chart source. -/
def fixedChartPhase (c : AtlasChart M) (p : CotangentBundle M) : Phase := by
  classical
  exact if p.proj ∈ c.chart.source then
    (c.chart p.proj, fun i => fixedCovector c p (coordinateBasis i))
  else (0, 0)

theorem fixedChartPhase_of_mem (c : AtlasChart M) (p : CotangentBundle M)
    (hp : p.proj ∈ c.chart.source) :
    fixedChartPhase c p = (c.chart p.proj, fun i => fixedCovector c p (coordinateBasis i)) :=
  if_pos hp

private theorem covectorCLM_basis_values (L : CotangentModel) :
    covectorCLM (fun i => L (coordinateBasis i)) = L := by
  have h : (covectorCLM (fun i => L (coordinateBasis i))).toLinearMap = L.toLinearMap :=
    coordinateBasis.ext fun i => covectorCLM_apply_basis _ i
  exact ContinuousLinearMap.ext fun v => DFunLike.congr_fun h v

theorem fixedChartPhase_preferred (c : M) (p : CotangentBundle M)
    (hp : p.proj ∈ (chartAt CoordinateSpace c).source) :
    fixedChartPhase (.atPoint c) p = (chartAt CoordinateSpace c p.proj, cotangentCoords c p) := by
  rw [fixedChartPhase_of_mem _ p hp]
  apply Prod.ext
  · rfl
  funext i
  change fixedCovector (.atPoint c) p (coordinateBasis i) = cotangentCoords c p i
  rw [cotangentCoords, cotangentTrivialization_apply, ChartDifferential.tangentFrame_eq_mfderiv_symm c _ hp]
  rfl

/-- The cotangent lift of the fixed transition uses the transpose of the reverse Jacobian. -/
def fixedPhaseTransition (c d : AtlasChart M) (z : Phase) : Phase :=
  let y := c.transition d z.1
  let A := fderiv ℝ (d.transition c) y
  (y, fun i => covectorCLM z.2 (A (coordinateBasis i)))

/-- The forward transition is evaluated on the part of the c-coordinate domain common to d. -/
def phaseOverlap (c d : AtlasChart M) : Set Phase := Prod.fst ⁻¹' (c.transition d).source

omit [IsManifold Model ∞ M] in
theorem isOpen_phaseOverlap (c d : AtlasChart M) : IsOpen (phaseOverlap c d) :=
  (c.transition d).open_source.preimage continuous_fst

theorem fixedChartPhase_mem_overlap (c d : AtlasChart M) (p : CotangentBundle M)
    (hc : p.proj ∈ c.chart.source) (hd : p.proj ∈ d.chart.source) :
    fixedChartPhase c p ∈ phaseOverlap c d := by
  rw [fixedChartPhase_of_mem c p hc]
  change c.chart p.proj ∈ (c.transition d).source
  refine ⟨c.chart.mapsTo hc, ?_⟩
  change c.chart.symm (c.chart p.proj) ∈ d.chart.source
  rwa [c.chart.left_inv hc]

/-- The two fixed chart coordinates of one actual covector are related by the cotangent lift. -/
theorem fixedPhaseTransition_fixedChartPhase (c d : AtlasChart M) (p : CotangentBundle M)
    (hc : p.proj ∈ c.chart.source) (hd : p.proj ∈ d.chart.source) :
    fixedPhaseTransition c d (fixedChartPhase c p) = fixedChartPhase d p := by
  rw [fixedChartPhase_of_mem c p hc, fixedChartPhase_of_mem d p hd]
  unfold fixedPhaseTransition
  have hbase : c.transition d (c.chart p.proj) = d.chart p.proj := by
    change d.chart (c.chart.symm (c.chart p.proj)) = _
    rw [c.chart.left_inv hc]
  simp only [hbase, covectorCLM_basis_values]
  apply Prod.ext
  · rfl
  funext i
  simp only [fixedCovector, ContinuousLinearMap.comp_apply]
  rw [inverseFrame_change c d p.proj hc hd]
  rfl

omit [IsManifold Model ∞ M] in
theorem continuousOn_fixedPhaseTransition (c d : AtlasChart M) :
    ContinuousOn (fixedPhaseTransition c d) (phaseOverlap c d) := by
  let U := phaseOverlap c d
  let e := c.transition d
  let e' := d.transition c
  have hsymm : e.symm = e' := by
    simp only [e, e', AtlasChart.transition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  have hbase : ContinuousOn (fun z : Phase => e z.1) U :=
    e.continuousOn.comp continuous_fst.continuousOn (fun _ hz => hz)
  have hderiv : ContinuousOn (fderiv ℝ e') e'.source :=
    (d.smooth_transition c).continuousOn_fderiv_of_isOpen e'.open_source (by simp)
  have hD : ContinuousOn (fun z : Phase => fderiv ℝ e' (e z.1)) U :=
    hderiv.comp hbase (fun z hz => by rw [← hsymm]; exact e.mapsTo hz)
  apply hbase.prodMk
  apply continuousOn_pi.mpr
  intro i
  exact (continuous_covectorCLM.comp_continuousOn continuous_snd.continuousOn).clm_apply
    (hD.clm_apply continuous_const.continuousOn)

theorem continuousOn_fixedChartPhase (c : AtlasChart M) :
    ContinuousOn (fixedChartPhase c) ((fun p : CotangentBundle M => p.proj) ⁻¹' c.chart.source) := by
  intro p hp
  let q := p.proj
  let b : AtlasChart M := .atPoint q
  let U := (fun a : CotangentBundle M => a.proj) ⁻¹' (b.chart.source ∩ c.chart.source)
  let f := fun a : CotangentBundle M => (b.chart a.proj, cotangentCoords q a)
  have hU : IsOpen U := (b.chart.open_source.inter c.chart.open_source).preimage
    continuous_cotangent_projection
  have hpU : p ∈ U := ⟨mem_chart_source CoordinateSpace q, hp⟩
  have hf : ContinuousOn f U := by
    apply (b.chart.continuousOn.comp continuous_cotangent_projection.continuousOn
      (fun _ ha => ha.1)).prodMk
    exact (continuousOn_cotangentCoords q).mono (fun _ ha => ha.1)
  have hmaps : MapsTo f U (phaseOverlap b c) := fun a ha => by
    rw [show f a = fixedChartPhase b a from (fixedChartPhase_preferred q a ha.1).symm]
    exact fixedChartPhase_mem_overlap b c a ha.1 ha.2
  have hcomp := (continuousOn_fixedPhaseTransition b c).comp hf hmaps
  have heq : EqOn (fixedChartPhase c) (fixedPhaseTransition b c ∘ f) U := fun a ha => by
    change fixedChartPhase c a = fixedPhaseTransition b c (f a)
    rw [show f a = fixedChartPhase b a from (fixedChartPhase_preferred q a ha.1).symm,
      fixedPhaseTransition_fixedChartPhase b c a ha.1 ha.2]
  exact ((hcomp.congr heq).continuousAt (hU.mem_nhds hpU)).continuousWithinAt

section Measures

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The reference chart convention, extended by zero away from the actual chart source. -/
theorem measurable_fixedChartPhase_comp (lift : X → CotangentBundle M) (hlift : Continuous lift)
    (c : AtlasChart M) : Measurable (fixedChartPhase c ∘ lift) := by
  classical
  let f := fixedChartPhase c ∘ lift
  let V := (fun a : X => (lift a).proj) ⁻¹' c.chart.source
  have hV : MeasurableSet V :=
    (c.chart.open_source.preimage (continuous_cotangent_projection.comp hlift)).measurableSet
  have hf : ContinuousOn f V :=
    (continuousOn_fixedChartPhase c).comp hlift.continuousOn (fun _ ha => ha)
  have heq : V.piecewise f (fun _ => (0, 0)) = f := by
    funext a
    by_cases ha : a ∈ V
    · exact piecewise_eq_of_mem V f _ ha
    · rw [piecewise_eq_of_notMem V f _ ha]
      exact (if_neg ha).symm
  rw [← show V.piecewise f (fun _ => (0, 0)) = fixedChartPhase c ∘ lift from heq]
  exact hf.measurable_piecewise continuous_const.continuousOn hV

/-- Fix the incoming measure. Both chart measures are the pushforwards of its one restriction
to the actual base overlap, and the change of coordinates maps the first to the second. -/
theorem fixedChart_pushforwards (lift : X → CotangentBundle M) (hlift : Continuous lift)
    (μ : Measure X) (c d : AtlasChart M) :
    let ν := μ.restrict ((fun a => (lift a).proj) ⁻¹' (c.chart.source ∩ d.chart.source))
    let μc := Measure.map (fixedChartPhase c ∘ lift) ν
    let μd := Measure.map (fixedChartPhase d ∘ lift) ν
    AEMeasurable (fixedChartPhase c ∘ lift) ν ∧
      AEMeasurable (fixedChartPhase d ∘ lift) ν ∧
      AEMeasurable (fixedPhaseTransition c d) μc ∧
      Measure.map (fixedPhaseTransition c d) μc = μd := by
  classical
  intro ν μc μd
  let U := phaseOverlap c d
  have hU : MeasurableSet U := (isOpen_phaseOverlap c d).measurableSet
  have hO : MeasurableSet ((fun a : X => (lift a).proj) ⁻¹' (c.chart.source ∩ d.chart.source)) :=
    ((c.chart.open_source.inter d.chart.open_source).preimage
      (continuous_cotangent_projection.comp hlift)).measurableSet
  have hc : AEMeasurable (fixedChartPhase c ∘ lift) ν :=
    (measurable_fixedChartPhase_comp lift hlift c).aemeasurable
  have hd : AEMeasurable (fixedChartPhase d ∘ lift) ν :=
    (measurable_fixedChartPhase_comp lift hlift d).aemeasurable
  have hbaseAE : ∀ᵐ a ∂ν, (lift a).proj ∈ c.chart.source ∩ d.chart.source := ae_restrict_mem hO
  have hphaseAE : ∀ᵐ z ∂μc, z ∈ U :=
    (ae_map_iff hc hU).2
      (hbaseAE.mono (fun a ha => fixedChartPhase_mem_overlap c d (lift a) ha.1 ha.2))
  have htransition : AEMeasurable (fixedPhaseTransition c d) μc :=
    ⟨U.piecewise (fixedPhaseTransition c d) (fun _ => (0, 0)),
      (continuousOn_fixedPhaseTransition c d).measurable_piecewise continuous_const.continuousOn hU,
      hphaseAE.mono fun _ hz => (piecewise_eq_of_mem U _ _ hz).symm⟩
  refine ⟨hc, hd, htransition, ?_⟩
  change Measure.map (fixedPhaseTransition c d) (Measure.map _ ν) = _
  rw [AEMeasurable.map_map_of_aemeasurable htransition hc]
  exact Measure.map_congr (hbaseAE.mono
    (fun a ha => fixedPhaseTransition_fixedChartPhase c d (lift a) ha.1 ha.2))

end Measures

end Burnett.Geometry.FixedCotangentChart
