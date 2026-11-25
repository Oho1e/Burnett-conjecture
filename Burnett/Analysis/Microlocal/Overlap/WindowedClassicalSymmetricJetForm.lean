import Burnett.Analysis.Microlocal.Overlap.SymmetricJetWindowPrincipalChange
import Burnett.Analysis.Microlocal.Overlap.SymmetricJetFormCovarianceTrace
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartGeometricBridge

/-! The actual form with compact-window symbols and one cosphere contraction. -/
set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 6300000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Matrix Filter MeasureTheory Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase fixedChartPhase_of_mem)
open Burnett.F07.IntrinsicAmplitudeCoordinates (components)
open Burnett.RicciSymbol (Index)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.AtlasOverlapKernel
open scoped BigOperators ComplexConjugate ComplexOrder ContDiff Manifold Matrix Topology

open private coordinate_in_transition transition_at_coordinate
  from Burnett.Analysis.Microlocal.Overlap.AtlasCovectorGramNaturality

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold Model ∞ M] [MeasurableSpace M] [BorelSpace M]

/-- The classical full symbol and bounded realization can be chosen separately
on every compact chart window. Its principal value on that window represents
the fixed chart principal of the actual global form. -/
structure WindowedClassicalSymmetricJetForm
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B) (Q : SymmetricJetGlobalForm M) where
  principal : AtlasChart M → JetSlot → JetSlot → E → E → ℂ
  window : ∀ (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKc : K ⊆ c.chart.target),
    Nonempty (CompactSymmetricJetWindowData B hB hn Q c (principal c) K hK hKc)
  kernel : SymmetricJetPairingKernel M
  separated_action : HasSeparatedSymmetricJetKernel (ManifoldVolume.geometricMeasure B) Q kernel
  kernel_continuous : ∀ (c d : AtlasChart M) (S T : Set M), IsCompact S → IsCompact T →
    S ⊆ c.chart.source → T ⊆ d.chart.source → Disjoint S T →
    ∀ i j, ContinuousOn (uncurry (symmetricJetKernelEntry kernel c d i j)) (S ×ˢ T)

omit [T2Space M] [SecondCountableTopology M] [IsManifold Model ∞ M] [MeasurableSpace M] [BorelSpace M] in
private theorem receivingJetOverlapWeight_matrix_at_chart (c d : AtlasChart M) (x : M)
    (hc : x ∈ c.chart.source) (i j : JetSlot) :
    receivingJetOverlapWeight c d i j (c.chart x) = atlasJetTransition c d x i j := by
  rw [receivingJetOverlapWeight, transition_at_coordinate c d x hc, rawReceivingJetTransition,
    Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  rfl

/-- Evaluate the principal form at a fixed actual cosphere point. -/
def windowedClassicalFormMatrix
    {B : Field (M := M)} {hB : IsSmooth B} {hn : IsNondegenerate B}
    {Q : SymmetricJetGlobalForm M} {r : Metric (M := M)}
    (P : WindowedClassicalSymmetricJetForm B hB hn Q) (c : AtlasChart M) (p : Cosphere r) :
    Matrix JetSlot JetSlot ℂ :=
  let z := fixedChartPhase c p.val
  fun i j => P.principal c i j z.1 (WithLp.toLp 2 z.2)

/-- The principal forms of independently chosen compact localizations of the
same actual form satisfy the actual three-slot congruence. -/
theorem windowedClassicalFormMatrix_change
    {B : Field (M := M)} {hB : IsSmooth B} {hn : IsNondegenerate B}
    {Q : SymmetricJetGlobalForm M} {r : Metric (M := M)}
    (P : WindowedClassicalSymmetricJetForm B hB hn Q)
    (c d : AtlasChart M) (p : Cosphere r)
    (hc : projection p ∈ c.chart.source) (hd : projection p ∈ d.chart.source) :
    windowedClassicalFormMatrix P c p = (atlasJetTransition c d (projection p))ᴴ *
      windowedClassicalFormMatrix P d p * atlasJetTransition c d (projection p) := by
  let x := c.chart (projection p)
  let ξ := WithLp.toLp 2 (fixedChartPhase c p.val).2
  have hx : x ∈ (c.transition d).source := coordinate_in_transition c d (projection p) hc hd
  have hξ : ξ ≠ 0 := by
    intro h
    exact atlasChartUnitCovector_ne_zero c p hc (congrArg WithLp.ofLp h)
  obtain ⟨ε, hε, hBall⟩ := Metric.mem_nhds_iff.mp ((c.transition d).open_source.mem_nhds hx)
  let K := Metric.closedBall x (ε / 2)
  let L := Metric.closedBall x (ε / 4)
  have hKU : K ⊆ (c.transition d).source :=
    (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hBall
  have hLK : L ⊆ interior K :=
    (Metric.closedBall_subset_ball (by linarith : ε / 4 < ε / 2)).trans Metric.ball_subset_interior_closedBall
  have hxL : x ∈ interior L := Metric.ball_subset_interior_closedBall (Metric.mem_ball_self (by positivity))
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKc : K ⊆ c.chart.target := fun y hy => (hKU hy).1
  have hK' := hK.image_of_continuousOn ((c.transition d).continuousOn.mono hKU)
  have hK'd : c.transition d '' K ⊆ d.chart.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact ((c.transition d).mapsTo (hKU hy)).1
  obtain ⟨C⟩ := P.window c K hK hKc
  obtain ⟨D⟩ := P.window d (c.transition d '' K) hK' hK'd
  have hChange (i j : JetSlot) := compactSymmetricJetWindowData_principal_change
    B hB hn Q c d K L hK (isCompact_closedBall _ _) hLK hKU (convex_closedBall _ _)
    hKc hK' hK'd (P.principal c) (P.principal d) C D x hxL ξ hξ i j
  have hFreq : frozenChartFrequency c d hx ξ = WithLp.toLp 2 (fixedChartPhase d p.val).2 := by
    rw [← chartTransitionFrequency_eq_frozen c d hx]
    exact receivingFrequency_eq_fixedChartPhase c d p.val hc hd
  have hcBase : (fixedChartPhase c p.val).1 = x := congrArg Prod.fst (fixedChartPhase_of_mem c p.val hc)
  have hdBase : (fixedChartPhase d p.val).1 = c.transition d x := by
    rw [transition_at_coordinate c d (projection p) hc]
    exact congrArg Prod.fst (fixedChartPhase_of_mem d p.val hd)
  let U := atlasJetTransition c d (projection p)
  ext i j
  calc
    _ = P.principal c i j x ξ := by simp only [windowedClassicalFormMatrix, hcBase, ξ]
    _ = ∑ k : JetSlot, ∑ l : JetSlot, conj (U k i) * windowedClassicalFormMatrix P d p k l * U l j := by
      simpa only [receivingJetOverlapWeight_matrix_at_chart c d (projection p) hc, hFreq, hdBase,
        windowedClassicalFormMatrix, x, U] using hChange i j
    _ = _ := by
      change _ = (Uᴴ * windowedClassicalFormMatrix P d p * U) i j
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
      exact Finset.sum_comm

def windowedClassicalFormDensity
    {B : Field (M := M)} {hB : IsSmooth B} {hn : IsNondegenerate B}
    {Q : SymmetricJetGlobalForm M} {r : Metric (M := M)}
    (P : WindowedClassicalSymmetricJetForm B hB hn Q)
    (A : IntrinsicAmplitudeCovariance r) (p : Cosphere r) : ℂ :=
  let d := AtlasChart.atPoint (projection p)
  conj ((windowedClassicalFormMatrix P d p * atlasJetCovarianceMatrix d A.density p).trace)

theorem windowedClassicalFormDensity_eq_chart
    {B : Field (M := M)} {hB : IsSmooth B} {hn : IsNondegenerate B}
    {Q : SymmetricJetGlobalForm M} {r : Metric (M := M)}
    (P : WindowedClassicalSymmetricJetForm B hB hn Q)
    (A : IntrinsicAmplitudeCovariance r) (c : AtlasChart M) (p : Cosphere r)
    (hc : projection p ∈ c.chart.source) :
    windowedClassicalFormDensity P A p =
      conj ((windowedClassicalFormMatrix P c p * atlasJetCovarianceMatrix c A.density p).trace) := by
  let d := AtlasChart.atPoint (projection p)
  have hd : projection p ∈ d.chart.source := mem_chart_source E _
  have h := windowedClassicalFormMatrix_change P c d p hc hd
  exact congrArg (starRingEnd ℂ) (trace_atlasJetCovariance_form_change c d A.density p hc hd _ _ h).symm

theorem ae_windowedClassicalFormDensity_eq_entries
    {B : Field (M := M)} {hB : IsSmooth B} {hn : IsNondegenerate B}
    {Q : SymmetricJetGlobalForm M} {r : Metric (M := M)}
    (P : WindowedClassicalSymmetricJetForm B hB hn Q)
    (A : IntrinsicAmplitudeCovariance r) (c : AtlasChart M)
    (hPos : ∀ᵐ p ∂A.control, ∀ b : Module.Basis Index ℝ (TangentSpace Model (projection p)),
      (components b (A.density p)).PosSemidef)
    (K : Set M) (hK : MeasurableSet K) (hKc : K ⊆ c.chart.source) :
    ∀ᵐ p ∂A.control.restrict (amplitudeCosphereWindow r K),
      (∑ i, ∑ j, conj (windowedClassicalFormMatrix P c p i j) * atlasOrderedJetEntry c A.density p j i) =
        windowedClassicalFormDensity P A p := by
  filter_upwards [ae_restrict_mem (μ := A.control) (measurableSet_amplitudeCosphereWindow r hK),
    ae_receivingClassicalFormDensity_eq_trace A c hPos K hK hKc (windowedClassicalFormMatrix P c)]
    with p hp hTrace
  exact hTrace.trans (windowedClassicalFormDensity_eq_chart P A c p (hKc hp)).symm

end Burnett.Microlocal.Overlap
