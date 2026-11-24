import Burnett.Analysis.Microlocal.Overlap.ReceivingChartVolumeInputs
import Burnett.Geometry.FlatRigidity.WeakCurvature

/-! Smooth compact source cutoffs for every ordered receiving jet slot. -/

set_option autoImplicit false
set_option maxRecDepth 3100
set_option maxHeartbeats 2300000

noncomputable section
namespace Burnett.Microlocal.AtlasVolumeGradient

open Set Filter MeasureTheory Burnett.RicciSymbol Burnett.Fourier
open Burnett.Geometry ConnectionDifference ConnectionCoordinateChange ManifoldMetric ManifoldMetricSequence
open ManifoldBilinear ChartVolume ManifoldMetricTransition MetricJetNaturality TensorCoordinateChange MaximalChart
open Burnett.F05.CoordinateCurl Burnett.F05.ChartVolumeBridge Burnett.F05.OverlapCovariantGradient
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet
open scoped Manifold ContDiff Topology BigOperators InnerProduct

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def inverseJetEntry (c d : AtlasChart M) (i j : JetSlot) (x : CoordinateSpace) : ℝ :=
  let A := derivativeMatrix (fderiv ℝ (d.transition c) (c.transition d x))
  A j.1 i.1 * A j.2.1 i.2.1 * A j.2.2 i.2.2

omit [IsManifold Model ∞ M] in
theorem inverseJetEntry_smooth (c d : AtlasChart M) (i j : JetSlot) :
    ContDiffOn ℝ ∞ (inverseJetEntry c d i j) (c.transition d).source := by
  have h (a b : Index) := (fixedJacobian_entry_smooth d c a b).comp (c.smooth_transition d)
    (show MapsTo (c.transition d) (c.transition d).source (d.transition c).source from (c.transition d).mapsTo)
  exact ((h j.1 i.1).mul (h j.2.1 i.2.1)).mul (h j.2.2 i.2.2)

omit [IsManifold Model ∞ M] in
theorem exists_ordered_source_cutoffs (c d : AtlasChart M) (K : Set CoordinateSpace)
    (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source) (η : D)
    (hη : tsupport (η : CoordinateSpace → ℝ) ⊆ (c.transition d) '' K) (i : JetSlot) :
    ∃ a : JetSlot → D, (∀ j, tsupport (a j : CoordinateSpace → ℝ) ⊆ K) ∧
      ∀ j x, x ∈ (c.transition d).source →
        (a j : CoordinateSpace → ℝ) x = (η : CoordinateSpace → ℝ) (c.transition d x) * inverseJetEntry c d i j x := by
  let e := c.transition d
  obtain ⟨L,_,_,hLU,χ,hχ,hc,hs,_,hone⟩ := FlatRigidity.exists_smooth_cutoff_on_compact_chart hK e.open_source hKU
  let f (j : JetSlot) (x : CoordinateSpace) := (η : CoordinateSpace → ℝ) (e x) * inverseJetEntry c d i j x
  have hf (j : JetSlot) : ContDiffOn ℝ ∞ (f j) e.source := ((test_smooth η).comp_contDiffOn
    (c.smooth_transition d)).mul (inverseJetEntry_smooth c d i j)
  let a (j : JetSlot) : D := ⟨fun x => χ x * f j x,⟨Burnett.Analysis.LocalWeakDerivative.contDiff_test_mul_local
    e.open_source hχ (hs.trans hLU) (hf j),hc.mul_right⟩⟩
  have hz (x : CoordinateSpace) (hx : x ∈ e.source) (hKx : x ∉ K) : (η : CoordinateSpace → ℝ) (e x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    rintro hy
    obtain ⟨y,hy,he⟩ := hη hy
    exact hKx (e.injOn (hKU hy) hx he ▸ hy)
  refine ⟨a,?_,?_⟩
  · intro j
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hout
    apply hx
    change χ x * f j x = 0
    by_cases hU : x ∈ e.source
    · simp only [f,hz x hU hout,zero_mul,mul_zero]
    · exact mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport (fun h => hU (hLU (hs h)))) _
  · intro j x hx
    change χ x * f j x = _
    by_cases hxin : x ∈ K
    · rw [hone x hxin,one_mul]
    · change χ x * f j x = f j x
      simp only [f,hz x hx hxin,zero_mul,mul_zero]

end Burnett.Microlocal.AtlasVolumeGradient
