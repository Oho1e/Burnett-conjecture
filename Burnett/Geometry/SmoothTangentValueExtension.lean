import Burnett.Geometry.ChartVectorField
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.SmoothTangentValueExtension

open Bundle Set
open scoped Manifold ContDiff Topology
open ManifoldMetric ChartVectorField ConnectionDifference

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M]

/-- A true smooth cutoff times one actual preferred tangent-frame vector. -/
def supportedFrame (c : M) (v : CoordinateSpace) (f : SmoothBumpFunction Model c) : Field (M := M) :=
  fun m => f m • tangentFrame c m v

theorem isSmooth_supportedFrame (c : M) (v : CoordinateSpace) (f : SmoothBumpFunction Model c) :
    IsSmooth (supportedFrame c v f) := by
  exact f.contMDiff.contMDiffOn.smul_section_of_tsupport
    (chartAt CoordinateSpace c).open_source f.tsupport_subset_chartAt_source
    (ManifoldMetric.contMDiffOn_frame c v)

/-- Every actual tangent-fiber value admits a genuine global smooth section.
    The cutoff is local; no global frame or nonvanishing section is assumed. -/
theorem exists_isSmooth_value (m : M) (v : TangentSpace Model m) :
    ∃ X : Field (M := M), IsSmooth X ∧ X m = v := by
  let f : SmoothBumpFunction Model m := Classical.choice inferInstance
  let e := trivializationAt CoordinateSpace (TangentSpace Model) m
  let w : CoordinateSpace := (e ⟨m, v⟩).2
  refine ⟨supportedFrame m w f, isSmooth_supportedFrame m w f, ?_⟩
  change f m • tangentFrame m m w = v
  rw [f.eq_one, one_smul]
  change e.symmL ℝ m (e ⟨m, v⟩).2 = v
  simpa only [Trivialization.symmL_apply] using
    e.symm_apply_apply_mk (mem_chart_source CoordinateSpace m) v

end Burnett.Geometry.SmoothTangentValueExtension
