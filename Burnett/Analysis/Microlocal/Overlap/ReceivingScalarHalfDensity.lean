import Burnett.Analysis.Microlocal.Overlap.ReceivingChartVolumeInputs

/-! Physical scalar chart lifts and their half-density representatives. -/
set_option autoImplicit false

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set Classical Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Microlocal.AtlasVolumeGradient (fixedHalfDensity)
open scoped ContDiff Manifold

local notation "E" => CoordinateSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- Undo the genuine volume half-density on the chart and extend by zero. -/
def receivingScalarPhysicalLift (B : Field (M := M)) (c : AtlasChart M) (f : E → ℂ) : M → ℂ :=
  c.chart.source.indicator (fun p => (fixedHalfDensity B c (c.chart p) : ℂ)⁻¹ * f (c.chart p))

theorem fixedHalfDensity_pos (B : Field (M := M)) (hn : IsNondegenerate B) (c : AtlasChart M)
    (x : E) (hx : x ∈ c.chart.target) : 0 < fixedHalfDensity B c x :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (abs_pos.mpr (fixedForm_det_ne_zero B hn c hx)))

omit [IsManifold Model ∞ M] in
theorem receivingScalarPhysicalLift_support (B : Field (M := M)) (c : AtlasChart M)
    (f : E → ℂ) (K : Set E) (hf : support f ⊆ K) :
    support (receivingScalarPhysicalLift B c f) ⊆ c.chart.symm '' K := by
  intro p hp
  have hpc : p ∈ c.chart.source := support_indicator_subset hp
  have hf' : f (c.chart p) ≠ 0 := by
    intro hzero
    exact hp (by simp [receivingScalarPhysicalLift, hpc, hzero])
  exact ⟨c.chart p, hf hf', c.chart.left_inv hpc⟩

/-- The half-density representative, extended by zero from the chart. -/
def receivingScalarTestHalfDensity (B : Field (M := M)) (c : AtlasChart M) (f : M → ℂ) : E → ℂ :=
  c.chart.target.indicator (fun x => (fixedHalfDensity B c x : ℂ) * f (c.chart.symm x))

end Burnett.Microlocal.Overlap
