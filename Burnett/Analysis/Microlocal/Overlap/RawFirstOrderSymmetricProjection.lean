import Burnett.Analysis.Microlocal.Overlap.RawFirstOrderJetTransition
import Burnett.Analysis.Microlocal.Overlap.IntrinsicJetSymmetricProjection

/-! Actual ordered-coordinate symmetrization commutes with the chart change. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set Burnett.Geometry
open ConnectionDifference ManifoldMetric MaximalChart
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold

local notation "E" => CoordinateSpace

/-- Symmetrize the two tensor slots, keeping the ordered derivative slot. -/
def symmetrizeOrderedJet (w : JetSlot → ℂ) : JetSlot → ℂ :=
  fun i => (2 : ℂ)⁻¹ * (w i + w (jetPairSwap i))

theorem symmetrizeOrderedJet_jetFiberCoordinates {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Module.Basis Burnett.RicciSymbol.Index ℝ V) (F : ComplexCovariantJet V) :
    symmetrizeOrderedJet (jetFiberCoordinates b F) =
      jetFiberCoordinates b (projectComplexSymmetricJet V F : ComplexCovariantJet V) := by
  funext i
  symm
  change jetFiberCoordinates b ((2 : ℂ)⁻¹ • (F + swapComplexCovariantJet V F)) i = _
  simp only [map_smul, map_add, Pi.smul_apply, Pi.add_apply, jetFiberCoordinates_swap, smul_eq_mul, symmetrizeOrderedJet]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

theorem rawReceivingJetTransition_symmetrizeOrderedJet (c d : AtlasChart M) (x : M)
    (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source) (w : JetSlot → ℂ) :
    rawReceivingJetTransition c d (c.chart x) (symmetrizeOrderedJet w) =
      symmetrizeOrderedJet (rawReceivingJetTransition c d (c.chart x) w) := by
  let W := jetFiberCoordinates (chartTangentBasis d x hd)
  obtain ⟨F, rfl⟩ := W.surjective w
  change rawReceivingJetTransition c d (c.chart x)
      (symmetrizeOrderedJet (jetFiberCoordinates (chartTangentBasis d x hd) F)) = _
  rw [symmetrizeOrderedJet_jetFiberCoordinates, rawReceivingJetTransition_jetFiberCoordinates c d x hc hd]
  change _ = symmetrizeOrderedJet
    (rawReceivingJetTransition c d (c.chart x) (jetFiberCoordinates (chartTangentBasis d x hd) F))
  rw [rawReceivingJetTransition_jetFiberCoordinates c d x hc hd, symmetrizeOrderedJet_jetFiberCoordinates]

/-- At every coordinate point of the overlap, the actual input transition
preserves the symmetric projection. -/
theorem rawReceivingJetTransition_symmetrizeOrderedJet_on_overlap
    (c d : AtlasChart M) {y : E} (hy : y ∈ (c.transition d).source) (w : JetSlot → ℂ) :
    rawReceivingJetTransition c d y (symmetrizeOrderedJet w) =
      symmetrizeOrderedJet (rawReceivingJetTransition c d y w) := by
  let x := c.chart.symm y
  have hc : x ∈ c.chart.source := c.chart.symm_mapsTo hy.1
  have hd : x ∈ d.chart.source := hy.2
  have he : c.chart x = y := c.chart.right_inv hy.1
  simpa only [he] using rawReceivingJetTransition_symmetrizeOrderedJet c d x hc hd w

end Burnett.Microlocal.Overlap
