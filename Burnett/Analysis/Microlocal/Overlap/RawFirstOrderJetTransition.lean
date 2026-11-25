import Burnett.Analysis.Microlocal.Overlap.IntrinsicJetEndomorphism
import Burnett.Geometry.MetricJetNaturality

/-! The actual smooth transition on all ordered covariant jet components. -/
set_option autoImplicit false
set_option maxHeartbeats 3900000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Matrix Set Burnett.Geometry
open ConnectionDifference ManifoldMetric MaximalChart ChartVolume
open Burnett.Geometry.MetricJetNaturality (jacobian_entry_differentiable)
open Burnett.F05.OverlapCovectors (tensorJetTransition tensorPairTransition)
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis chartTangentBasis_change fixedCotangentTransitionMatrix)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped BigOperators ContDiff Kronecker Manifold Matrix Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- From d-components to c-components, with all three ordered covariant slots. -/
def rawReceivingJetTransition (c d : AtlasChart M) (y : E) : (JetSlot → ℂ) →ₗ[ℂ] (JetSlot → ℂ) :=
  (tensorJetTransition ((derivativeMatrix (fderiv ℝ (c.transition d) y))ᵀ)).mulVecLin

omit [IsManifold Model ∞ M] in
theorem rawReceivingJetTransition_differentiableAt (c d : AtlasChart M) (y : E)
    (hy : y ∈ (c.transition d).source) (w : JetSlot → ℂ) (k : JetSlot) :
    DifferentiableAt ℝ (fun z => rawReceivingJetTransition c d z w k) y := by
  have hSmooth : ContDiffAt ℝ ∞ (c.transition d) y :=
    (c.smooth_transition d).contDiffAt ((c.transition d).open_source.mem_nhds hy)
  have hDiff : ContDiffAt ℝ ∞ (fderiv ℝ (c.transition d)) y := hSmooth.fderiv_right (by simp)
  have hJac : DifferentiableAt ℝ (fderiv ℝ (c.transition d)) y := hDiff.differentiableAt (by simp)
  let D (z : E) (a b : Burnett.RicciSymbol.Index) : ℂ :=
    derivativeMatrix (fderiv ℝ (c.transition d) z) b a
  have hD (a b : Burnett.RicciSymbol.Index) : DifferentiableAt ℝ (fun z => D z a b) y :=
    Complex.ofRealCLM.differentiableAt.comp y (jacobian_entry_differentiable (c.transition d) y hJac b a)
  simp only [rawReceivingJetTransition, mulVecLin_apply, mulVec, dotProduct, tensorJetTransition, tensorPairTransition]
  change DifferentiableAt ℝ
    (fun z => ∑ j : JetSlot, D z k.1 j.1 * (D z k.2.1 j.2.1 * D z k.2.2 j.2.2) * w j) y
  exact DifferentiableAt.fun_sum (fun j _ =>
    ((hD k.1 j.1).mul ((hD k.2.1 j.2.1).mul (hD k.2.2 j.2.2))).mul (differentiableAt_const (w j)))

theorem rawReceivingJetTransition_jetFiberCoordinates (c d : AtlasChart M) (x : M)
    (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source)
    (F : ComplexCovariantJet (TangentSpace Model x)) :
    rawReceivingJetTransition c d (c.chart x) (jetFiberCoordinates (chartTangentBasis d x hd) F) =
      jetFiberCoordinates (chartTangentBasis c x hc) F := by
  exact (jetFiberCoordinates_change (chartTangentBasis d x hd) (chartTangentBasis c x hc)
    (fixedCotangentTransitionMatrix d c x) (chartTangentBasis_change d c x hd hc) F).symm

end Burnett.Microlocal.Overlap
