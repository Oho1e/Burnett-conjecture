import Burnett.Results.PaperResultsStatement
import Burnett.Results.OriginalForwardKineticResult

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4200

noncomputable section

namespace Burnett.PaperStatement

open Set MeasureTheory
open TopologicalSpace (Opens)
open scoped ContDiff ENNReal Manifold Topology
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open UnitNullCompactness CotangentAngularExtension ActualTestLift FiniteCausalVolume OpenRegion
open IntrinsicScalarEinstein ContravariantTensor
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

attribute [local instance] puncturedMeasurable puncturedBorel

theorem variationalTransport (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M)) :
    VariationalTransport r B g := by
  intro admissible σ μ witness
  obtain ⟨hσ, quadratic, A, hA, hReceive, hPhysical⟩ := witness
  obtain ⟨_, hCompact, hNull, _, _⟩ := quadratic
  exact C04.originalVariationalTransport r B g admissible.smoothLimit admissible.smoothSequence
    admissible.lorentzLimit admissible.lorentzSequence admissible.vacuum admissible.locallyUniform
    admissible.compactFirstDerivative σ hσ A μ hA hReceive hPhysical hNull hCompact

theorem forwardKineticLimit (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M)) :
    ForwardKineticLimit r B g := by
  intro admissible
  obtain ⟨σ, hσ, A, μ, hA, hPhysical, _, hRegular, hCompact, hNull, hMoments, hScalar, _, hTransport, lifts⟩ :=
    C04.exists_originalForwardKineticMeasure r B g admissible.smoothLimit admissible.smoothSequence
      admissible.lorentzLimit admissible.lorentzSequence admissible.timeOriented admissible.vacuum
      admissible.locallyUniform admissible.compactFirstDerivative
  refine ⟨σ, μ, hσ, ⟨A, hA, hPhysical⟩, ⟨hRegular, hCompact, hNull, hScalar, hMoments⟩, hTransport, ?_⟩
  intro U o hIntrinsic
  have hChart : ChartGlobalHyperbolicity o :=
    (chartGlobalHyperbolicity_iff_intrinsicPiecewise
      (isSmooth_restrictBilinear U B admissible.smoothLimit)
      (hasLorentzSignature_restrictBilinear U admissible.lorentzLimit) o).2 hIntrinsic
  obtain ⟨ν, hReg, hNullRegion, hMass, hStress, hFullTransport⟩ := lifts U o hChart
  refine ⟨ν, hReg, hNullRegion, ?_, hStress, hFullTransport⟩
  intro K hK
  obtain ⟨hMoment, hBound⟩ := hMass K hK
  exact ⟨hMoment.trans_lt hBound, hMoment⟩

end Burnett.PaperStatement
