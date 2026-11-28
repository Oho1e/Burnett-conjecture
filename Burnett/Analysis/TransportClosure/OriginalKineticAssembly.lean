import Burnett.Analysis.Microlocal.Overlap.OriginalQuadraticTheorem
import Burnett.Analysis.TransportClosure.OriginalTransportFromLocalBounds
import Burnett.Analysis.TransportClosure.ActualTransportRepresentation

set_option autoImplicit false
set_option maxHeartbeats 6300000
set_option maxRecDepth 3900

noncomputable section

namespace Burnett.C04

open Set MeasureTheory
open scoped ContDiff ENNReal Manifold Topology
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open UnitNullCompactness IntrinsicScalarEinstein
open Burnett.Geometry.ActualTestLift (actualHamiltonDerivative)
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian FixedChartNaturality)
open Burnett.Microlocal.Overlap

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The local numerical bound is imposed on the very measure constructed by
the quadratic theorem, with the angular constant chosen before the patch scale. -/
def HasOriginalChartwiseTwoScaleBounds (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (μ : Measure (Cosphere r)) : Prop :=
  ∀ (c : M) (b : CotangentBundle M → ℝ), IsDegreeOneTransportTest b →
    IsAntipodallyOdd b → HasCompactTransportBaseSupportIn b (chartAt CoordinateSpace c).source →
    let I := ∫ p in {p : Cosphere r | p.val.proj ∈ (chartAt CoordinateSpace c).source},
      chartHamiltonDerivative c B hn b p.val ∂μ
    ∃ C α β δ₀ : ℝ, 0 < α ∧ 0 < β ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ D F ℓ₀ : ℝ, 0 < ℓ₀ ∧
        ∀ ℓ : ℝ, 0 < ℓ → ℓ < ℓ₀ → |4 * I| ≤ C * δ ^ β + D * ℓ ^ α + F * ℓ

/-- The genuine global Hamilton equation on the unit cosphere, including
integrability for the full smooth one-homogeneous compact-base test class. -/
def HasOriginalCosphereTransport (r : Metric (M := M)) (B : Field (M := M))
    (μ : Measure (Cosphere r)) : Prop :=
  ∀ a : CotangentBundle M → ℝ, IsDegreeOneTransportTest a →
    Integrable (fun p : Cosphere r => actualHamiltonDerivative B a p.val) μ ∧
      (∫ p : Cosphere r, actualHamiltonDerivative B a p.val ∂μ) = 0

/-- The quadratic construction and C04 give all global conclusions of the
forward kinetic result on one original subsequence, given the chartwise
two-scale estimate for the exact witnesses of that construction. -/
theorem exists_originalKineticMeasure_of_chartwise_twoScale_bounds
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hSigG : ∀ n, HasLorentzSignature (g n))
    (hTime : ∃ V : ChartVectorField.Field (M := M), ChartVectorField.IsSmooth V ∧ ∀ x, B x (V x) (V x) < 0)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hBound : ∀ (σ : ℕ → ℕ), StrictMono σ →
      ∀ (A : IntrinsicAmplitudeCovariance r) (μ : Measure (Cosphere r)),
      HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A →
      HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A →
      HasOriginalWindowedClassicalSymmetricJetPairings r B g hB hg hSig.isNondegenerate
        hSig.isSymmetric (fun n => (hSigG n).isSymmetric) σ A →
      (∀ hM : Nonempty M, letI := hM
        HasOriginalGeometricSymmetricJetOperatorPairings r B g hB hg hSig.isNondegenerate
          hSig.isSymmetric (fun n => (hSigG n).isSymmetric) σ A) →
      HasIntrinsicSymmetricJetMeasure A.control (intrinsicSymmetricJetCovariance A.density) →
      HasSymmetricJetRicciRange B hSig.isNondegenerate A.control (intrinsicSymmetricJetCovariance A.density) →
      HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ →
      IsLocallyFiniteMeasure μ → μ.Regular →
      (∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤) →
      μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0 →
      HasOriginalChartwiseTwoScaleBounds r B hSig.isNondegenerate μ) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ A : IntrinsicAmplitudeCovariance r, ∃ μ : Measure (Cosphere r),
        HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A ∧
        HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ ∧
        IsLocallyFiniteMeasure μ ∧ μ.Regular ∧
        (∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤) ∧
        μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0 ∧
        HasCosphereEinsteinMoments r B hSig.isNondegenerate μ ∧
        (∀ x, intrinsicScalar B hSig.isNondegenerate x = 0) ∧ FixedChartNaturality μ ∧
        HasOriginalCosphereTransport r B μ := by
  obtain ⟨σ, hσ, A, μ, hA, hReceive, hWindow, hGeom, hJet, hRange,
    hPhysical, hFin, hReg, hCompact, hNull, hMom, hScalar, hNature⟩ :=
    F07.exists_quadraticOriginalMeasure r B g hB hg hSig hSigG hTime hv hconv hb
  have hLocal := hBound σ hσ A μ hA hReceive hWindow hGeom hJet hRange hPhysical hFin hReg hCompact hNull
  have hTr := originalTransport_of_chartwise_twoScale_bounds r B g hB hg hSig
    (fun n => (hSigG n).isSymmetric) (fun n => (hSigG n).isNondegenerate)
    hconv hb hv σ hσ A μ hA hPhysical hNull hCompact hLocal
  refine ⟨σ, hσ, A, μ, hA, hPhysical, hFin, hReg, hCompact, hNull, hMom, hScalar, hNature, ?_⟩
  intro a ha
  have hEq : (fun p : Cosphere r => actualHamiltonDerivative B a p.val) =
      (fun p : Cosphere r => basePointHamiltonDerivative B hSig.isNondegenerate a p.val) :=
    funext fun p => actualHamiltonDerivative_eq_basePointHamiltonDerivative r B hSig.isNondegenerate
      hSig.isSymmetric a ha.1 p
  rw [hEq]
  exact hTr a ha

end Burnett.C04
