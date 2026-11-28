import Burnett.Analysis.Microlocal.Overlap.OriginalVacuumIntrinsicAmplitude
import Burnett.Analysis.Microlocal.Overlap.OriginalReceivingLocalClassicalAssembly
import Burnett.Geometry.Causality.IntrinsicPiecewiseStrongCausality
import Burnett.Geometry.Cotangent.OpenRegion.CosphereMeasure
import Burnett.Geometry.Cotangent.OpenRegion.Metrics
import Burnett.Geometry.Cotangent.WeightedMomentumTransport

set_option autoImplicit false

noncomputable section

namespace Burnett.PaperStatement

open Set MeasureTheory
open TopologicalSpace (Opens)
open scoped ContDiff ENNReal Manifold Topology
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open UnitNullCompactness CotangentAngularExtension ActualTestLift FiniteCausalVolume OpenRegion
open IntrinsicScalarEinstein ContravariantTensor
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian)
open Burnett.Microlocal.Overlap

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

attribute [local instance] puncturedMeasurable puncturedBorel

/-- Original vacuum sequence and smooth time-oriented limit, as in `eq:admissible`. -/
structure Admissible (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M)) : Prop where
  smoothLimit : IsSmooth B
  smoothSequence : ∀ n, IsSmooth (g n)
  lorentzLimit : HasLorentzSignature B
  lorentzSequence : ∀ n, HasLorentzSignature (g n)
  timeOriented : ∃ V : ChartVectorField.Field (M := M), ChartVectorField.IsSmooth V ∧ ∀ x, B x (V x) (V x) < 0
  vacuum : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)
  locallyUniform : LocallyUniformlyConverges r g B
  compactFirstDerivative : AuxiliaryAdmissibility.CompactDhBound r B g

/-- The actual ambient transport test from `eq:transport`. -/
def DegreeOneCompactBase (a : CotangentBundle M → ℝ) : Prop :=
  ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent ∧
    (∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), a (cotangentScale t p) = t * a p) ∧
    ∃ K : Set M, IsCompact K ∧ ∀ p ∈ puncturedCotangent, p.proj ∉ K → a p = 0

def CosphereTransport (r : Metric (M := M)) (B : Field (M := M)) (μ : Measure (Cosphere r)) : Prop :=
  ∀ a : CotangentBundle M → ℝ, DegreeOneCompactBase a →
    Integrable (fun p : Cosphere r => actualHamiltonDerivative B a p.val) μ ∧
    (∫ p : Cosphere r, actualHamiltonDerivative B a p.val ∂μ) = 0

/-- The measure conclusions of the quadratic theorem on the auxiliary unit section. -/
def QuadraticConclusions (r : Metric (M := M)) (B : Field (M := M))
    (hL : HasLorentzSignature B) (μ : Measure (Cosphere r)) : Prop :=
  μ.Regular ∧
    (∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤) ∧
    μ {p | hamiltonian B hL.isNondegenerate p ≠ 0} = 0 ∧
    (∀ x, intrinsicScalar B hL.isNondegenerate x = 0) ∧
    ∀ Q : ContravariantTwoTensor M, IsTensorTest Q →
      Integrable (einsteinPair B hL.isNondegenerate Q) (ManifoldVolume.geometricMeasure B) ∧
      Integrable (fun p : Cosphere r => intrinsicTensorPhase Q p.val) μ ∧
      (∫ x, einsteinPair B hL.isNondegenerate Q x ∂ManifoldVolume.geometricMeasure B) =
        ∫ p : Cosphere r, intrinsicTensorPhase Q p.val ∂μ

/-- Provenance of the fixed quadratic witness, including the original
covariance behind its contraction. The covariance is an internal witness. -/
def QuadraticWitness (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (h : Admissible r B g) (σ : ℕ → ℕ) (μ : Measure (Cosphere r)) : Prop :=
  StrictMono σ ∧ QuadraticConclusions r B h.lorentzLimit μ ∧
    ∃ A : IntrinsicAmplitudeCovariance r,
      HasOriginalIntrinsicAmplitude r B g h.smoothLimit h.smoothSequence h.lorentzLimit.isNondegenerate σ A ∧
      HasOriginalReceivingLocalClassicalPairings r B g h.smoothLimit h.smoothSequence h.lorentzLimit.isNondegenerate σ A ∧
      HasIntrinsicPhysicalContraction r B h.lorentzLimit.isNondegenerate A μ

/-- `thm:variational-transport` for the given quadratic witness. -/
def VariationalTransport (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M)) : Prop :=
  ∀ (h : Admissible r B g) (σ : ℕ → ℕ) (μ : Measure (Cosphere r)),
    QuadraticWitness r B g h σ μ → CosphereTransport r B μ

/-- The full cotangent equations of `thm:main` on one open subspacetime. -/
def RegionConclusions (U : Opens M) (r : Metric (M := M)) (B : Field (M := M))
    (hL : HasLorentzSignature B) (μ : Measure (Cosphere r))
    (ν : Measure (puncturedCotangent (M := U))) : Prop :=
  let rU := restrictRiemannian U r
  let gU := restrictBilinear U B
  let hnU : IsNondegenerate gU := fun p => hL.isNondegenerate p.val
  ν.Regular ∧ ν {p | dualEnergy gU hnU p.val ≠ 0} = 0 ∧
    (∀ K : Set U, IsCompact K →
      let Q := {p : puncturedCotangent (M := U) | p.val.1 ∈ K}
      let moment := ∫⁻ p : puncturedCotangent (M := U), ENNReal.ofReal
        (Q.indicator (fun q : puncturedCotangent (M := U) => (cotangentNorm rU q.val)^2) p) ∂ν
      moment < ⊤ ∧
        moment = (cosphereMeasureOfOpen U r μ) ((projection (r := rU)) ⁻¹' K)) ∧
    (∀ Q : ContravariantTwoTensor U, IsTensorTest Q →
      Integrable (einsteinPair gU hnU Q) (ManifoldVolume.geometricMeasure gU) ∧
      Integrable (fun p : puncturedCotangent (M := U) => intrinsicTensorPhase Q p.val) ν ∧
      (∫ x, einsteinPair gU hnU Q x ∂ManifoldVolume.geometricMeasure gU) =
        ∫ p : puncturedCotangent (M := U), intrinsicTensorPhase Q p.val ∂ν) ∧
    ∀ b : CotangentBundle U → ℝ,
      ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ b puncturedCotangent →
      HasCompactSupport (fun p : puncturedCotangent (M := U) => b p.val) →
      Integrable (fun p : puncturedCotangent (M := U) => actualHamiltonDerivative gU b p.val) ν ∧
      (∫ p : puncturedCotangent (M := U), actualHamiltonDerivative gU b p.val ∂ν) = 0

/-- `thm:main` with the physical contraction of the original covariance
on one subsequence. Open-region global hyperbolicity uses intrinsic
piecewise C¹ causal curves. -/
def ForwardKineticLimit (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M)) : Prop :=
  ∀ h : Admissible r B g,
    ∃ (σ : ℕ → ℕ) (μ : Measure (Cosphere r)), StrictMono σ ∧
      (∃ A : IntrinsicAmplitudeCovariance r,
        HasOriginalIntrinsicAmplitude r B g h.smoothLimit h.smoothSequence h.lorentzLimit.isNondegenerate σ A ∧
        HasIntrinsicPhysicalContraction r B h.lorentzLimit.isNondegenerate A μ) ∧
      QuadraticConclusions r B h.lorentzLimit μ ∧ CosphereTransport r B μ ∧
      ∀ (U : Opens M) (o : TimeOrientation (restrictBilinear U B)),
        IntrinsicPiecewiseGlobalHyperbolicity o →
        ∃ ν : Measure (puncturedCotangent (M := U)), RegionConclusions U r B h.lorentzLimit μ ν

end Burnett.PaperStatement
