import Burnett.Analysis.Microlocal.Overlap.OriginalGeometricSymmetricJetOperatorLimit

/-! The single original subsequence in the paper's quadratic theorem. -/
set_option autoImplicit false
set_option maxRecDepth 4400
set_option maxHeartbeats 4400000

noncomputable section

namespace Burnett.F07

open MeasureTheory Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence IntrinsicScalarEinstein
open Burnett.Geometry.UnitCosphere (Cosphere FixedChartNaturality hamiltonian projection)
open Burnett.Microlocal.Overlap
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The quadratic theorem starts with the paper's admissibility conditions.
One strict subsequence determines the actual intrinsic covariance and its
physical contraction with all Einstein moments and fixed-chart naturality. -/
theorem exists_quadraticOriginalMeasure
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hSigG : ∀ n, HasLorentzSignature (g n))
    (_hTime : ∃ V : ChartVectorField.Field (M := M), ChartVectorField.IsSmooth V ∧ ∀ x, B x (V x) (V x) < 0)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ A : IntrinsicAmplitudeCovariance r, ∃ μ : Measure (Cosphere r),
        HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A ∧
        HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A ∧
        HasOriginalWindowedClassicalSymmetricJetPairings r B g hB hg hSig.isNondegenerate
          hSig.isSymmetric (fun n => (hSigG n).isSymmetric) σ A ∧
        (∀ hM : Nonempty M, letI := hM
          HasOriginalGeometricSymmetricJetOperatorPairings r B g hB hg hSig.isNondegenerate
            hSig.isSymmetric (fun n => (hSigG n).isSymmetric) σ A) ∧
        HasIntrinsicSymmetricJetMeasure A.control (intrinsicSymmetricJetCovariance A.density) ∧
        HasSymmetricJetRicciRange B hSig.isNondegenerate A.control (intrinsicSymmetricJetCovariance A.density) ∧
        HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ ∧
        IsLocallyFiniteMeasure μ ∧ μ.Regular ∧
        (∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤) ∧
        μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0 ∧
        HasCosphereEinsteinMoments r B hSig.isNondegenerate μ ∧
        (∀ x, intrinsicScalar B hSig.isNondegenerate x = 0) ∧ FixedChartNaturality μ := by
  let hsG (n : ℕ) := (hSigG n).isSymmetric
  let hnG (n : ℕ) := (hSigG n).isNondegenerate
  obtain ⟨σ, hσ, A, μ, hA, hLocal, hGlobal, hJet, hRange, hRest⟩ :=
    exists_originalVacuum_symmetricJetMeasure_windowedClassicalPairings_and_EinsteinMoments
      r B g hB hg hSig hsG hnG hconv hb hv id strictMono_id
  have hGeometric (hM : Nonempty M) :
      letI := hM
      HasOriginalGeometricSymmetricJetOperatorPairings r B g hB hg hSig.isNondegenerate
        hSig.isSymmetric hsG σ A := by
    letI := hM
    exact hasOriginalGeometricSymmetricJetOperatorPairings_of_windowed r B g hB hg
      hSig.isNondegenerate hSig.isSymmetric hsG σ A hGlobal
  exact ⟨σ, hσ, A, μ, hA, hLocal, hGlobal, hGeometric, hJet, hRange, hRest⟩

end Burnett.F07
