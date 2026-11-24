import Burnett.Analysis.Microlocal.Overlap.OriginalReceivingClassicalPairings
import Burnett.Analysis.Microlocal.Overlap.IntrinsicJetAmplitudeMeasure

/-! One original refinement, one intrinsic amplitude, and one physical measure. -/

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 1850000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear
open ContravariantTensor IntrinsicScalarEinstein MaximalChart
open UnitCosphere (Cosphere projection hamiltonian FixedChartNaturality)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold ComplexOrder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The original refinement simultaneously provides the represented
classical tests in every fixed chart, the positive actual jet covariance,
and all Einstein moments of its physical contraction. -/
theorem exists_originalVacuum_intrinsicAmplitude_receivingPairings_and_EinsteinMoments
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧
      ∃ A : IntrinsicAmplitudeCovariance r, ∃ μ : Measure (Cosphere r),
        HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
        HasOriginalReceivingPaperPairings r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
        (∀ᵐ p ∂A.control, ∀ b : Module.Basis Index ℝ (TangentSpace Model (projection p)),
          (jetAmplitudeComponents b (intrinsicJetAmplitude A.density p)).PosSemidef) ∧
        (∀ (c : AtlasChart M) {K : Set M}, IsCompact K → K ⊆ c.chart.source → ∀ i j : JetSlot,
          IntegrableOn (fun p => atlasIntrinsicJetComponent c A.density p i j)
            (amplitudeCosphereWindow r K) A.control) ∧
        HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ ∧
        IsLocallyFiniteMeasure μ ∧ μ.Regular ∧
        (∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤) ∧
        μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0 ∧
        HasCosphereEinsteinMoments r B hSig.isNondegenerate μ ∧
        (∀ x, intrinsicScalar B hSig.isNondegenerate x = 0) ∧ FixedChartNaturality μ := by
  obtain ⟨t, ht, A, μ, hA, hPhysical⟩ := exists_originalVacuum_intrinsicAmplitude_and_cosphereEinsteinMoments
    r B g hB hg hSig hsG hnG hconv hb hv s hs
  have hPairs := hasOriginalReceivingPaperPairings_of_intrinsicAmplitude r B g hB hg hSig.isSymmetric hsG
    hSig.isNondegenerate hnG hconv hb hv (s ∘ t) (hs.comp ht) A hA
  obtain ⟨hJet, hJetI⟩ := original_intrinsicJetAmplitude_positive_and_integrable r B g hB hg hSig.isSymmetric hsG
    hSig.isNondegenerate hnG hconv hb hv (s ∘ t) (hs.comp ht) A hA
  exact ⟨t, ht, A, μ, hA, hPairs, hJet, hJetI, hPhysical⟩

end Burnett.Microlocal.Overlap
