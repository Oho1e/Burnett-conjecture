import Burnett.Analysis.Microlocal.Overlap.IntrinsicSymmetricJetMeasure
import Burnett.Analysis.Microlocal.Overlap.IntrinsicJetRicciRange
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartCovariantPairing

/-! One extraction for the true covariant pairings, symmetric jet measure and physical moments. -/
set_option autoImplicit false
set_option maxRecDepth 4800
set_option maxHeartbeats 4100000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Module Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear
open IntrinsicScalarEinstein MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian FixedChartNaturality)
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The density takes values in covector insertions of symmetric amplitudes in the actual Ricci kernel. -/
def HasSymmetricJetRicciRange {r : Metric (M := M)} (B : Field (M := M)) (hn : IsNondegenerate B)
    (τ : Measure (Cosphere r)) (D : SymmetricJetEndomorphismField r) : Prop :=
  ∀ᵐ p ∂τ,
    let x := projection p
    let b := chartTangentBasis (AtlasChart.atPoint x) x (mem_chart_source CoordinateSpace x)
    letI : FiniteDimensional ℝ (TangentSpace Model x) := Module.Finite.of_basis b
    ∀ F : complexSymmetricJet (TangentSpace Model x), ∃ k : ComplexBilinearForm (TangentSpace Model x),
      (∀ u v, k u v = k v u) ∧
      complexFiberRicciSymbol (covariantForm B x) (hn x) p.val.2.toLinearMap k = 0 ∧
      (D p F : ComplexCovariantJet (TangentSpace Model x)) = insertCovariantJet p.val.2.toLinearMap k

omit [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
theorem original_hasSymmetricJetRicciRange {r : Metric (M := M)} {B : Field (M := M)} {g : ℕ → Field (M := M)}
    {hB : IsSmooth B} {hg : ∀ n, IsSmooth (g n)} {hn : IsNondegenerate B}
    {σ : ℕ → ℕ} {A : IntrinsicAmplitudeCovariance r} (hs : IsSymmetric B)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hn σ A) :
    HasSymmetricJetRicciRange B hn A.control (intrinsicSymmetricJetCovariance A.density) := by
  filter_upwards [hA.2.2.2.2.2] with p hp
  intro x F
  obtain ⟨k, hk, hR, hOut⟩ := intrinsicJetCovarianceEndomorphism_range_gradientRicci hs hp.2.2 F
  let V := TangentSpace Model x
  let y : ComplexCovariantJet V := intrinsicJetCovarianceEndomorphism A.density p F
  have hy := intrinsicJetCovarianceEndomorphism_mem_symmetric hp.2.2 F
  refine ⟨k, hk, hR, ?_⟩
  change (projectComplexSymmetricJet V y : ComplexCovariantJet V) = _
  exact (coe_projectComplexSymmetricJet_of_mem y hy).trans hOut

/-- The original refinement simultaneously determines the represented tests
on the original covariant jets, the positive measure on their actual symmetric
fibers, and the physical measure with all Einstein moments. -/
theorem exists_originalVacuum_symmetricJetMeasure_covariantPairings_and_EinsteinMoments
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧
      ∃ A : IntrinsicAmplitudeCovariance r, ∃ μ : Measure (Cosphere r),
        HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
        HasOriginalReceivingCovariantPaperPairings r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
        HasIntrinsicSymmetricJetMeasure A.control (intrinsicSymmetricJetCovariance A.density) ∧
        HasSymmetricJetRicciRange B hSig.isNondegenerate A.control (intrinsicSymmetricJetCovariance A.density) ∧
        HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ ∧
        IsLocallyFiniteMeasure μ ∧ μ.Regular ∧
        (∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤) ∧
        μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0 ∧
        HasCosphereEinsteinMoments r B hSig.isNondegenerate μ ∧
        (∀ x, intrinsicScalar B hSig.isNondegenerate x = 0) ∧ FixedChartNaturality μ := by
  obtain ⟨t, ht, A, μ, hA, hPhysical⟩ := exists_originalVacuum_intrinsicAmplitude_and_cosphereEinsteinMoments
    r B g hB hg hSig hsG hnG hconv hb hv s hs
  have hPairings := hasOriginalReceivingCovariantPaperPairings_of_intrinsicAmplitude r B g hB hg
    hSig.isSymmetric hsG hSig.isNondegenerate hnG hconv hb hv (s ∘ t) (hs.comp ht) A hA
  have hMeasure := original_hasIntrinsicSymmetricJetMeasure r B g hB hg hSig.isSymmetric hsG
    hSig.isNondegenerate hnG hconv hb hv (s ∘ t) (hs.comp ht) A hA
  exact ⟨t, ht, A, μ, hA, hPairings, hMeasure, original_hasSymmetricJetRicciRange hSig.isSymmetric hA, hPhysical⟩

end Burnett.Microlocal.Overlap
