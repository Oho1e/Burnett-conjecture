import Burnett.Analysis.Microlocal.Overlap.GeometricSymmetricJetWindowAdmission
import Burnett.Analysis.Microlocal.Overlap.OriginalWindowedClassicalDefectWitness

/-! Read the actual geometric operator limits on the one original witness. -/
set_option autoImplicit false
set_option maxRecDepth 4900
set_option maxHeartbeats 6100000
set_option synthInstance.maxHeartbeats 420000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Filter MeasureTheory Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart IntrinsicScalarEinstein
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian FixedChartNaturality)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ComplexConjugate ContDiff Manifold Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold Model ∞ M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

/-- The same original covariance and subsequence test every admitted
single geometric operator with the actual auxiliary Gram and volume. -/
def HasOriginalGeometricSymmetricJetOperatorPairings
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r) : Prop :=
  ∀ (L : smoothCompactSymmetricJet M →ₗ[ℂ] SymmetricJetSection M)
    (hL : ∀ u, IsSmoothSymmetricJetSection (L u))
    (a : AtlasChart M → JetSlot → JetSlot → E → E → ℂ)
    (hPrincipal : ∀ (c : AtlasChart M) i j,
      ContDiffOn ℝ ∞ (uncurry (a c i j)) (c.chart.target ×ˢ ({0}ᶜ : Set E)))
    (hDegree : ∀ (c : AtlasChart M) i j x, x ∈ c.chart.target → ∀ s : ℝ, 0 < s →
      ∀ ξ : E, ξ ≠ 0 → a c i j x (s • ξ) = a c i j x ξ)
    (hLocal : HasOrdinarySymmetricJetWindowSymbols r B hB hn L a)
    (K : SymmetricJetLinearKernel M)
    (hKernel : ∀ (T : Set M), IsCompact T → ∀ (u : smoothCompactSymmetricJet M),
      symmetricJetSectionSupport u.val ⊆ T → ∀ p ∉ T, ∀ v : SymmetricJetFiber M p,
        symmetricJetFiberGram r p v (L u p) =
          ∫ q in T, pairSymmetricJetLinearKernel r K p q v (u.val q) ∂ManifoldVolume.geometricMeasure B)
    (hK : ∀ (c d : AtlasChart M) (S T : Set M), IsCompact S → IsCompact T →
      S ⊆ c.chart.source → T ⊆ d.chart.source → Disjoint S T →
      ∀ i j, ContinuousOn (uncurry (symmetricJetLinearKernelEntry K c d i j)) (S ×ˢ T))
    (α ρ : M → ℝ) (hα : ContMDiff Model 𝓘(ℝ) ∞ α) (hρ : ContMDiff Model 𝓘(ℝ) ∞ ρ)
    (hαc : HasCompactSupport α) (hρc : HasCompactSupport ρ),
    let P := windowedClassicalSymmetricJetForm_of_geometricOperator
      r B hB hn L hL a hPrincipal hDegree hLocal K hKernel hK
    let G (p : Cosphere r) := ((α (projection p) * ρ (projection p) : ℝ) : ℂ) *
      windowedClassicalFormDensity P A p
    Integrable G A.control ∧
    Tendsto (fun n =>
      let v := originalCovariantGlobalCutoffTest r B g hB hg hsB hsG α hα hαc (σ n)
      let u := originalCovariantGlobalCutoffTest r B g hB hg hsB hsG ρ hρ hρc (σ n)
      conj (∫ p, symmetricJetFiberGram r p (v.val p) (L u p) ∂ManifoldVolume.geometricMeasure B))
      atTop (𝓝 (∫ p, G p ∂A.control))

theorem hasOriginalGeometricSymmetricJetOperatorPairings_of_windowed
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r)
    (hPairs : HasOriginalWindowedClassicalSymmetricJetPairings r B g hB hg hn hsB hsG σ A) :
    HasOriginalGeometricSymmetricJetOperatorPairings r B g hB hg hn hsB hsG σ A := by
  intro L hL a hPrincipal hDegree hLocal K hKernel hK α ρ hα hρ hαc hρc P G
  exact hPairs (geometricSymmetricJetOperatorForm r B hB L hL) P α ρ hα hρ hαc hρc

/-- Consume the operator class on the original extraction, retaining the
same covariance, null physical measure, and Einstein moments. -/
theorem exists_originalVacuum_geometricSymmetricJetOperatorPairings_and_EinsteinMoments
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧
      ∃ A : IntrinsicAmplitudeCovariance r, ∃ μ : Measure (Cosphere r),
        HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
        HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
        HasOriginalWindowedClassicalSymmetricJetPairings r B g hB hg hSig.isNondegenerate
          hSig.isSymmetric hsG (s ∘ t) A ∧
        HasOriginalGeometricSymmetricJetOperatorPairings r B g hB hg hSig.isNondegenerate
          hSig.isSymmetric hsG (s ∘ t) A ∧
        HasIntrinsicSymmetricJetMeasure A.control (intrinsicSymmetricJetCovariance A.density) ∧
        HasSymmetricJetRicciRange B hSig.isNondegenerate A.control (intrinsicSymmetricJetCovariance A.density) ∧
        HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ ∧
        IsLocallyFiniteMeasure μ ∧ μ.Regular ∧
        (∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤) ∧
        μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0 ∧
        HasCosphereEinsteinMoments r B hSig.isNondegenerate μ ∧
        (∀ x, intrinsicScalar B hSig.isNondegenerate x = 0) ∧ FixedChartNaturality μ := by
  obtain ⟨t, ht, A, μ, hA, hLocal, hGlobal, hJet, hRange, hRest⟩ :=
    exists_originalVacuum_symmetricJetMeasure_windowedClassicalPairings_and_EinsteinMoments
      r B g hB hg hSig hsG hnG hconv hb hv s hs
  have hOperator := hasOriginalGeometricSymmetricJetOperatorPairings_of_windowed r B g hB hg
    hSig.isNondegenerate hSig.isSymmetric hsG (s ∘ t) A hGlobal
  exact ⟨t, ht, A, μ, hA, hLocal, hGlobal, hOperator, hJet, hRange, hRest⟩

end Burnett.Microlocal.Overlap
