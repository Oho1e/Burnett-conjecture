import Burnett.Analysis.Microlocal.Overlap.WindowedClassicalGlobalLimit
import Burnett.Analysis.Microlocal.Overlap.OriginalReceivingLocalClassicalAssembly

/-! The original extraction simultaneously tests the actual global classical forms. -/
set_option autoImplicit false
set_option maxRecDepth 4800
set_option maxHeartbeats 6100000
set_option synthInstance.maxHeartbeats 390000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart IntrinsicScalarEinstein
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian FixedChartNaturality)
open scoped ComplexConjugate ContDiff Manifold Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold Model ∞ M] [MeasurableSpace M] [BorelSpace M]

/-- Every actual compact-window classical form is tested along the one
original subsequence and with its one intrinsic symmetric covariance. -/
def HasOriginalWindowedClassicalSymmetricJetPairings
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r) : Prop :=
  ∀ (Q : SymmetricJetGlobalForm M) (P : WindowedClassicalSymmetricJetForm B hB hn Q)
    (α ρ : M → ℝ) (hα : ContMDiff Model 𝓘(ℝ) ∞ α) (hρ : ContMDiff Model 𝓘(ℝ) ∞ ρ)
    (hαc : HasCompactSupport α) (hρc : HasCompactSupport ρ),
    let G (p : Cosphere r) := ((α (projection p) * ρ (projection p) : ℝ) : ℂ) *
      windowedClassicalFormDensity P A p
    Integrable G A.control ∧
    Tendsto (fun n => conj (Q (originalCovariantGlobalCutoffTest r B g hB hg hsB hsG α hα hαc (σ n))
        (originalCovariantGlobalCutoffTest r B g hB hg hsB hsG ρ hρ hρc (σ n))))
      atTop (𝓝 (∫ p, G p ∂A.control))

theorem hasOriginalWindowedClassicalSymmetricJetPairings_of_intrinsicAmplitude
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hn σ A)
    (hLocal : HasOriginalReceivingLocalClassicalPairings r B g hB hg hn σ A) :
    HasOriginalWindowedClassicalSymmetricJetPairings r B g hB hg hn hsB hsG σ A := by
  intro Q P α ρ hα hρ hαc hρc G
  exact tendsto_originalCovariantGlobalCutoffTest_windowedClassical r B g hB hg hn hsB hsG hconv hb
    σ hσ.tendsto_atTop A hLocal (hA.2.2.2.2.2.mono (fun _ hp => hp.2.1))
    Q P α ρ hα hρ hαc hρc

/-- A single extraction supplies the full chart and actual bundle tests, its
positive Ricci-localized covariance, and the same physical Einstein measure. -/
theorem exists_originalVacuum_symmetricJetMeasure_windowedClassicalPairings_and_EinsteinMoments
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
        HasIntrinsicSymmetricJetMeasure A.control (intrinsicSymmetricJetCovariance A.density) ∧
        HasSymmetricJetRicciRange B hSig.isNondegenerate A.control (intrinsicSymmetricJetCovariance A.density) ∧
        HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ ∧
        IsLocallyFiniteMeasure μ ∧ μ.Regular ∧
        (∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤) ∧
        μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0 ∧
        HasCosphereEinsteinMoments r B hSig.isNondegenerate μ ∧
        (∀ x, intrinsicScalar B hSig.isNondegenerate x = 0) ∧ FixedChartNaturality μ := by
  obtain ⟨t, ht, A, μ, hA, hLocal, hJet, hRange, hPhysical⟩ :=
    exists_originalVacuum_symmetricJetMeasure_localClassicalPairings_and_EinsteinMoments
      r B g hB hg hSig hsG hnG hconv hb hv s hs
  have hGlobal := hasOriginalWindowedClassicalSymmetricJetPairings_of_intrinsicAmplitude r B g hB hg
    hSig.isNondegenerate hSig.isSymmetric hsG hconv hb (s ∘ t) (hs.comp ht) A hA hLocal
  exact ⟨t, ht, A, μ, hA, hLocal, hGlobal, hJet, hRange, hPhysical⟩

end Burnett.Microlocal.Overlap
