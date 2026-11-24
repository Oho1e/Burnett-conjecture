import Burnett.Analysis.Microlocal.Overlap.OriginalSymmetricJetEinsteinAssembly
import Burnett.Analysis.Microlocal.Overlap.LocalClassicalPuncturedPrincipal

/-! One original refinement carries every actual classical full-symbol test in every receiving chart. -/
set_option autoImplicit false
set_option maxRecDepth 4900
set_option maxHeartbeats 4200000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set Filter Function MeasureTheory Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear
open IntrinsicScalarEinstein MaximalChart
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeCovariantGradientSchwartz)
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian FixedChartNaturality)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.X02.SobolevTestJet (D)
open scoped ComplexConjugate ContDiff InnerProduct Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

local notation "E" => CoordinateSpace

/-- The original covariant half-density pairing in every compatible chart.
The actual operator is given by its local full-symbol pairing. Only the
punctured principal symbol occurs in the limit. -/
def HasOriginalReceivingLocalClassicalPairings
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r) : Prop :=
  ∀ (c : AtlasChart M) (K : Set M), IsCompact K → ∀ (hKc : K ⊆ c.chart.source)
    (η₀ η₁ : D) (h₀ : tsupport (η₀ : E → ℝ) ⊆ c.chart '' K)
    (h₁ : tsupport (η₁ : E → ℝ) ⊆ c.chart '' K)
    (T : ComplexL2 E →L[ℂ] ComplexL2 E) (b a : E → E → ℂ),
    ContDiffOn ℝ ∞ (uncurry b) (c.chart.target ×ˢ univ) →
    ContDiffOn ℝ ∞ (uncurry a) (c.chart.target ×ˢ ({0}ᶜ : Set E)) →
    (∀ x ∈ c.chart.target, ∀ s : ℝ, 0 < s → ∀ ξ : E, ξ ≠ 0 → a x (s • ξ) = a x ξ) →
    (∀ S : Set E, IsCompact S → S ⊆ c.chart.target → ∃ R : ℝ,
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ ξ : E, R ≤ ‖ξ‖ →
        (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => b y ξ - a y ξ) x‖ ≤ C) →
    (∀ f v : SchwartzMap E ℂ, tsupport (f : E → ℂ) ⊆ c.chart.target →
      tsupport (v : E → ℂ) ⊆ tsupport (η₁ : E → ℝ) →
      inner ℂ (f.toLp 2 volume) (T (v.toLp 2 volume)) = classicalLeftPairing b f v) →
    ∀ i j : JetSlot,
      let h₀c := h₀.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
      let h₁c := h₁.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
      let u := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η₀ h₀c
      let v := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η₁ h₁c
      let τ := A.control.restrict (amplitudeCosphereWindow r K)
      let G (p : Cosphere r) :=
        let z := fixedChartPhase c p.val
        conj ((physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) * a z.1 (WithLp.toLp 2 z.2)) *
          atlasOrderedJetEntry c A.density p j i
      Integrable G τ ∧ Tendsto (fun n => inner ℂ (T ((v (σ n) j).toLp 2 volume))
        ((u (σ n) i).toLp 2 volume)) atTop (𝓝 (∫ p, G p ∂τ))

theorem hasOriginalReceivingLocalClassicalPairings_of_intrinsicAmplitude
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A) :
    HasOriginalReceivingLocalClassicalPairings r B g hB hg hnB σ A := by
  have hP := hasOriginalReceivingPaperPairings_of_intrinsicAmplitude r B g hB hg hsB hsG
    hnB hnG hconv hb hv σ hσ A hA
  intro c K hK hKc η₀ η₁ h₀ h₁ T b a hBD hAD hDeg hLarge hAct i j h₀c h₁c u v τ G
  obtain ⟨hI, hLim⟩ := tendsto_originalVolume_receivingLocalFullPairing_of_puncturedPrincipal
    r B g hB hg hnB σ A hP c K hK hKc η₀ η₁ h₀ h₁ T b a hBD hAD hDeg hLarge hAct i j
  have hErr := (tendsto_fixedVolumeCovariantPaperPairing_sub_partial r B g hB hg hnB hconv hb
    c η₀ η₁ h₀c h₁c T i j).comp hσ.tendsto_atTop
  refine ⟨hI, ?_⟩
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using hErr.add hLim

/-- The same symmetric covariance and null physical measure support every
local test of the original covariant gradients on the same refinement. -/
theorem exists_originalVacuum_symmetricJetMeasure_localClassicalPairings_and_EinsteinMoments
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧
      ∃ A : IntrinsicAmplitudeCovariance r, ∃ μ : Measure (Cosphere r),
        HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
        HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
        HasIntrinsicSymmetricJetMeasure A.control (intrinsicSymmetricJetCovariance A.density) ∧
        HasSymmetricJetRicciRange B hSig.isNondegenerate A.control (intrinsicSymmetricJetCovariance A.density) ∧
        HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ ∧
        IsLocallyFiniteMeasure μ ∧ μ.Regular ∧
        (∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤) ∧
        μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0 ∧
        HasCosphereEinsteinMoments r B hSig.isNondegenerate μ ∧
        (∀ x, intrinsicScalar B hSig.isNondegenerate x = 0) ∧ FixedChartNaturality μ := by
  obtain ⟨t, ht, A, μ, hA, _, hMeasure, hRange, hPhysical⟩ :=
    exists_originalVacuum_symmetricJetMeasure_covariantPairings_and_EinsteinMoments
      r B g hB hg hSig hsG hnG hconv hb hv s hs
  exact ⟨t, ht, A, μ, hA,
    hasOriginalReceivingLocalClassicalPairings_of_intrinsicAmplitude r B g hB hg
      hSig.isSymmetric hsG hSig.isNondegenerate hnG hconv hb hv (s ∘ t) (hs.comp ht) A hA,
    hMeasure, hRange, hPhysical⟩

end Burnett.Microlocal.Overlap
