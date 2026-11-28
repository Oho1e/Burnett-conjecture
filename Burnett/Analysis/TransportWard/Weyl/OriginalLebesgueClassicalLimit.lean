import Burnett.Analysis.TransportWard.Weyl.LebesgueGradientInput
import Burnett.Analysis.Microlocal.Overlap.CompactClassicalQuantization
import Burnett.Analysis.Microlocal.Overlap.OriginalReceivingClassicalPairings

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 2600

noncomputable section

namespace Burnett.V03

open Function Filter MeasureTheory Set Burnett.Geometry ConnectionDifference ManifoldMetric
open ManifoldBilinear ManifoldMetricSequence MaximalChart Burnett.Fourier
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.AtlasVolumeGradient (fixedGradientSchwartz)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open scoped ContDiff Manifold Topology InnerProduct

open private atlasAngularPhaseCode_fst from Burnett.Analysis.Microlocal.Overlap.ReceivingClassicalCoverAssembly

local notation "E₀" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The actual compact classical left test on raw chart gradients has the
reciprocal-volume weighted limit on the original F05 amplitude. -/
theorem tendsto_originalLebesgue_receivingFullClassicalPairing
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ c.chart '' K)
    (b a : E₀ → E₀ → ℂ) (S : Set E₀) (hS : IsCompact S)
    (hbS : ∀ ξ, tsupport (fun x => b x ξ) ⊆ S) (haS : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S)
    (hbDiff : ContDiff ℝ ∞ (uncurry b))
    (haDiff : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E₀)))
    (haZero : ContDiff ℝ ∞ (fun x => a x 0)) (haDegree : ∀ x, DegreeZero (a x))
    (R : ℝ) (hLarge : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ : E₀, R ≤ ‖ξ‖ →
      (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => b y ξ - a y ξ) x‖ ≤ C)
    (i j : JetSlot) :
    let hχc := hχ.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let u := fixedGradientSchwartz B g hB hg c χ hχc
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let F (p : Cosphere r) :=
      let x := c.chart (projection p)
      ((((χ : E₀ → ℝ) x)^2 * (fixedCoordinateVolumeDensity B c x)⁻¹ : ℝ) : ℂ) *
        a x (WithLp.toLp 2 (atlasChartUnitCovector c p)) * atlasOrderedJetEntry c A.density p i j
    Integrable F τ ∧
      Tendsto (fun n => classicalLeftPairing b (u (σ n) i) (u (σ n) j))
        atTop (𝓝 (∫ p, F p ∂τ)) := by
  intro hχc u τ F
  let η := inverseHalfDensityWindow B hB hnB c χ hχc
  have hηK := (inverseHalfDensityWindow_tsupport B hB hnB c χ hχc).trans hχ
  have hη : IsCompact (tsupport (η : E₀ → ℝ)) := test_compactSupport η
  obtain ⟨T,hAct,hRep⟩ := exists_classicalFullSymbolOperator b a S hS hbS haS hbDiff haDiff haZero
    haDegree R hLarge
  obtain ⟨hI,hLim⟩ := tendsto_originalVolume_receivingClassicalPairing_globalAmplitude
    r B g hB hg hsB hsG hnB hnG hconv hb hv σ hσ A hA c K hK hKc a S hS haS haDiff
    haZero haDegree η η hηK hηK T (hRep _ hη) i j
  have hAE : receivingClassicalTest c A a η η i j =ᵐ[τ] F := by
    have hW := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
    filter_upwards [ae_restrict_mem (μ := A.control) hW] with p hp
    dsimp only [receivingClassicalTest,F]
    rw [atlasAngularPhaseCode_symbol_eq_unitCovector c p (hKc hp) a haDegree,
      atlasAngularPhaseCode_fst c p (hKc hp)]
    rw [inverseHalfDensityWindow_pairingWeight B hB hnB c χ hχc]
  refine ⟨hI.congr hAE,?_⟩
  change Tendsto _ atTop (𝓝 (∫ p, receivingClassicalTest c A a η η i j p ∂τ)) at hLim
  rw [integral_congr_ae hAE] at hLim
  exact hLim.congr (fun n => by
    rw [fixedVolumeGradientSchwartz_inverseHalfDensityWindow B g hB hg hnB c χ hχc (σ n) i,
      fixedVolumeGradientSchwartz_inverseHalfDensityWindow B g hB hg hnB c χ hχc (σ n) j,hAct])

end Burnett.V03
