import Burnett.Analysis.Microlocal.Overlap.OriginalAngularCosphereConsumer
import Burnett.Analysis.Microlocal.Overlap.GlobalAmplitudeEntryMeasure

/-! Use the original compact-chart angular action to read the single global amplitude. -/

set_option autoImplicit false
set_option maxRecDepth 2800
set_option maxHeartbeats 1900000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Function Filter MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Geometry.UnitNullCompactness (cotangentCoords)
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ComplexConjugate ContDiff Manifold Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
variable [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The local normalized principal action reads the ordered amplitude entry of the
very same global covariance, integrated on the chosen compact base restriction. -/
theorem tendsto_originalVolume_angularAction_globalAmplitudeOn
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B)
    (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalAmplitudeChartLaws r B g hB hg hnB σ A)
    (K : Set M) (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus)
    (a : E → E → ℂ) (hSupport : ∀ ξ, tsupport (fun x => a x ξ) ⊆ chartAt E q.center '' K)
    (hJoint : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (hZero : ContDiff ℝ ∞ (fun x => a x 0)) (hDegree : ∀ x, DegreeZero (a x))
    (i j : JetSlot) :
    let f := originalVolumeAngularInput B g hB hg hnB q
    let fA (p : Cosphere r) :=
      let ξ := cotangentCoords q.center p.val
      (a (chartAt E q.center (projection p)) (WithLp.toLp 2 ξ) * (ξ i.1 : ℂ) * (ξ j.1 : ℂ)) *
        intrinsicAmplitudeMatrix q.center A.density p j.2 i.2
    Integrable fA (A.control.restrict (amplitudeCosphereWindow r K)) ∧
      Tendsto (fun n => ∫ x, conj (f (σ n) i x) *
        firstOrderAction (inverseCutoffAngularSymbol q.cutoff a) (f (σ n) j) x)
        atTop (𝓝 (∫ p in amplitudeCosphereWindow r K, fA p ∂A.control)) := by
  intro f fA
  let τ := A.control.restrict (amplitudeCosphereWindow r K)
  let F (p : Cosphere r) := intrinsicAmplitudeMatrix q.center A.density p j.2 i.2
  let W := cosphereAngularJetWeight r q a i.1 j.1
  obtain ⟨hF, hEq⟩ := original_globalAmplitude_entryMeasure_on_compactChart r B g hB hg hsB hsG hnB hnG
    hconv hb hv σ hσ A hA q ν hfin hRep hK hSub j.2 i.2
  have hI : Integrable F τ := hF
  change τ.withDensityᵥ F = normalizedCosphereAmplitudeEntryOn r q ν hfin j.2 i.2 K at hEq
  obtain ⟨hW, C, hC, hBound⟩ := cosphereAngularJetWeight_measurable_bounded r q a hJoint i.1 j.1
  have hFormula : (fun p => W p * F p) =ᵐ[τ] fA := by
    change (fun p => W p * F p) =ᵐ[A.control.restrict (amplitudeCosphereWindow r K)] fA
    rw [(hA q ν hfin hRep K hK hSub).1]
    filter_upwards [ae_chartAmplitudeTraceControl_restrict_exists_windowPoint r q ν hfin
      hK.isClosed.measurableSet] with p hp
    obtain ⟨z, _, rfl⟩ := hp
    exact congrArg (fun b : ℂ => b * F (chartUnitCospherePoint r q z))
      (cosphereAngularJetWeight_eq_actual r q a hDegree i.1 j.1 z)
  refine ⟨(hI.bdd_mul hW.aestronglyMeasurable ⟨C, hBound⟩).congr hFormula, ?_⟩
  have hLim := tendsto_originalVolume_angularAction_cosphereAmplitudeEntryOn r B g hB hg hsB hsG hnB hnG
    hconv hb hv q σ hσ ν hfin hRep K hK hSub a hSupport hJoint hZero hDegree i j
  have hReplace : complexMeasureBorelIntegral (normalizedCosphereAmplitudeEntryOn r q ν hfin j.2 i.2 K) W =
      ∫ p, W p * F p ∂τ := by
    rw [← hEq]
    refine complexMeasureBorelIntegral_eq_of_setIntegrals _ τ id measurable_id F hI ?_ W hW C hC hBound
    intro S hS
    change (τ.withDensityᵥ F) S = ∫ p in S, F p ∂τ
    exact withDensityᵥ_apply hI hS
  change Tendsto _ atTop (𝓝 (∫ p, fA p ∂τ))
  rw [← integral_congr_ae hFormula, ← hReplace]
  exact hLim

end Burnett.Microlocal.Overlap
