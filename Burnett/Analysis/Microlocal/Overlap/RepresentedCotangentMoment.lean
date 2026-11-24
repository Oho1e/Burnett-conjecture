import Burnett.Analysis.Microlocal.Overlap.RepresentedChartMoment
import Burnett.Analysis.Microlocal.PhysicalChartCover
import Burnett.Analysis.Microlocal.Overlap.NormalizedCotangentPhysicalMeasure

set_option autoImplicit false
set_option maxHeartbeats 540000
noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.RicciSymbol
open Burnett.Analysis.LocalWeakRicciIdentification
  (coordinateMeasure_test_integrable coordinateRicci_component_smoothOn)
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricTransition
open ManifoldMetricSequence BackgroundConnection CurvatureDifference UnitNullCompactness
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.FixedChartGeometricDensity (auxiliaryUnitCovector roundCovector)
open Burnett.X02.SobolevTestJet (D Space test_smooth test_compactSupport)
open scoped ContDiff Manifold Topology ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- The common chart law transfers the Ricci moment to the ambient cotangent
measure on that chart's full nonzero-cutoff locus. -/
theorem original_chartRicci_eq_cotangent_secondMoment
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (μ : Measure (CotangentBundle M))
    (hPatch : μ.restrict ((fun p : CotangentBundle M => p.proj) ⁻¹' q.nonzeroLocus) =
      (normalizedCotangentPhysicalMeasure q r B hSig.isNondegenerate ν hf).restrict
        ((fun p : CotangentBundle M => p.proj) ⁻¹' q.nonzeroLocus))
    (ψ : D) (hψ : tsupport (ψ : Space → ℝ) ⊆ {x | (q.cutoff : Space → ℝ) x ≠ 0})
    (b d : Index) :
    let R (x : Space) := (ψ : Space → ℝ) x *
      coordinateRicci (computedConnection (coordinateBilinear B q.center)) x b d
    let F (p : CotangentBundle M) := (ψ : Space → ℝ) (chartAt CoordinateSpace q.center p.proj) *
      (cotangentCoords q.center p b * cotangentCoords q.center p d)
    let S := (fun p : CotangentBundle M => p.proj) ⁻¹' q.nonzeroLocus
    let V := ManifoldVolume.coordinateMeasure B q.center
    Integrable R V ∧ IntegrableOn F S μ ∧ (∫ x, R x ∂V) = ∫ p in S, F p ∂μ := by
  classical
  intro R F S V
  let e := chartAt CoordinateSpace q.center
  let m := chartPhysicalJetMeasure r B hSig.isNondegenerate q ν hf
  let ray := chartAuxiliaryRay r q
  let ξ (p : Chart q.ball) := auxiliaryUnitCovector (chartAuxiliaryInverse r q p.1) (roundCovector p)
  have hS : MeasurableSet S := continuous_cotangent_projection.measurable q.isOpen_nonzeroLocus.measurableSet
  have hSub : S ⊆ (fun p : CotangentBundle M => p.proj) ⁻¹' e.source := fun _ hp => hp.1
  have hBase : ContinuousOn (fun p : CotangentBundle M => e p.proj) S :=
    e.continuousOn.comp continuous_cotangent_projection.continuousOn hSub
  have hFiber (i : Index) : ContinuousOn (fun p : CotangentBundle M => cotangentCoords q.center p i) S :=
    (continuous_apply i).comp_continuousOn ((continuousOn_cotangentCoords q.center).mono hSub)
  have hF : ContinuousOn F S :=
    ((test_smooth ψ).continuous.comp_continuousOn hBase).mul ((hFiber b).mul (hFiber d))
  have hTest : Measurable (S.indicator F) :=
    hF.measurable_piecewise continuous_const.continuousOn hS
  have hCutoff : Measurable (chartInverseCutoffSquare q) :=
    (((test_smooth q.cutoff).continuous.measurable.comp
      (continuous_subtype_val.comp continuous_fst).measurable).inv.pow_const 2).ennreal_ofReal
  have hFinite : ∀ᵐ p ∂m, chartInverseCutoffSquare q p < ⊤ :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  let f (p : Chart q.ball) := ((ψ : Space → ℝ) p.1 * ((q.cutoff : Space → ℝ) p.1 ^ 2)⁻¹) *
    (ξ p b * ξ p d)
  have hRaySrc (p : Chart q.ball) : (ray p).proj ∈ e.source :=
    e.symm_mapsTo (q.ball_in_chart p.1.property)
  have hRayPoint (p : Chart q.ball) :
      f p = (chartInverseCutoffSquare q p).toReal • S.indicator F (ray p) := by
    have hCoord : e (ray p).proj = p.1 := e.right_inv (q.ball_in_chart p.1.property)
    have hFCoord : F (ray p) = (ψ : Space → ℝ) p.1 * (ξ p b * ξ p d) := by
      change (ψ : Space → ℝ) (e (ray p).proj) *
        (cotangentCoords q.center (ray p) b * cotangentCoords q.center (ray p) d) = _
      rw [hCoord, chartAuxiliaryRay_coords]
    have hN : ray p ∈ S ↔ (q.cutoff : Space → ℝ) p.1 ≠ 0 := by
      change ((ray p).proj ∈ e.source ∧ (q.cutoff : Space → ℝ) (e (ray p).proj) ≠ 0) ↔ _
      rw [hCoord, and_iff_right (hRaySrc p)]
    dsimp only [f]
    rw [smul_eq_mul, chartInverseCutoffSquare, ENNReal.toReal_ofReal (sq_nonneg _), ← inv_pow]
    by_cases hpIn : ray p ∈ S
    · rw [indicator_of_mem hpIn, hFCoord]
      ring
    · have hzero : (ψ : Space → ℝ) p.1 = 0 := by
        by_contra hne
        exact hpIn (hN.mpr (hψ (subset_tsupport _ hne)))
      simp only [indicator_of_notMem hpIn, hzero, zero_mul, mul_zero]
  have hLeft : Integrable R V :=
    coordinateMeasure_test_integrable B hB q.center (test_smooth ψ) (test_compactSupport ψ)
      (fun _ hx => q.ball_in_chart (q.cutoff_support (subset_tsupport _ (hψ hx))))
      (coordinateRicci_component_smoothOn B hB hSig.isNondegenerate q.center b d)
  have hWeight : Continuous (fun p : Chart q.ball =>
      (ψ : Space → ℝ) p.1 * ((q.cutoff : Space → ℝ) p.1 ^ 2)⁻¹) :=
    (test_smooth (inverseSquareTest q.cutoff ψ hψ)).continuous.comp
      (continuous_subtype_val.comp continuous_fst)
  have hξ (i : Index) : Continuous (fun p => ξ p i) := by
    have h : ContinuousOn (fun p => cotangentCoords q.center (ray p) i) univ :=
      (continuous_apply i).comp_continuousOn ((continuousOn_cotangentCoords q.center).comp
        (continuous_chartAuxiliaryRay r q).continuousOn (fun p _ => hRaySrc p))
    exact (continuousOn_univ.mp h).congr fun p => congrFun (chartAuxiliaryRay_coords r q p) i
  letI : IsFiniteMeasure m := isFiniteMeasure_chartPhysicalJetMeasure r B hB hSig.isNondegenerate q ν hf
  have hLocal : Integrable f m := (hWeight.mul ((hξ b).mul (hξ d))).integrable_of_hasCompactSupport
    (isClosed_tsupport f).isCompact
  have hRight : IntegrableOn F S μ := by
    rw [IntegrableOn, hPatch]
    refine (integrable_indicator_iff hS).mp ?_
    rw [normalizedCotangentPhysicalMeasure]
    apply (integrable_map_measure hTest.aestronglyMeasurable
      (continuous_chartAuxiliaryRay r q).measurable.aemeasurable).2
    exact (integrable_withDensity_iff_integrable_smul₀' hCutoff.aemeasurable hFinite).2
      (hLocal.congr (Eventually.of_forall hRayPoint))
  refine ⟨hLeft, hRight, ?_⟩
  have hHere := original_chartRicci_eq_physical_secondMoment r B g hB hg hSig hsG hnG hconv hb hv
    q σ hσ ν hf hRep ψ hψ b d
  calc
    (∫ x, R x ∂V) = ∫ p, f p ∂m := hHere
    _ = ∫ p in S, F p ∂μ := by
      rw [hPatch, ← integral_indicator hS, normalizedCotangentPhysicalMeasure,
        integral_map (continuous_chartAuxiliaryRay r q).measurable.aemeasurable hTest.aestronglyMeasurable,
        integral_withDensity_eq_integral_toReal_smul hCutoff hFinite]
      exact integral_congr_ae (Eventually.of_forall hRayPoint)

end Burnett.Microlocal.Overlap
