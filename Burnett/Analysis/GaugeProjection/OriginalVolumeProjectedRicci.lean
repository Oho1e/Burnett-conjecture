import Burnett.Analysis.GaugeProjection.ProjectedAmplitudeCovariance
import Burnett.Analysis.Microlocal.OriginalVolumeRicciKernel

set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable section

namespace Burnett.P01

open MeasureTheory Matrix Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.F05.ActualCoordinateRicciDensity
open Burnett.F05.ActualCoordinateCurlDensity Burnett.F05.ChartVolumeAmplitude
open Burnett.Microlocal.FixedChartGeometricDensity Burnett.Microlocal.CountableAuxiliaryCharts
open Burnett.Microlocal.CurlDensity Burnett.Microlocal.RicciRow
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.MatrixMeasureAssembly Burnett.Microlocal.PhysicalDensity
open Burnett.Microlocal.SmoothAngularTests
open scoped BigOperators ContDiff Manifold Matrix ComplexOrder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

private theorem roundCovector_ne_zero (q : CompactChartInput M) (p : Chart q.ball) :
    roundCovector p ≠ 0 := by
  intro heq
  simpa only [heq, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_ne_one] using
    roundCovector_dual_pairing p

variable [IsManifold Model ∞ M]

private theorem measurableSet_roundNullShell (B : Field (M := M)) (hB : IsSmooth B)
    (hnB : IsNondegenerate B) (q : CompactChartInput M) :
    MeasurableSet (nullShell (fun p : Chart q.ball => backgroundInverse B q.center p.1)
      roundCovector) := by
  have hG : Continuous (fun y : q.ball.Point => backgroundInverse B q.center y) := by
    have hInv : ContinuousOn (backgroundInverse B q.center)
        (chartAt CoordinateSpace q.center).target :=
      InverseField.continuousOn_matrixInverse _ _
      (ManifoldBilinear.continuousOn_components B hB q.center)
      (fun _ hx => ManifoldVolumeRegularity.coordinate_det_ne_zero B hnB q.center hx)
    exact continuousOn_iff_continuous_restrict.mp (hInv.mono q.ball_in_chart)
  have hξ (a : Index) : Continuous (fun p : Chart q.ball => roundCovector p a) :=
    ((sphereCoordinate a).continuous.comp continuous_snd).congr
      (fun p => sphereCoordinate_apply a p.2)
  have hs : Continuous (fun p : Chart q.ball =>
      symbolNorm (backgroundInverse B q.center p.1) (roundCovector p)) :=
    continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
      ((((continuous_apply b).comp (continuous_apply a)).comp
        (hG.comp continuous_fst)).mul (hξ a)).mul (hξ b)
  exact (isClosed_eq hs continuous_const).measurableSet

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- On the original trace, the very same projected amplitude used for the
mixed pairings is positive, vanishes off the characteristic cone, and has
the Lorenz contraction on the cone. -/
theorem ae_originalVolume_projectedCovariance_ricciPolarization
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
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin) :
    ∀ᵐ p ∂traceMeasure ν,
      let ξ := roundCovector p
      let G := backgroundInverse B q.center p.1
      let P := principalGaugeProjectionMatrix p.2
      let PP := P * chartRoundAmplitude q.ball ν hfin p * Pᴴ
      PP.PosSemidef ∧ (symbolNorm G ξ ≠ 0 → PP = 0) ∧
      (symbolNorm G ξ = 0 → ∀ (v : Pair → ℂ) (b : Index),
        let H := tensorOfVector (PP *ᵥ v)
        IsSymmetricComplexTensor H ∧ complexContracted G ξ H b =
          complexMetricTrace G H * ((ξ b / 2 : ℝ) : ℂ)) := by
  filter_upwards [ae_originalVolume_roundAmplitude_in_ricciKernel r B g hB hg hsB hsG
    hnB hnG hconv hb hv q σ hσ ν hfin hRep] with p hp
  dsimp only
  have hξ := roundCovector_ne_zero q p
  refine ⟨hp.1.mul_mul_conjTranspose_same _, fun hs => ?_, fun hs v b => ?_⟩
  · exact projectedCoordinateCovariance_eq_zero_off_null
      (backgroundInverse B q.center p.1) p.2 _ hξ hs (fun v => (hp.2 v).2)
  · exact projectedCoordinateCovariance_null_contracted
      (backgroundInverse B q.center p.1) p.2 _
      (backgroundInverse_symmetric B hsB hnB q p.1) hξ hs hp.2 v b

/-- The original and projected fixed-chart physical measures agree on all
Borel events on the same round angular section. -/
theorem originalVolume_roundNullMeasure_projected_eq
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
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin) :
    let G (p : Chart q.ball) := backgroundInverse B q.center p.1
    let P (p : Chart q.ball) := principalGaugeProjectionMatrix p.2
    let A := chartRoundAmplitude q.ball ν hfin
    nullPhysicalMeasure (traceMeasure ν) G roundCovector
        (fun _ => (1 : Matrix Pair Pair ℂ)) (fun p => P p * A p * (P p)ᴴ) =
      nullPhysicalMeasure (traceMeasure ν) G roundCovector (fun _ => 1) A := by
  intro G P A
  apply nullPhysicalMeasure_projectedAmplitudeCovariance_eq (traceMeasure ν) G
    (fun p : Chart q.ball => (p.2 : CoordinateSpace)) A (measurableSet_roundNullShell B hB hnB q)
  have hKernel := ae_originalVolume_roundAmplitude_in_ricciKernel r B g hB hg hsB hsG
    hnB hnG hconv hb hv q σ hσ ν hfin hRep
  filter_upwards [ae_restrict_of_ae hKernel] with p hp
  exact ⟨backgroundInverse_symmetric B hsB hnB q p.1, roundCovector_ne_zero q p, hp.1, hp.2⟩

end Burnett.P01
