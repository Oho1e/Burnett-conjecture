import Burnett.Analysis.Microlocal.ActualChartAuxiliarySection
import Burnett.Analysis.Microlocal.OriginalVolumeRicciKernel

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Burnett.F05.OriginalVolumeAuxiliaryAmplitude

open MeasureTheory Matrix Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.F05.ActualChartAuxiliarySection Burnett.F05.ActualCoordinateRicciDensity
open Burnett.F05.ActualCoordinateCurlDensity Burnett.F05.ChartVolumeAmplitude
open Burnett.Microlocal.FixedChartGeometricDensity Burnett.Microlocal.CountableAuxiliaryCharts
open Burnett.Microlocal.CurlDensity Burnett.Microlocal.RicciRow
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.MatrixMeasureAssembly
open scoped ContDiff Manifold Matrix ComplexOrder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The covariance density of the amplitudes contracted at the auxiliary unit ray. -/
def chartAuxiliaryAmplitude (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (p : Chart q.ball) : Matrix Pair Pair ℂ :=
  let R := chartAuxiliaryInverse r q p.1
  auxiliaryAmplitudeCovariance R (auxiliaryUnitCovector R (roundCovector p))
    (chartPhysicalCovariance q.ball ν hfin p)

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- The same physical jet covariance has both its round and its metric-unit
factorization. The amplitude gains the square of the auxiliary norm. -/
theorem ae_originalVolume_auxiliaryAmplitude
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
      let R := chartAuxiliaryInverse r q p.1
      let η := auxiliaryUnitCovector R ξ
      let S := chartAuxiliaryAmplitude r q ν hfin p
      S.PosSemidef ∧
      (∀ i j : JetSlot, chartPhysicalCovariance q.ball ν hfin p i j =
        (η i.1 : ℂ) * (η j.1 : ℂ) * S i.2 j.2) ∧
      S = ((symbolNorm R ξ : ℝ) : ℂ) • chartRoundAmplitude q.ball ν hfin p ∧
      ∀ v : Pair → ℂ, let k (a b : Index) := (S *ᵥ v) (a, b)
        IsSymmetricComplexTensor k ∧
          ∀ a b, complexRicciSymbol (backgroundInverse B q.center p.1) η k a b = 0 := by
  have hF := ae_originalVolume_round_covariance_factor r B g hB hg hnB hsB hsG
    hconv hb q σ hσ ν hfin hRep
  have hRic := ae_all_iff.mpr (ae_originalVolume_ricciRows_same_density r B g hB hg hsB hsG
    hnB hnG hconv hb hv q σ hσ ν hfin hRep)
  obtain ⟨_, _, _, _, _, hDensity, _⟩ := hRep
  filter_upwards [hF, hRic, hDensity] with p hf hr hp
  dsimp only
  let ξ := roundCovector p
  let R := chartAuxiliaryInverse r q p.1
  let η := auxiliaryUnitCovector R ξ
  let G := backgroundInverse B q.center p.1
  let N := chartPhysicalCovariance q.ball ν hfin p
  have hn : 0 < symbolNorm R ξ := chartAuxiliaryNorm_pos r q p
  have hRic0 : ricciJetMatrix G ξ * N = 0 := by
    ext i j
    exact congrFun (hr i) j
  have hcurl : curlMatrix η * N * (curlMatrix η)ᴴ = 0 := by
    unfold η auxiliaryUnitCovector
    rw [curlMatrix_rescale, Matrix.smul_mul, hf.2.1, smul_zero, Matrix.zero_mul]
  have hricci : ricciJetMatrix G η * N * (ricciJetMatrix G η)ᴴ = 0 := by
    unfold η auxiliaryUnitCovector
    rw [ricciJetMatrix_rescale, Matrix.smul_mul, hRic0, smul_zero, Matrix.zero_mul]
  obtain ⟨hS, hFactor, hEntry, hKernel⟩ := auxiliary_covariance_factorization_and_kernel
    R G η (auxiliaryUnitCovector_unit R ξ hn)
    (backgroundInverse_symmetric B hsB hnB q p.1) N hp.1.transpose hf.1 hcurl hricci
  refine ⟨hS, hEntry, ?_, hKernel⟩
  have hscale := auxiliary_factorization_amplitude_scale R ξ (roundCovector_dual_pairing p)
    hn N hFactor
  rw [auxiliaryScale, inv_pow, inv_inv, Real.sq_sqrt hn.le] at hscale
  exact hscale

end Burnett.F05.OriginalVolumeAuxiliaryAmplitude
