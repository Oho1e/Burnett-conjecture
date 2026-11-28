import Burnett.Analysis.Microlocal.Overlap.GlobalIntrinsicAmplitudePositiveKernel
import Burnett.Analysis.Microlocal.Overlap.ChartAmplitudeContractions
import Burnett.Analysis.Microlocal.Overlap.AtlasAngularPhaseEncoding

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 2600

noncomputable section

namespace Burnett.V03

open Filter MeasureTheory Set Burnett.Geometry ConnectionDifference ManifoldMetric
open ManifoldBilinear ManifoldMetricSequence MaximalChart UnitNullCompactness
open Burnett.RicciSymbol Burnett.Microlocal.Overlap
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitude (intrinsicPhysicalWeight intrinsicPhysicalWeight_eq_chart orderedChartAmplitudeComponents)
open Burnett.F05.ActualChartAuxiliarySection (chartAuxiliaryCosphere chartAuxiliaryRay)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.ActualCoordinateRicciDensity (backgroundInverse_symmetric)
open Burnett.Microlocal.RicciRow (backgroundInverse)
open Burnett.Microlocal.PhysicalDensity (physicalContraction tensorOfVector)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.FixedChartGeometricDensity (auxiliaryUnitCovector roundCovector)
open scoped ContDiff Manifold ComplexOrder Matrix MatrixOrder

local notation "E₀" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]

/-- The receiving auxiliary unit covector is the preferred-chart covector
used by the canonical Euler symbol at the same cotangent point. -/
theorem atlasChartUnitCovector_eq_preferred {r : Metric (M := M)} (c : M) (p : Cosphere r)
    (hp : projection p ∈ (chartAt E₀ c).source) :
    atlasChartUnitCovector (.atPoint c) p = cotangentCoords c p.val := by
  unfold atlasChartUnitCovector
  rw [FixedCotangentChart.fixedChartPhase_preferred c p.val hp]

variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The given original receiving-chart ordered matrix has the Ricci
kernel and the physical quarter weight of the same global amplitude. -/
theorem ae_original_preferredAtlasAmplitude_kernel_and_weight
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalAmplitudeChartLaws r B g hB hg hnB σ A)
    (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (K : Set M) (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus) :
    let c := AtlasChart.atPoint q.center
    ∀ᵐ p ∂(A.control.restrict (amplitudeCosphereWindow r K)),
      let x := c.chart (projection p)
      let G := backgroundInverse B q.center x
      let ξ := atlasChartUnitCovector c p
      let C := atlasAmplitudeMatrix c A.density p
      ξ ≠ 0 ∧ C.PosSemidef ∧ IsSymmetricTensor G ∧
        (∀ v : Pair → ℂ,
          let k := tensorOfVector (C *ᵥ v)
          IsSymmetricComplexTensor k ∧ ∀ a b, complexRicciSymbol G ξ k a b = 0) ∧
        intrinsicPhysicalWeight B hnB A.density p = ((1 / 4 : ℂ) * physicalContraction G C).re := by
  intro c
  have hLoc := hA.ae_positive_unitTrace_ricciKernel hsB hsG hnG hconv hb hv hσ q ν hf hRep hK hSub
  filter_upwards [hLoc] with p hp
  obtain ⟨z,_,rfl,_,hPSD,_,_,hRicci⟩ := hp
  let p := chartAuxiliaryCosphere r q z
  let e := chartAt E₀ q.center
  have hz := q.ball_in_chart z.1.property
  have hpc : projection p ∈ e.source := e.symm_mapsTo hz
  have hx : c.chart (projection p) = z.1.val := e.right_inv hz
  have hMat : atlasAmplitudeMatrix c A.density p = orderedChartAmplitudeComponents r q A.density z := by
    rw [atlasAmplitudeMatrix_of_mem c A.density p hpc,
      orderedChartAmplitudeComponents_eq_chartComponents r q A.density z hpc]
  have hξ := atlasChartUnitCovector_preferred_ray r q z
  dsimp only
  rw [hMat,hx,hξ]
  refine ⟨hξ ▸ atlasChartUnitCovector_ne_zero c p hpc,hPSD,
    backgroundInverse_symmetric B hsB hnB q z.1,hRicci,?_⟩
  exact intrinsicPhysicalWeight_eq_chart r B hsB hnB q A.density z

end Burnett.V03
