import Burnett.Analysis.Microlocal.Overlap.GlobalIntrinsicAmplitudeBasisPositivity

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1800000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Matrix Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.UnitCosphere (projection)
open Burnett.F05.ActualChartAuxiliarySection (chartAuxiliaryCosphere chartAuxiliaryInverse)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (chartAuxiliaryAmplitude)
open Burnett.F07.IntrinsicAmplitudeCoordinates (components)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.FixedChartGeometricDensity (auxiliaryUnitCovector roundCovector)
open Burnett.Microlocal.RicciRow (backgroundInverse)
open Burnett.F07.IntrinsicAmplitude (auxiliaryTraceInBasis auxiliaryTraceLinear intrinsicAuxiliaryTrace
   orderedChartAmplitudeComponents)
open Burnett.Geometry.IntrinsicScalarEinstein (inverseMetricTensor)
open scoped ContDiff Manifold Matrix ComplexOrder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The same global amplitude has unit intrinsic auxiliary trace and positive
components in all actual bases almost everywhere. At the same points a
represented chart reads the original matrix and its symmetric Ricci kernel. -/
theorem HasOriginalAmplitudeChartLaws.ae_global_positive_unitTrace_ricciKernel
    {r : Metric (M := M)} {B : Field (M := M)} {g : ℕ → Field (M := M)}
    {hB : IsSmooth B} {hg : ∀ n, IsSmooth (g n)} {hnB : IsNondegenerate B}
    {σ : ℕ → ℕ} {A : IntrinsicAmplitudeCovariance r}
    (hA : HasOriginalAmplitudeChartLaws r B g hB hg hnB σ A)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (hσ : StrictMono σ)
    (q : ℕ → CompactChartInput M) (cover : ⋃ i, (q i).cutoffLocusAbove (1 / 2) = univ)
    (ν : ∀ i, (JetSlot → ℂ) → Measure (Chart (q i).ball))
    (hf : ∀ i v, IsFiniteMeasure (ν i v))
    (hRep : ∀ i, let a := q i
      RepresentsCompactJetPairings a.ball
        (originalGradient_volumeWeightedL2 B g hB hg hnB a.center a.cutoff
          (a.cutoff_support.trans a.ball_in_chart)) σ (ν i) (hf i)) :
    ∀ᵐ p ∂A.control,
      intrinsicAuxiliaryTrace r A.density p = 1 ∧
      (∀ b : Module.Basis Index ℝ (TangentSpace Model (projection p)),
        (components b (A.density p)).PosSemidef ∧
          auxiliaryTraceInBasis b (inverseMetricTensor r.inner (GlobalLeviCivita.inner_nondegenerate r)
            (projection p)) (A.density p) = 1) ∧
      ∃ i : ℕ, ∃ z ∈ amplitudeChartWindow r (q i) ((q i).compactCutoffLocus (1 / 2)),
        chartAuxiliaryCosphere r (q i) z = p ∧
        let C := orderedChartAmplitudeComponents r (q i) A.density z
        C = (chartAmplitudeTraceWeight r (q i) (ν i) (hf i) p)⁻¹ •
          chartAuxiliaryAmplitude r (q i) (ν i) (hf i) z ∧
        C.PosSemidef ∧ auxiliaryTraceLinear (chartAuxiliaryInverse r (q i) z.1) C = 1 ∧
        ∀ v : Pair → ℂ,
          let k (a b : Index) := (C *ᵥ v) (a, b)
          let η := auxiliaryUnitCovector (chartAuxiliaryInverse r (q i) z.1) (roundCovector z)
          IsSymmetricComplexTensor k ∧
            ∀ a b, complexRicciSymbol (backgroundInverse B (q i).center z.1) η k a b = 0 := by
  let K (i : ℕ) := (q i).compactCutoffLocus (1 / 2)
  let U (i : ℕ) := amplitudeCosphereWindow r (K i)
  have hK (i : ℕ) : IsCompact (K i) := (q i).isCompact_compactCutoffLocus (1 / 2)
  have hSub (i : ℕ) : K i ⊆ (q i).nonzeroLocus :=
    (q i).compactCutoffLocus_subset_nonzeroLocus (by norm_num)
  have hCover : ⋃ i, U i = univ := by
    refine eq_univ_of_forall fun p => ?_
    have hp : projection p ∈ ⋃ i, (q i).cutoffLocusAbove (1 / 2) :=
      cover.symm ▸ mem_univ (projection p)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨i, (q i).cutoffLocusAbove_subset_compactCutoffLocus (by norm_num) hi⟩
  have hUnion : A.control.restrict (⋃ i, U i) = A.control := by
    rw [hCover, Measure.restrict_univ]
  rw [← hUnion, ae_restrict_iUnion_iff]
  intro i
  have hBasis := hA.ae_positive_unitTrace_in_basis hsB hsG hnG hconv hb hv hσ
    (q i) (ν i) (hf i) (hRep i) (hK i) (hSub i)
  have hKernel := hA.ae_positive_unitTrace_ricciKernel hsB hsG hnG hconv hb hv hσ
    (q i) (ν i) (hf i) (hRep i) (hK i) (hSub i)
  filter_upwards [hBasis, hKernel] with p hBasisAt hKernelAt
  obtain ⟨z, hz, hp, hC, hPos, hChartTrace, hTrace, hRicci⟩ := hKernelAt
  exact ⟨hTrace, hBasisAt, i, z, hz, hp, hC, hPos, hChartTrace, hRicci⟩

end Burnett.Microlocal.Overlap
