import Burnett.Analysis.Microlocal.Overlap.GlobalIntrinsicAmplitudePositiveKernel

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1300000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Matrix Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.UnitCosphere (projection)
open Burnett.F05.ActualChartAuxiliarySection (chartAuxiliaryCosphere)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OverlapCovectors (tensorPairTransition)
open Burnett.F07.IntrinsicAmplitudeCoordinates
  (AmplitudeTensor components components_change chartComponents chartTangentBasis)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.F07.IntrinsicAmplitude (auxiliaryTraceInBasis intrinsicAuxiliaryTrace_eq_basis )
open Burnett.Geometry.IntrinsicScalarEinstein (inverseMetricTensor)
open scoped BigOperators ContDiff Manifold Matrix ComplexOrder

/-- Hermitian semidefiniteness of a four-slot covariance holds in every real basis. -/
theorem components_posSemidef_of_basis {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b e : Module.Basis Index ℝ V) (F : AmplitudeTensor V)
    (hPos : (components b F).PosSemidef) : (components e F).PosSemidef := by
  classical
  let T : Matrix Index Index ℝ := fun i j => b.repr (e i) j
  have hT (i : Index) : e i = ∑ j, T i j • b j := (b.sum_repr (e i)).symm
  rw [components_change b e T hT F]
  exact hPos.mul_mul_conjTranspose_same (tensorPairTransition T)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- There is one full-measure event on which every real basis of each actual
tangent fiber reads a positive semidefinite covariance of unit auxiliary trace. -/
theorem HasOriginalAmplitudeChartLaws.ae_positive_unitTrace_in_basis
    {r : Metric (M := M)} {B : Field (M := M)} {g : ℕ → Field (M := M)}
    {hB : IsSmooth B} {hg : ∀ n, IsSmooth (g n)} {hnB : IsNondegenerate B}
    {σ : ℕ → ℕ} {A : IntrinsicAmplitudeCovariance r}
    (hA : HasOriginalAmplitudeChartLaws r B g hB hg hnB σ A)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (hσ : StrictMono σ)
    (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus) :
    ∀ᵐ p ∂A.control.restrict (amplitudeCosphereWindow r K),
      ∀ b : Module.Basis Index ℝ (TangentSpace Model (projection p)),
        (components b (A.density p)).PosSemidef ∧
          auxiliaryTraceInBasis b (inverseMetricTensor r.inner (GlobalLeviCivita.inner_nondegenerate r)
            (projection p)) (A.density p) = 1 := by
  filter_upwards [hA.ae_positive_unitTrace_ricciKernel hsB hsG hnG hconv hb hv hσ q ν hf hRep hK hSub]
    with p hp
  obtain ⟨z, _, rfl, _, hPos, _, hUnit, _⟩ := hp
  let p := chartAuxiliaryCosphere r q z
  have hx : projection p ∈ (chartAt CoordinateSpace q.center).source :=
    (chartAt CoordinateSpace q.center).symm_mapsTo (q.ball_in_chart z.1.property)
  let b := chartTangentBasis (.atPoint q.center) (projection p) hx
  have hPosB : (components b (A.density p)).PosSemidef := by
    change (chartComponents (.atPoint q.center) (projection p) hx (A.density p)).PosSemidef
    rw [← orderedChartAmplitudeComponents_eq_chartComponents r q A.density z hx]
    exact hPos
  intro e
  exact ⟨components_posSemidef_of_basis b e (A.density p) hPosB,
    (intrinsicAuxiliaryTrace_eq_basis r A.density p e).symm.trans hUnit⟩

end Burnett.Microlocal.Overlap
