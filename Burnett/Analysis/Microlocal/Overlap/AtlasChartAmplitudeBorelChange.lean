import Burnett.Analysis.Microlocal.Overlap.AtlasChartAmplitudeIntegrability
import Burnett.Geometry.Cotangent.FixedChartNaturality

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 1300000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence UnitNullCompactness
open MaximalChart (AtlasChart)
open UnitCosphere (Cosphere projection)
open FixedCotangentChart (Phase fixedChartPhase fixedPhaseTransition phaseOverlap isOpen_phaseOverlap
  continuousOn_fixedPhaseTransition measurable_fixedChartPhase_comp fixedChartPhase_mem_overlap
  fixedPhaseTransition_fixedChartPhase)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open scoped ComplexConjugate ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- Extend the true cotangent lift of a chart transition by zero off its phase domain. -/
def borelAtlasPhaseTransition (c d : AtlasChart M) : Phase → Phase := by
  classical
  exact (phaseOverlap c d).piecewise (fixedPhaseTransition c d) (fun _ => (0, 0))

theorem measurable_borelAtlasPhaseTransition (c d : AtlasChart M) :
    Measurable (borelAtlasPhaseTransition c d) := by
  classical
  exact (continuousOn_fixedPhaseTransition c d).measurable_piecewise continuous_const.continuousOn
    (isOpen_phaseOverlap c d).measurableSet

variable [IsManifold Model ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- The target chart's finite complex entry measure equals the weighted
source entry sum pushed along the true cotangent lift on the common window. -/
theorem atlasAmplitudeEntryMeasure_change_on_compact
    (r : Metric (M := M)) (c d : AtlasChart M) (J : AmplitudeCovarianceDensity r)
    (μ : Measure (Cosphere r)) {K : Set M} (hK : IsCompact K)
    (hSub : K ⊆ c.chart.source ∩ d.chart.source)
    (hSrc : ∀ i j, Integrable (fun p => atlasAmplitudeMatrix c J p i j)
      (μ.restrict (amplitudeCosphereWindow r K))) (i j : Pair) :
    let ρ := μ.restrict (amplitudeCosphereWindow r K)
    let φ (b : AtlasChart M) := fixedChartPhase b ∘ (Subtype.val : Cosphere r → CotangentBundle M)
    let T (p : Cosphere r) := atlasAmplitudeTransition c d (projection p)
    let weighted (p : Cosphere r) := ∑ k : Pair, ∑ l : Pair,
      (T p i l * conj (T p j k)) * atlasAmplitudeMatrix c J p l k
    ((ρ.withDensityᵥ (fun p => atlasAmplitudeMatrix d J p i j)).map (φ d) : ComplexMeasure Phase) =
      ((ρ.withDensityᵥ weighted).map (φ c)).map (borelAtlasPhaseTransition c d) := by
  classical
  intro ρ φ T weighted
  let G := borelAtlasPhaseTransition c d
  have hφ (b : AtlasChart M) : Measurable (φ b) :=
    measurable_fixedChartPhase_comp (Subtype.val : Cosphere r → CotangentBundle M)
      continuous_subtype_val b
  have hG : Measurable G := measurable_borelAtlasPhaseTransition c d
  have hW := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  have hOn : ∀ᵐ p ∂ρ, projection p ∈ c.chart.source ∩ d.chart.source :=
    (ae_restrict_mem (μ := μ) hW).mono (fun _ hp => hSub hp)
  have hEntry : (fun p => atlasAmplitudeMatrix d J p i j) =ᵐ[ρ] weighted := by
    filter_upwards [hOn] with p hp
    exact atlasAmplitudeMatrix_entry_change c d J p hp.1 hp.2 i j
  have hPhase : (φ d) =ᵐ[ρ] G ∘ (φ c) := by
    filter_upwards [hOn] with p hp
    change fixedChartPhase d p.val =
      (phaseOverlap c d).piecewise (fixedPhaseTransition c d) (fun _ => (0, 0))
        (fixedChartPhase c p.val)
    rw [piecewise_eq_of_mem _ _ _ (fixedChartPhase_mem_overlap c d p.val hp.1 hp.2)]
    exact (fixedPhaseTransition_fixedChartPhase c d p.val hp.1 hp.2).symm
  have hI : Integrable weighted ρ := integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ =>
    integrable_atlasAmplitudeMatrix_change_terms_on_compact r c d J μ hK hSub hSrc i j k l
  calc
    _ = (ρ.withDensityᵥ weighted).map (φ d) :=
      congrArg (fun m : ComplexMeasure (Cosphere r) => m.map (φ d)) (WithDensityᵥEq.congr_ae hEntry)
    _ = _ := by
      ext S hS
      rw [VectorMeasure.map_apply _ (hφ d) hS, VectorMeasure.map_apply _ hG hS,
        VectorMeasure.map_apply _ (hφ c) (hG hS),
        withDensityᵥ_apply hI (hφ d hS), withDensityᵥ_apply hI (hφ c (hG hS))]
      apply setIntegral_congr_set
      filter_upwards [hPhase] with p hp
      change (φ d p ∈ S) = (G (φ c p) ∈ S)
      exact congrArg (fun z : Phase => z ∈ S) hp

variable [SecondCountableTopology M]

/-- The original chart witnesses give the complex Borel entry law for any
two compatible charts and any compact subset of their common source. -/
theorem original_globalAmplitude_atlasChart_entryMeasure_change_on_compact
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (q : ℕ → CompactChartInput M) (cover : ⋃ i, (q i).cutoffLocusAbove (1 / 2) = univ)
    (ν : ∀ i, (JetSlot → ℂ) → Measure (Chart (q i).ball))
    (hf : ∀ i v, IsFiniteMeasure (ν i v))
    (hRep : ∀ i, let a := q i
      RepresentsCompactJetPairings a.ball
        (originalGradient_volumeWeightedL2 B g hB hg hnB a.center a.cutoff
          (a.cutoff_support.trans a.ball_in_chart)) σ (ν i) (hf i))
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalAmplitudeChartLaws r B g hB hg hnB σ A)
    (c d : AtlasChart M) {K : Set M} (hK : IsCompact K)
    (hSub : K ⊆ c.chart.source ∩ d.chart.source) (i j : Pair) :
    let ρ := A.control.restrict (amplitudeCosphereWindow r K)
    let φ (b : AtlasChart M) := fixedChartPhase b ∘ (Subtype.val : Cosphere r → CotangentBundle M)
    let T (p : Cosphere r) := atlasAmplitudeTransition c d (projection p)
    let weighted (p : Cosphere r) := ∑ k : Pair, ∑ l : Pair,
      (T p i l * conj (T p j k)) * atlasAmplitudeMatrix c A.density p l k
    ((ρ.withDensityᵥ (fun p => atlasAmplitudeMatrix d A.density p i j)).map (φ d) : ComplexMeasure Phase) =
      ((ρ.withDensityᵥ weighted).map (φ c)).map (borelAtlasPhaseTransition c d) :=
  atlasAmplitudeEntryMeasure_change_on_compact r c d A.density A.control hK hSub
    (fun a b => original_globalAmplitude_integrable_atlasChart_on_compact r B g hB hg hsB hsG hnB hnG
      hconv hb hv σ hσ q cover ν hf hRep A hA c hK (hSub.trans inter_subset_left) a b) i j

end Burnett.Microlocal.Overlap
