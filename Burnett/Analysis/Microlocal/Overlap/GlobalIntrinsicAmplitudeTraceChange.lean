import Burnett.Analysis.Microlocal.Overlap.CompactIntrinsicAmplitudeTraceChange

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 1200000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open UnitCosphere (Cosphere projection)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff ENNReal Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- Compare both globally assembled controls and tensor densities on the same
original subsequence. The positive radial map preserves the actual base, and
the target trace is taken on the old normalized tensor in that fiber. -/
theorem original_globalIntrinsicAmplitude_trace_changeAuxiliary
    (r r' : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (q : ℕ → CompactChartInput M) (cover : ⋃ i, (q i).cutoffLocusAbove (1 / 2) = univ)
    (ν : ∀ i, (JetSlot → ℂ) → Measure (Chart (q i).ball))
    (hf : ∀ i v, IsFiniteMeasure (ν i v))
    (hRep : ∀ i, let a := q i
      RepresentsCompactJetPairings a.ball
        (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate a.center a.cutoff
          (a.cutoff_support.trans a.ball_in_chart)) σ (ν i) (hf i))
    (A : IntrinsicAmplitudeCovariance r) (A' : IntrinsicAmplitudeCovariance r')
    (hA : HasOriginalAmplitudeChartLaws r B g hB hg hSig.isNondegenerate σ A)
    (hA' : HasOriginalAmplitudeChartLaws r' B g hB hg hSig.isNondegenerate σ A') :
    let F := renormalizeUnitCosphere r r'
    let t := intrinsicAmplitudeTraceInMetric r r' A.density
    AEMeasurable t A.control ∧ (∀ᵐ p ∂A.control, 0 < t p) ∧
      A'.control = (A.control.withDensity
        (fun p => cotangentAuxiliaryWeight r' p.val * ENNReal.ofReal (t p))).map F ∧
      (∀ᵐ p ∂A.control, pullbackAmplitudeDensity r r' A'.density p = (t p)⁻¹ • A.density p) := by
  intro F t
  let K (i : ℕ) := (q i).compactCutoffLocus (1 / 2)
  let U (i : ℕ) := amplitudeCosphereWindow r (K i)
  let U' (i : ℕ) := amplitudeCosphereWindow r' (K i)
  have hK (i : ℕ) : IsCompact (K i) := (q i).isCompact_compactCutoffLocus (1 / 2)
  have hSub (i : ℕ) : K i ⊆ (q i).nonzeroLocus :=
    (q i).compactCutoffLocus_subset_nonzeroLocus (by norm_num)
  have hU (i : ℕ) : MeasurableSet (U i) :=
    measurableSet_amplitudeCosphereWindow r (hK i).isClosed.measurableSet
  have hU' (i : ℕ) : MeasurableSet (U' i) :=
    measurableSet_amplitudeCosphereWindow r' (hK i).isClosed.measurableSet
  have hCover (aux : Metric (M := M)) : ⋃ i, amplitudeCosphereWindow aux (K i) = univ := by
    refine eq_univ_of_forall fun p => ?_
    have hp : projection p ∈ ⋃ i, (q i).cutoffLocusAbove (1 / 2) :=
      cover.symm ▸ mem_univ (projection p)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨i, (q i).cutoffLocusAbove_subset_compactCutoffLocus (by norm_num) hi⟩
  have hPre (i : ℕ) : F ⁻¹' U' i = U i := by
    ext p
    change projection (F p) ∈ K i ↔ projection p ∈ K i
    rw [show projection (F p) = projection p from renormalizeUnitCosphere_projection r r' p]
  have hLocal (i : ℕ) := original_intrinsicAmplitude_trace_changeAuxiliary_on_compactChart
    r r' B g hB hg hSig hsG hnG hconv hb hv σ hσ A A' hA hA' (q i) (ν i) (hf i) (hRep i)
      (hK i) (hSub i)
  have hMeas : AEMeasurable t A.control := by
    have hLocalMeas (i : ℕ) : AEMeasurable t (A.control.restrict (U i)) := (hLocal i).1
    have hUnion := aemeasurable_iUnion_iff.mpr hLocalMeas
    rwa [show ⋃ i, U i = univ from hCover r, Measure.restrict_univ] at hUnion
  have hProperties : ∀ᵐ p ∂A.control, 0 < t p ∧
      pullbackAmplitudeDensity r r' A'.density p = (t p)⁻¹ • A.density p := by
    have hUnion := (ae_restrict_iUnion_iff U (fun p => 0 < t p ∧
      pullbackAmplitudeDensity r r' A'.density p = (t p)⁻¹ • A.density p)).mpr
      (fun i => (hLocal i).2.1.and (hLocal i).2.2.2)
    rwa [show ⋃ i, U i = univ from hCover r, Measure.restrict_univ] at hUnion
  refine ⟨hMeas, hProperties.mono (fun _ hp => hp.1), ?_, hProperties.mono (fun _ hp => hp.2)⟩
  apply Measure.ext_of_iUnion_eq_univ (show ⋃ i, U' i = univ from hCover r')
  intro i
  have hF : MeasurableEmbedding F := measurableEmbedding_renormalizeUnitCosphere r r'
  rw [Measure.restrict_map hF.measurable (hU' i), hPre i, restrict_withDensity (hU i)]
  exact (hLocal i).2.2.1

end Burnett.Microlocal.Overlap
