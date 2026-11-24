import Burnett.Analysis.Microlocal.Overlap.GlobalIntrinsicAmplitudePositiveKernel
import Burnett.Analysis.Microlocal.Overlap.OriginalTracePhysicalContraction

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 2100000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set Filter MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence UnitNullCompactness
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian measurableEmbedding_coe)
open Burnett.F05.ActualChartAuxiliarySection (chartAuxiliaryCosphere)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.F07.IntrinsicAmplitude (intrinsicPhysicalWeight)
open scoped ContDiff Manifold ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- The null restriction and quarter contraction of one intrinsic covariance. -/
def HasIntrinsicPhysicalContraction (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (A : IntrinsicAmplitudeCovariance r) (μ : Measure (Cosphere r)) : Prop :=
  let Z : Set (Cosphere r) := {p | hamiltonian B hn p = 0}
  let τ := A.control.restrict Z
  let w := intrinsicPhysicalWeight B hn A.density
  MeasurableSet Z ∧ AEMeasurable w τ ∧ (∀ᵐ p ∂τ, 0 ≤ w p) ∧
    μ = τ.withDensity (fun p => ENNReal.ofReal (w p))

/-- Contract the intrinsic covariance on the null shell. The resulting measure
is the original physical measure whose chart laws use the same witnesses. -/
theorem original_globalPhysicalContraction_of_chartLaws
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
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
    (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalAmplitudeChartLaws r B g hB hg hSig.isNondegenerate σ A)
    (μ : Measure (Cosphere r))
    (hChart : ∀ i,
      let S := (fun p : CotangentBundle M => p.proj) ⁻¹' (q i).nonzeroLocus
      (μ.map (Subtype.val : Cosphere r → CotangentBundle M)).restrict S =
        (normalizedCotangentPhysicalMeasure (q i) r B hSig.isNondegenerate (ν i) (hf i)).restrict S) :
    HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ := by
  unfold HasIntrinsicPhysicalContraction
  intro Z η w
  let K (i : ℕ) := (q i).compactCutoffLocus (1 / 2)
  let U (i : ℕ) := amplitudeCosphereWindow r (K i)
  let ctrl (i : ℕ) := chartAmplitudeTraceControl r (q i) (ν i) (hf i)
  let localWeight (i : ℕ) := chartNormalizedPhysicalWeight r B (q i) (ν i) (hf i)
  have hK (i : ℕ) : IsCompact (K i) := (q i).isCompact_compactCutoffLocus (1 / 2)
  have hSub (i : ℕ) : K i ⊆ (q i).nonzeroLocus :=
    (q i).compactCutoffLocus_subset_nonzeroLocus (by norm_num)
  have hU (i : ℕ) : MeasurableSet (U i) :=
    measurableSet_amplitudeCosphereWindow r (hK i).isClosed.measurableSet
  have hCover : ⋃ i, U i = univ := by
    refine eq_univ_of_forall fun p => ?_
    have hp : projection p ∈ ⋃ i, (q i).cutoffLocusAbove (1 / 2) :=
      cover.symm ▸ mem_univ (projection p)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨i, (q i).cutoffLocusAbove_subset_compactCutoffLocus (by norm_num) hi⟩
  have hData (i : ℕ) := original_chartCospherePhysicalMeasure_eq_amplitudeTraceControl
    r B g hB hg hSig hsG hnG hconv hb hv (q i) σ hσ (ν i) (hf i) (hRep i)
  have hZ : MeasurableSet Z := (hData 0).1
  have hCommute (m : Measure (Cosphere r)) (i : ℕ) :
      (m.restrict Z).restrict (U i) = (m.restrict (U i)).restrict Z := by
    rw [Measure.restrict_restrict (hU i), Measure.restrict_restrict hZ, inter_comm]
  have hLaws (i : ℕ) := hA (q i) (ν i) (hf i) (hRep i) (K i) (hK i) (hSub i)
  have hControl (i : ℕ) : η.restrict (U i) = ((ctrl i).restrict Z).restrict (U i) := by
    change (A.control.restrict Z).restrict (U i) = ((ctrl i).restrict Z).restrict (U i)
    rw [hCommute A.control i, hCommute (ctrl i) i]
    exact congrArg (fun m : Measure (Cosphere r) => m.restrict Z) (hLaws i).1
  have hWeight (i : ℕ) : w =ᵐ[η.restrict (U i)] localWeight i := by
    rw [hControl i, hCommute (ctrl i) i]
    apply ae_restrict_of_ae
    filter_upwards [(hLaws i).2, ae_chartAmplitudeTraceControl_restrict_exists_windowPoint
      r (q i) (ν i) (hf i) (hK i).isClosed.measurableSet] with p hField hp
    obtain ⟨z, _, rfl⟩ := hp
    have hComponents := orderedChartAmplitudeComponents_eq_original_of_density_eq
      r (q i) (ν i) (hf i) A.density z hField
    exact physicalWeight_eq_chartNormalizedPhysicalWeight r B hSig.isSymmetric
      hSig.isNondegenerate (q i) (ν i) (hf i) A.density z hComponents
  have hMeasOn (i : ℕ) : AEMeasurable w (η.restrict (U i)) := by
    have hLocal : AEMeasurable (localWeight i) (η.restrict (U i)) :=
      (hControl i).symm ▸ (hData i).2.1.mono_measure Measure.restrict_le_self
    exact hLocal.congr (hWeight i).symm
  have hMeas : AEMeasurable w η := by
    have h := aemeasurable_iUnion_iff.mpr hMeasOn
    rwa [hCover, Measure.restrict_univ] at h
  have hPosOn (i : ℕ) : ∀ᵐ p ∂η.restrict (U i), 0 ≤ w p := by
    have hLocal : ∀ᵐ p ∂η.restrict (U i), 0 ≤ localWeight i p :=
      (hControl i).symm ▸ ae_restrict_of_ae (hData i).2.2.1
    filter_upwards [hLocal, hWeight i] with p hp hw
    rwa [hw]
  have hPos : ∀ᵐ p ∂η, 0 ≤ w p := by
    have hAll : ∀ᵐ p ∂η, ∀ i, p ∈ U i → 0 ≤ w p :=
      ae_all_iff.mpr fun i => (ae_restrict_iff' (hU i)).mp (hPosOn i)
    filter_upwards [hAll] with p hp
    have hm : p ∈ ⋃ i, U i := hCover.symm ▸ mem_univ p
    obtain ⟨i, hi⟩ := mem_iUnion.mp hm
    exact hp i hi
  refine ⟨hZ, hMeas, hPos, Measure.ext_of_iUnion_eq_univ hCover fun i => ?_⟩
  let e : Cosphere r → CotangentBundle M := Subtype.val
  have he : MeasurableEmbedding e := measurableEmbedding_coe r
  let S := (fun p : CotangentBundle M => p.proj) ⁻¹' K i
  have hS : MeasurableSet S :=
    ((hK i).isClosed.preimage continuous_cotangent_projection).measurableSet
  let μi := chartCospherePhysicalMeasure r B hSig.isNondegenerate (q i) (ν i) (hf i)
  have hMap : (μ.restrict (U i)).map e = (μi.restrict (U i)).map e := by
    change (μ.restrict (e ⁻¹' S)).map e = (μi.restrict (e ⁻¹' S)).map e
    rw [← Measure.restrict_map he.measurable hS, ← Measure.restrict_map he.measurable hS]
    rw [show μi.map e = _ from map_chartCospherePhysicalMeasure r B hSig.isNondegenerate (q i) (ν i) (hf i)]
    exact Measure.restrict_congr_mono (preimage_mono (hSub i)) (hChart i)
  have hEq : μ.restrict (U i) = μi.restrict (U i) := by
    simpa only [he.comap_map] using congrArg (Measure.comap e) hMap
  have hDensity : μi = ((ctrl i).restrict Z).withDensity (fun p => ENNReal.ofReal (localWeight i p)) :=
    (hData i).2.2.2
  rw [restrict_withDensity (hU i), hEq, hDensity, restrict_withDensity (hU i), ← hControl i]
  exact withDensity_congr_ae ((hWeight i).symm.mono fun _ h => congrArg ENNReal.ofReal h)

end Burnett.Microlocal.Overlap
