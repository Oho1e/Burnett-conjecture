import Burnett.Analysis.Microlocal.Overlap.NormalizedPhysicalOverlap
import Burnett.Geometry.MeasureGluing
import Mathlib.Topology.Metrizable.Urysohn

/-! Glue the normalized positive physical measures on the actual cotangent bundle. -/

set_option autoImplicit false
set_option maxHeartbeats 450000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence
open Burnett.Geometry.CotangentAngularExtension
  (CotangentModelWithCorners cotangentBundle_t2Space cotangentBundle_secondCountable
    cotangentBundle_sigmaCompact finiteDimensional_cotangentModel isClosed_cotangentUnitNull)
open Burnett.Geometry.UnitNullCompactness
  (CotangentBundle CotangentModel cotangentUnitNull continuous_cotangent_projection isCompact_cotangentUnitNull_over)
open Burnett.F05.ActualChartAuxiliarySection (chartAuxiliaryRay)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

omit [MeasurableSpace M] [BorelSpace M] in
private theorem regular_cotangent_measure (μ : Measure (CotangentBundle M))
    [IsLocallyFiniteMeasure μ] : μ.Regular := by
  letI := cotangentBundle_t2Space (M := M)
  letI := cotangentBundle_secondCountable (M := M)
  letI := cotangentBundle_sigmaCompact (M := M)
  letI := finiteDimensional_cotangentModel
  letI : LocallyCompactSpace (ModelProd CoordinateSpace CotangentModel) :=
    CotangentModelWithCorners.locallyCompactSpace
  letI : LocallyCompactSpace (CotangentBundle M) :=
    ChartedSpace.locallyCompactSpace (ModelProd CoordinateSpace CotangentModel) (CotangentBundle M)
  infer_instance

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M] in
private theorem normalized_measure_finite_on_halfCutoff
    (r : Metric (M := M)) (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v)) :
    normalizedCotangentPhysicalMeasure q r B hn ν hfin
      ((fun y : CotangentBundle M => y.proj) ⁻¹' q.cutoffLocusAbove (1 / 2)) < ⊤ := by
  have hSet := (q.isOpen_cutoffLocusAbove (1 / 2)).preimage continuous_cotangent_projection
  apply normalizedCotangentPhysicalMeasure_lt_top_of_cutoff_lower_bound q r B hn ν hfin hB
    hSet.measurableSet (by norm_num : (0 : ℝ) < (1 / 2))
  intro z hz
  let e := chartAt CoordinateSpace q.center
  have h : (1 / 2 : ℝ) < ‖(q.cutoff : CoordinateSpace → ℝ) (e (e.symm z.1))‖ := hz.2
  rw [e.right_inv (q.ball_in_chart z.1.property)] at h
  simpa only [Real.norm_eq_abs] using h.le

/-- A countable family whose half-cutoff loci cover the manifold gives a
regular positive measure on the cotangent bundle. The same measure agrees
on each nonzero locus with every original witness on the same subsequence. -/
theorem exists_glued_originalVacuum_physicalMeasure
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (charts : ℕ → CompactChartInput M) (cover : (⋃ i, (charts i).cutoffLocusAbove (1 / 2)) = univ)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : ∀ i : ℕ, (JetSlot → ℂ) → Measure (Chart (charts i).ball))
    (hfin : ∀ i v, IsFiniteMeasure (ν i v))
    (hRep : ∀ i, let q := charts i
      RepresentsCompactJetPairings q.ball
        (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
          (q.cutoff_support.trans q.ball_in_chart)) σ (ν i) (hfin i)) :
    ∃ μ : Measure (CotangentBundle M), IsLocallyFiniteMeasure μ ∧ μ.Regular ∧
      μ (cotangentUnitNull r B hSig.isNondegenerate)ᶜ = 0 ∧
      (∀ K : Set M, IsCompact K →
        μ ((fun p : CotangentBundle M => p.proj) ⁻¹' K) < ⊤) ∧
      ∀ (q : CompactChartInput M) (νq : (JetSlot → ℂ) → Measure (Chart q.ball))
        (hfq : ∀ v, IsFiniteMeasure (νq v)),
        RepresentsCompactJetPairings q.ball
          (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
            (q.cutoff_support.trans q.ball_in_chart)) σ νq hfq →
        μ.restrict ((fun p : CotangentBundle M => p.proj) ⁻¹' q.nonzeroLocus) =
          (normalizedCotangentPhysicalMeasure q r B hSig.isNondegenerate νq hfq).restrict
            ((fun p : CotangentBundle M => p.proj) ⁻¹' q.nonzeroLocus) := by
  let proj := fun p : CotangentBundle M => p.proj
  let U : ℕ → Set (CotangentBundle M) := fun i => proj ⁻¹' (charts i).cutoffLocusAbove (1 / 2)
  let chartMeasures : ℕ → Measure (CotangentBundle M) :=
    fun i => normalizedCotangentPhysicalMeasure (charts i) r B hSig.isNondegenerate (ν i) (hfin i)
  let μ := MeasureGluing.glued U chartMeasures
  have hOpen (i : ℕ) : IsOpen (U i) :=
    ((charts i).isOpen_cutoffLocusAbove (1 / 2)).preimage continuous_cotangent_projection
  have hU (i : ℕ) : MeasurableSet (U i) := (hOpen i).measurableSet
  have hCover : ⋃ i, U i = univ := by
    change (⋃ i, proj ⁻¹' (charts i).cutoffLocusAbove (1 / 2)) = univ
    rw [← preimage_iUnion, cover, preimage_univ]
  have hSub (i : ℕ) : U i ⊆ proj ⁻¹' (charts i).nonzeroLocus :=
    preimage_mono ((charts i).cutoffLocusAbove_subset_nonzeroLocus (by norm_num : (0 : ℝ) < (1 / 2)))
  have hCompat (i j : ℕ) : (chartMeasures i).restrict (U i ∩ U j) =
      (chartMeasures j).restrict (U i ∩ U j) := by
    have hInter : U i ∩ U j ⊆ proj ⁻¹' ((charts i).nonzeroLocus ∩ (charts j).nonzeroLocus) :=
      fun _ hz => ⟨hSub i hz.1, hSub j hz.2⟩
    exact Measure.restrict_congr_mono hInter
      (originalVacuum_normalizedCotangentPhysicalMeasure_restrict_overlap (charts i) (charts j)
        r B g hB hg hSig hsG hnG hconv hb hv σ hσ (ν i) (hfin i) (ν j) (hfin j) (hRep i) (hRep j))
  have hLocalValue (i : ℕ) : μ (U i) = chartMeasures i (U i) := by
    have h := congrArg (fun m : Measure (CotangentBundle M) => m univ)
      (MeasureGluing.glued_restrict U hU hCover chartMeasures hCompat i)
    simpa only [Measure.restrict_apply_univ] using h
  have hFinite (i : ℕ) : μ (U i) < ⊤ := by
    rw [hLocalValue i]
    exact normalized_measure_finite_on_halfCutoff r B hB hSig.isNondegenerate (charts i) (ν i) (hfin i)
  letI : IsLocallyFiniteMeasure μ := ⟨fun x => by
    have hx : x ∈ ⋃ i, U i := hCover.symm ▸ mem_univ x
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨U i, (hOpen i).mem_nhds hi, hFinite i⟩⟩
  have hClosed := isClosed_cotangentUnitNull r B hB hSig.isNondegenerate hSig.isSymmetric
  have hNull : μ (cotangentUnitNull r B hSig.isNondegenerate)ᶜ = 0 := by
    change (Measure.sum (fun i => (chartMeasures i).restrict (disjointed U i)))
      (cotangentUnitNull r B hSig.isNondegenerate)ᶜ = 0
    rw [Measure.sum_apply _ hClosed.measurableSet.compl]
    have hPiece (i : ℕ) : ((chartMeasures i).restrict (disjointed U i))
        (cotangentUnitNull r B hSig.isNondegenerate)ᶜ = 0 := by
      rw [Measure.restrict_apply hClosed.measurableSet.compl]
      exact measure_mono_null inter_subset_left
        (normalizedCotangentPhysicalMeasure_compl_null (charts i) r B hSig.isNondegenerate
          (ν i) (hfin i) hB hSig.isSymmetric)
    simp only [hPiece, tsum_zero]
  refine ⟨μ, inferInstance, regular_cotangent_measure μ, hNull, ?_, ?_⟩
  · intro K hK
    have h := (isCompact_cotangentUnitNull_over r B hB hSig.isNondegenerate hSig.isSymmetric hK).measure_lt_top
      (μ := μ)
    change μ (cotangentUnitNull r B hSig.isNondegenerate ∩ proj ⁻¹' K) < ⊤ at h
    rw [inter_comm, measure_inter_conull hNull] at h
    exact h
  · intro q νq hfq hRq
    let V := proj ⁻¹' q.nonzeroLocus
    have hV : MeasurableSet V := (q.isOpen_nonzeroLocus.preimage continuous_cotangent_projection).measurableSet
    apply MeasureGluing.glued_restrict_of_compatible U hU hCover chartMeasures V hV
      (normalizedCotangentPhysicalMeasure q r B hSig.isNondegenerate νq hfq)
    intro i
    have hInter : U i ∩ V ⊆ proj ⁻¹' ((charts i).nonzeroLocus ∩ q.nonzeroLocus) :=
      fun _ hz => ⟨hSub i hz.1, hz.2⟩
    exact Measure.restrict_congr_mono hInter
      (originalVacuum_normalizedCotangentPhysicalMeasure_restrict_overlap (charts i) q
        r B g hB hg hSig hsG hnG hconv hb hv σ hσ (ν i) (hfin i) νq hfq (hRep i) hRq)

end Burnett.Microlocal.Overlap
