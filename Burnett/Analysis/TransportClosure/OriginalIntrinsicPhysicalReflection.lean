import Burnett.Analysis.TransportClosure.OriginalChartPhysicalReflection
import Burnett.Analysis.TransportClosure.IntrinsicCotangentAntipodal
import Burnett.Analysis.Microlocal.Overlap.OriginalVacuumIntrinsicAmplitude
import Burnett.Analysis.Microlocal.Overlap.GluedPhysicalMeasure

/-! The actual original physical measure is invariant under fiber reflection. -/
set_option autoImplicit false
set_option maxRecDepth 4100
set_option maxHeartbeats 4300000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence UnitNullCompactness
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Geometry.UnitCosphere (Cosphere antipode fromAmbient map_fromAmbient_eq_of_unitNull
  measurableEmbedding_antipode measurableEmbedding_coe projection)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- Local invariance glues on the original represented cover, whose chart
windows are preserved exactly by the negative radial map. -/
theorem originalVolume_ambientPhysicalMeasure_antipodal
    [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (σ : ℕ → ℕ) (μ : Measure (CotangentBundle M))
    (q : ℕ → CompactChartInput M) (hCover : (⋃ i, (q i).cutoffLocusAbove (1 / 2)) = univ)
    (ν : ∀ i, (JetSlot → ℂ) → Measure (Chart (q i).ball)) (hf : ∀ i v, IsFiniteMeasure (ν i v))
    (hRep : ∀ i, let a := q i
      RepresentsCompactJetPairings a.ball
        (originalGradient_volumeWeightedL2 B g hB hg hn a.center a.cutoff
          (a.cutoff_support.trans a.ball_in_chart)) σ (ν i) (hf i))
    (hChart : ∀ i, let S := (fun p : CotangentBundle M => p.proj) ⁻¹' (q i).nonzeroLocus
      μ.restrict S = (normalizedCotangentPhysicalMeasure (q i) r B hn (ν i) (hf i)).restrict S) :
    μ.map (cotangentScale (-1)) = μ := by
  let R := cotangentScale (-1) (M := M)
  let proj (p : CotangentBundle M) := p.proj
  let U (i : ℕ) := proj ⁻¹' (q i).cutoffLocusAbove (1 / 2)
  have hAll : ⋃ i, U i = univ := by
    change (⋃ i, proj ⁻¹' (q i).cutoffLocusAbove (1 / 2)) = univ
    rw [← preimage_iUnion, hCover, preimage_univ]
  have hMeas : Measurable R :=
    (continuous_cotangentScale.comp (continuous_const.prodMk continuous_id)).measurable
  apply Measure.ext_of_iUnion_eq_univ hAll
  intro i
  have hU : MeasurableSet (U i) :=
    (((q i).isOpen_cutoffLocusAbove (1 / 2)).preimage continuous_cotangent_projection).measurableSet
  have hUR : R ⁻¹' U i = U i := rfl
  let m := normalizedCotangentPhysicalMeasure (q i) r B hn (ν i) (hf i)
  have hEq : μ.restrict (U i) = m.restrict (U i) :=
    Measure.restrict_congr_mono (preimage_mono ((q i).cutoffLocusAbove_subset_nonzeroLocus (by norm_num))) (hChart i)
  have hm : m.map R = m := originalVolume_normalizedCotangentPhysicalMeasure_antipodal
    r B g hB hg hs hn (q i) σ (ν i) (hf i) (hRep i)
  calc
    _ = (μ.restrict (U i)).map R := by rw [Measure.restrict_map hMeas hU, hUR]
    _ = (m.restrict (U i)).map R := congrArg (Measure.map R) hEq
    _ = (m.map R).restrict (U i) := by rw [Measure.restrict_map hMeas hU, hUR]
    _ = _ := (congrArg (fun n => n.restrict (U i)) hm).trans hEq.symm

variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The reflection property holds for the very same physical contraction
of the actual covariance. The proof keeps the original subsequence and chart
witnesses and identifies the measure through its defining contraction. -/
theorem originalIntrinsicPhysicalContraction_antipodal
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (μ : Measure (Cosphere r))
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPhysical : HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ) :
    μ.map (antipode r) = μ := by
  letI : MeasurableSpace (CotangentBundle M) := borel _
  letI : BorelSpace (CotangentBundle M) := ⟨rfl⟩
  by_cases hM : Nonempty M
  · letI : Nonempty M := hM
    obtain ⟨q, hCover, ν, hf, hRep⟩ := hA.1 hM
    have hRaw (i : ℕ) := (hRep i).1
    obtain ⟨m, _, _, hNull, _, hChart⟩ := exists_glued_originalVacuum_physicalMeasure
      r B g hB hg hSig hsG hnG hconv hb hv q hCover σ hσ ν hf hRaw
    have hChart' (i : ℕ) := hChart (q i) (ν i) (hf i) (hRaw i)
    have hEven := originalVolume_ambientPhysicalMeasure_antipodal r B g hB hg hSig.isSymmetric
      hSig.isNondegenerate σ m q hCover ν hf hRaw hChart'
    let e : Cosphere r → CotangentBundle M := Subtype.val
    let μ' := fromAmbient r m
    have he : MeasurableEmbedding e := measurableEmbedding_coe r
    have hEmbed : μ'.map e = m := map_fromAmbient_eq_of_unitNull r B hSig.isNondegenerate m hNull
    have hP := original_globalPhysicalContraction_of_chartLaws r B g hB hg hSig hsG hnG
      hconv hb hv σ hσ q hCover ν hf hRaw A hA.2.2.2.2.1 μ' (fun i => by rw [hEmbed]; exact hChart' i)
    have hSame : μ = μ' := hPhysical.2.2.2.trans hP.2.2.2.symm
    have hCommuting : e ∘ antipode r = cotangentScale (-1) ∘ e := rfl
    have hScale : Measurable (cotangentScale (-1) : CotangentBundle M → CotangentBundle M) :=
      (continuous_cotangentScale.comp (continuous_const.prodMk continuous_id)).measurable
    have hMap : (μ'.map (antipode r)).map e = μ'.map e := by
      rw [Measure.map_map he.measurable (measurableEmbedding_antipode r).measurable, hCommuting,
        ← Measure.map_map hScale he.measurable, hEmbed, hEven]
    rw [hSame]
    simpa only [he.comap_map] using congrArg (Measure.comap e) hMap
  · letI : IsEmpty M := not_nonempty_iff.mp hM
    letI : IsEmpty (Cosphere r) := ⟨fun p => isEmptyElim (projection p)⟩
    rw [μ.eq_zero_of_isEmpty, Measure.map_zero]

end Burnett.Microlocal.Overlap
