import Burnett.Analysis.Microlocal.Overlap.GluedPhysicalMeasure
import Burnett.Analysis.Microlocal.Overlap.CountableOriginalPhysicalMeasures

/-! A common subsequence and one global measure from the original vacuum sequence. -/

set_option autoImplicit false
set_option maxHeartbeats 360000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence
open Burnett.Geometry.UnitNullCompactness (CotangentBundle cotangentUnitNull)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts
  (CompactChartInput RepresentsCompactJetPairings exists_countable_compactChartInput_cover)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M] [Nonempty M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- The original vacuum sequence admits one strict refinement and a global
regular positive measure supported on the actual auxiliary unit null
covectors. On each represented nonzero chart locus it restricts to the
normalized physical measure of that original witness. -/
theorem exists_originalVacuum_globalPhysicalMeasure
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧
      ∃ charts : ℕ → CompactChartInput M,
        (⋃ i, (charts i).cutoffLocusAbove (1 / 2)) = univ ∧
        ∃ ν : ∀ i : ℕ, (JetSlot → ℂ) → Measure (Chart (charts i).ball),
          ∃ hfin : ∀ i v, IsFiniteMeasure (ν i v),
            (∀ i, let q := charts i
              RepresentsCompactJetPairings q.ball
                (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
                  (q.cutoff_support.trans q.ball_in_chart)) (s ∘ t) (ν i) (hfin i) ∧
              Burnett.P01.RepresentsVolumeProjectedPairings B g q (s ∘ t) (ν i) (hfin i)) ∧
            ∃ μ : Measure (CotangentBundle M), IsLocallyFiniteMeasure μ ∧ μ.Regular ∧
              μ (cotangentUnitNull r B hSig.isNondegenerate)ᶜ = 0 ∧
              (∀ K : Set M, IsCompact K →
                μ ((fun p : CotangentBundle M => p.proj) ⁻¹' K) < ⊤) ∧
              ∀ (q : CompactChartInput M) (νq : (JetSlot → ℂ) → Measure (Chart q.ball))
                (hfq : ∀ v, IsFiniteMeasure (νq v)),
                RepresentsCompactJetPairings q.ball
                  (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
                    (q.cutoff_support.trans q.ball_in_chart)) (s ∘ t) νq hfq →
                μ.restrict ((fun p : CotangentBundle M => p.proj) ⁻¹' q.nonzeroLocus) =
                  (normalizedCotangentPhysicalMeasure q r B hSig.isNondegenerate νq hfq).restrict
                    ((fun p : CotangentBundle M => p.proj) ⁻¹' q.nonzeroLocus) := by
  obtain ⟨charts, hCover, _⟩ := exists_countable_compactChartInput_cover (M := M)
  obtain ⟨t, ht, ν, hfin, hCharts⟩ := exists_countable_originalVolume_physicalJetMeasures
    r B g hB hg hSig hsG hnG hconv hb hv charts s hs
  obtain ⟨μ, hLoc, hReg, hNull, hFinite, hPatch⟩ := exists_glued_originalVacuum_physicalMeasure
    r B g hB hg hSig hsG hnG hconv hb hv charts hCover (s ∘ t) (hs.comp ht) ν hfin
      (fun i => (hCharts i).1)
  exact ⟨t, ht, charts, hCover, ν, hfin, (fun i => ⟨(hCharts i).1, (hCharts i).2.1⟩),
    μ, hLoc, hReg, hNull, hFinite, hPatch⟩

omit [Nonempty M] in
/-- The global physical measure and its chart law, including the empty base. -/
theorem exists_originalVacuum_globalPhysicalMeasure_and_chartLaw
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧ ∃ μ : Measure (CotangentBundle M),
      IsLocallyFiniteMeasure μ ∧ μ.Regular ∧
      μ (cotangentUnitNull r B hSig.isNondegenerate)ᶜ = 0 ∧
      (∀ K : Set M, IsCompact K →
        μ ((fun p : CotangentBundle M => p.proj) ⁻¹' K) < ⊤) ∧
      ∀ (q : CompactChartInput M) (νq : (JetSlot → ℂ) → Measure (Chart q.ball))
        (hfq : ∀ v, IsFiniteMeasure (νq v)),
        RepresentsCompactJetPairings q.ball
          (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
            (q.cutoff_support.trans q.ball_in_chart)) (s ∘ t) νq hfq →
        μ.restrict ((fun p : CotangentBundle M => p.proj) ⁻¹' q.nonzeroLocus) =
          (normalizedCotangentPhysicalMeasure q r B hSig.isNondegenerate νq hfq).restrict
            ((fun p : CotangentBundle M => p.proj) ⁻¹' q.nonzeroLocus) := by
  by_cases hM : Nonempty M
  · letI : Nonempty M := hM
    obtain ⟨t, ht, _, _, _, _, _, μ, hLoc, hReg, hNull, hFinite, hPatch⟩ :=
      exists_originalVacuum_globalPhysicalMeasure r B g hB hg hSig hsG hnG hconv hb hv s hs
    exact ⟨t, ht, μ, hLoc, hReg, hNull, hFinite, hPatch⟩
  · refine ⟨id, strictMono_id, 0, inferInstance, inferInstance, by simp, ?_, ?_⟩
    · intro K _
      simp
    · intro q
      exact (hM ⟨q.center⟩).elim

end Burnett.Microlocal.Overlap
