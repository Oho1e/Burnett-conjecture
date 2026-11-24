import Burnett.Analysis.Microlocal.Overlap.GlobalOriginalAmplitudeContraction
import Burnett.Analysis.Microlocal.Overlap.IntrinsicAmplitudeRicciKernel
import Burnett.Analysis.Microlocal.Overlap.IntrinsicAmplitudeUniqueness
import Burnett.Analysis.Microlocal.Overlap.CosphereEinsteinMoments

/-! Use one original refinement for the intrinsic amplitude and the Einstein moments. -/

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 2400000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence UnitNullCompactness
open ContravariantTensor IntrinsicScalarEinstein
open Burnett.Geometry.UnitCosphere
  (Cosphere projection hamiltonian measurableEmbedding_coe FixedChartNaturality fixedChartNaturality)
open Burnett.Analysis.ScalarCurvatureFromMoments
  (HasRicciMoments scalarFlat_and_EinsteinMoments_of_null_RicciMoments)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F07.IntrinsicAmplitude (intrinsicAuxiliaryTrace)
open Burnett.F07.IntrinsicAmplitudeCoordinates (components)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ComplexOrder ContDiff Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The original subsequence retains its represented chart cover, including
the projected pairings with the same chart witnesses. -/
def HasOriginalRepresentedCover
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (σ : ℕ → ℕ) : Prop :=
  Nonempty M → ∃ q : ℕ → CompactChartInput M,
    (⋃ i, (q i).cutoffLocusAbove (1 / 2)) = univ ∧
    ∃ ν : ∀ i, (JetSlot → ℂ) → Measure (Chart (q i).ball),
      ∃ hf : ∀ i v, IsFiniteMeasure (ν i v),
        ∀ i, let a := q i
          RepresentsCompactJetPairings a.ball
            (originalGradient_volumeWeightedL2 B g hB hg hn a.center a.cutoff
              (a.cutoff_support.trans a.ball_in_chart)) σ (ν i) (hf i) ∧
            Burnett.P01.RepresentsVolumeProjectedPairings B g a σ (ν i) (hf i)

/-- The covariance formed from the original represented charts, with regular
positive control and the intrinsic fiber constraints on a common full measure set. -/
def HasOriginalIntrinsicAmplitude (r : Metric (M := M)) (B : Field (M := M))
    (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hn : IsNondegenerate B) (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r) : Prop :=
  HasOriginalRepresentedCover B g hB hg hn σ ∧
  IsLocallyFiniteMeasure A.control ∧ A.control.Regular ∧
  (∀ K : Set M, IsCompact K → A.control (projection ⁻¹' K) < ⊤) ∧
  HasOriginalAmplitudeChartLaws r B g hB hg hn σ A ∧
  ∀ᵐ p ∂A.control, intrinsicAuxiliaryTrace r A.density p = 1 ∧
    (∀ b : Module.Basis Index ℝ (TangentSpace Model (projection p)),
      (components b (A.density p)).PosSemidef) ∧
    HasIntrinsicAmplitudeRicciKernel r B hn A.density p

/-- The physical contraction of the intrinsic amplitude on one original
subsequence gives the same cosphere measure for every Einstein moment. -/
theorem exists_originalVacuum_intrinsicAmplitude_and_cosphereEinsteinMoments
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧
      ∃ A : IntrinsicAmplitudeCovariance r, ∃ μ : Measure (Cosphere r),
        HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
        HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ ∧
        IsLocallyFiniteMeasure μ ∧ μ.Regular ∧
        (∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤) ∧
        μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0 ∧
        HasCosphereEinsteinMoments r B hSig.isNondegenerate μ ∧
        (∀ x, intrinsicScalar B hSig.isNondegenerate x = 0) ∧ FixedChartNaturality μ := by
  letI : MeasurableSpace (CotangentBundle M) := borel _
  letI : BorelSpace (CotangentBundle M) := ⟨rfl⟩
  by_cases hM : Nonempty M
  · letI : Nonempty M := hM
    obtain ⟨t, ht, q, hCover, ν, hf, hRep, μ, _, _, hNull, _, μr, hmap,
      hLocR, hRegR, hFiniteR, hNullR, hChart⟩ :=
      exists_originalVacuum_physicalMeasure_on_cosphere_and_representedChartMoments
        r B g hB hg hSig hsG hnG hconv hb hv s hs
    obtain ⟨A, hLocalA, hFiniteA, hLaws⟩ :=
      original_globalIntrinsicAmplitude_of_representedCharts r B g hB hg hSig.isSymmetric
        hsG hSig.isNondegenerate hnG hconv hb hv (s ∘ t) (hs.comp ht) q hCover ν hf
        (fun i => (hRep i).1)
    have hPhysical := original_globalPhysicalContraction_of_chartLaws r B g hB hg hSig
      hsG hnG hconv hb hv (s ∘ t) (hs.comp ht) q hCover ν hf (fun i => (hRep i).1)
      A hLaws μr (fun i => (hChart (q i) (ν i) (hf i) (hRep i).1).1)
    have hAmplitude : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate (s ∘ t) A := by
      letI : IsLocallyFiniteMeasure A.control := hLocalA
      refine ⟨fun _ => ⟨q, hCover, ν, hf, hRep⟩, hLocalA,
        regular_measure_on_unitCosphere r A.control, hFiniteA, hLaws, ?_⟩
      filter_upwards [hLaws.ae_global_positive_unitTrace_ricciKernel hSig.isSymmetric hsG hnG
        hconv hb hv (hs.comp ht) q hCover ν hf (fun i => (hRep i).1),
        hLaws.ae_intrinsicAmplitudeRicciKernel hSig.isSymmetric hsG hnG hconv hb hv
          (hs.comp ht) q hCover ν hf (fun i => (hRep i).1)] with p hp hKernel
      exact ⟨hp.1, fun b => (hp.2.1 b).1, hKernel⟩
    have hCoverage : ⋃ i, (q i).nonzeroLocus = univ := by
      refine eq_univ_of_forall fun x => ?_
      have hx : x ∈ ⋃ i, (q i).cutoffLocusAbove (1 / 2) := hCover.symm ▸ mem_univ x
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i, (q i).cutoffLocusAbove_subset_nonzeroLocus (by norm_num) hi⟩
    let e : Cosphere r → CotangentBundle M := Subtype.val
    have he : MeasurableEmbedding e := measurableEmbedding_coe r
    have hRicci : HasRicciMoments B (μr.map e) := by
      refine hasRicciMoments_of_nonzero_chartMoments B hB hSig.isSymmetric hSig.isNondegenerate
        q hCoverage (μr.map e) ?_
      intro i ψ hψ a b
      exact (hChart (q i) (ν i) (hf i) (hRep i).1).2 ψ hψ a b
    have hMapNull : (μr.map e) (cotangentUnitNull r B hSig.isNondegenerate)ᶜ = 0 := by
      have heq : μr.map e = μ := hmap
      rw [heq]
      exact hNull
    obtain ⟨hScalar, hEinstein⟩ := scalarFlat_and_EinsteinMoments_of_null_RicciMoments
      r B hB hSig.isSymmetric hSig.isNondegenerate (μr.map e) hMapNull hRicci
    refine ⟨t, ht, A, μr, hAmplitude, hPhysical, hLocR, hRegR, hFiniteR, hNullR,
      ?_, hScalar, fixedChartNaturality μr⟩
    intro Q hQ
    obtain ⟨hBase, hPhase, hEq⟩ := hEinstein Q hQ
    exact ⟨hBase, he.integrable_map_iff.mp hPhase,
      hEq.trans (he.integral_map (intrinsicTensorPhase Q))⟩
  · letI : IsEmpty M := not_nonempty_iff.mp hM
    letI : IsEmpty (Cosphere r) := ⟨fun p => isEmptyElim (projection p)⟩
    let A : IntrinsicAmplitudeCovariance r := ⟨0, fun _ => 0⟩
    let μ : Measure (Cosphere r) := 0
    refine ⟨id, strictMono_id, A, μ, ?_, ?_, inferInstance, inferInstance,
      by simp [μ], by simp [μ], ?_, isEmptyElim, fixedChartNaturality μ⟩
    · refine ⟨fun h => (hM h).elim, ?_, ?_, by simp [A], ?_, by simp [A]⟩
      · change IsLocallyFiniteMeasure (0 : Measure (Cosphere r))
        infer_instance
      · change (0 : Measure (Cosphere r)).Regular
        infer_instance
      · intro q
        exact (hM ⟨q.center⟩).elim
    · unfold HasIntrinsicPhysicalContraction
      have hZ : {p : Cosphere r | hamiltonian B hSig.isNondegenerate p = 0} = ∅ :=
        Set.eq_empty_of_isEmpty _
      simp [A, μ, hZ]
    · intro Q _
      rw [(ManifoldVolume.geometricMeasure B).eq_zero_of_isEmpty]
      simp [μ]

end Burnett.Microlocal.Overlap
