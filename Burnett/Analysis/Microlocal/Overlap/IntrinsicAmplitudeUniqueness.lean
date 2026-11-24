import Burnett.Analysis.Microlocal.Overlap.GlobalIntrinsicAmplitude
import Mathlib.Topology.Metrizable.Urysohn

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1300000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set Filter MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear UnitNullCompactness
open Burnett.Geometry.UnitCosphere (Cosphere projection isClosed_unitCosphere)
open Burnett.Geometry.CotangentAngularExtension
  (CotangentModelWithCorners cotangentBundle_t2Space cotangentBundle_secondCountable
    cotangentBundle_sigmaCompact finiteDimensional_cotangentModel)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

section Regularity

variable [T2Space M] [SecondCountableTopology M]

/-- A locally finite measure on the actual full auxiliary section is regular. -/
theorem regular_measure_on_unitCosphere (r : Metric (M := M)) (μ : Measure (Cosphere r))
    [IsLocallyFiniteMeasure μ] : μ.Regular := by
  letI := cotangentBundle_t2Space (M := M)
  letI := cotangentBundle_secondCountable (M := M)
  letI := cotangentBundle_sigmaCompact (M := M)
  letI := finiteDimensional_cotangentModel
  letI : LocallyCompactSpace (ModelProd CoordinateSpace CotangentModel) :=
    CotangentModelWithCorners.locallyCompactSpace
  letI : LocallyCompactSpace (CotangentBundle M) :=
    ChartedSpace.locallyCompactSpace (ModelProd CoordinateSpace CotangentModel) (CotangentBundle M)
  letI := (isClosed_unitCosphere r).sigmaCompactSpace
  letI := (isClosed_unitCosphere r).locallyCompactSpace
  infer_instance

end Regularity

/-- The original subsequence and a represented cover determine the auxiliary
trace exactly and the intrinsic density up to equality almost everywhere. -/
theorem intrinsicAmplitude_agree_of_originalChartLaws
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (σ : ℕ → ℕ)
    (q : ℕ → CompactChartInput M) (cover : ⋃ i, (q i).cutoffLocusAbove (1 / 2) = univ)
    (ν : ∀ i, (JetSlot → ℂ) → Measure (Chart (q i).ball))
    (hf : ∀ i v, IsFiniteMeasure (ν i v))
    (hRep : ∀ i, let a := q i
      RepresentsCompactJetPairings a.ball
        (originalGradient_volumeWeightedL2 B g hB hg hn a.center a.cutoff
          (a.cutoff_support.trans a.ball_in_chart)) σ (ν i) (hf i))
    (A D : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalAmplitudeChartLaws r B g hB hg hn σ A)
    (hD : HasOriginalAmplitudeChartLaws r B g hB hg hn σ D) :
    A.control = D.control ∧ ∀ᵐ p ∂A.control, A.density p = D.density p := by
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
  have hOnA (i : ℕ) := hA (q i) (ν i) (hf i) (hRep i) (K i) (hK i) (hSub i)
  have hOnD (i : ℕ) := hD (q i) (ν i) (hf i) (hRep i) (K i) (hK i) (hSub i)
  refine ⟨Measure.ext_of_iUnion_eq_univ hCover fun i => (hOnA i).1.trans (hOnD i).1.symm, ?_⟩
  have hLocal (i : ℕ) : ∀ᵐ p ∂A.control.restrict (U i), A.density p = D.density p := by
    have hEq : A.control.restrict (U i) = _ := (hOnA i).1
    rw [hEq]
    filter_upwards [(hOnA i).2, (hOnD i).2] with p hpA hpD
    exact hpA.trans hpD.symm
  have h := (ae_restrict_iUnion_iff (μ := A.control) U
    (fun p => A.density p = D.density p)).mpr hLocal
  rwa [hCover, Measure.restrict_univ] at h

end Burnett.Microlocal.Overlap
