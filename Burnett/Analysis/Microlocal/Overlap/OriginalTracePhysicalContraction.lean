import Burnett.Analysis.Microlocal.Overlap.CompactAmplitudeAuxiliaryControl
import Burnett.Analysis.Microlocal.Overlap.OriginalPhysicalJetMeasure
import Burnett.Analysis.Microlocal.Overlap.AuxiliaryTraceReconstruction
import Burnett.Analysis.Microlocal.Overlap.ChartAmplitudeContractions

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1400000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.UnitCosphere (Cosphere hamiltonian)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude
  (ae_originalVolume_auxiliaryAmplitude chartAuxiliaryAmplitude)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.PhysicalDensity (physicalContraction)
open Burnett.Microlocal.RicciRow (backgroundInverse)
open Burnett.RicciSymbol (Tensor2)
open Burnett.F07.IntrinsicAmplitude
  (auxiliaryTraceLinear_nonneg_and_eq_zero_iff
    aemeasurable_auxiliaryTraceLinear auxiliaryTrace_normalization_preserves_positive_contraction
    chartAuxiliaryInverse_posDef orderedChartAmplitudeComponents intrinsicPhysicalWeight
    intrinsicPhysicalWeight_eq_chart)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity)
open scoped ComplexOrder ContDiff Manifold ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private def quarterPhysicalContractionLinear (G : Tensor2) : Matrix Pair Pair ℂ →ₗ[ℝ] ℝ where
  toFun A := ((1 / 4 : ℂ) * physicalContraction G A).re
  map_add' A D := by
    simp only [physicalContraction, Matrix.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]
  map_smul' c A := by
    simp only [physicalContraction, Matrix.smul_apply, Algebra.mul_smul_comm,
      ← Finset.smul_sum, Complex.smul_re, RingHom.id_apply]

private def liftChartBackgroundInverse (r : Metric (M := M)) (B : Field (M := M))
    (q : CompactChartInput M) : Cosphere r → Tensor2 :=
  Function.extend (chartAuxiliaryCosphere r q) (fun z : Chart q.ball =>
    backgroundInverse B q.center z.1) (fun _ => 0)

private theorem liftChartBackgroundInverse_apply [T2Space M]
    (r : Metric (M := M)) (B : Field (M := M)) (q : CompactChartInput M) (z : Chart q.ball) :
    liftChartBackgroundInverse r B q (chartAuxiliaryCosphere r q z) =
      backgroundInverse B q.center z.1 :=
  (measurableEmbedding_chartAuxiliaryCosphere r q).injective.extend_apply _ _ _

/-- The real quarter contraction of the trace-normalized original amplitude
in the actual chart, lifted to the auxiliary cosphere. -/
def chartNormalizedPhysicalWeight (r : Metric (M := M)) (B : Field (M := M))
    (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball))
    (hfin : ∀ a, IsFiniteMeasure (ν a)) (p : Cosphere r) : ℝ :=
  quarterPhysicalContractionLinear (liftChartBackgroundInverse r B q p)
    ((chartAmplitudeTraceWeight r q ν hfin p)⁻¹ •
      liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hfin) p)

theorem chartNormalizedPhysicalWeight_on_chart [T2Space M]
    (r : Metric (M := M)) (B : Field (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ a, IsFiniteMeasure (ν a))
    (z : Chart q.ball) :
    chartNormalizedPhysicalWeight r B q ν hfin (chartAuxiliaryCosphere r q z) =
      ((1 / 4 : ℂ) * physicalContraction (backgroundInverse B q.center z.1)
        ((chartAmplitudeTraceWeight r q ν hfin (chartAuxiliaryCosphere r q z))⁻¹ •
          chartAuxiliaryAmplitude r q ν hfin z)).re := by
  rw [chartNormalizedPhysicalWeight, liftChartBackgroundInverse_apply, liftChartAmplitude_apply]
  rfl

/-- A tensor field with these normalized ordered components has the same
weight when contracted in the intrinsic statement. -/
theorem physicalWeight_eq_chartNormalizedPhysicalWeight [T2Space M]
    (r : Metric (M := M)) (B : Field (M := M)) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball))
    (hfin : ∀ a, IsFiniteMeasure (ν a)) (J : AmplitudeCovarianceDensity r) (z : Chart q.ball)
    (hJ : orderedChartAmplitudeComponents r q J z =
      (chartAmplitudeTraceWeight r q ν hfin (chartAuxiliaryCosphere r q z))⁻¹ •
        chartAuxiliaryAmplitude r q ν hfin z) :
    intrinsicPhysicalWeight B hn J (chartAuxiliaryCosphere r q z) =
      chartNormalizedPhysicalWeight r B q ν hfin (chartAuxiliaryCosphere r q z) :=
  (intrinsicPhysicalWeight_eq_chart r B hs hn q J z).trans (by
    rw [hJ, chartNormalizedPhysicalWeight_on_chart])

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- The original vacuum witness yields exactly its original physical chart
measure when the normalized quarter contraction is integrated against the
auxiliary amplitude trace control on the null shell. -/
theorem original_chartCospherePhysicalMeasure_eq_amplitudeTraceControl
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ a, IsFiniteMeasure (ν a))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin) :
    let Z : Set (Cosphere r) := {p | hamiltonian B hSig.isNondegenerate p = 0}
    let τ := (chartAmplitudeTraceControl r q ν hfin).restrict Z
    let wNorm := chartNormalizedPhysicalWeight r B q ν hfin
    MeasurableSet Z ∧ AEMeasurable wNorm τ ∧ (∀ᵐ p ∂τ, 0 ≤ wNorm p) ∧
      chartCospherePhysicalMeasure r B hSig.isNondegenerate q ν hfin =
        τ.withDensity (fun p => ENNReal.ofReal (wNorm p)) := by
  intro Z τ wNorm
  let f := chartAuxiliaryCosphere r q
  let rawControl := chartCosphereControlMeasure r q ν
  let R := liftChartAuxiliaryInverse r q
  let A₀ := chartAuxiliaryAmplitude r q ν hfin
  let A := liftChartAmplitude r q A₀
  let t := chartAmplitudeTraceWeight r q ν hfin
  let L (p : Cosphere r) := quarterPhysicalContractionLinear (liftChartBackgroundInverse r B q p)
  let w (p : Cosphere r) := L p (A p)
  let d (z : Chart q.ball) := (chartPhysicalJetContraction r B q ν hfin z).re
  have hEmb : MeasurableEmbedding f := measurableEmbedding_chartAuxiliaryCosphere r q
  have hData := ae_originalVolume_auxiliaryAmplitude r B g hB hg hSig.isSymmetric hsG
    hSig.isNondegenerate hnG hconv hb hv q σ hσ ν hfin hRep
  have hCut := withDensity_absolutelyContinuous (traceMeasure ν) (chartInverseCutoffSquare q)
  have hA : ∀ᵐ p ∂rawControl, Matrix.PosDef (R p) ∧ (A p).PosSemidef := by
    change ∀ᵐ p ∂((traceMeasure ν).withDensity (chartInverseCutoffSquare q)).map f,
      Matrix.PosDef (R p) ∧ (A p).PosSemidef
    apply hEmb.ae_map_iff.mpr
    filter_upwards [hCut.ae_le hData] with z hz
    change Matrix.PosDef (liftChartAuxiliaryInverse r q (chartAuxiliaryCosphere r q z)) ∧
      (liftChartAmplitude r q A₀ (chartAuxiliaryCosphere r q z)).PosSemidef
    rw [liftChartAuxiliaryInverse_apply, liftChartAmplitude_apply]
    exact ⟨chartAuxiliaryInverse_posDef r q z, hz.1⟩
  have ht : AEMeasurable t rawControl :=
    aemeasurable_auxiliaryTraceLinear rawControl R A
      (fun i j => (measurable_liftChartAuxiliaryInverse_entry r q i j).aemeasurable)
      (fun i j => (measurable_liftChartAmplitude_entry r q A₀ i j
        (measurable_chartAuxiliaryAmplitude_entry r q ν hfin i j)).aemeasurable)
  have hwOnChart : w ∘ f =ᵐ[traceMeasure ν] d := by
    filter_upwards [hData] with z hz
    change quarterPhysicalContractionLinear
      (liftChartBackgroundInverse r B q (chartAuxiliaryCosphere r q z))
      (liftChartAmplitude r q A₀ (chartAuxiliaryCosphere r q z)) = d z
    rw [liftChartBackgroundInverse_apply, liftChartAmplitude_apply]
    exact (congrArg Complex.re
      (chartPhysicalJetWeight_contraction_eq_auxiliaryAmplitude r B q ν hfin z hz.2.1)).symm
  have hd : AEMeasurable d (traceMeasure ν) := Complex.continuous_re.measurable.comp_aemeasurable
    (integrable_chartPhysicalJetContraction r B hB hSig.isNondegenerate q ν hfin).aestronglyMeasurable.aemeasurable
  have hw : AEMeasurable w rawControl :=
    hEmb.aemeasurable_map_iff.mpr ((hd.congr hwOnChart.symm).mono_ac hCut)
  have hOnCutNull : w ∘ f =ᵐ[((traceMeasure ν).restrict
      (chartAuxiliaryNull r B hSig.isNondegenerate q)).withDensity (chartInverseCutoffSquare q)] d :=
    (withDensity_absolutelyContinuous _ _).ae_eq (ae_restrict_of_ae hwOnChart)
  have hdPos := (ae_original_chartPhysicalJetContraction_nonneg_real r B g hB hg hSig hsG hnG
    hconv hb hv q σ hσ ν hfin hRep).mono (fun _ hz => hz.1)
  obtain ⟨hZ, _, hwPos, hPhysical⟩ := chartCospherePhysicalMeasure_eq_controlDensity
    r B hB hSig.isSymmetric hSig.isNondegenerate q ν hfin w hOnCutNull hdPos
  have hτRestrict : τ ≪ rawControl.restrict Z := by
    change (rawControl.withDensity (fun p => ENNReal.ofReal (t p))).restrict Z ≪ rawControl.restrict Z
    rw [restrict_withDensity hZ]
    exact withDensity_absolutelyContinuous _ _
  have hτ : τ ≪ rawControl := hτRestrict.trans Measure.restrict_le_self.absolutelyContinuous
  have hwNorm (p : Cosphere r) : wNorm p = (t p)⁻¹ * w p :=
    (L p).map_smul (t p)⁻¹ (A p)
  refine ⟨hZ, ((ht.inv.mul hw).mono_ac hτ).congr (Filter.Eventually.of_forall (fun p =>
    (hwNorm p).symm)), ?_, ?_⟩
  · filter_upwards [hτRestrict.ae_le hwPos, hτ.ae_le hA] with p hp hRA
    have htPos : 0 ≤ t p :=
      (auxiliaryTraceLinear_nonneg_and_eq_zero_iff (R p) hRA.1 (A p) hRA.2).1
    rw [hwNorm]
    exact mul_nonneg (inv_nonneg.mpr htPos) hp
  · exact hPhysical.trans
      (auxiliaryTrace_normalization_preserves_positive_contraction rawControl R A hA ht L hw Z hZ).symm

end Burnett.Microlocal.Overlap
