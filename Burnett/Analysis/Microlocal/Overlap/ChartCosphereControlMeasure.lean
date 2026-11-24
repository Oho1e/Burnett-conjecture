import Burnett.Analysis.Microlocal.ChartAuxiliaryEmbedding
import Burnett.Analysis.Microlocal.Overlap.NormalizedCotangentPhysicalMeasure

set_option autoImplicit false
set_option maxRecDepth 2500

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear UnitNullCompactness
open Burnett.Geometry.UnitCosphere (Cosphere hamiltonian measurableEmbedding_coe)
open Burnett.Geometry.CotangentAngularExtension (contMDiff_dualEnergy)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.X02.SobolevTestJet (test_smooth)
open scoped ContDiff Manifold ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The normalized trace of the original gradient measure before the null
restriction, pushed along the actual auxiliary chart embedding. -/
def chartCosphereControlMeasure (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) : Measure (Cosphere r) :=
  ((traceMeasure ν).withDensity (chartInverseCutoffSquare q)).map (chartAuxiliaryCosphere r q)

/-- The physical chart measure uses the very same cutoff normalization and lift
as the trace measure. -/
def chartCospherePhysicalMeasure (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v)) :
    Measure (Cosphere r) :=
  ((chartPhysicalJetMeasure r B hn q ν hfin).withDensity (chartInverseCutoffSquare q)).map
    (chartAuxiliaryCosphere r q)

private theorem withDensity_map_embedding {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : MeasurableEmbedding f) (μ : Measure X) (w : Y → ℝ≥0∞) :
    (μ.map f).withDensity w = (μ.withDensity (w ∘ f)).map f := by
  ext S hS
  rw [withDensity_apply _ hS, Measure.restrict_map hf.measurable hS,
    hf.lintegral_map, hf.map_apply, withDensity_apply _ (hf.measurable hS)]
  rfl

/-- The local physical measure is exactly the null part of the lifted original
trace weighted by any real function that recovers the chart contraction. -/
theorem chartCospherePhysicalMeasure_eq_controlDensity [T2Space M]
    (r : Metric (M := M)) (B : Field (M := M)) (hB : IsSmooth B)
    (hs : IsSymmetric B) (hn : IsNondegenerate B) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (w : Cosphere r → ℝ)
    (hw : w ∘ chartAuxiliaryCosphere r q =ᵐ[((traceMeasure ν).restrict
      (chartAuxiliaryNull r B hn q)).withDensity (chartInverseCutoffSquare q)]
      fun z => (chartPhysicalJetContraction r B q ν hfin z).re)
    (hpos : ∀ᵐ z ∂(traceMeasure ν).restrict (chartAuxiliaryNull r B hn q),
      0 ≤ (chartPhysicalJetContraction r B q ν hfin z).re) :
    let Z : Set (Cosphere r) := {p | hamiltonian B hn p = 0}
    let τ := (chartCosphereControlMeasure r q ν).restrict Z
    MeasurableSet Z ∧ AEMeasurable w τ ∧ (∀ᵐ p ∂τ, 0 ≤ w p) ∧
      chartCospherePhysicalMeasure r B hn q ν hfin =
        τ.withDensity (fun p => ENNReal.ofReal (w p)) := by
  intro Z τ
  let f := chartAuxiliaryCosphere r q
  let N := chartAuxiliaryNull r B hn q
  let κ := (traceMeasure ν).restrict N
  let C := chartInverseCutoffSquare q
  let d (z : Chart q.ball) := (chartPhysicalJetContraction r B q ν hfin z).re
  let weighted := κ.withDensity C
  have hf : MeasurableEmbedding f := measurableEmbedding_chartAuxiliaryCosphere r q
  have hZ : MeasurableSet Z :=
    (isClosed_eq (((contMDiff_dualEnergy B hB hn hs).continuous.comp
      continuous_subtype_val).div_const 2) continuous_const).measurableSet
  have hpre : f ⁻¹' Z = N := by
    ext z
    change dualEnergy B hn (chartAuxiliaryRay r q z) / 2 = 0 ↔
      dualEnergy B hn (chartAuxiliaryRay r q z) = 0
    simp
  have hτ : τ = weighted.map f := by
    change (((traceMeasure ν).withDensity C).map f).restrict Z = (κ.withDensity C).map f
    rw [Measure.restrict_map hf.measurable hZ, hpre, restrict_withDensity
      (measurableSet_chartAuxiliaryNull r B hB hs hn q)]
  have hC : Measurable C := ENNReal.measurable_ofReal.comp
    ((((test_smooth q.cutoff).continuous.measurable.comp continuous_subtype_val.measurable).comp
      continuous_fst.measurable).inv.pow_const 2)
  have hd : AEMeasurable d κ := Complex.continuous_re.measurable.comp_aemeasurable
    ((integrable_chartPhysicalJetContraction r B hB hn q ν hfin).mono_measure
      Measure.restrict_le_self).aestronglyMeasurable.aemeasurable
  have hAC : weighted ≪ κ := withDensity_absolutelyContinuous _ _
  have hmatch : w ∘ f =ᵐ[weighted] d := hw
  have hdm : AEMeasurable d weighted := ⟨hd.mk d, hd.measurable_mk, hAC.ae_eq hd.ae_eq_mk⟩
  refine ⟨hZ, hτ.symm ▸ hf.aemeasurable_map_iff.mpr (hdm.congr hmatch.symm), ?_, ?_⟩
  · rw [hτ]
    apply hf.ae_map_iff.mpr
    have hpositive : ∀ᵐ z ∂weighted, 0 ≤ d z := hAC.ae_le hpos
    filter_upwards [hpositive, hmatch] with z hz he
    change 0 ≤ (w ∘ f) z
    exact he.symm ▸ hz
  · rw [hτ, withDensity_map_embedding hf]
    change ((κ.withDensity (fun z => ENNReal.ofReal (d z))).withDensity C).map f =
      (weighted.withDensity ((fun p => ENNReal.ofReal (w p)) ∘ f)).map f
    apply congrArg (Measure.map f)
    have hsame : weighted.withDensity ((fun p => ENNReal.ofReal (w p)) ∘ f) =
        weighted.withDensity (fun z => ENNReal.ofReal (d z)) :=
      withDensity_congr_ae (hmatch.fun_comp ENNReal.ofReal)
    rw [hsame]
    have hd' : AEMeasurable (fun z => ENNReal.ofReal (d z)) κ :=
      ENNReal.measurable_ofReal.comp_aemeasurable hd
    change (κ.withDensity (fun z => ENNReal.ofReal (d z))).withDensity C =
      (κ.withDensity C).withDensity (fun z => ENNReal.ofReal (d z))
    rw [← withDensity_mul₀ hd' hC.aemeasurable, ← withDensity_mul₀ hC.aemeasurable hd', mul_comm]

variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- Inclusion of the lifted chart measure is the registered normalized
cotangent measure of that chart. -/
theorem map_chartCospherePhysicalMeasure (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v)) :
    (chartCospherePhysicalMeasure r B hn q ν hfin).map
        (Subtype.val : Cosphere r → CotangentBundle M) =
      normalizedCotangentPhysicalMeasure q r B hn ν hfin := by
  unfold chartCospherePhysicalMeasure normalizedCotangentPhysicalMeasure
  rw [Measure.map_map (measurableEmbedding_coe r).measurable
    (continuous_chartAuxiliaryCosphere r q).measurable]
  rfl

end Burnett.Microlocal.Overlap
