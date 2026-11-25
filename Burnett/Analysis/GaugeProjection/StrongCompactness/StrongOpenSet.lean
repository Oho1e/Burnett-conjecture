import Burnett.Analysis.GaugeProjection.StrongCompactness.StrongLocalMeasure
import Mathlib.Topology.Compactness.Lindelof

/-! Cover an arbitrary open region by cutoffs and close convergence of the whole original sequence. -/
set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 4900000

noncomputable section
namespace Burnett.P01

open Filter MeasureTheory Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Microlocal.Overlap
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

local notation "E" => CoordinateSpace

/-- Whole-sequence convergence for every chart cutoff supported in the open region. -/
def HasStrongProjectedGradientOn (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (U : Set M) : Prop :=
  ∀ (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target),
    c.chart.symm '' tsupport (χ : E → ℝ) ⊆ U →
    Tendsto (receivingStrongProjectionEnergy B g hB hg c χ hχ) atTop (𝓝 0)

omit [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
private theorem exists_receivingCutoffLocus_in_open (U : Set M) (hU : IsOpen U) (x : U) :
    ∃ χ : D, let c := AtlasChart.atPoint x.val
      (tsupport (χ : E → ℝ) ⊆ c.chart.target) ∧
      (c.chart.symm '' tsupport (χ : E → ℝ) ⊆ U) ∧ x.val ∈ receivingCutoffLocus c χ := by
  let c := AtlasChart.atPoint x.val
  let O := c.chart.target ∩ c.chart.symm ⁻¹' U
  have hx : x.val ∈ c.chart.source := mem_chart_source E x.val
  have hc : c.chart x.val ∈ O := ⟨c.chart.mapsTo hx, by
    change c.chart.symm (c.chart x.val) ∈ U
    rw [c.chart.left_inv hx]
    exact x.property⟩
  have hO : IsOpen O := c.chart.isOpen_inter_preimage_symm hU
  obtain ⟨η, hη, hηc, hηO, V, _, hKV, _, hηV⟩ := exists_projectedChartCutoff
    (isCompact_singleton (x := c.chart x.val)) hO (singleton_subset_iff.mpr hc)
  let χ : D := ⟨η, hη, hηc⟩
  refine ⟨χ, hηO.trans inter_subset_left, ?_, hx, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (hηO hy).2
  · have hone := hηV (hKV (mem_singleton (c.chart x.val)))
    change (χ : E → ℝ) (c.chart x.val) ≠ 0
    rw [show (χ : E → ℝ) (c.chart x.val) = 1 from hone]
    norm_num

/-- Whole-sequence strong convergence forces every represented physical
measure of that sequence to vanish over the open region. -/
theorem physicalMeasure_zero_over_open_of_hasStrongProjectedGradientOn
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (μ : Measure (Cosphere r)) (hPhysical : HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ)
    (U : Set M) (hU : IsOpen U) (hStrong : HasStrongProjectedGradientOn B g hB hg U) :
    μ (projection ⁻¹' U) = 0 := by
  classical
  let χ (x : U) := (exists_receivingCutoffLocus_in_open U hU x).choose
  have hχ (x : U) := (exists_receivingCutoffLocus_in_open U hU x).choose_spec
  let c (x : U) := AtlasChart.atPoint x.val
  let V (x : U) := receivingCutoffLocus (c x) (χ x)
  have hCover : U ⊆ ⋃ x : U, V x := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, (hχ ⟨x, hx⟩).2.2⟩
  have hNull (x : U) : μ (projection ⁻¹' V x) = 0 := by
    have h := hStrong (c x) (χ x) (hχ x).1 (hχ x).2.1
    exact (tendsto_receivingStrongProjectionEnergy_zero_iff_physicalMeasure r B g hB hg hSig hconv σ hσ A hA
      hPair μ hPhysical (c x) (χ x) (hχ x).1).mp (h.comp hσ.tendsto_atTop)
  obtain ⟨J, hJ, hSub⟩ := (HereditarilyLindelof_LindelofSets U).elim_countable_subcover
    V (fun x => isOpen_receivingCutoffLocus (c x) (χ x)) hCover
  letI : Countable J := hJ.to_subtype
  have hNullUnion : μ (⋃ x : J, projection ⁻¹' V x.val) = 0 :=
    measure_iUnion_null_iff.mpr (fun x => hNull x.val)
  refine measure_mono_null (fun p hp => ?_) hNullUnion
  obtain ⟨x, hx⟩ := mem_iUnion.mp (hSub hp)
  obtain ⟨hxJ, hpx⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨⟨x, hxJ⟩, hpx⟩

/-- Subsequential vanishing of the original physical measures on the region
proves convergence for every cutoff along the entire original sequence. -/
theorem hasStrongProjectedGradientOn_of_null_physical_subsequence_refinements
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hconv : LocallyUniformlyConverges r g B) (U : Set M)
    (hMeasures : ∀ s : ℕ → ℕ, StrictMono s →
      ∃ t : ℕ → ℕ, StrictMono t ∧ ∃ A : IntrinsicAmplitudeCovariance r, ∃ μ : Measure (Cosphere r),
        HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
        HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
        HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ ∧ μ (projection ⁻¹' U) = 0) :
    HasStrongProjectedGradientOn B g hB hg U := by
  intro c χ hχ hSupport
  apply tendsto_of_strictMono_subsequence_refinements
  intro s hs
  obtain ⟨t, ht, A, μ, hA, hPair, hPhysical, hμ⟩ := hMeasures s hs
  have hLocus : receivingCutoffLocus c χ ⊆ U := (receivingCutoffLocus_subset_support_inverse c χ).trans hSupport
  have hZero := measure_mono_null (preimage_mono hLocus) hμ
  exact ⟨t, ht, (tendsto_receivingStrongProjectionEnergy_zero_iff_physicalMeasure r B g hB hg hSig hconv
    (s ∘ t) (hs.comp ht) A hA hPair μ hPhysical c χ hχ).mpr hZero⟩

end Burnett.P01
