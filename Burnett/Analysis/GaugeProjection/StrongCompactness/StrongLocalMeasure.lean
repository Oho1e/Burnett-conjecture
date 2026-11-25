import Burnett.Analysis.GaugeProjection.StrongCompactness.HomogeneousReceivingBridge
import Burnett.Analysis.GaugeProjection.StrongCompactness.ReceivingPhysicalMeasureZero

/-! The original coordinate strong criterion detects the same physical measure on the entire cutoff locus. -/
set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 4400000

noncomputable section
namespace Burnett.P01

open Filter MeasureTheory Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Microlocal.Overlap
open Burnett.Geometry.UnitCosphere (Cosphere projection continuous_projection)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase fixedChartPhase_of_mem)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

local notation "E" => CoordinateSpace

/-- The base open set actually tested by the cutoff in the receiving chart. -/
def receivingCutoffLocus (c : AtlasChart M) (χ : D) : Set M :=
  c.chart.source ∩ c.chart ⁻¹' Function.support (χ : E → ℝ)

omit [IsManifold Model ∞ M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
theorem isOpen_receivingCutoffLocus (c : AtlasChart M) (χ : D) : IsOpen (receivingCutoffLocus c χ) :=
  c.chart.isOpen_inter_preimage (isClosed_eq (test_smooth χ).continuous continuous_const).isOpen_compl

omit [IsManifold Model ∞ M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
theorem receivingCutoffLocus_subset_support_inverse (c : AtlasChart M) (χ : D) :
    receivingCutoffLocus c χ ⊆ c.chart.symm '' tsupport (χ : E → ℝ) := by
  intro x hx
  exact ⟨c.chart x, subset_tsupport _ hx.2, c.chart.left_inv hx.1⟩

/-- The same physical measure annihilates the nonzero part of the cutoff
exactly when the actual homogeneous projected derivative tends to zero along
the same subsequence in the whole Euclidean coordinate space. -/
theorem tendsto_receivingStrongProjectionEnergy_zero_iff_physicalMeasure
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (μ : Measure (Cosphere r)) (hPhysical : HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) :
    Tendsto (fun n => receivingStrongProjectionEnergy B g hB hg c χ hχ (σ n)) atTop (𝓝 0) ↔
      μ (projection ⁻¹' (receivingCutoffLocus c χ)) = 0 := by
  let K := c.chart.symm '' tsupport (χ : E → ℝ)
  have hK : IsCompact K := (test_compactSupport χ).image_of_continuousOn (c.chart.symm.continuousOn.mono hχ)
  have hKc : K ⊆ c.chart.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact c.chart.symm.mapsTo (hχ hy)
  have hχK : tsupport (χ : E → ℝ) ⊆ c.chart '' K := by
    intro x hx
    exact ⟨c.chart.symm x, ⟨x, hx, rfl⟩, c.chart.right_inv (hχ hx)⟩
  let V := amplitudeCosphereWindow r K
  let W := projection (r := r) ⁻¹' receivingCutoffLocus c χ
  let τ := A.control.restrict V
  let Q (p : Cosphere r) := receivingProjectedAmplitudeCovariance c A.density p
  have hV := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  have hW := ((continuous_projection r).isOpen_preimage _ (isOpen_receivingCutoffLocus c χ)).measurableSet
  have hWV : W ⊆ V := fun _ hp => receivingCutoffLocus_subset_support_inverse c χ hp
  have hWChart : W ⊆ projection ⁻¹' c.chart.source := fun _ hp => hp.1
  have hR : τ.restrict W = A.control.restrict W := by
    change (A.control.restrict V).restrict W = _
    rw [Measure.restrict_restrict hW, inter_eq_left.mpr hWV]
  have hCond : ∀ᵐ p ∂τ, p ∈ W ↔ (χ : E → ℝ) (fixedChartPhase c p.val).1 ≠ 0 := by
    filter_upwards [ae_restrict_mem (μ := A.control) hV] with p hp
    have hc := hKc hp
    change (projection p ∈ c.chart.source ∧ c.chart (projection p) ∈ Function.support (χ : E → ℝ)) ↔ _
    rw [fixedChartPhase_of_mem c p.val hc]
    exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
  have hEquiv : (∀ᵐ p ∂τ, (χ : E → ℝ) (fixedChartPhase c p.val).1 ≠ 0 → Q p = 0) ↔
      ∀ᵐ p ∂A.control.restrict W, Q p = 0 := by
    rw [← hR, ae_restrict_iff' hW]
    constructor <;> intro h <;> filter_upwards [h, hCond] with p hp he
    · exact fun h => hp (he.mp h)
    · exact fun h => hp (he.mpr h)
  have hEnergy := tendsto_receivingStrongProjectionEnergy_zero_iff r B g hB hg hSig.isNondegenerate hconv σ hσ
    A hA hPair c K hK hKc χ hχK
  have hMass := intrinsicPhysicalMeasure_restrict_eq_zero_iff_receivingProjectedAmplitudeCovariance_ae_eq_zero
    hSig A hA μ hPhysical c W hW hWChart
  change _ ↔ μ W = 0
  rw [← Measure.restrict_eq_zero]
  exact hEnergy.trans (hEquiv.trans hMass.symm)

end Burnett.P01
