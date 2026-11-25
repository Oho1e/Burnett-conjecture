import Burnett.Analysis.Microlocal.Overlap.RawFirstOrderAtlasChange
import Burnett.Analysis.Microlocal.Overlap.RawFirstOrderJetTransition
import Burnett.Analysis.Microlocal.Overlap.GlobalUnweightedFirstOrderRange

/-! A compatible actual first-order action has one principal symbol on the original jet fiber. -/
set_option autoImplicit false
set_option maxRecDepth 4400
set_option maxHeartbeats 5600000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter Set Matrix MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Analysis.HminusWeightedDual (negativeEnergy)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Matrix Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The local expressions of one first-order action agree on chart overlaps
on smooth tests. The input transition is the actual covariant jet transition. -/
def HasCompatibleRawFirstOrderActions {Rows J L : Type} [Fintype J] [Fintype L]
    {Y : M → Type} [∀ x, AddCommGroup (Y x)] [∀ x, Module ℂ (Y x)]
    (coordinates : ∀ (c : AtlasChart M) (x : M), x ∈ c.chart.source → Y x ≃ₗ[ℂ] (Rows → ℂ))
    (a : AtlasChart M → Rows → J → E → ℝ) (v : AtlasChart M → Rows → J → E)
    (i : AtlasChart M → Rows → J → JetSlot)
    (b : AtlasChart M → Rows → L → E → ℝ) (j : AtlasChart M → Rows → L → JetSlot) : Prop :=
  ∀ (c d : AtlasChart M) (x : M) (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source)
    (u : JetSlot → E → ℂ), (∀ k, ContDiff ℝ ∞ (u k)) →
    (fun s => receivingRawFirstOrderRow (a c s) (v c s) (i c s) (b c s) (j c s)
      (fun k y => rawReceivingJetTransition c d y (fun l => u l (c.transition d y)) k) (c.chart x)) =
      ((coordinates d x hd).symm.trans (coordinates c x hc))
        (fun s => receivingRawFirstOrderRow (a d s) (v d s) (i d s) (b d s) (j d s) u (d.chart x))

/-- Choose one atlas chart at each actual point to construct the principal map.
Compatibility of the differential action gives its representation in every chart. -/
theorem exists_intrinsicRawFirstOrderSymbol_of_actual_chart_action
    {Rows J L : Type} [Fintype J] [Fintype L]
    {Y : M → Type} [∀ x, AddCommGroup (Y x)] [∀ x, Module ℂ (Y x)]
    (coordinates : ∀ (c : AtlasChart M) (x : M), x ∈ c.chart.source → Y x ≃ₗ[ℂ] (Rows → ℂ))
    (a : AtlasChart M → Rows → J → E → ℝ) (v : AtlasChart M → Rows → J → E)
    (i : AtlasChart M → Rows → J → JetSlot)
    (b : AtlasChart M → Rows → L → E → ℝ) (j : AtlasChart M → Rows → L → JetSlot)
    (hAction : HasCompatibleRawFirstOrderActions coordinates a v i b j) (r : Metric (M := M)) :
    ∃ S : ∀ p : Cosphere r, complexSymmetricJet (TangentSpace Model (projection p)) →ₗ[ℂ] Y (projection p),
      ∀ (c : AtlasChart M) (p : Cosphere r) (hp : projection p ∈ c.chart.source)
        (F : complexSymmetricJet (TangentSpace Model (projection p))),
        coordinates c (projection p) hp (S p F) =
          (fun s : Rows => receivingRawFirstOrderSymbol c (a c s) (v c s) (i c s) p) *ᵥ
            jetFiberCoordinates (chartTangentBasis c (projection p) hp)
              (F : ComplexCovariantJet (TangentSpace Model (projection p))) := by
  let atPoint (p : Cosphere r) := AtlasChart.atPoint (projection p)
  have hPoint (p : Cosphere r) : projection p ∈ (atPoint p).chart.source := mem_chart_source E _
  let P (c : AtlasChart M) (p : Cosphere r) : Matrix Rows JetSlot ℂ :=
    fun s => receivingRawFirstOrderSymbol c (a c s) (v c s) (i c s) p
  let S (p : Cosphere r) : complexSymmetricJet (TangentSpace Model (projection p)) →ₗ[ℂ] Y (projection p) :=
    (coordinates (atPoint p) (projection p) (hPoint p)).symm.toLinearMap.comp
      ((P (atPoint p) p).mulVecLin.comp
        ((jetFiberCoordinates (chartTangentBasis (atPoint p) (projection p) (hPoint p))).toLinearMap.comp
          (complexSymmetricJet (TangentSpace Model (projection p))).subtype))
  refine ⟨S, ?_⟩
  intro c p hc F
  let x := projection p
  let d := atPoint p
  have hd : x ∈ d.chart.source := hPoint p
  have hSource : c.chart x ∈ (c.transition d).source := by
    refine ⟨c.chart.mapsTo hc, ?_⟩
    change c.chart.symm (c.chart x) ∈ d.chart.source
    rwa [c.chart.left_inv hc]
  let W (e : AtlasChart M) (he : x ∈ e.chart.source) :=
    jetFiberCoordinates (chartTangentBasis e x he)
      (F : ComplexCovariantJet (TangentSpace Model x))
  have h := receivingRawFirstOrderSymbol_mulVec_change_of_chart_action c d p hc hd
    (a c) (v c) (i c) (b c) (j c) (a d) (v d) (i d) (b d) (j d)
    (rawReceivingJetTransition c d) ((coordinates d x hd).symm.trans (coordinates c x hc)).toLinearMap
    (rawReceivingJetTransition_differentiableAt c d (c.chart x) hSource)
    (hAction c d x hc hd) (W d hd)
  change P c p *ᵥ rawReceivingJetTransition c d (c.chart x) (W d hd) =
    coordinates c x hc ((coordinates d x hd).symm (P d p *ᵥ W d hd)) at h
  have hW : rawReceivingJetTransition c d (c.chart x) (W d hd) = W c hc :=
    rawReceivingJetTransition_jetFiberCoordinates c d x hc hd _
  rw [hW] at h
  exact h.symm

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- The principal map is constructed from the actual compatibility of the
action before applying localization to the original intrinsic covariance. -/
theorem original_intrinsic_symmetricJet_kernel_of_compatible_firstOrderActions
    {Rows J L : Type} [Fintype Rows] [Fintype J] [Fintype L]
    {Y : M → Type} [∀ x, AddCommGroup (Y x)] [∀ x, Module ℂ (Y x)]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (coordinates : ∀ (c : AtlasChart M) (x : M), x ∈ c.chart.source → Y x ≃ₗ[ℂ] (Rows → ℂ))
    (a : AtlasChart M → Rows → J → E → ℝ) (v : AtlasChart M → Rows → J → E)
    (i : AtlasChart M → Rows → J → JetSlot)
    (b : AtlasChart M → Rows → L → E → ℝ) (j : AtlasChart M → Rows → L → JetSlot)
    (ha : ∀ c s h, ContDiffOn ℝ ∞ (a c s h) c.chart.target)
    (hb₀ : ∀ c s h, ContDiffOn ℝ ∞ (b c s h) c.chart.target)
    (hAction : HasCompatibleRawFirstOrderActions coordinates a v i b j)
    (hLocal : ∀ (c : AtlasChart M) (χ : D), tsupport (χ : E → ℝ) ⊆ c.chart.target →
      ∃ F : Rows → ℕ → SchwartzMap E ℂ,
        (∀ s n x, F s n x = ((χ : E → ℝ) x : ℂ) * receivingRawFirstOrderRow
          (a c s) (v c s) (i c s) (b c s) (j c s) (receivingRawCovariantJet r B g c n) x) ∧
        ∀ s, Tendsto (fun n => negativeEnergy (F s n)) Filter.atTop (𝓝 0)) :
    ∃ S : ∀ p : Cosphere r, complexSymmetricJet (TangentSpace Model (projection p)) →ₗ[ℂ] Y (projection p),
      (∀ (c : AtlasChart M) (p : Cosphere r) (hp : projection p ∈ c.chart.source)
        (F : complexSymmetricJet (TangentSpace Model (projection p))),
        coordinates c (projection p) hp (S p F) =
          (fun s : Rows => receivingRawFirstOrderSymbol c (a c s) (v c s) (i c s) p) *ᵥ
            jetFiberCoordinates (chartTangentBasis c (projection p) hp)
              (F : ComplexCovariantJet (TangentSpace Model (projection p)))) ∧
      ∀ᵐ p ∂A.control, ∀ F : complexSymmetricJet (TangentSpace Model (projection p)),
        S p (intrinsicSymmetricJetCovariance A.density p F) = 0 := by
  obtain ⟨S, hS⟩ := exists_intrinsicRawFirstOrderSymbol_of_actual_chart_action coordinates a v i b j hAction r
  refine ⟨S, hS, ?_⟩
  exact original_intrinsic_symmetricJet_kernel_of_unweightedChartSources r B g hB hg hsB hsG hnB hnG
    hconv hb hv σ hσ A hA a v i b j ha hb₀ hLocal Y S coordinates hS

end Burnett.Microlocal.Overlap
