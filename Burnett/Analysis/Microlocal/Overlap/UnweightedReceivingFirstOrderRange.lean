import Burnett.Analysis.Microlocal.Overlap.UnweightedReceivingFirstOrder

/-! Localization for a smooth receiving chart system on the actual original jet. -/
set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 5000000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Matrix Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Analysis.HminusWeightedDual (negativeEnergy)
open Burnett.Analysis.LocalWeakDerivative (contDiff_test_mul_local)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Microlocal.AtlasVolumeGradient (fixedHalfDensity fixedVolumeCovariantGradientSchwartz)
open Burnett.Microlocal.BesselLocalization (firstOrderRow physicalCoefficient)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.RowKernelDensity (groupRow)
open Burnett.P01 (exists_projectedChartCutoff inverseHalfDensityCutoff inverseHalfDensityCutoff_tsupport)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open scoped BigOperators ContDiff InnerProduct Manifold Matrix Topology

open private fixedHalfDensity_pos from Burnett.Analysis.GaugeProjection.StrongCompactness.ReceivingCutoff

local notation "E" => CoordinateSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The principal row of the unweighted coordinate system at the original
auxiliary unit covector. -/
def receivingRawFirstOrderSymbol {r : Metric (M := M)} {J : Type} [Fintype J]
    (c : AtlasChart M) (a : J → E → ℝ) (v : J → E) (i : J → JetSlot) (p : Cosphere r) : JetSlot → ℂ :=
  let ξ := WithLp.toLp 2 (atlasChartUnitCovector c p)
  let x := c.chart (projection p)
  groupRow i (fun h => (a h x : ℂ) * (inner ℝ ξ (v h) : ℂ))

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- For locally smooth coefficients, the ordinary unweighted strong H⁻¹
hypothesis localizes the range of the original covariance in the unchanged
principal row on the open cutoff window. -/
theorem original_receiving_covariant_kernel_of_unweightedFirstOrderSources
    {Rows : Type*} {J L : Type} [Fintype Rows] [Fintype J] [Fintype L]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart '' K)
    (a : Rows → J → E → ℝ) (v : Rows → J → E) (i : Rows → J → JetSlot)
    (b : Rows → L → E → ℝ) (j : Rows → L → JetSlot)
    (ha : ∀ s h, ContDiffOn ℝ ∞ (a s h) c.chart.target)
    (hb₀ : ∀ s h, ContDiffOn ℝ ∞ (b s h) c.chart.target)
    (F : Rows → ℕ → SchwartzMap E ℂ)
    (hF : ∀ s n x, F s n x = ((χ : E → ℝ) x : ℂ) *
      receivingRawFirstOrderRow (a s) (v s) (i s) (b s) (j s) (receivingRawCovariantJet r B g c n) x)
    (hStrong : ∀ s, Tendsto (fun n => negativeEnergy (F s n)) atTop (𝓝 0)) :
    let P (p : Cosphere r) : Matrix Rows JetSlot ℂ := fun s => receivingRawFirstOrderSymbol c (a s) (v s) (i s) p
    ∀ᵐ p ∂A.control.restrict (amplitudeCosphereWindow r K), (χ : E → ℝ) (c.chart (projection p)) ≠ 0 →
      P p * atlasJetCovarianceOperator c A.density p = 0 ∧
      ∀ z : JetSlot → ℂ, P p *ᵥ (atlasJetCovarianceOperator c A.density p *ᵥ z) = 0 := by
  intro P
  have hχc := hχ.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
  obtain ⟨θ, hθ, hθC, hθc, W, _, hχW, _, hOne⟩ :=
    exists_projectedChartCutoff (test_compactSupport χ) c.chart.open_target hχc
  let a' (s : Rows) (h : J) : D := ⟨fun x => θ x * a s h x,
    contDiff_test_mul_local c.chart.open_target hθ hθc (ha s h), hθC.mul_right⟩
  let b' (s : Rows) (h : L) : D := ⟨fun x => θ x * b s h x,
    contDiff_test_mul_local c.chart.open_target hθ hθc (hb₀ s h), hθC.mul_right⟩
  have hA' (s : Rows) (h : J) (x : E) (hx : x ∈ tsupport (χ : E → ℝ)) :
      (a' s h : E → ℝ) x = a s h x := by
    change θ x * a s h x = a s h x
    rw [show θ x = 1 from hOne (hχW hx), one_mul]
  have hB' (s : Rows) (h : L) (x : E) (hx : x ∈ tsupport (χ : E → ℝ)) :
      (b' s h : E → ℝ) x = b s h x := by
    change θ x * b s h x = b s h x
    rw [show θ x = 1 from hOne (hχW hx), one_mul]
  have hF' (s : Rows) (n : ℕ) (x : E) :
      F s n x = ((χ : E → ℝ) x : ℂ) * receivingRawFirstOrderRow
        (fun h => (a' s h : E → ℝ)) (v s) (i s) (fun h => (b' s h : E → ℝ)) (j s)
          (receivingRawCovariantJet r B g c n) x := by
    rw [hF]
    by_cases hx : x ∈ tsupport (χ : E → ℝ)
    · simp only [receivingRawFirstOrderRow, fun h => hA' s h x hx, fun h => hB' s h x hx]
    · simp only [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero, zero_mul]
  let d := inverseHalfDensityCutoff B hB hnB c χ hχc
  have hdK : tsupport (d : E → ℝ) ⊆ c.chart '' K :=
    (inverseHalfDensityCutoff_tsupport B hB hnB c χ hχc).trans hχ
  have hRange := original_receiving_covariant_firstOrderSystem_kernel_of_negativeEnergy
    r B g hB hg hsB hsG hnB hnG hconv hb hv σ hσ A hA c K hK hKc d hdK a' v i b' j
    (fun s => negativeEnergy_of_realized_unweightedFirstOrderSource r B g hB hg hnB hconv hb c χ hχc
      (a' s) (v s) (i s) (b' s) (j s) (F s) (hF' s) (hStrong s))
  filter_upwards [hRange] with p hp hNonzero
  let x := c.chart (projection p)
  have hx := subset_tsupport (χ : E → ℝ) hNonzero
  have hd : (d : E → ℝ) x ≠ 0 :=
    mul_ne_zero hNonzero (inv_ne_zero (fixedHalfDensity_pos B hnB c (hχc hx)).ne')
  have hSym : (fun s : Rows => receivingFirstOrderSymbol c (a' s) (v s) (i s) p) = P p := by
    funext s k
    simp only [receivingFirstOrderSymbol, receivingRawFirstOrderSymbol, P, groupRow, physicalCoefficient]
    apply Finset.sum_congr rfl
    intro h _
    rw [hA' s h _ hx]
  simpa only [hSym] using hp hd

end Burnett.Microlocal.Overlap
