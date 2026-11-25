import Burnett.Analysis.GaugeProjection.StrongCompactness.ReceivingProjectionEnergy
import Burnett.Analysis.GaugeProjection.StrongCompactness.ProjectedEnergyZero

/-! The full projected energy detects the covariance over the actual cutoff locus. -/
set_option autoImplicit false
set_option maxRecDepth 4900
set_option maxHeartbeats 5400000

noncomputable section
namespace Burnett.P01

open MeasureTheory Set Filter Matrix Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeCovariantGradientSchwartz)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase)
open Burnett.RicciSymbol (Index Covector)
open Burnett.X02.SobolevTestJet (D)
open scoped Matrix MatrixOrder ComplexOrder BigOperators ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

local notation "E" => CoordinateSpace

omit [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
private theorem chartFrequency_square_sum_pos {r : Metric (M := M)}
    (c : AtlasChart M) (p : Cosphere r) (hc : projection p ∈ c.chart.source) :
    0 < ∑ d : Index, (atlasChartUnitCovector c p d)^2 := by
  have hnz : atlasChartUnitCovector c p ≠ 0 := atlasChartUnitCovector_ne_zero c p hc
  apply lt_of_le_of_ne (Finset.sum_nonneg (fun d _ => sq_nonneg (atlasChartUnitCovector c p d)))
  intro he
  apply hnz
  funext d
  have hd := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun i _ =>
    sq_nonneg (atlasChartUnitCovector c p i))).mp he.symm d (Finset.mem_univ d)
  exact pow_eq_zero hd

/-- Every component and every derivative is included in the same full-space
squared norm. The limit vanishes exactly where the nonzero cutoff tests zero
projected amplitude from the original covariance. -/
theorem tendsto_receiving_projection_energy_zero_iff
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hn σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hn σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (η : D) (hη : tsupport (η : E → ℝ) ⊆ c.chart '' K) :
    let hηc := hη.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let u d n a b := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η hηc (σ n) (d, a, b)
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    Tendsto (fun n => ∑ d : Index, ∑ k : OrderedPair,
      ‖(projectionFullSchwartz (u d n) k.1 k.2).toLp 2 volume‖^2) atTop (𝓝 0) ↔
      ∀ᵐ p ∂τ, (η : E → ℝ) (fixedChartPhase c p.val).1 ≠ 0 →
        let P := principalGaugeProjectionMatrix (WithLp.toLp 2 (atlasChartUnitCovector c p))
        P * atlasAmplitudeMatrix c A.density p * Pᴴ = 0 := by
  intro hηc u τ
  let uη (p : Cosphere r) := (η : E → ℝ) (fixedChartPhase c p.val).1
  let ξ (p : Cosphere r) := WithLp.toLp 2 (atlasChartUnitCovector c p)
  let N (p : Cosphere r) := atlasAmplitudeMatrix c A.density p
  let Q (p : Cosphere r) := principalGaugeProjectionMatrix (ξ p) * N p * (principalGaugeProjectionMatrix (ξ p))ᴴ
  let w (p : Cosphere r) := (uη p)^2 * ∑ d : Index, (atlasChartUnitCovector c p d)^2
  let H (d : Index) (k : OrderedPair) (p : Cosphere r) :=
    (uη p)^2 * (atlasChartUnitCovector c p d)^2 * ((Q p) k k).re
  have hP (d : Index) (k : OrderedPair) := tendsto_receiving_projectionEnergy r B g hB hg hn σ A hPair
    c K hK hKc η hη d k
  have hI (d : Index) (k : OrderedPair) : Integrable (H d k) τ := (hP d k).1
  let L (d : Index) (k : OrderedPair) (n : ℕ) := ‖(projectionFullSchwartz (u d n) k.1 k.2).toLp 2 volume‖^2
  have hLim (d : Index) (k : OrderedPair) : Tendsto (L d k) atTop (𝓝 (∫ p, H d k p ∂τ)) := (hP d k).2
  have hSum := tendsto_finset_sum (Finset.univ : Finset Index) (fun d _ =>
    tendsto_finset_sum (Finset.univ : Finset OrderedPair) (fun k _ => hLim d k))
  let J (p : Cosphere r) := ∑ d : Index, ∑ k : OrderedPair, H d k p
  have hJ : Integrable J τ := integrable_finset_sum _ (fun d _ => integrable_finset_sum _ (fun k _ => hI d k))
  have hSumIntegral : (∑ d : Index, ∑ k : OrderedPair, ∫ p, H d k p ∂τ) = ∫ p, J p ∂τ := by
    simp only [J]
    rw [integral_finset_sum _ (fun d _ => integrable_finset_sum _ (fun k _ => hI d k))]
    exact Finset.sum_congr rfl (fun d _ => (integral_finset_sum _ (fun k _ => hI d k)).symm)
  have hJ' (p : Cosphere r) : J p = w p * (Q p).trace.re := by
    calc
      J p = ∑ d : Index, ((uη p)^2 * (atlasChartUnitCovector c p d)^2) * (Q p).trace.re := by
        simp only [J, H, Matrix.trace, Complex.re_sum, Finset.mul_sum, Matrix.diag_apply]
      _ = w p * (Q p).trace.re := by simp only [w, Finset.mul_sum, Finset.sum_mul]
  have hTrace : Integrable (fun p => w p * (Q p).trace.re) τ := hJ.congr (Eventually.of_forall hJ')
  have hWindow := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  have hPos : ∀ᵐ p ∂τ, (N p).PosSemidef := by
    have hBasis := hA.2.2.2.2.2
    filter_upwards [ae_restrict_of_ae hBasis, ae_restrict_mem (μ := A.control) hWindow] with p hp hw
    have hc := hKc hw
    rw [show N p = _ from atlasAmplitudeMatrix_of_mem c A.density p hc]
    exact hp.2.1 (chartTangentBasis c (projection p) hc)
  have hw (p : Cosphere r) : 0 ≤ w p :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun d _ => sq_nonneg _))
  have hZero := integral_projectedWeight_trace_re_eq_zero_iff τ ξ N w (Eventually.of_forall hw) hPos hTrace
  have hDetect : (∀ᵐ p ∂τ, w p ≠ 0 → Q p = 0) ↔ (∀ᵐ p ∂τ, uη p ≠ 0 → Q p = 0) := by
    have hne : ∀ᵐ p ∂τ, w p ≠ 0 ↔ uη p ≠ 0 := by
      filter_upwards [ae_restrict_mem (μ := A.control) hWindow] with p hp
      have hq := (chartFrequency_square_sum_pos c p (hKc hp)).ne'
      simp [w, hq]
    constructor <;> intro ha <;> filter_upwards [ha, hne] with p hp he
    · exact fun h => hp (he.mpr h)
    · exact fun h => hp (he.mp h)
  rw [hSumIntegral, integral_congr_ae (Eventually.of_forall hJ')] at hSum
  change Tendsto (fun n => ∑ d : Index, ∑ k : OrderedPair, L d k n) atTop (𝓝 0) ↔
    ∀ᵐ p ∂τ, uη p ≠ 0 → Q p = 0
  rw [← hDetect, ← hZero]
  exact ⟨fun h => tendsto_nhds_unique hSum h, fun h => h ▸ hSum⟩

end Burnett.P01
