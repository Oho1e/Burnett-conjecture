import Burnett.Analysis.TransportPatches.ReceivingMatrixMultiplierEnergy
import Burnett.Analysis.GaugeProjection.StrongCompactness.HomogeneousReceivingBridge

/-! The original whole-space coordinate defect norm on its fixed subsequence. -/

set_option autoImplicit false
set_option maxRecDepth 5300
set_option maxHeartbeats 7100000

noncomputable section

namespace Burnett.C02

open Set Filter Function MeasureTheory Matrix Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Microlocal.Overlap Burnett.Microlocal.AtlasVolumeGradient
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase)
open Burnett.RicciSymbol (Index)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open Burnett.A07 (coordinateDerivative)
open Burnett.P01 (ProjectionSchwartzMatrix receivingCutoffFluctuation
  exists_receiving_cutoff_metric_and_derivative_error inverseHalfDensityCutoff
  inverseHalfDensityCutoff_tsupport fixedWeightedCutoff_inverseHalfDensityCutoff)
open scoped BigOperators ComplexConjugate ContDiff InnerProduct Manifold Matrix Topology

local notation "E" => CoordinateSpace

variable {J : Type*}

/-- Actual whole-space weak derivatives of the matrix-multiplied input. -/
def multiplierCoordinateDerivative (T : ClassicalMatrixMultiplier J)
    (z : ProjectionSchwartzMatrix) (d : Index) (k : J) : ComplexL2 E :=
  T.output (fun i => (coordinateDerivative d (z i.1 i.2)).toLp 2 volume) k

theorem multiplierCoordinateDerivative_weak (T : ClassicalMatrixMultiplier J)
    (z : ProjectionSchwartzMatrix) (d : Index) (k : J) (f : SchwartzMap E ℂ) :
    inner ℂ ((coordinateDerivative d f).toLp 2 volume)
      (T.output (fun i => (z i.1 i.2).toLp 2 volume) k) =
      -inner ℂ (f.toLp 2 volume) (multiplierCoordinateDerivative T z d k) :=
  T.output_weak_coordinateDerivative (fun i => z i.1 i.2) f d k

theorem multiplierCoordinateDerivative_norm_sq [Fintype J] (T : ClassicalMatrixMultiplier J)
    (z : ProjectionSchwartzMatrix) :
    ‖WithLp.toLp 2 (fun a : Index × J => multiplierCoordinateDerivative T z a.1 a.2)‖^2 =
      ∑ d : Index, ∑ k : J, ‖multiplierCoordinateDerivative T z d k‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [PiLp.toLp_apply]
  exact Fintype.sum_prod_type (fun a : Index × J => ‖multiplierCoordinateDerivative T z a.1 a.2‖^2)

private theorem norm_sq_tendsto_of_sub_tendsto_zero {X : Type*} [NormedAddCommGroup X]
    (v w : ℕ → X) (C : ℝ)
    (hClose : Tendsto (fun n => v n - w n) atTop (𝓝 0))
    (hW : Tendsto (fun n => ‖w n‖^2) atTop (𝓝 C)) :
    Tendsto (fun n => ‖v n‖^2) atTop (𝓝 C) := by
  have hC : 0 ≤ C := ge_of_tendsto' hW (fun _ => sq_nonneg _)
  have hRoot := (Real.continuous_sqrt.tendsto C).comp hW
  change Tendsto (fun n => Real.sqrt (‖w n‖^2)) atTop (𝓝 (Real.sqrt C)) at hRoot
  have hW' : Tendsto (fun n => ‖w n‖) atTop (𝓝 (Real.sqrt C)) := by
    simpa only [Real.sqrt_sq (norm_nonneg _)] using hRoot
  have hDelta : Tendsto (fun n => ‖v n‖ - ‖w n‖) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (by simpa only [norm_zero] using hClose.norm)
    simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (v n) (w n)
  have hV := hDelta.add hW'
  simpa only [sub_add_cancel, zero_add, Real.sq_sqrt hC] using hV.pow 2

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold Model ∞ M] [SecondCountableTopology M]

/-- The coordinate density of the smooth physical volume. -/
def chartVolumeDensity (B : Field (M := M)) (c : AtlasChart M) (x : E) : ℝ :=
  Real.sqrt |Matrix.det (metricComponents (fixedForm B c) x)|

/-- The same ordered amplitude with the coordinate Lebesgue density. -/
def chartLebesgueAmplitude {r : Metric (M := M)} (B : Field (M := M)) (c : AtlasChart M)
    (A : IntrinsicAmplitudeCovariance r) (p : Cosphere r) : Matrix OrderedPair OrderedPair ℂ :=
  (((chartVolumeDensity B c (fixedChartPhase c p.val).1)⁻¹ : ℝ) : ℂ) • atlasAmplitudeMatrix c A.density p

/-- The already extracted covariance gives the exact global squared L²
norm of the coordinate derivative of the actual localized multiplier field. -/
theorem tendsto_originalGlobalDefectNorm [Fintype J]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hn σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart '' K) (T : ClassicalMatrixMultiplier J) :
    let hχc := hχ.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let z := receivingCutoffFluctuation B g hB hg c χ hχc
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let H (p : Cosphere r) :=
      let x := (fixedChartPhase c p.val).1
      let ξ : E := WithLp.toLp 2 (atlasChartUnitCovector c p)
      let P := T.principal ξ
      ((χ : E → ℝ) x)^2 * ‖ξ‖^2 * (P * chartLebesgueAmplitude B c A p * Pᴴ).trace.re
    Integrable H τ ∧ Tendsto (fun n => ∑ d : Index, ∑ k : J,
      ‖multiplierCoordinateDerivative T (z (σ n)) d k‖^2) atTop (𝓝 (∫ p, H p ∂τ)) := by
  intro hχc z τ H
  let η := inverseHalfDensityCutoff B hB hn c χ hχc
  have hηs := inverseHalfDensityCutoff_tsupport B hB hn c χ hχc
  have hη : tsupport (η : E → ℝ) ⊆ c.chart '' K := hηs.trans hχ
  have hηc : tsupport (η : E → ℝ) ⊆ c.chart.target := hηs.trans hχc
  have hχeq : fixedWeightedCutoff B hB hn c η hηc = χ :=
    fixedWeightedCutoff_inverseHalfDensityCutoff B hB hn c χ hχc
  obtain ⟨z', hz', _, hErr⟩ := exists_receiving_cutoff_metric_and_derivative_error r B g hB hg hconv c χ hχc
  have hzz : z' = z := by
    funext n i j
    ext x
    exact hz' n x i j
  subst z'
  let u (d : Index) (n : ℕ) (i : OrderedPair) :=
    (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η hηc (σ n) (d, i)).toLp 2 volume
  let v (d : Index) (n : ℕ) (i : OrderedPair) :=
    (coordinateDerivative d (z (σ n) i.1 i.2)).toLp 2 volume
  have hFixed (n : ℕ) (d : Index) (i : OrderedPair) :
      fixedVolumeGradientSchwartz B g hB hg hn c η hηc n (d, i) =
        fixedGradientSchwartz B g hB hg c χ hχc n (d, i) := by
    ext x
    rw [fixedVolumeGradientSchwartz_apply, fixedGradientSchwartz_apply]
    have he := congrFun (congrArg Subtype.val hχeq) x
    change (η : E → ℝ) x * fixedHalfDensity B c x = (χ : E → ℝ) x at he
    rw [he]
  have hInput (d : Index) (i : OrderedPair) :
      Tendsto (fun n => v d n i - u d n i) atTop (𝓝 0) := by
    have hCov := fixedVolumeCovariantGradient_sub_partial_tendsto_zero r B g hB hg hn hconv c η hηc (d, i)
    simp only [hFixed] at hCov
    have hh := ((hErr d i.1 i.2).comp hσ.tendsto_atTop).sub (hCov.comp hσ.tendsto_atTop)
    refine Tendsto.congr (fun n => ?_) (by simpa only [sub_zero] using hh)
    dsimp only [Function.comp_apply, u, v]
    abel
  let ξ (p : Cosphere r) : E := WithLp.toLp 2 (atlasChartUnitCovector c p)
  let Q (p : Cosphere r) :=
    T.principal (ξ p) * atlasAmplitudeMatrix c A.density p * (T.principal (ξ p))ᴴ
  let F (d : Index) (k : J) (p : Cosphere r) :=
    ((η : E → ℝ) (fixedChartPhase c p.val).1)^2 * (atlasChartUnitCovector c p d)^2 * (Q p k k).re
  have hPair' (d : Index) (k : J) := tendsto_receiving_matrixMultiplierEnergy r B g hB hg hn σ A
    hPair c K hK hKc η hη d T k
  have hI (d : Index) (k : J) : Integrable (F d k) τ := (hPair' d k).1
  have hActual (d : Index) (k : J) :
      Tendsto (fun n => ‖multiplierCoordinateDerivative T (z (σ n)) d k‖^2)
        atTop (𝓝 (∫ p, F d k p ∂τ)) :=
    norm_sq_tendsto_of_sub_tendsto_zero
      (fun n => T.output (v d n) k) (fun n => T.output (u d n) k) _
      (T.output_sub_tendsto_zero (v d) (u d) (hInput d) k) (hPair' d k).2
  have hAll := tendsto_finset_sum (Finset.univ : Finset Index) (fun d _ =>
    tendsto_finset_sum (Finset.univ : Finset J) (fun k _ => hActual d k))
  let G (p : Cosphere r) := ∑ d : Index, ∑ k : J, F d k p
  have hG : Integrable G τ := integrable_finset_sum _ (fun d _ => integrable_finset_sum _ (fun k _ => hI d k))
  have hGIntegral : (∑ d : Index, ∑ k : J, ∫ p, F d k p ∂τ) = ∫ p, G p ∂τ := by
    simp only [G]
    rw [integral_finset_sum _ (fun d _ => integrable_finset_sum _ (fun k _ => hI d k))]
    exact Finset.sum_congr rfl (fun d _ => (integral_finset_sum _ (fun k _ => hI d k)).symm)
  have hGPoint (p : Cosphere r) : G p = H p := by
    let x := (fixedChartPhase c p.val).1
    have hηsq : ((η : E → ℝ) x)^2 =
        ((χ : E → ℝ) x)^2 * (chartVolumeDensity B c x)⁻¹ := by
      change (((χ : E → ℝ) x) * (fixedHalfDensity B c x)⁻¹)^2 = _
      rw [mul_pow, inv_pow]
      simp only [fixedHalfDensity, chartVolumeDensity, Real.sq_sqrt (Real.sqrt_nonneg _)]
    have hξsq : (∑ d : Index, (atlasChartUnitCovector c p d)^2) = ‖ξ p‖^2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [ξ, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
    have hTrace :
        (T.principal (ξ p) * chartLebesgueAmplitude B c A p * (T.principal (ξ p))ᴴ).trace.re =
          (chartVolumeDensity B c x)⁻¹ * (Q p).trace.re := by
      simp only [chartLebesgueAmplitude, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Q, x]
    calc
      G p = ∑ d : Index, (((η : E → ℝ) x)^2 * (atlasChartUnitCovector c p d)^2) * (Q p).trace.re := by
        simp only [G, F, Matrix.trace, Matrix.diag_apply, Complex.re_sum, Finset.mul_sum, x]
      _ = ((η : E → ℝ) x)^2 * (∑ d : Index, (atlasChartUnitCovector c p d)^2) * (Q p).trace.re := by
        simp only [Finset.mul_sum, Finset.sum_mul]
      _ = H p := by
        change _ = ((χ : E → ℝ) x)^2 * ‖ξ p‖^2 *
          (T.principal (ξ p) * chartLebesgueAmplitude B c A p * (T.principal (ξ p))ᴴ).trace.re
        rw [hηsq, hξsq, hTrace]
        ring
  rw [hGIntegral, integral_congr_ae (Eventually.of_forall hGPoint)] at hAll
  exact ⟨hG.congr (Eventually.of_forall hGPoint), hAll⟩

end Burnett.C02
