import Burnett.Analysis.TransportPatches.ActualThinConeL2
import Burnett.Analysis.TransportPatches.FrozenErrorInterpolation
import Burnett.Analysis.GaugeProjection.ProjectedFiniteLp
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.MikhlinApplications

/-! Finite-exponent estimates for the same actual thin complement. -/

set_option autoImplicit false
set_option maxRecDepth 5200
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Matrix Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.RicciSymbol (Index Tensor2)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01
open Burnett.A02.FrequencySplit (homogeneous_multiplier_all_Lp)
open Burnett.Analysis.ProjectiveNullCaps (thinConeProfile thinConeProfile_degreeZero)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ContDiff Manifold Matrix Topology ENNReal

open private thinComplement_contDiffOn from Burnett.Analysis.TransportPatches.ActualThinConeL2
open private projectionMatrixLpNorm_le_sum entry_eLpNorm_le_projectionMatrixLpNorm
  from Burnett.Analysis.GaugeProjection.ProjectedFiniteLp

local notation "E" => CoordinateSpace

private theorem actualThinConeComplement_gradient_eq (m : Tensor2) {η : ℝ} (hη : 0 < η)
    (inner outer : ℝ) (w : ProjectionSchwartzMatrix) (d : Index) (k : OrderedPair) :
    multiplierCoordinateDerivative (actualThinConeComplementMultiplier m hη inner outer) w d k =
      fourierMultiplier (thinComplementScalar m hη inner outer)
        ((projectionFullSchwartz (projectionMatrixDerivative d w) k.1 k.2).toLp 2 volume) := by
  rw [multiplierCoordinateDerivative, actualThinConeComplementMultiplier_output]
  apply congrArg (fourierMultiplier (thinComplementScalar m hη inner outer))
  symm
  change schwartzLpMap (projectionFullSchwartz (projectionMatrixDerivative d w) k.1 k.2) = _
  simp only [projectionFullSchwartz, map_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact gaugeProjectionComponent_toLp_eq_multiplier k.1 k.2 i j (projectionMatrixDerivative d w i j)

/-- The Mikhlin realization on the actual original gradient, with a bound
using only one derivative of the raw cutoff field. -/
theorem exists_actualThinConeComplement_finiteLp (m : Tensor2) {η : ℝ} (hη : 0 < η)
    (inner outer p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ProjectionSchwartzMatrix, ∀ d : Index, ∀ k : OrderedPair,
      let e := multiplierCoordinateDerivative (actualThinConeComplementMultiplier m hη inner outer) w d k
      MemLp (e : E → ℂ) (ENNReal.ofReal p) volume ∧
        (eLpNorm' (e : E → ℂ) p volume).toReal ≤ C * (projectionMatrixLpNorm p
          (projectionMatrixDerivative d w)).toReal := by
  let s := fun ξ : E => 1 - thinConeProfile m η inner outer ξ
  obtain ⟨a, S, C, ha, hS, hL2, _⟩ := homogeneous_multiplier_all_Lp s
    (thinComplement_contDiffOn m hη inner outer)
    (fun t ht ξ => by dsimp only [s]; rw [thinConeProfile_degreeZero _ _ _ _ t ht.ne' ξ]) p hp
  obtain ⟨C₀, hC₀, hProj⟩ := exists_projectionFullSchwartz_finiteLp_bounds p hp
  let P := ENNReal.ofReal p
  have hp₁ : 1 ≤ P := by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  letI : Fact (1 ≤ P) := ⟨hp₁⟩
  have hReal (f : E → ℂ) : eLpNorm f P volume = eLpNorm' f p volume := by
    rw [eLpNorm_eq_eLpNorm' (ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1).trans_le hp₁)) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith)]
  refine ⟨max C 0 * C₀.toReal, mul_nonneg (le_max_right _ _) ENNReal.toReal_nonneg, ?_⟩
  intro w d k e
  let f := projectionFullSchwartz (projectionMatrixDerivative d w) k.1 k.2
  have hSY : (S (f.toLp P volume) : E → ℂ) =ᵐ[volume] (e : E → ℂ) := by
    rw [show e = fourierMultiplier (thinComplementScalar m hη inner outer) (f.toLp 2 volume) from
      actualThinConeComplement_gradient_eq m hη inner outer w d k]
    have h := hL2 f (f.memLp 2 volume) (f.memLp P volume)
    rw [fourierMultiplier_congr_ae a _ (Eventually.of_forall fun ξ => (ha ξ).trans
      (thinComplementScalar_apply m hη inner outer ξ).symm)] at h
    exact h
  refine ⟨(memLp_congr_ae hSY).1 (Lp.memLp (S (f.toLp P volume))), ?_⟩
  let W := projectionMatrixLpNorm p (projectionMatrixDerivative d w)
  have hW : W < ⊤ := (projectionMatrixLpNorm_le_sum p hp₁ _).trans_lt
    (ENNReal.sum_lt_top.mpr (fun i _ => ENNReal.sum_lt_top.mpr fun j _ =>
      ((projectionMatrixDerivative d w i j).memLp P volume).eLpNorm_lt_top))
  have hRaw : ‖f.toLp P volume‖ ≤ C₀.toReal * W.toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae (f.coeFn_toLp P volume)]
    have h := (entry_eLpNorm_le_projectionMatrixLpNorm p
      (projectionFullSchwartz (projectionMatrixDerivative d w)) k.1 k.2).trans
      (hProj (projectionMatrixDerivative d w)).1
    simpa only [ENNReal.toReal_mul] using ENNReal.toReal_mono (ENNReal.mul_lt_top hC₀ hW).ne h
  calc
    _ = ‖S (f.toLp P volume)‖ := by
      rw [Lp.norm_def, eLpNorm_congr_ae hSY, hReal]
    _ ≤ C * ‖f.toLp P volume‖ := hS _
    _ ≤ max C 0 * ‖f.toLp P volume‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hRaw (le_max_right _ _)

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- With the local finite-exponent gradient bound of the raw cutoff field,
the actual thin-complement gradient vanishes strongly in whole-space L³. -/
theorem exists_actualThinConeComplement_strong3
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hn σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hn σ A)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x₀ ∈ K, ∀ ℓ : ℝ, (∀ x ∈ K, ‖x - x₀‖ ≤ ℓ) →
      ∀ (η inner outer : ℝ) (hη : 0 < η), 0 ≤ inner → inner < outer → L * ℓ ≤ inner * η →
      ∀ (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ K),
      let z := receivingCutoffFluctuation B g hB hg c χ (hχ.trans hKU)
      let T := actualThinConeComplementMultiplier (chartInverseMetric B c x₀) hη inner outer
      ∀ (d : Index) (k : OrderedPair) (p : ℝ), 3 < p →
        (∃ B₀ : ℝ, ∀ᶠ n in atTop,
          (projectionMatrixLpNorm p (projectionMatrixDerivative d (z (σ n)))).toReal ≤ B₀) →
        Tendsto (fun n => (eLpNorm' (multiplierCoordinateDerivative T (z (σ n)) d k : E → ℂ) 3 volume).toReal)
          atTop (𝓝 0) := by
  obtain ⟨L, hL, hThin⟩ := exists_actualThinConeComplement_tendsto_zero r B g hB hg hs hn hconv
    σ hσ A hA hPair c K hK hConv hKU
  refine ⟨L, hL, ?_⟩
  intro x₀ hx₀ ℓ hℓ η inner outer hη hInner hIO hSmall χ hχ z T d k p hp hRaw
  let u n := multiplierCoordinateDerivative T (z (σ n)) d k
  have hUnion := hThin x₀ hx₀ ℓ hℓ η inner outer hη hInner hIO hSmall χ hχ
  have h₂ : Tendsto u atTop (𝓝 0) := by
    have hEval := (PiLp.continuous_apply (p := 2) (β := fun _ : Index × OrderedPair => ComplexL2 E) (d, k)).tendsto 0
    simpa only [PiLp.toLp_apply, PiLp.zero_apply, Function.comp_def] using hEval.comp hUnion
  obtain ⟨C, hC, hBound⟩ := exists_actualThinConeComplement_finiteLp (chartInverseMetric B c x₀)
    hη inner outer p (by linarith)
  obtain ⟨B₀, hB₀⟩ := hRaw
  have hLp (n : ℕ) := hBound (z (σ n)) d k
  have hEq (n : ℕ) : eLpNorm' (u n : E → ℂ) 2 volume = eLpNorm (u n : E → ℂ) 2 volume := by
    rw [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    norm_num
  have hpFinite (n : ℕ) : eLpNorm' (u n : E → ℂ) p volume < ⊤ := by
    have he := (hLp n).1.eLpNorm_lt_top
    rwa [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr (by linarith)) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith)] at he
  have h₂Norm : Tendsto (fun n => (eLpNorm' (u n : E → ℂ) 2 volume).toReal) atTop (𝓝 0) := by
    simp_rw [hEq, ← Lp.norm_def]
    simpa only [Function.comp_def, norm_zero] using (continuous_norm.tendsto (0 : ComplexL2 E)).comp h₂
  refine frozenError_strong3_of_strong2 hp (fun n => (u n : E → ℂ))
    (fun n => Lp.aestronglyMeasurable (u n)) (fun n => by rw [hEq]; exact Lp.eLpNorm_lt_top (u n))
    hpFinite h₂Norm (C * B₀) ?_
  intro ε hε
  filter_upwards [hB₀] with n hn
  exact ((hLp n).2.trans (mul_le_mul_of_nonneg_left hn hC)).trans (le_add_of_nonneg_right hε.le)

end Burnett.C02
