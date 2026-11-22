import Burnett.Analysis.GaugeProjection.MatrixLipschitzCoefficientBound
import Burnett.Analysis.GaugeProjection.SmoothLipschitzApproximation

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

namespace Burnett.P01

open Filter MeasureTheory
open Burnett.A02.FrequencySplit (E)
open Burnett.Fourier
open scoped NNReal Topology

private theorem norm_coefficientProduct_sub_le (f g : E → ℂ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (hg : LipschitzWith L g) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ x, ‖g x - f x‖ ≤ δ) (w : SchwartzMap E ℂ) :
    ‖projectionLipschitzCoefficientProductL2 g L hg w -
      projectionLipschitzCoefficientProductL2 f L hf w‖ ≤ δ * ‖w.toLp 2 volume‖ := by
  let u := projectionLipschitzCoefficientProductL2 g L hg w
  let v := projectionLipschitzCoefficientProductL2 f L hf w
  let q := w.toLp 2 volume
  have hnorm : ‖u - v‖ ≤ ‖δ • q‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub u v, Lp.coeFn_smul δ q, w.coeFn_toLp 2 volume,
      projectionLipschitzCoefficientProductL2_ae g L hg w,
      projectionLipschitzCoefficientProductL2_ae f L hf w] with x hsub hs hw hu hv
    change q x = w x at hw
    change u x = g x * w x at hu
    change v x = f x * w x at hv
    rw [hsub, hs, Pi.sub_apply, Pi.smul_apply, hu, hv, hw, ← sub_mul, norm_mul, norm_smul,
      Real.norm_of_nonneg hδ]
    exact mul_le_mul_of_nonneg_right (h x) (norm_nonneg _)
  simpa only [u, v, q, norm_smul, Real.norm_of_nonneg hδ] using hnorm

/-- The physical differentiated commutator satisfies the same estimate for
every globally Lipschitz coefficient, by smooth approximation preserving its
Lipschitz seminorm. The input here is a Schwartz matrix field. -/
theorem exists_projectionGeneralLipschitzCommutatorL2_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Fin 4) (f : E → ℂ) (L : ℝ≥0) (hL : LipschitzWith L f)
      (w : ProjectionSchwartzMatrix),
      ‖projectionLipschitzCommutatorL2 b f L hL w‖ ≤ C * (L : ℝ) * ‖projectionMatrixToL2 w‖ := by
  obtain ⟨C, hC, estimate⟩ := exists_projectionLipschitzCommutatorL2_bound
  refine ⟨C, hC, fun b f L hL w => ?_⟩
  let ε (n : ℕ) := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have approx (n : ℕ) := exists_smooth_lipschitz_approximation f L hL (ε n) (hε n)
  choose g hg hgLip hclose using approx
  let A (n : ℕ) (u : ProjectionSchwartzMatrix) : ProjectionL2Matrix :=
    fun i j => projectionLipschitzCoefficientProductL2 (g n) L (hgLip n) (u i j)
  let B (u : ProjectionSchwartzMatrix) : ProjectionL2Matrix :=
    fun i j => projectionLipschitzCoefficientProductL2 f L hL (u i j)
  have ht (u : ProjectionSchwartzMatrix) : Tendsto (fun n => A n u) atTop (𝓝 (B u)) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    rw [tendsto_iff_dist_tendsto_zero]
    have hzero : Tendsto (fun n => ((L : ℝ) * ε n) * ‖(u i j).toLp 2 volume‖) atTop (𝓝 0) := by
      simpa only [mul_zero, zero_mul] using (hlim.const_mul (L : ℝ)).mul_const ‖(u i j).toLp 2 volume‖
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hzero
    rw [dist_eq_norm]
    exact norm_coefficientProduct_sub_le f (g n) L hL (hgLip n) _
      (mul_nonneg L.coe_nonneg (hε n).le) (hclose n) (u i j)
  let d := projectionMatrixDerivative b w
  have hfirst := projectionFullL2.continuous.continuousAt.tendsto.comp (ht d)
  have hsecond := ht (projectionFullSchwartz d)
  have hconv : Tendsto (fun n => projectionLipschitzCommutatorL2 b (g n) L (hgLip n) w)
      atTop (𝓝 (projectionLipschitzCommutatorL2 b f L hL w)) := hfirst.sub hsecond
  exact le_of_tendsto' hconv.norm fun n => estimate b (g n) (hg n) L (hgLip n) w

end Burnett.P01
