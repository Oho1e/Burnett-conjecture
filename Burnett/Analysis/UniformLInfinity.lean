import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Actual L-infinity bounds from uniform bounds, including restricted
measures. No finiteness assumption on the total measure is required.
Measurability/L-infinity membership of the represented functions remains
an explicit input to the normed-space convergence statement. -/

noncomputable section

namespace Burnett.Analysis

open MeasureTheory Filter
open scoped Topology ENNReal

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]

theorem norm_toLp_top_le_of_ae_bound {μ : Measure X} {f : X → F}
    (hf : MemLp f ∞ μ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ‖hf.toLp f‖ ≤ C := by
  rw [Lp.norm_toLp]
  apply ENNReal.toReal_le_of_le_ofReal hC
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound hb

theorem norm_toLp_top_restrict_le {μ : Measure X} {K : Set X}
    (hK : MeasurableSet K) {f : X → F} (hf : MemLp f ∞ (μ.restrict K))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ K, ‖f x‖ ≤ C) :
    ‖hf.toLp f‖ ≤ C := by
  apply norm_toLp_top_le_of_ae_bound hf hC
  filter_upwards [ae_restrict_mem hK] with x hx
  exact hb x hx

/-- Uniform convergence on a measurable fixed set implies convergence in
the actual L-infinity norm of the restricted measure. The functions are
not silently truncated after applying a nonlocal operator. -/
theorem tendsto_toLp_top_of_uniformlyOn_zero {ι : Type*} {l : Filter ι}
    {μ : Measure X} {K : Set X} (hK : MeasurableSet K) (f : ι → X → F)
    (hf : ∀ i, MemLp (f i) ∞ (μ.restrict K))
    (hu : TendstoUniformlyOn f (fun _ => 0) l K) :
    Tendsto (fun i => (hf i).toLp (f i)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (ε / 2) (half_pos hε)] with i hi
  rw [dist_zero_right]
  apply (norm_toLp_top_restrict_le hK (hf i) (half_pos hε).le ?_).trans_lt
    (half_lt_self hε)
  intro x hx
  have hh := hi x hx
  simpa only [dist_zero_left] using hh.le

end Burnett.Analysis
