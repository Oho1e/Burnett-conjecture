import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Burnett.X02.L2Bounds

abbrev Space := EuclideanSpace ℝ (Fin 4)

/-- A genuine L² estimate; both sides have explicit MemLp witnesses, so no
conversion of an infinite seminorm to zero is involved. -/
theorem norm_toLp_le_of_abs_le {f g : Space → ℝ}
    (hf : MemLp f 2 (volume : Measure Space)) (hg : MemLp g 2 volume)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, |f x| ≤ C * |g x|) :
    ‖hf.toLp f‖ ≤ C * ‖hg.toLp g‖ := by
  have hCg := hg.const_smul C
  have hnorm : ‖hf.toLp f‖ ≤ ‖hCg.toLp (C • g)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hf.coeFn_toLp, hCg.coeFn_toLp] with x hfx hCgx
    rw [hfx, hCgx]
    change |f x| ≤ |C * g x|
    rw [abs_mul, abs_of_nonneg hC]
    exact h x
  change ‖hf.toLp f‖ ≤ ‖C • hg.toLp g‖ at hnorm
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using hnorm

theorem toLp_tendsto_zero_of_bound {ι : Type*} {l : Filter ι}
    {f : ι → Space → ℝ} {g : Space → ℝ}
    (hf : ∀ i, MemLp (f i) 2 (volume : Measure Space)) (hg : MemLp g 2 volume)
    {C : ι → ℝ} (hC : ∀ i, 0 ≤ C i) (hCt : Tendsto C l (𝓝 0))
    (h : ∀ i x, |f i x| ≤ C i * |g x|) :
    Tendsto (fun i => (hf i).toLp (f i)) l (𝓝 0) := by
  apply squeeze_zero_norm
  · intro i
    exact norm_toLp_le_of_abs_le (hf i) hg (hC i) (h i)
  · simpa only [zero_mul] using hCt.mul_const ‖hg.toLp g‖

#print axioms norm_toLp_le_of_abs_le
#print axioms toLp_tendsto_zero_of_bound

end Burnett.X02.L2Bounds
