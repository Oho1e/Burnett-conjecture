import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit.CMBilinearDual

open MeasureTheory Metric Set
open scoped ContDiff ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A real compact smooth bump, regarded as a complex Schwartz function. -/
def schwartzBump {c : V} (b : ContDiffBump c) : SchwartzMap V ℂ :=
  (b.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp b.contDiff)

theorem schwartzBump_apply {c : V} (b : ContDiffBump c) (x : V) :
    schwartzBump b x = (b x : ℂ) := rfl

variable [MeasurableSpace V] [BorelSpace V]

private theorem exists_schwartz_dist_lt
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {f : V → ℂ} (hc : Continuous f)
    (hs : HasCompactSupport f) (hf : MemLp f p (volume : Measure V))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : SchwartzMap V ℂ, dist (hf.toLp f) (g.toLp p volume) < ε := by
  obtain ⟨R, hR, hsupport⟩ := hs.isBounded.subset_closedBall_lt 0 (0 : V)
  let b : ContDiffBump (0 : V) := ⟨R, R + 1, hR, by linarith⟩
  let B := schwartzBump b
  let δ := ε / (2 * (‖B.toLp p volume‖ + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨u, hu, hclose⟩ := (hs.uniformContinuous_of_continuous hc).exists_contDiff_dist_le hδ
  let g : SchwartzMap V ℂ :=
    ((b.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right).toSchwartzMap
      ((Complex.ofRealCLM.contDiff.comp b.contDiff).mul hu)
  have fixed (x : V) : (b x : ℂ) * f x = f x := by
    by_cases hx : x ∈ tsupport f
    · rw [b.one_of_mem_closedBall (hsupport hx), Complex.ofReal_one, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have pointwise (x : V) : ‖g x - f x‖ ≤ δ * ‖B x‖ := by
    change ‖(b x : ℂ) * u x - f x‖ ≤ δ * ‖(b x : ℂ)‖
    rw [← fixed x, ← mul_sub, norm_mul, mul_comm δ]
    exact mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using (hclose x).le)
      (norm_nonneg _)
  have hbound :
      eLpNorm ((g : V → ℂ) - f) p volume ≤ ENNReal.ofReal δ * eLpNorm (B : V → ℂ) p volume :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Filter.Eventually.of_forall pointwise) p
  have hfinite : ENNReal.ofReal δ * eLpNorm (B : V → ℂ) p volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (B.memLp p volume).2.ne
  have hnorm := ENNReal.toReal_mono hfinite hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le, ← SchwartzMap.norm_toLp] at hnorm
  refine ⟨g, ?_⟩
  rw [dist_comm, dist_eq_norm]
  change ‖(g.memLp p volume).toLp (g : V → ℂ) - hf.toLp f‖ < ε
  rw [← MemLp.toLp_sub, Lp.norm_toLp]
  apply hnorm.trans_lt
  have hden : 0 < 2 * (‖B.toLp p volume‖ + 1) := by positivity
  have hmul : δ * (2 * (‖B.toLp p volume‖ + 1)) = ε := div_mul_cancel₀ ε hden.ne'
  nlinarith [mul_nonneg hδ.le (norm_nonneg (B.toLp p volume))]

/-- Actual Schwartz functions are dense in each finite normed Lᵖ on V. -/
theorem schwartz_toLp_denseRange (p : ℝ≥0∞) (hp : p ≠ ⊤) [Fact (1 ≤ p)] :
    DenseRange (fun f : SchwartzMap V ℂ => f.toLp p (volume : Measure V)) := by
  apply Metric.denseRange_iff.mpr
  intro f ε hε
  have hε₀ : 0 < ε / 4 := by positivity
  obtain ⟨g, hgs, hdist, hgc, hg⟩ :=
    (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le hp
      (ENNReal.ofReal_ne_zero_iff.mpr hε₀)
  have hfg : dist f (hg.toLp g) ≤ ε / 4 := by
    rw [dist_eq_norm, ← Lp.toLp_coeFn f (Lp.memLp f), ← MemLp.toLp_sub, Lp.norm_toLp]
    exact (ENNReal.toReal_le_of_le_ofReal hε₀.le hdist)
  obtain ⟨q, hq⟩ := exists_schwartz_dist_lt p hgc hgs hg (show 0 < ε / 2 by positivity)
  exact ⟨q, (dist_triangle f (hg.toLp g) (q.toLp p volume)).trans_lt (by linarith)⟩

end Burnett.A02.FrequencySplit.CMBilinearDual
