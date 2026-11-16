import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Density of genuine Schwartz functions in complex L²(volume).
The intermediate continuous compactly supported function is smoothed on
the whole space, then multiplied by one fixed smooth compact cutoff.
The L² error is controlled by that fixed cutoff's finite L² norm. -/

noncomputable section

namespace Burnett.Fourier

open MeasureTheory Filter Metric Set
open scoped ContDiff Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem norm_toLp_le_of_norm_le {f g : V → ℂ}
    (hf : MemLp f 2 (volume : Measure V)) (hg : MemLp g 2 volume)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖f x‖ ≤ C * ‖g x‖) :
    ‖hf.toLp f‖ ≤ C * ‖hg.toLp g‖ := by
  have hCg := hg.const_smul C
  have hb : ‖hf.toLp f‖ ≤ ‖hCg.toLp (C • g)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hf.coeFn_toLp, hCg.coeFn_toLp] with x hfx hCgx
    rw [hfx, hCgx]
    simpa only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using h x
  change ‖hf.toLp f‖ ≤ ‖C • hg.toLp g‖ at hb
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using hb

/-- A continuous compactly supported function has arbitrarily close
Schwartz approximants in the actual whole-space L² norm. -/
theorem exists_schwartz_dist_lt_of_continuous_compactSupport
    {g : V → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hg : MemLp g 2 (volume : Measure V)) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : SchwartzMap V ℂ, dist (hg.toLp g) (q.toLp 2 volume) < ε := by
  obtain ⟨R, hR, hgR⟩ := hgs.isBounded.subset_closedBall_lt 0 (0 : V)
  let b : ContDiffBump (0 : V) := ⟨R, R + 1, hR, by linarith⟩
  let B : SchwartzMap V ℂ :=
    (b.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp b.contDiff)
  let δ : ℝ := ε / (2 * (‖B.toLp 2 volume‖ + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨h, hhs, hclose⟩ :=
    (hgs.uniformContinuous_of_continuous hgc).exists_contDiff_dist_le hδ
  let q : SchwartzMap V ℂ :=
    ((b.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right).toSchwartzMap
      ((Complex.ofRealCLM.contDiff.comp b.contDiff).mul hhs)
  have hbg (x : V) : (b x : ℂ) * g x = g x := by
    by_cases hx : x ∈ tsupport g
    · rw [b.one_of_mem_closedBall (hgR hx), Complex.ofReal_one, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hpoint (x : V) : ‖(q : V → ℂ) x - g x‖ ≤ δ * ‖B x‖ := by
    change ‖(b x : ℂ) * h x - g x‖ ≤ δ * ‖(b x : ℂ)‖
    rw [← hbg x, ← mul_sub, norm_mul]
    have hc := (hclose x).le
    rw [dist_eq_norm] at hc
    exact (mul_le_mul_of_nonneg_left hc (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hnorm : ‖q.toLp 2 volume - hg.toLp g‖ ≤ δ * ‖B.toLp 2 volume‖ := by
    exact norm_toLp_le_of_norm_le ((q.memLp 2 volume).sub hg) (B.memLp 2 volume)
      hδ.le hpoint
  refine ⟨q, ?_⟩
  rw [dist_comm, dist_eq_norm]
  apply hnorm.trans_lt
  have hden : 0 < 2 * (‖B.toLp 2 volume‖ + 1) := by positivity
  have hmul : δ * (2 * (‖B.toLp 2 volume‖ + 1)) = ε :=
    div_mul_cancel₀ ε hden.ne'
  nlinarith [mul_nonneg hδ.le (norm_nonneg (B.toLp 2 volume))]

/-- Genuine Schwartz → L²(volume) density, with no density assumption. -/
theorem schwartz_toLp_denseRange :
    DenseRange (fun f : SchwartzMap V ℂ => f.toLp 2 (volume : Measure V)) := by
  apply Metric.denseRange_iff.mpr
  intro f ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨g, hgs, hdist, hgc, hg⟩ :=
    (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le (by norm_num)
      (ENNReal.ofReal_ne_zero_iff.mpr hε4)
  have hfg : dist f (hg.toLp g) ≤ ε / 4 := by
    rw [dist_eq_norm, ← Lp.toLp_coeFn f (Lp.memLp f), ← MemLp.toLp_sub,
      Lp.norm_toLp]
    have hb := (ENNReal.toReal_le_toReal ((Lp.memLp f).sub hg).2.ne
      ENNReal.ofReal_ne_top).mpr hdist
    simpa only [ENNReal.toReal_ofReal hε4.le] using hb
  obtain ⟨q, hq⟩ := exists_schwartz_dist_lt_of_continuous_compactSupport hgc hgs hg
    (show 0 < ε / 2 by positivity)
  refine ⟨q, (dist_triangle f (hg.toLp g) (q.toLp 2 volume)).trans_lt ?_⟩
  linarith

end Burnett.Fourier
