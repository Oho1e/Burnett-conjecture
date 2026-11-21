import Burnett.Analysis.PrincipalEnergy.Localization.GlobalOrderOneH1Pair
import Burnett.Analysis.PrincipalEnergy.Localization.ProperActionLocalization

set_option autoImplicit false
set_option maxHeartbeats 5800000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Set Metric Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy
open scoped BigOperators ContDiff ComplexConjugate InnerProductSpace

/-- The tested order-one bound is a genuine L² norm bound on inputs for
which the actual output has compact support. -/
theorem exists_firstOrderAction_global_h1_action_bound {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hs : ContDiff ℝ ∞ (uncurry a))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : SchwartzMap Space ℂ),
      HasCompactSupport (firstOrderAction a f) →
        ∃ hT : MemLp (firstOrderAction a f) 2 volume,
          ‖hT.toLp (firstOrderAction a f)‖ ≤ C * coordinateH1 f := by
  obtain ⟨C, hC, hBound⟩ := exists_firstOrderAction_global_h1_pair_bound ha hs hb
  refine ⟨C, hC, fun f hf => ?_⟩
  have hT : MemLp (firstOrderAction a f) 2 volume :=
    (firstOrderAction_continuous_and_bounded ha.frequency hs.continuous f).1.memLp_of_hasCompactSupport hf
  obtain ⟨R, hR, hBall⟩ := hf.isBounded.subset_closedBall_lt 0 (0 : Space)
  obtain ⟨χ, hχ, _, hχVal, hχOne⟩ := exists_radialSchwartzCutoff R (R+1) hR (by linarith)
  let T := hT.toLp (firstOrderAction a f)
  let M := C*coordinateH1 f
  have hM : 0 ≤ M := mul_nonneg hC (Real.sqrt_nonneg _)
  have hTest (g : SchwartzMap Space ℂ) : ‖⟪g.toLp 2 volume,T⟫_ℂ‖ ≤ M*‖g.toLp 2 volume‖ := by
    let g' := scalarSchwartzProduct χ g
    have hg' : HasCompactSupport (g' : Space → ℂ) := hχ.mul_right
    have hNorm : ‖g'.toLp 2 volume‖ ≤ ‖g.toLp 2 volume‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      simpa only [Fintype.sum_unique] using scalarCutoff_sum_norm_sq_le (fun _ : Unit => χ)
        (fun _ x => (hχVal x).1) (fun _ x => (hχVal x).2.1)
        (fun x => by simpa only [Fintype.sum_unique] using (hχVal x).2.2) g
    have hEq : ⟪g.toLp 2 volume,T⟫_ℂ = ∫ x, conj (g' x)*firstOrderAction a f x := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [g.coeFn_toLp 2 volume, MemLp.coeFn_toLp hT] with x hg hx
      change inner ℂ ((g.toLp 2 volume) x) ((hT.toLp _) x) = _
      rw [hg, hx, RCLike.inner_apply']
      by_cases hv : firstOrderAction a f x = 0
      · simp only [hv, mul_zero]
      · have hnorm : ‖x‖ ≤ R := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hBall (subset_closure hv)
        simp only [g', scalarSchwartzProduct_apply, hχOne x hnorm, one_mul]
    rw [hEq]
    exact (hBound f g' hg').trans (mul_le_mul_of_nonneg_left hNorm hM)
  have hAll (v : ComplexL2 Space) : ‖⟪v,T⟫_ℂ‖ ≤ M*‖v‖ := by
    apply (schwartz_toLp_denseRange (V := Space)).induction_on (p := fun v => ‖⟪v,T⟫_ℂ‖ ≤ M*‖v‖) v
    · exact isClosed_le (continuous_id.inner continuous_const).norm (continuous_const.mul continuous_norm)
    · exact hTest
  refine ⟨hT, ?_⟩
  change ‖T‖ ≤ M
  have h := hAll T
  rw [inner_self_eq_norm_sq_to_K, norm_pow] at h
  change ‖((‖T‖ : ℝ) : ℂ)‖^2 ≤ M*‖T‖ at h
  rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), pow_two] at h
  by_cases hz : ‖T‖=0
  · rw [hz]
    exact hM
  · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg T) (Ne.symm hz))).mp h

/-- The proper support of the original Fourier kernel gives the required
compact output for every compact input. -/
theorem exists_firstOrderAction_global_h1_bound_of_properSupport {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hs : ContDiff ℝ ∞ (uncurry a))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hProper : ProperKernelRelation (firstOrderKernelRelation a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : SchwartzMap Space ℂ), HasCompactSupport (f : Space → ℂ) →
      ∃ hT : MemLp (firstOrderAction a f) 2 volume, ‖hT.toLp (firstOrderAction a f)‖ ≤ C * coordinateH1 f := by
  obtain ⟨C, hC, hB⟩ := exists_firstOrderAction_global_h1_action_bound ha hs hb
  refine ⟨C, hC, fun f hf => ?_⟩
  obtain ⟨K, hK, _, hT⟩ := exists_firstOrderAction_support_of_properSupport ha.frequency hProper f hf
  exact hB f (hK.of_isClosed_subset isClosed_closure hT)

end Burnett.Analysis.CarlesonEmbedding
