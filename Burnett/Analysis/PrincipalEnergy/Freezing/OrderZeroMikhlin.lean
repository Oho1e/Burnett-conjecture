import Burnett.Analysis.PrincipalEnergy.Freezing.OrderZeroFrequencyProfiles
import Burnett.Analysis.PrincipalEnergy.Freezing.DyadicOrderZeroWindows

set_option autoImplicit false
set_option maxHeartbeats 2800000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped BigOperators ContDiff ENNReal FourierTransform Topology

private theorem normalized_mikhlin_weight (k : Index → ℤ) :
    1 + ‖spatialModeFrequency 5 k‖ ≤ spatialLatticeWeight k := by
  rw [spatialModeFrequency, norm_smul, Real.norm_of_nonneg (by norm_num : 0 ≤ (2 * 5 : ℝ)⁻¹),
    spatialLatticeWeight]
  exact add_le_add_left (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)) _

/-- The actual whole-space multiplier bound applies to nonhomogeneous
smooth order-zero symbols. The constant depends on the normalized
Mikhlin budget and is uniform in the centered finite band truncations. -/
theorem exists_order_zero_mikhlin_L3_bound :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (m : E → ℝ), ContDiff ℝ ∞ m →
      ∀ D : ℝ, 0 ≤ D → MikhlinOrderZeroBudget m D →
      ∀ u : SchwartzMap E ℂ,
        let W := normalizedComplexFourierAction (fun ξ => (m ξ : ℂ)) u
        MemLp W (ENNReal.ofReal 3) volume ∧
          eLpNorm W (ENNReal.ofReal 3) volume ≤ (K * ENNReal.ofReal D) *
            eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume := by
  obtain ⟨a, shape, ac, cut⟩ := mikhlin_profile_exists (fun _ => (1 : ℝ)) contDiff_const.contDiffOn
  obtain ⟨V, Vfin, groups⟩ := exists_grouped_annular_family_L3_bound a ac cut
  obtain ⟨P, P0, profile⟩ := exists_normalized_order_zero_annular_expansion
  let I := Index → ℤ
  let w (k : I) := spatialLatticeWeight k
  let s₀ (k : I) := w k ^ 1 / w k ^ 8
  let total := ∑' k : I, s₀ k
  have wpos (k : I) : 0 < w k := by unfold w spatialLatticeWeight; positivity
  have hS : Summable s₀ := summable_spatial_lattice_weighted_decay 8 1 (by decide) (by decide)
  have pos (k : I) : 0 ≤ s₀ k := div_nonneg (pow_nonneg (wpos k).le _) (pow_nonneg (wpos k).le _)
  have T0 : 0 ≤ total := tsum_nonneg pos
  let K := V * ENNReal.ofReal (P * total)
  have Kfin : K < ⊤ := ENNReal.mul_lt_top Vfin ENNReal.ofReal_lt_top
  refine ⟨K, Kfin, ?_⟩
  intro m hm D D0 jet u W
  let p := ENNReal.ofReal 3
  let Y := eLpNorm (u : E → ℂ) p volume
  let d (k : I) := P * D / w k ^ 8
  let q (k : I) := spatialModeFrequency 5 k
  let weight (k : I) := d k * (1 + ‖q k‖)
  have d0 (k : I) : 0 ≤ d k := div_nonneg (mul_nonneg P0 D0) (pow_nonneg (wpos k).le _)
  have upper (k : I) : weight k ≤ (P * D) * s₀ k := by
    refine (mul_le_mul_of_nonneg_left (normalized_mikhlin_weight k) (d0 k)).trans_eq ?_
    dsimp only [s₀, d]
    rw [pow_one, div_eq_mul_inv, div_eq_mul_inv]
    ring
  have sw : Summable weight := Summable.of_nonneg_of_le (fun k => mul_nonneg (d0 k) (by positivity))
    upper (hS.mul_left (P * D))
  have tw : (∑' k : I, weight k) ≤ (P * D) * total := by
    exact (sw.tsum_le_tsum upper (hS.mul_left _)).trans_eq tsum_mul_left
  let t (N : ℕ) := ((2 : ℝ)^N)⁻¹
  let J (N : ℕ) := Finset.range (N + N)
  let s (N j : ℕ) : ℝ := (2 : ℝ)^j * t N
  let aN (N : ℕ) (ξ : E) : ℂ := ∑ j ∈ J N, a (s N j • ξ) * (m ξ : ℂ)
  let c (N : ℕ) (k : I) (j : ℕ) := normalizedMikhlinCubeCoefficient m (s N j) k
  have t0 (N : ℕ) : 0 < t N := by unfold t; positivity
  have spos (N j : ℕ) : 0 < s N j := mul_pos (by positivity) (t0 N)
  have hMass (ξ : E) (hne : ξ ≠ 0) : ‖m ξ‖ ≤ D := by
    simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using jet 0 (by decide) ξ hne
  have mNC (N : ℕ) : Continuous (aN N) :=
    continuous_finset_sum _ fun j _ => (a.continuous.comp (continuous_const.smul continuous_id)).mul
      (Complex.continuous_ofReal.comp hm.continuous)
  have mNB (N : ℕ) (ξ : E) : ‖aN N ξ‖ ≤ 2 * D := by
    dsimp only [aN, J, s]
    rw [← Finset.sum_mul, mikhlin_telescope (fun _ : E => (1 : ℝ)) (fun _ _ _ => rfl) a shape _ (t0 N)]
    simp only [Complex.ofReal_one, mul_one]
    by_cases hn : ξ = 0
    · subst ξ
      simp only [smul_zero, sub_self, Complex.ofReal_zero, zero_mul, norm_zero]
      positivity
    · rw [norm_mul, Complex.norm_real, Complex.norm_real]
      refine mul_le_mul ?_ (hMass ξ hn) (norm_nonneg _) (by norm_num)
      have top (y : E) : ‖mikhlinBall y‖ ≤ 1 := by
        rw [Real.norm_of_nonneg mikhlinBall.nonneg]
        exact mikhlinBall.le_one
      exact (norm_sub_le _ _).trans ((add_le_add (top _) (top _)).trans_eq (by norm_num))
  have latticeExpansion (N : ℕ) (ξ : E) :
      HasSum (fun k => groupedAnnularSymbol a (t N) (q k) (J N) (c N k) ξ) (aN N ξ) := by
    have scaleExpansion (j : ℕ) (_ : j ∈ J N) :
        HasSum (fun k : I => c N k j * patchFourierPhase (s N j • ξ) (q k) * a (s N j • ξ))
          (a (s N j • ξ) * (m ξ : ℂ)) := by
      by_cases zero : a (s N j • ξ) = 0
      · simp only [zero, mul_zero, zero_mul]
        exact hasSum_zero
      · have between := cut _ zero
        have val : (s N j)⁻¹ • (s N j • ξ) = ξ := by rw [smul_smul, inv_mul_cancel₀ (spos N j).ne', one_smul]
        have h := ((profile m hm D D0 jet (s N j) (spos N j)).2 _ between.1.le between.2.le)
        rw [val] at h
        have out := h.mul_right (a (s N j • ξ))
        rw [mul_comm (m ξ : ℂ) (a (s N j • ξ))] at out
        exact out
    exact hasSum_sum scaleExpansion
  let wN (N : ℕ) := normalizedComplexFourierAction (aN N) u
  have nBounds (N : ℕ) : MemLp (wN N) p volume ∧ eLpNorm (wN N) p volume ≤ (K * ENNReal.ofReal D) * Y := by
    have choose := groups (t N) (t0 N) (J N) q (c N) d d0
      (fun k j => (profile m hm D D0 jet (s N j) (spos N j)).1 k) sw
      (aN N) (mNC N).measurable (2*D) (mNB N) (latticeExpansion N) u
    refine ⟨choose.1, choose.2.trans ?_⟩
    refine (mul_le_mul_right' (mul_le_mul_left' (ENNReal.ofReal_le_ofReal tw) _) _).trans_eq ?_
    dsimp only [K]
    rw [mul_right_comm P D total, ENNReal.ofReal_mul (mul_nonneg P0 T0)]
    simp only [Y, mul_assoc]
    rfl
  have hx (ξ : E) (hne : ξ ≠ 0) : ∀ᶠ N : ℕ in atTop, aN N ξ = (m ξ : ℂ) := by
    filter_upwards [mikhlin_scale_partition (fun _ : E => (1 : ℝ)) (fun _ _ _ => rfl) a shape ξ hne] with N hN
    dsimp only [aN, J, s]
    rw [← Finset.sum_mul]
    change (∑ j ∈ Finset.range (N+N), a (bandFactor N j • ξ)) * (m ξ : ℂ) = _
    rw [hN, Complex.ofReal_one, one_mul]
  have conv (x : E) : Tendsto (fun N => wN N x) atTop (𝓝 (W x)) := by
    let F := SchwartzMap.fourierTransformCLM ℂ u
    let phase (ξ : E) := patchFourierPhase ξ x
    have phaseC : Continuous phase := by
      unfold phase patchFourierPhase Burnett.Microlocal.Overlap.baseFourierPhase
      fun_prop
    dsimp only [wN,W]
    simp_rw [normalized_complex_fourier_action_integral]
    refine tendsto_integral_of_dominated_convergence (fun ξ => (2 * D) * ‖F ξ‖)
      (fun N => (phaseC.mul ((mNC N).mul F.continuous)).aestronglyMeasurable)
      (F.integrable.norm.const_mul _) (fun N => Eventually.of_forall fun ξ => ?_) ?_
    · change ‖phase ξ * (aN N ξ * F ξ)‖ ≤ _
      simp only [phase, norm_mul, patch_fourier_phase_norm, one_mul]
      exact mul_le_mul_of_nonneg_right (mNB N ξ) (norm_nonneg _)
    · filter_upwards [(Set.countable_singleton (0 : E)).ae_notMem volume] with ξ hξ
      have nξ : ξ ≠ 0 := fun h => hξ (by simp only [Set.mem_singleton_iff, h])
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hx ξ nξ] with N h
      simp only [h]
  have limit := (Lp.eLpNorm_lim_le_liminf_eLpNorm (p := p)
    (fun N => (nBounds N).1.1) _ (Eventually.of_forall conv)).trans
    ((liminf_le_liminf (Eventually.of_forall (fun N => (nBounds N).2))).trans_eq (liminf_const _))
  have Wcont : Continuous W := normalized_complex_fourier_action_continuous _ (Complex.continuous_ofReal.comp hm.continuous).measurable
    (max D ‖m 0‖) (fun ξ => by
      change ‖(m ξ : ℂ)‖ ≤ max D ‖m 0‖
      rw [Complex.norm_real]
      by_cases hξ : ξ = 0
      · rw [hξ]; exact le_max_right _ _
      · exact (hMass ξ hξ).trans (le_max_left _ _)) u
  exact ⟨⟨Wcont.aestronglyMeasurable, limit.trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top Kfin ENNReal.ofReal_lt_top) (u.memLp p volume).eLpNorm_lt_top)⟩, limit⟩

end Burnett.A03
