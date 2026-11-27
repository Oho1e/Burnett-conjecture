import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalSymbolMixedJets

set_option autoImplicit false
set_option maxHeartbeats 7500000

noncomputable section

namespace Burnett.V03

open Function Filter Metric Set Burnett.A03 Burnett.A02.FrequencySplit
open scoped ContDiff BigOperators Topology

/-- The original homogeneous symbol has uniform mixed spatial and angular
derivatives on a fixed annulus. Read them from its actual smooth infrared
regularization by dilating frequencies into the unchanged region. -/
theorem compact_homogeneous_symbol_mixed_jet_budget
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a β : E → E → V) (K : Set E) (hK : IsCompact K)
    (hβ : ContDiff ℝ ∞ (uncurry β)) (hOff : ∀ x ∉ K, ∀ ξ, β x ξ = 0)
    (hMatch : ∀ x ξ, 1 < ‖ξ‖ → β x ξ = a x ξ)
    (hHom : ∀ x (t : ℝ), 0 < t → ∀ ξ, a x (t • ξ) = t • a x ξ) :
    ∃ U : Set E, IsOpen U ∧ sphere (0 : E) 1 ⊆ U ∧
      (∀ x, ContDiffOn ℝ ∞ (a x) U) ∧
      (∀ ξ, ContDiff ℝ ∞ (fun x => a x ξ)) ∧
      (∀ r : ℕ, ∀ ξ ∈ U, ContDiff ℝ ∞ (fun x => iteratedFDeriv ℝ r (a x) ξ)) ∧
      ∀ H N : ℕ, ∃ D : ℝ, 0 ≤ D ∧
        ∀ r ≤ H, ∀ j ≤ N, ∀ x ξ, ξ ∈ U →
          ‖iteratedFDeriv ℝ j (fun y => iteratedFDeriv ℝ r (a y) ξ) x‖ ≤ D := by
  let U := {ξ : E | 1 / 2 < ‖ξ‖ ∧ ‖ξ‖ < 2}
  let F (x ξ : E) := (3 : ℝ)⁻¹ • β x ((3 : ℝ) • ξ)
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hSphere : sphere (0 : E) 1 ⊆ U := by
    intro ξ hξ
    have hNorm : ‖ξ‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hξ
    change 1 / 2 < ‖ξ‖ ∧ ‖ξ‖ < 2
    rw [hNorm]
    norm_num
  have hF : ContDiff ℝ ∞ (uncurry F) := contDiff_const.smul
    (hβ.comp (contDiff_fst.prodMk (contDiff_const.smul contDiff_snd)))
  have hSame (x ξ : E) (hξ : ξ ∈ U) : a x ξ = F x ξ := by
    have hLarge : 1 < ‖(3 : ℝ) • ξ‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      have hm : 1 / 2 < ‖ξ‖ := hξ.1
      linarith
    unfold F
    rw [hMatch _ _ hLarge, hHom x 3 (by norm_num), smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  have hFreq (x : E) : ContDiff ℝ ∞ (F x) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hSameD (r : ℕ) (x ξ : E) (hξ : ξ ∈ U) :
      iteratedFDeriv ℝ r (a x) ξ = iteratedFDeriv ℝ r (F x) ξ := by
    have heq : a x =ᶠ[𝓝 ξ] F x := by
      have hNear : ∀ᶠ η in 𝓝 ξ, η ∈ U := hU.mem_nhds hξ
      filter_upwards [hNear] with η hη
      exact hSame x η hη
    exact (heq.iteratedFDeriv ℝ r).eq_of_nhds
  have hBase (ξ : E) : ContDiff ℝ ∞ (fun x => a x ξ) := by
    by_cases h0 : ξ = 0
    · subst ξ
      have hZ (x : E) : a x 0 = 0 := by
        have hh := hHom x 2 (by norm_num) 0
        rw [smul_zero, two_smul] at hh
        apply add_left_cancel (a := a x 0)
        exact hh.symm.trans (add_zero _).symm
      simp only [hZ]
      exact contDiff_const
    · let r := ‖ξ‖
      let η := r⁻¹ • ξ
      have hr : 0 < r := norm_pos_iff.mpr h0
      have hη : η ∈ sphere (0 : E) 1 := by
        change dist η 0 = 1
        rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
        exact inv_mul_cancel₀ hr.ne'
      have hξ : r • η = ξ := by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      have hRewrite (x : E) : a x ξ = r • F x η := by
        rw [← hSame x η (hSphere hη), ← hHom x r hr, hξ]
      simp only [hRewrite]
      exact contDiff_const.smul (hF.comp (contDiff_id.prodMk contDiff_const))
  let G (r : ℕ) (x ξ : E) := iteratedFDeriv ℝ r (F x) ξ
  have hG (r : ℕ) : ContDiff ℝ ∞ (uncurry (G r)) := smooth_right_slice_iterated_fderiv F hF r
  have hGS (r : ℕ) (ξ : E) : ContDiff ℝ ∞ (fun x => G r x ξ) :=
    (hG r).comp (contDiff_id.prodMk contDiff_const)
  refine ⟨U, hU, hSphere, (fun x => (hFreq x).contDiffOn.congr (fun ξ hξ => hSame x ξ hξ)),
    hBase, ?_, ?_⟩
  · intro r ξ hξ
    simpa only [G, ← hSameD r _ ξ hξ] using hGS r ξ
  · intro H N
    let Q := K ×ˢ closedBall (0 : E) 2
    have hQ : IsCompact Q := hK.prod (isCompact_closedBall _ _)
    have jet (r j : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ x ξ, ξ ∈ U →
        ‖iteratedFDeriv ℝ j (fun y => G r y ξ) x‖ ≤ D := by
      let Gswap (ξ x : E) := G r x ξ
      let D₀ (p : E × E) := ‖iteratedFDeriv ℝ j (fun y => G r y p.2) p.1‖
      have hGSmooth : ContDiff ℝ ∞ (uncurry Gswap) := (hG r).comp (contDiff_snd.prodMk contDiff_fst)
      have hDSmooth : Continuous D₀ :=
        ((smooth_right_slice_iterated_fderiv Gswap hGSmooth j).continuous.comp
          (continuous_snd.prodMk continuous_fst)).norm
      obtain ⟨D, hD⟩ := hQ.bddAbove_image hDSmooth.continuousOn
      refine ⟨max D 0, le_max_right _ _, fun x ξ hξ => ?_⟩
      by_cases hx : x ∈ K
      · have hξQ : ξ ∈ closedBall (0 : E) 2 := by
          rw [mem_closedBall, dist_zero_right]
          exact hξ.2.le
        exact (hD (mem_image_of_mem D₀ (show (x, ξ) ∈ Q from ⟨hx, hξQ⟩))).trans (le_max_left _ _)
      · have hZ : (fun y => G r y ξ) =ᶠ[𝓝 x] 0 := by
          filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
          have hZero : F y = 0 := by
            funext v
            simp only [F, hOff y hy, smul_zero, Pi.zero_apply]
          change iteratedFDeriv ℝ r (F y) ξ = 0
          rw [hZero]
          change iteratedFDeriv ℝ r (fun _ : E => (0 : V)) ξ = 0
          rw [iteratedFDeriv_zero_fun, Pi.zero_apply]
        have hJet := (hZ.iteratedFDeriv ℝ j).eq_of_nhds
        change iteratedFDeriv ℝ j (fun y => G r y ξ) x =
          iteratedFDeriv ℝ j (fun _ : E => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin r => E) V)) x at hJet
        rw [hJet, iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
        exact le_max_right _ _
    choose D hD hBd using fun (p : Fin (H + 1) × Fin (N + 1)) => jet p.1.val p.2.val
    refine ⟨∑ p, D p, Finset.sum_nonneg (fun p _ => hD p), ?_⟩
    intro r hr j hj x ξ hξ
    let p : Fin (H + 1) × Fin (N + 1) := (⟨r, Nat.lt_succ_of_le hr⟩, ⟨j, Nat.lt_succ_of_le hj⟩)
    have hSameSlice : (fun y => iteratedFDeriv ℝ r (a y) ξ) = fun y => G r y ξ :=
      funext fun y => hSameD r y ξ hξ
    rw [hSameSlice]
    exact (hBd p x ξ hξ).trans (Finset.single_le_sum (fun q _ => hD q) (Finset.mem_univ p))

/-- Dilation of the same smooth cutoff recovers the frequency jets at
each nonzero frequency, jointly with the base point. -/
theorem compact_homogeneous_symbol_punctured_jets
    (a β : E → E → ℂ) (hβ : ContDiff ℝ ∞ (uncurry β))
    (hMatch : ∀ x ξ, 1 < ‖ξ‖ → β x ξ = a x ξ)
    (hHom : ∀ x (t : ℝ), 0 < t → ∀ ξ, a x (t • ξ) = t • a x ξ) :
    CompactBaseFrequencyJets a {ξ | ξ ≠ 0} := by
  have model (ξ : E) (hξ : ξ ≠ 0) : ∃ (F : E → E → ℂ) (U : Set E),
      ContDiff ℝ ∞ (uncurry F) ∧ IsOpen U ∧ ξ ∈ U ∧
        ∀ x η, η ∈ U → a x η = F x η := by
    let t := 2 / ‖ξ‖
    let U := {η : E | ‖ξ‖ / 2 < ‖η‖}
    let F (x η : E) := t⁻¹ • β x (t • η)
    have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have ht : 0 < t := div_pos (by norm_num) hξ0
    refine ⟨F, U, contDiff_const.smul
      (hβ.comp (contDiff_fst.prodMk (contDiff_const.smul contDiff_snd))),
      isOpen_lt continuous_const continuous_norm, ?_, ?_⟩
    · change ‖ξ‖ / 2 < ‖ξ‖
      linarith
    intro x η hη
    have hLarge : 1 < ‖t • η‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht.le]
      change 1 < (2 / ‖ξ‖) * ‖η‖
      rw [div_mul_eq_mul_div, lt_div_iff₀ hξ0, one_mul]
      change ‖ξ‖ / 2 < ‖η‖ at hη
      linarith
    unfold F
    rw [hMatch _ _ hLarge, hHom x t ht, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  have localEq (F : E → E → ℂ) (U : Set E) (hU : IsOpen U)
      (hSame : ∀ x η, η ∈ U → a x η = F x η) (x ξ : E) (hξ : ξ ∈ U) :
      a x =ᶠ[𝓝 ξ] F x := by
    have hNear : ∀ᶠ η in 𝓝 ξ, η ∈ U := hU.mem_nhds hξ
    filter_upwards [hNear] with η hη
    exact hSame x η hη
  refine ⟨?_, ?_, ?_⟩
  · intro x ξ hξ
    obtain ⟨F, U, hF, hU, hMem, hSame⟩ := model ξ hξ
    have hx : ContDiff ℝ ∞ (F x) := hF.comp (contDiff_const.prodMk contDiff_id)
    exact (hx.contDiffAt.congr_of_eventuallyEq (localEq F U hU hSame x ξ hMem)).contDiffWithinAt
  · intro r ξ hξ
    obtain ⟨F, U, hF, hU, hMem, hSame⟩ := model ξ hξ
    have eq : (fun x => iteratedFDeriv ℝ r (a x) ξ) = fun x => iteratedFDeriv ℝ r (F x) ξ :=
      funext fun x => ((localEq F U hU hSame x ξ hMem).iteratedFDeriv ℝ r).eq_of_nhds
    rw [eq]
    exact (smooth_right_slice_iterated_fderiv F hF r).comp (contDiff_id.prodMk contDiff_const)
  · intro r p hp
    obtain ⟨F, U, hF, hU, hMem, hSame⟩ := model p.2 hp.2
    have hNear : ∀ᶠ q : E × E in 𝓝 p, q.2 ∈ U := (hU.preimage continuous_snd).mem_nhds hMem
    have eq : (fun q : E × E => iteratedFDeriv ℝ r (a q.1) q.2) =ᶠ[𝓝 p]
        (fun q : E × E => iteratedFDeriv ℝ r (F q.1) q.2) := by
      filter_upwards [hNear] with q hq
      exact ((localEq F U hU hSame q.1 q.2 hq).iteratedFDeriv ℝ r).eq_of_nhds
    exact ((smooth_right_slice_iterated_fderiv F hF r).continuous.continuousAt.congr_of_eventuallyEq
      eq).continuousWithinAt

end Burnett.V03
