import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.MetricSpace.ProperSpace

set_option autoImplicit false
set_option maxHeartbeats 6200000

noncomputable section

namespace Burnett.Analysis

open Function Filter Set
open scoped BigOperators ContDiff Topology

variable {X E V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Keep the base directions fixed and scale only the frequency directions. -/
def frequencyDirectionScale (t : ℝ) : X × E →L[ℝ] X × E :=
  (ContinuousLinearMap.id ℝ X).prodMap (t • ContinuousLinearMap.id ℝ E)

private theorem frequencyDirectionScale_apply (t : ℝ) (p : X × E) :
    frequencyDirectionScale t p = (p.1, t • p.2) := rfl

private theorem norm_frequencyDirectionScale_le (t : ℝ) (ht : 0 ≤ t) {R : ℝ}
    (hR : 1 ≤ R) (htR : t ≤ R) :
    ‖frequencyDirectionScale (X := X) (E := E) t‖ ≤ R := by
  refine ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hR) ?_
  intro p
  rw [frequencyDirectionScale_apply, norm_prod_le_iff, norm_smul, Real.norm_of_nonneg ht]
  exact ⟨(norm_fst_le p).trans (le_mul_of_one_le_left (norm_nonneg p) hR),
    mul_le_mul htR (norm_snd_le p) (norm_nonneg _) (zero_le_one.trans hR)⟩

variable [ProperSpace E]

/-- Once the frequency is above the fixed cutoff, positive homogeneity
rescales normalized joint derivatives to a single compact shell. The
remaining derivatives are bounded on the compact low-frequency set. -/
theorem exists_scaled_joint_orderOne_of_compactBase_of_homogeneousTail
    (F : X × E → V) (hF : ContDiff ℝ ∞ F) {K : Set X} (hK : IsCompact K)
    (hSupp : ∀ x ∉ K, ∀ ξ : E, F (x, ξ) = 0)
    (hHom : ∀ (x : X) (ξ : E), 1 < ‖ξ‖ → ∀ t : ℝ, 1 ≤ t → F (x, t • ξ) = t • F (x, ξ))
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : X × E,
      ‖(iteratedFDeriv ℝ k F p).compContinuousLinearMap
        (fun _ => frequencyDirectionScale (1 + ‖p.2‖))‖ ≤ C * (1 + ‖p.2‖) := by
  have hk : (k : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
  have hD : Continuous (fun p => ‖iteratedFDeriv ℝ k F p‖) := (hF.continuous_iteratedFDeriv hk).norm
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_closedBall (0 : E) 2)).bddAbove_image hD.continuousOn
  let C := max B 0 * (3 : ℝ) ^ k
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hJet (p : X × E) (hp : p.1 ∈ K) (hξ : ‖p.2‖ ≤ 2) (s : ℝ) (hs : 0 ≤ s) (hs3 : s ≤ 3) :
      ‖(iteratedFDeriv ℝ k F p).compContinuousLinearMap (fun _ => frequencyDirectionScale s)‖ ≤ C := by
    have hpB : p ∈ K ×ˢ Metric.closedBall (0 : E) 2 := ⟨hp, by simpa using hξ⟩
    have hBp : ‖iteratedFDeriv ℝ k F p‖ ≤ max B 0 :=
      (hB (mem_image_of_mem _ hpB)).trans (le_max_left _ _)
    have hS := norm_frequencyDirectionScale_le (X := X) (E := E) s hs (by norm_num) hs3
    calc
      _ ≤ ‖iteratedFDeriv ℝ k F p‖ * ‖frequencyDirectionScale (X := X) (E := E) s‖ ^ k := by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          (iteratedFDeriv ℝ k F p).norm_compContinuousLinearMap_le (fun _ => frequencyDirectionScale s)
      _ ≤ C := mul_le_mul hBp (pow_le_pow_left₀ (norm_nonneg _) hS k) (by positivity) (le_max_right _ _)
  refine ⟨C, hC, fun p => ?_⟩
  by_cases hp : p.1 ∈ K
  · by_cases hFreq : ‖p.2‖ ≤ 2
    · exact (hJet p hp hFreq _ (by positivity) (by linarith)).trans
        (le_mul_of_one_le_right hC (le_add_of_nonneg_right (norm_nonneg _)))
    · let t := ‖p.2‖ / 2
      let q : X × E := (p.1, t⁻¹ • p.2)
      let w := 1 + ‖p.2‖
      have ht : 1 ≤ t := by dsimp only [t]; linarith [lt_of_not_ge hFreq]
      have ht0 : 0 < t := zero_lt_one.trans_le ht
      have hqN : ‖q.2‖ = 2 := by
        change ‖t⁻¹ • p.2‖ = 2
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht0.le)]
        have h := inv_mul_cancel₀ ht0.ne'
        have htEq : ‖p.2‖ = 2 * t := by dsimp only [t]; ring
        rw [htEq]
        calc
          t⁻¹ * (2 * t) = 2 * (t⁻¹ * t) := by ring
          _ = 2 := by rw [h, mul_one]
      have hqp : frequencyDirectionScale t q = p := by
        rw [frequencyDirectionScale_apply]
        change (p.1, t • (t⁻¹ • p.2)) = p
        rw [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
      have hOp : IsOpen {z : X × E | 1 < ‖z.2‖} :=
        isOpen_lt continuous_const continuous_snd.norm
      have hEg : F ∘ frequencyDirectionScale t =ᶠ[𝓝 q] t • F := by
        filter_upwards [hOp.mem_nhds (show 1 < ‖q.2‖ by rw [hqN]; norm_num)] with z hz
        exact hHom z.1 z.2 hz t ht
      have hDeriv :
          (iteratedFDeriv ℝ k F p).compContinuousLinearMap (fun _ => frequencyDirectionScale t) =
            t • iteratedFDeriv ℝ k F q := by
        have h := (hEg.iteratedFDeriv ℝ k).self_of_nhds
        rw [(frequencyDirectionScale t).iteratedFDeriv_comp_right hF q hk, hqp,
          iteratedFDeriv_const_smul_apply ((hF.of_le hk).contDiffAt)] at h
        exact h
      have hNormW : 0 ≤ w / t := div_nonneg (by dsimp only [w]; positivity) ht0.le
      have hWt : w / t ≤ 3 := by
        apply (div_le_iff₀ ht0).mpr
        dsimp only [w]
        have htEq : ‖p.2‖ = 2 * t := by dsimp only [t]; ring
        linarith
      have hCompose :
          (iteratedFDeriv ℝ k F p).compContinuousLinearMap (fun _ => frequencyDirectionScale w) =
            t • (iteratedFDeriv ℝ k F q).compContinuousLinearMap
              (fun _ => frequencyDirectionScale (w / t)) := by
        apply ContinuousMultilinearMap.ext
        intro v
        have h := DFunLike.congr_fun hDeriv (fun j => frequencyDirectionScale (w / t) (v j))
        have hMaps (z : X × E) :
            frequencyDirectionScale t (frequencyDirectionScale (w / t) z) = frequencyDirectionScale w z := by
          simp only [frequencyDirectionScale_apply, smul_smul]
          rw [mul_comm t, div_mul_cancel₀ _ ht0.ne']
        simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.smul_apply, hMaps] using h
      change ‖(iteratedFDeriv ℝ k F p).compContinuousLinearMap (fun _ => frequencyDirectionScale w)‖ ≤ C * w
      rw [hCompose, norm_smul, Real.norm_of_nonneg ht0.le]
      have hqt : t ≤ w := by dsimp only [t, w]; linarith [norm_nonneg p.2]
      exact (mul_le_mul_of_nonneg_left (hJet q hp hqN.le _ hNormW hWt) ht0.le).trans
        ((mul_comm t C).le.trans (mul_le_mul_of_nonneg_left hqt hC))
  · have hN : Prod.fst ⁻¹' Kᶜ ∈ 𝓝 p := (hK.isClosed.isOpen_compl.preimage continuous_fst).mem_nhds hp
    have hEq : F =ᶠ[𝓝 p] fun _ => (0 : V) := by
      filter_upwards [hN] with z hz
      exact hSupp z.1 hz z.2
    rw [(hEq.iteratedFDeriv ℝ k).self_of_nhds, iteratedFDeriv_zero_fun, Pi.zero_apply]
    have hz : (0 : ContinuousMultilinearMap ℝ (fun _ : Fin k => X × E) V).compContinuousLinearMap
        (fun _ => frequencyDirectionScale (1 + ‖p.2‖)) = 0 := by
      apply ContinuousMultilinearMap.ext
      intro _
      rfl
    rw [hz, norm_zero]
    positivity

end Burnett.Analysis
