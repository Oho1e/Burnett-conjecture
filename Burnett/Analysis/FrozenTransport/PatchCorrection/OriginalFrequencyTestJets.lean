import Burnett.Analysis.FrozenTransport.PatchCorrection.UniformAngularJets

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.V11

open Set Metric
open Burnett.A02.FrequencySplit (E Joint)
open scoped ContDiff BigOperators
open private continuousOn_secondPartialJet from Burnett.Analysis.FrozenTransport.PatchCorrection.UniformAngularJets

/-- Joint smoothness of the original local test gives a single frequency-jet
bound on the unit sphere for every center in the compact receiving window. -/
theorem exists_uniform_originalFrequencyTest_jets
    (U K : Set E) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a (U ×ˢ {ξ : E | ξ ≠ 0})) (N : ℕ) :
    ∃ D₀ : ℝ, 0 ≤ D₀ ∧ ∀ x ∈ K, ∀ n ≤ N, ∀ ξ ∈ sphere (0 : E) 1,
      ‖iteratedFDeriv ℝ n (fun v => a (x, v)) ξ‖ ≤ D₀ := by
  classical
  let O := U ×ˢ {ξ : E | ξ ≠ 0}
  let Q := K ×ˢ sphere (0 : E) 1
  let F (p : Joint) := (a p : ℂ)
  have hO : IsOpen O := hU.prod (isOpen_ne_fun continuous_id continuous_const)
  have hQ : IsCompact Q := hK.prod (isCompact_sphere _ _)
  have hSub : Q ⊆ O := by
    intro p hp
    have hNorm : ‖p.2‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hp.2
    refine ⟨hKU hp.1, ?_⟩
    intro hzero
    rw [hzero, norm_zero] at hNorm
    exact zero_ne_one hNorm
  have hF : ContDiffOn ℝ ∞ F O := Complex.ofRealCLM.contDiff.comp_contDiffOn ha
  have bound (n : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ K, ∀ ξ ∈ sphere (0 : E) 1,
      ‖iteratedFDeriv ℝ n (fun v => a (x, v)) ξ‖ ≤ D := by
    let jets (p : Joint) := ‖iteratedFDeriv ℝ n (fun v => F (p.1, v)) p.2‖
    have hJets : ContinuousOn jets Q := (continuousOn_secondPartialJet hO hF n).norm.mono hSub
    obtain ⟨D, hD⟩ := hQ.bddAbove_image hJets
    refine ⟨max D 0, le_max_right _ _, ?_⟩
    intro x hx ξ hξ
    have hmem : (x, ξ) ∈ Q := ⟨hx, hξ⟩
    have hSlice : ContDiff ℝ ∞ (fun v : E => (x, v)) := contDiff_const.prodMk contDiff_id
    have hLocal : ContDiffAt ℝ ∞ (fun v : E => a (x, v)) ξ :=
      (ha.contDiffAt (hO.mem_nhds (hSub hmem))).comp ξ hSlice.contDiffAt
    have hn : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have eq : jets (x, ξ) = ‖iteratedFDeriv ℝ n (fun v => a (x, v)) ξ‖ :=
      Complex.ofRealLI.norm_iteratedFDeriv_comp_left hLocal hn
    rw [← eq]
    exact (hD (mem_image_of_mem jets hmem)).trans (le_max_left _ _)
  choose D hD hBound using bound
  refine ⟨∑ n ∈ Finset.range (N + 1), D n, Finset.sum_nonneg (fun n _ => hD n), ?_⟩
  intro x hx n hn ξ hξ
  exact (hBound n x hx ξ hξ).trans
    (Finset.single_le_sum (fun j _ => hD j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))

end Burnett.V11
