import Burnett.Analysis.TransportWard.Weyl.CompactPrincipalJets
import Burnett.Analysis.PrincipalEnergy.Freezing.CompactOrderOneModes

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.V03

open Filter Function Metric Set Burnett.A03 Burnett.A02.FrequencySplit
open scoped ContDiff Topology

/-- A compact base for the original symbol and the same smooth infrared
regularization produce the actual spatial-series cutoff and jet budget. -/
theorem exists_compact_principal_series_data_of_infrared
    (a : E → E → ℝ) (β : E → E → ℂ) (K : Set E) (hK : IsCompact K)
    (hβ : ContDiff ℝ ∞ (uncurry β)) (hβOff : ∀ x ∉ K, ∀ ξ, β x ξ = 0)
    (hMatch : ∀ x ξ, 1 < ‖ξ‖ → β x ξ = (a x ξ : ℂ))
    (hOff : ∀ x ∉ K, ∀ ξ, a x ξ = 0)
    (hHom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ) :
    ∃ (P R : ℝ) (ρ : ContDiffBump (0 : E)) (M : ℝ),
      0 < P ∧ R < P ∧ tsupport (ρ : E → ℝ) ⊆ ball (0 : E) P ∧
      (∀ x ∈ closedBall (0 : E) R, ρ x = 1) ∧
      (∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0) ∧
      CompactBaseFrequencyJets (fun x ξ => (a x ξ : ℂ)) {ξ | ξ ≠ 0} ∧
      0 ≤ M ∧ CompactBaseOrderOneBudget a M := by
  let A (x ξ : E) := (a x ξ : ℂ)
  have hA (x : E) (t : ℝ) (ht : 0 < t) (ξ : E) :
      A x (t • ξ) = t • A x ξ := by
    simp only [A, hHom t ht x ξ, Complex.ofReal_mul, Complex.real_smul]
  have hJets := compact_homogeneous_symbol_punctured_jets A β hβ hMatch hA
  obtain ⟨U, _, hSphere, _, _, _, hMixed⟩ :=
    compact_homogeneous_symbol_mixed_jet_budget A β K hK hβ hβOff hMatch hA
  obtain ⟨M, hM, mixed⟩ := hMixed 7 8
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : E)
  let R := max R₀ 1
  let P := R + 2
  have hR : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
  have hRP : R < P := by dsimp [P]; linarith
  let ρ : ContDiffBump (0 : E) := ⟨R, R + 1, hR, by linarith⟩
  have hRK : K ⊆ closedBall (0 : E) R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  refine ⟨P, R, ρ, M, hR.trans hRP, hRP, ?_, ?_, ?_, hJets, hM, ?_⟩
  · rw [ρ.tsupport_eq]
    exact closedBall_subset_ball (by change R + 1 < R + 2; linarith)
  · intro x hx
    exact ρ.one_of_mem_closedBall hx
  · intro x ξ hx
    exact hOff x (fun h => hx (hRK h)) ξ
  · intro n hn ξ hξ x
    have near := hSphere hξ
    have hFirst := mixed n hn 0 (by omega) x ξ near
    exact ⟨by simpa only [norm_iteratedFDeriv_zero] using hFirst, mixed n hn 8 le_rfl x ξ near⟩

end Burnett.V03
