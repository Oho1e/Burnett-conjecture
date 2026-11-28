import Burnett.Analysis.TransportPatches.TransportPatchSummation

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.C04

open Filter
open scoped BigOperators Topology

/-- A common frozen-energy sum estimate and the volume-scaled freezing
error bound the limit of the retested principal integrals. -/
theorem fixed_patch_retested_limit_bound_of_frozen_tail {J : Type*}
    (s : Finset J) (principal frozen : ℕ → J → ℝ) (mass : J → ℝ) (I F W E : ℝ)
    (hF : 0 ≤ F) (hV : (∑ j ∈ s, mass j) ≤ W)
    (hPrincipal : Tendsto (fun n => ∑ j ∈ s, principal n j) atTop (𝓝 (4 * I)))
    (hFrozen : ∀ ε > 0, ∀ᶠ n in atTop, (∑ j ∈ s, |frozen n j|) ≤ E + ε)
    (hFreezing : ∀ j ∈ s, ∀ ε > 0, ∀ᶠ n in atTop,
      |principal n j - frozen n j| ≤ F * mass j + ε) :
    |4 * I| ≤ E + F * W := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let d := ε / (2 * ((s.card : ℝ) + 1))
  have hd : 0 < d := div_pos hε (by positivity)
  have hcard : (s.card : ℝ) * d ≤ ε / 2 := by
    dsimp only [d]
    have hden : (0 : ℝ) < 2 * ((s.card : ℝ) + 1) := by positivity
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith
  have hTail : ∀ᶠ n in atTop, ∀ j ∈ s, |principal n j - frozen n j| ≤ F * mass j + d :=
    s.eventually_all.mpr fun j hj => hFreezing j hj d hd
  apply le_of_tendsto hPrincipal.abs
  filter_upwards [hFrozen (ε / 2) (by positivity), hTail] with n hn he
  have hErr : (∑ j ∈ s, |principal n j - frozen n j|) ≤ F * W + ε / 2 := calc
    _ ≤ ∑ j ∈ s, (F * mass j + d) := Finset.sum_le_sum he
    _ = F * (∑ j ∈ s, mass j) + (s.card : ℝ) * d := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ F * W + ε / 2 := add_le_add (mul_le_mul_of_nonneg_left hV hF) hcard
  calc
    _ ≤ ∑ j ∈ s, |principal n j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ s, (|frozen n j| + |principal n j - frozen n j|) := by
      apply Finset.sum_le_sum
      intro j _
      have h := abs_add_le (principal n j - frozen n j) (frozen n j)
      rw [sub_add_cancel, add_comm] at h
      exact h
    _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith

/-- The shared compact volume turns the frozen and Weyl error budgets
into the chartwise two-scale estimate in the original order. -/
theorem two_scale_bound_of_retested_frozen_families {J : Type*}
    (I W Cnear F α β δ₀ : ℝ) (hF : 0 ≤ F) (hα : 0 < α) (hβ : 0 < β) (hδ₀ : 0 < δ₀)
    (hPatches : ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ R G ℓ₀ : ℝ, 0 < ℓ₀ ∧
      ∀ ℓ : ℝ, 0 < ℓ → ℓ < ℓ₀ →
        ∃ (s : Finset J) (principal frozen : ℕ → J → ℝ) (mass : J → ℝ),
          (∑ j ∈ s, mass j) ≤ W ∧
          Tendsto (fun n => ∑ j ∈ s, principal n j) atTop (𝓝 (4 * I)) ∧
          (∀ ε > 0, ∀ᶠ n in atTop, (∑ j ∈ s, |frozen n j|) ≤
            (Cnear * δ ^ β + R * ℓ ^ α + G * ℓ) * W + ε) ∧
          ∀ j ∈ s, ∀ ε > 0, ∀ᶠ n in atTop,
            |principal n j - frozen n j| ≤ (F * ℓ) * mass j + ε) :
    ∃ C α β δ₀ : ℝ, 0 < α ∧ 0 < β ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ D B ℓ₀ : ℝ, 0 < ℓ₀ ∧
        ∀ ℓ : ℝ, 0 < ℓ → ℓ < ℓ₀ → |4 * I| ≤ C * δ ^ β + D * ℓ ^ α + B * ℓ := by
  refine ⟨Cnear * W, α, β, δ₀, hα, hβ, hδ₀, ?_⟩
  intro δ hδ hδ'
  obtain ⟨R, G, ℓ₀, hℓ₀, hFixed⟩ := hPatches δ hδ hδ'
  refine ⟨R * W, (G + F) * W, ℓ₀, hℓ₀, ?_⟩
  intro ℓ hℓ hℓ'
  obtain ⟨s, principal, frozen, mass, hV, hPrincipal, hFrozen, hFreezing⟩ := hFixed ℓ hℓ hℓ'
  have h := fixed_patch_retested_limit_bound_of_frozen_tail s principal frozen mass I (F * ℓ) W
    ((Cnear * δ ^ β + R * ℓ ^ α + G * ℓ) * W)
    (mul_nonneg hF hℓ.le) hV hPrincipal hFrozen hFreezing
  convert h using 1
  ring

end Burnett.C04
