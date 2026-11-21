import Burnett.Analysis.PrincipalEnergy.Energy.CompactScalarMultiplier
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option maxHeartbeats 7200000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function
open scoped ContDiff Topology

private theorem isBounded_iteratedFDeriv_of_eq_one_off_compact {q : Space → ℝ}
    (hq : ContDiff ℝ ∞ q) {S : Set Space} (hS : IsCompact S)
    (hOff : ∀ x ∉ S, q x = 1) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖iteratedFDeriv ℝ n q x‖ ≤ M := by
  have hcont : Continuous (iteratedFDeriv ℝ n q) := by
    exact (hq.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).continuous_iteratedFDeriv'
  obtain ⟨C, hC⟩ := (hS.image hcont).isBounded.exists_norm_le
  refine ⟨max C 1, zero_le_one.trans (le_max_right _ _), fun x => ?_⟩
  by_cases hx : x ∈ S
  · exact (hC _ ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  · have he : q =ᶠ[𝓝 x] fun _ : Space => (1:ℝ) := by
      filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hx] with y hy
      exact hOff y hy
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ he n).eq_of_nhds]
    apply LE.le.trans _ (le_max_right C 1)
    by_cases hn : n = 0
    · subst n
      simp only [norm_iteratedFDeriv_zero, norm_one, le_refl]
    · rw [iteratedFDeriv_const_of_ne hn]
      simp

/-- A smooth positive density on a fixed chart admits a square-root extension
equal to one off the fixed outer cutoff, with uniform derivative bounds. -/
theorem exists_fixedChart_densitySqrt_extension {Ω K : Set Space}
    (hΩ : IsOpen Ω) (ρ θ : Space → ℝ) (hρ : ContDiffOn ℝ ∞ ρ Ω)
    (hpos : ∀ x ∈ Ω, 0 < ρ x) (hθ : ContDiff ℝ ∞ θ)
    (hθrange : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1) (hθcomp : HasCompactSupport θ)
    (hθsupport : tsupport θ ⊆ Ω) (hθone : ∀ x ∈ K, θ x = 1) :
    ∃ q : Space → ℝ, ContDiff ℝ ∞ q ∧ ContDiff ℝ ∞ (fun x => (q x)⁻¹) ∧
      (∀ x, 0 < q x) ∧ EqOn (fun x => (q x)^2) ρ K ∧
      (∀ x ∉ tsupport θ, q x = 1) ∧
      ∀ n : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x,
        ‖iteratedFDeriv ℝ n q x‖ ≤ M ∧ ‖iteratedFDeriv ℝ n (fun y => (q y)⁻¹) x‖ ≤ M := by
  let f (x : Space) := 1 - θ x + θ x * ρ x
  have hOff (x : Space) (hx : x ∉ tsupport θ) : f x = 1 := by
    have hzero : θ x = 0 := by by_contra h; exact hx (subset_closure h)
    simp [f, hzero]
  have hSmooth : ContDiff ℝ ∞ f := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Ω
    · exact (contDiffAt_const.sub hθ.contDiffAt).add (hθ.contDiffAt.mul (hρ.contDiffAt (hΩ.mem_nhds hx)))
    · have he : f =ᶠ[𝓝 x] fun _ : Space => (1:ℝ) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds (fun h => hx (hθsupport h))] with y hy
        exact hOff y hy
      exact contDiffAt_const.congr_of_eventuallyEq he
  have hF (x : Space) : 0 < f x := by
    by_cases hx : x ∈ tsupport θ
    · have hp := hpos x (hθsupport hx)
      have hr := hθrange x
      by_cases hz : θ x = 0
      · simp [f, hz]
      · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr hr.2) (mul_pos (lt_of_le_of_ne hr.1 (Ne.symm hz)) hp)
    · rw [hOff x hx]
      exact zero_lt_one
  let q (x : Space) := Real.sqrt (f x)
  have hq : ContDiff ℝ ∞ q := hSmooth.sqrt (fun x => (hF x).ne')
  have hQ (x : Space) : 0 < q x := Real.sqrt_pos.2 (hF x)
  have hi : ContDiff ℝ ∞ (fun x => (q x)⁻¹) := hq.inv (fun x => (hQ x).ne')
  have hEq (x : Space) (hx : x ∉ tsupport θ) : q x = 1 := by
    simp [q, hOff x hx]
  refine ⟨q, hq, hi, hQ, ?_, hEq, ?_⟩
  · intro x hx
    change (Real.sqrt (f x))^2 = ρ x
    rw [Real.sq_sqrt (hF x).le]
    simp [f, hθone x hx]
  · intro n
    obtain ⟨M, hM, bound⟩ := isBounded_iteratedFDeriv_of_eq_one_off_compact hq hθcomp hEq n
    obtain ⟨N, hN, boundInv⟩ := isBounded_iteratedFDeriv_of_eq_one_off_compact hi hθcomp
      (fun x hx => by simp [hEq x hx]) n
    exact ⟨max M N, hM.trans (le_max_left _ _), fun x =>
      ⟨(bound x).trans (le_max_left _ _), (boundInv x).trans (le_max_right _ _)⟩⟩

end Burnett.Analysis.CarlesonEmbedding
