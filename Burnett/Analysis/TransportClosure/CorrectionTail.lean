import Burnett.Analysis.TransportPatches.TransportPatchSummation
import Mathlib.Analysis.Complex.Norm

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.C04

open Filter
open scoped BigOperators Topology

/-- At fixed localization scale the residual uses one finite patch family
and one given refinement. Each literal complex correction has its original
factor of three in the signed identity, while their norms have a joint tail
bound. Taking real parts and summing the other patch bounds supplies the
inputs of the fixed-scale residual limit. -/
theorem fixed_patch_summed_residual_bound_of_actualCorrectionSum {J : Type*}
    (s : Finset J) (σ : ℕ → ℕ)
    (near replacement phase freezing : ℕ → J → ℝ) (far gauge : ℕ → J → ℂ)
    (residual error : ℕ → ℝ) (I ℓ W A R P F C : ℝ) (mass : J → ℝ)
    (hℓ : 0 < ℓ) (hOther : 0 ≤ A + R + P + F) (hC : 0 ≤ C)
    (hVolume : (∑ j ∈ s, mass j) ≤ W)
    (hIdentity : ∀ᶠ n in atTop, residual (σ n) = error (σ n) +
      ∑ j ∈ s, (near (σ n) j + replacement (σ n) j + phase (σ n) j + freezing (σ n) j +
        (3 * (far (σ n) j).re + 3 * (gauge (σ n) j).re)))
    (hResidual : Tendsto (fun n => residual (σ n)) atTop (𝓝 (4 * I)))
    (hError : Tendsto (fun n => error (σ n)) atTop (𝓝 0))
    (hNear : ∀ j ∈ s, ∀ ε > 0, ∀ᶠ n in atTop, |near (σ n) j| ≤ A * mass j + ε)
    (hReplacement : ∀ j ∈ s, ∀ ε > 0, ∀ᶠ n in atTop, |replacement (σ n) j| ≤ R * mass j + ε)
    (hPhase : ∀ j ∈ s, ∀ ε > 0, ∀ᶠ n in atTop, |phase (σ n) j| ≤ P * mass j + ε)
    (hFreezing : ∀ j ∈ s, ∀ ε > 0, ∀ᶠ n in atTop, |freezing (σ n) j| ≤ F * mass j + ε)
    (hCorrection : ∀ ε > 0, ∀ᶠ n in atTop,
      (∑ j ∈ s, (‖far (σ n) j‖ + ‖gauge (σ n) j‖)) ≤ C * ℓ * W + ε) :
    |4 * I| ≤ (A + R + P + F + 3 * C * ℓ) * W := by
  classical
  let core (n : ℕ) (j : J) := near (σ n) j + replacement (σ n) j + phase (σ n) j + freezing (σ n) j
  let correction (n : ℕ) (j : J) := 3 * (far (σ n) j).re + 3 * (gauge (σ n) j).re
  let coreSum (n : ℕ) := ∑ j ∈ s, core n j
  let correctionSum (n : ℕ) := ∑ j ∈ s, correction n j
  let total (n : ℕ) := error (σ n) + (coreSum n + correctionSum n)
  have coreTail (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n in atTop,
      |coreSum n| ≤ (A + R + P + F) * W + ε := by
    let t := ε / (4 * (s.card : ℝ) + 1)
    have hDen : 0 < 4 * (s.card : ℝ) + 1 := by positivity
    have ht : 0 < t := div_pos hε hDen
    have hCount : (s.card : ℝ) * (4 * t) ≤ ε := by
      change (s.card : ℝ) * (4 * (ε / (4 * (s.card : ℝ) + 1))) ≤ ε
      rw [← mul_assoc, ← mul_div_assoc, div_le_iff₀ hDen]
      nlinarith
    have hAll : ∀ᶠ n in atTop, ∀ j ∈ s, |core n j| ≤ (A + R + P + F) * mass j + 4 * t := by
      refine (s.eventually_all).2 fun j hj => ?_
      filter_upwards [hNear j hj t ht, hReplacement j hj t ht, hPhase j hj t ht,
        hFreezing j hj t ht] with n hN hR hP hF
      have h₁ := abs_add_le (near (σ n) j) (replacement (σ n) j)
      have h₂ := abs_add_le (near (σ n) j + replacement (σ n) j) (phase (σ n) j)
      have h₃ := abs_add_le (near (σ n) j + replacement (σ n) j + phase (σ n) j) (freezing (σ n) j)
      have hExpand : (A + R + P + F) * mass j + 4 * t =
          (A * mass j + t) + (R * mass j + t) + (P * mass j + t) + (F * mass j + t) := by ring
      rw [hExpand]
      change |near (σ n) j + replacement (σ n) j + phase (σ n) j + freezing (σ n) j| ≤ _
      linarith
    filter_upwards [hAll] with n hn
    calc
      |coreSum n| ≤ ∑ j ∈ s, |core n j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, ((A + R + P + F) * mass j + 4 * t) := Finset.sum_le_sum hn
      _ = (A + R + P + F) * (∑ j ∈ s, mass j) + (s.card : ℝ) * (4 * t) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A + R + P + F) * W + ε := add_le_add (mul_le_mul_of_nonneg_left hVolume hOther) hCount
  have correctionTail (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n in atTop,
      |correctionSum n| ≤ (3 * C * ℓ) * W + ε := by
    filter_upwards [hCorrection (ε / 3) (by positivity)] with n hn
    have entry (j : J) : |correction n j| ≤ 3 * (‖far (σ n) j‖ + ‖gauge (σ n) j‖) := by
      dsimp only [correction]
      calc
        _ ≤ |3 * (far (σ n) j).re| + |3 * (gauge (σ n) j).re| := abs_add_le _ _
        _ = 3 * (|(far (σ n) j).re| + |(gauge (σ n) j).re|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)) (by norm_num)
    calc
      |correctionSum n| ≤ ∑ j ∈ s, |correction n j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, 3 * (‖far (σ n) j‖ + ‖gauge (σ n) j‖) := Finset.sum_le_sum fun j _ => entry j
      _ = 3 * (∑ j ∈ s, (‖far (σ n) j‖ + ‖gauge (σ n) j‖)) := (Finset.mul_sum _ _ _).symm
      _ ≤ 3 * (C * ℓ * W + ε / 3) := mul_le_mul_of_nonneg_left hn (by norm_num)
      _ = (3 * C * ℓ) * W + ε := by ring
  have hTotal : Tendsto total atTop (𝓝 (4 * I)) := by
    apply hResidual.congr'
    filter_upwards [hIdentity] with n hn
    rw [hn]
    exact congrArg (fun x : ℝ => error (σ n) + x)
      (Finset.sum_add_distrib : (∑ j ∈ s, (core n j + correction n j)) = coreSum n + correctionSum n)
  have coeff : 0 ≤ A + R + P + F + 3 * C * ℓ :=
    add_nonneg hOther (mul_nonneg (mul_nonneg (by norm_num) hC) hℓ.le)
  have result := fixed_patch_summed_residual_bound
    (fun n (_ : Unit) => coreSum n) (fun n (_ : Unit) => correctionSum n)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    total (fun n => error (σ n)) (fun _ => 0)
    I ℓ W (A + R + P + F) (3 * C * ℓ) 0 0 0 (fun _ => W)
    (by simpa using coeff) (by simp) (fun n => by simp [total]) hTotal hError tendsto_const_nhds
    (fun _ ε hε => coreTail ε hε) (fun _ ε hε => correctionTail ε hε)
    (fun _ ε hε => Eventually.of_forall fun _ => by simpa using hε.le)
    (fun _ ε hε => Eventually.of_forall fun _ => by simpa using hε.le)
    (fun _ => Eventually.of_forall fun _ => by simp)
  simpa using result

end Burnett.C04
