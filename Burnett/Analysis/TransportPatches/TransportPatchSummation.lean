import Burnett.Analysis.TransportPatches.TransportNumericalLimit

/-! Taking the sequence limit in the full residual after fixed-parameter
patch summation. The individual signed patch terms need only upper bounds. -/
set_option autoImplicit false
noncomputable section

namespace Burnett.C04

open Filter Set
open scoped Topology BigOperators

/-- The bracket in the two correction budgets at paper lines 2918–2934. -/
def correctionEnvelope (ℓ e : ℝ) : ℝ :=
  e * (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e) * (1 + e / ℓ) +
    (ℓ + 2 * e) * (1 + e / ℓ)^3

/-- Freeze the localization scale before taking the sequence limit. -/
theorem tendsto_correctionEnvelope (ℓ : ℝ) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) : Tendsto (fun n => correctionEnvelope ℓ (e n)) atTop (𝓝 ℓ) := by
  have hC : Continuous (correctionEnvelope ℓ) := by
    unfold correctionEnvelope
    fun_prop
  simpa [correctionEnvelope] using (hC.continuousAt (x := 0)).tendsto.comp he

/-- Fixed-parameter sequence limit in the total signed residual. This
keeps the five patch contributions and the vanishing localization error
separate. The estimates for the actual near, replacement, phase, freezing,
and correction terms are the analytic inputs. -/
theorem fixed_patch_summed_residual_bound {J : Type*} [Fintype J]
    (near replacement phase freezing correction : ℕ → J → ℝ)
    (residual error e : ℕ → ℝ) (I ℓ W A R P F C : ℝ) (volume : J → ℝ)
    (hCoeff : 0 ≤ A + R + P + F + C * ℓ) (hVolume : (∑ j, volume j) ≤ W)
    (hIdentity : ∀ n, residual n = error n +
      ∑ j, (near n j + replacement n j + phase n j + freezing n j + correction n j))
    (hResidual : Tendsto residual atTop (𝓝 (4 * I)))
    (hError : Tendsto error atTop (𝓝 0)) (hE : Tendsto e atTop (𝓝 0))
    (hNear : ∀ j ε, 0 < ε → ∀ᶠ n in atTop, |near n j| ≤ A * volume j + ε)
    (hReplacement : ∀ j ε, 0 < ε → ∀ᶠ n in atTop,
      |replacement n j| ≤ R * volume j + ε)
    (hPhase : ∀ j ε, 0 < ε → ∀ᶠ n in atTop, |phase n j| ≤ P * volume j + ε)
    (hFreezing : ∀ j ε, 0 < ε → ∀ᶠ n in atTop, |freezing n j| ≤ F * volume j + ε)
    (hCorrection : ∀ j, ∀ᶠ n in atTop,
      |correction n j| ≤ C * volume j * correctionEnvelope ℓ (e n)) :
    |4 * I| ≤ (A + R + P + F + C * ℓ) * W := by
  classical
  let L := A + R + P + F + C * ℓ
  let K := ((Fintype.card J : ℝ) * 5 + 1)
  have hApprox (ε : ℝ) (hε : 0 < ε) : |4 * I| ≤ L * (∑ j, volume j) + K * ε := by
    have hSmall := (tendsto_order.1 hError.abs).2 ε (by simpa using hε)
    have hPatch : ∀ᶠ n in atTop, ∀ j,
        |near n j + replacement n j + phase n j + freezing n j + correction n j| ≤
          L * volume j + 5 * ε := by
      refine eventually_all.2 fun j => ?_
      have hLimit := (tendsto_correctionEnvelope ℓ e hE).const_mul (C * volume j)
      have hEnv := (tendsto_order.1 hLimit).2 (C * volume j * ℓ + ε) (by linarith)
      filter_upwards [hNear j ε hε, hReplacement j ε hε, hPhase j ε hε,
        hFreezing j ε hε, hCorrection j, hEnv] with n hA hR hP hF hC hB
      have hTriangle := abs_add_le (near n j + replacement n j + phase n j + freezing n j)
        (correction n j)
      have hTriangle₄ := abs_add_le (near n j + replacement n j + phase n j) (freezing n j)
      have hTriangle₃ := abs_add_le (near n j + replacement n j) (phase n j)
      have hTriangle₂ := abs_add_le (near n j) (replacement n j)
      have hCoeffExpand : L * volume j =
          A * volume j + R * volume j + P * volume j + F * volume j + C * volume j * ℓ := by
        dsimp [L]
        ring
      change C * volume j * correctionEnvelope ℓ (e n) < C * volume j * ℓ + ε at hB
      rw [hCoeffExpand]
      linarith
    apply le_of_tendsto_of_tendsto hResidual.abs tendsto_const_nhds
    filter_upwards [hSmall, hPatch] with n hSmallN hPatchN
    rw [hIdentity n]
    calc
      _ ≤ |error n| + ∑ j,
          |near n j + replacement n j + phase n j + freezing n j + correction n j| :=
        (abs_add_le _ _).trans (add_le_add_left (Finset.abs_sum_le_sum_abs _ _) _)
      _ ≤ ε + ∑ j, (L * volume j + 5 * ε) :=
        add_le_add hSmallN.le (Finset.sum_le_sum fun j _ => hPatchN j)
      _ = L * (∑ j, volume j) + K * ε := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [K]
        ring
  have hFixed : |4 * I| ≤ L * (∑ j, volume j) := by
    have hCont : Continuous (fun ε : ℝ => L * (∑ j, volume j) + K * ε) := by fun_prop
    have hT : Tendsto (fun ε : ℝ => L * (∑ j, volume j) + K * ε)
        (𝓝[>] 0) (𝓝 (L * (∑ j, volume j))) := by
      simpa only [mul_zero, add_zero] using
        (hCont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto hT
    filter_upwards [eventually_mem_nhdsWithin (s := Ioi (0 : ℝ))] with ε hε
    exact hApprox ε hε
  exact hFixed.trans (mul_le_mul_of_nonneg_left hVolume hCoeff)

end Burnett.C04
