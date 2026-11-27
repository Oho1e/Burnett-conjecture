import Burnett.Analysis.PrincipalEnergy.Freezing.ClassicalAmplitudePairingLimit
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false
set_option maxHeartbeats 4900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ComplexConjugate ContDiff ENNReal Topology

private theorem real_test_integral_eq_lebesgue_pairing
    (f : E → ℂ) (g : E → ℝ) (gc : ContDiff ℝ ∞ g) (gs : HasCompactSupport g) :
    let v := (gs.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp gc)
    (∫ x : E, g x • f x) = weylLebesguePairing f v := by
  intro v
  unfold weylLebesguePairing
  apply integral_congr_ae
  filter_upwards with x
  change (g x : ℂ) * f x = f x * conj (g x : ℂ)
  rw [Complex.conj_ofReal,mul_comm]

/-- For a given continuous compactly localized test with the usual
weak oscillatory representation, the actual test values are the left
action computed from that amplitude plus the given smoothing kernel. -/
theorem compact_radian_amplitude_test_eq_of_pairing_limit
    (A : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne A Rx Ry)
    (K : E → E → ℂ) (RK : ℝ) (Ks : ContDiff ℝ 1 (Function.uncurry K))
    (Ksupport : ∀ x y, x ∉ closedBall (0 : E) RK ∨ y ∉ closedBall (0 : E) RK → K x y = 0)
    (κ : ℕ → SchwartzMap E ℂ)
    (κB : ∀ n ξ, ‖κ n ξ‖ ≤ 1) (κlimit : ∀ ξ, Tendsto (fun n => κ n ξ) atTop (𝓝 1))
    (B : SchwartzMap E ℂ → E → ℂ) (Bc : ∀ u, Continuous (B u))
    (representation : ∀ (u v : SchwartzMap E ℂ),
      Tendsto (fun n => weylLebesguePairing (radianTwoPointCutoffAction A (κ n) u) v) atTop
        (𝓝 (weylLebesguePairing (B u - compactKernelAction K u) v))) :
    B = compactRadianAmplitudeTestAction A Rx Ry h K := by
  obtain ⟨_,_,ker⟩ := exists_compact_kernel_action_W13 K Ks RK Ksupport
  funext u
  let L := radianLeftQuantization (compactRadianReducedAmplitudeSymbol A Rx Ry h) u
  let D := B u - compactKernelAction K u
  have convergence := compact_radian_two_point_pairing_tendsto A Rx Ry h κ κB κlimit u
  have LC : Continuous L := convergence.1
  have KC : Continuous (compactKernelAction K u) := (ker u).2.2.1.continuous
  have DC : Continuous D := (Bc u).sub KC
  have pair (v : SchwartzMap E ℂ) : weylLebesguePairing L v = weylLebesguePairing D v :=
    tendsto_nhds_unique (convergence.2 v) (representation u v)
  have AE : L =ᵐ[(volume : Measure E)] D := by
    apply ae_eq_of_integral_contDiff_smul_eq (LC.locallyIntegrable (μ := volume))
      (DC.locallyIntegrable (μ := volume))
    intro g gc gs
    exact (real_test_integral_eq_lebesgue_pairing L g gc gs).trans
      ((pair _).trans (real_test_integral_eq_lebesgue_pairing D g gc gs).symm)
  have eq : L = D := (LC.ae_eq_iff_eq volume DC).mp AE
  change B u = L + compactKernelAction K u
  rw [eq]
  exact (sub_add_cancel (B u) (compactKernelAction K u)).symm

end Burnett.A03
