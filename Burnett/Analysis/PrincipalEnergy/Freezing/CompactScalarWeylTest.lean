import Burnett.Analysis.PrincipalEnergy.Freezing.CompactWeylFullTestConsumer
import Burnett.Analysis.TransportWard.Weyl.CompactPrincipalJets

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 5000

noncomputable section

namespace Burnett.A03

open Filter Function MeasureTheory Metric Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.V03
open scoped ContDiff ENNReal Topology

/-- A compact coordinate Weyl representation of a scalar classical test.
The actual complete symbol consists of the fixed infrared regularization
of its homogeneous principal symbol and a smooth order-zero symbol. A fixed
compact smooth kernel represents any smoothing part of the local test. -/
structure CompactScalarWeylTest where
  baseWindow : ContDiffBump (0 : E)
  principal : E → E → ℝ
  lower : E → E → ℝ
  principalSupport : ∀ x ξ, x ∉ closedBall (0 : E) baseWindow.rIn → principal x ξ = 0
  lowerSupport : ∀ x ξ, x ∉ closedBall (0 : E) baseWindow.rIn → lower x ξ = 0
  principalOdd : ∀ x ξ, principal x (-ξ) = -principal x ξ
  principalHomogeneous : ∀ t : ℝ, 0 < t → ∀ x ξ, principal x (t • ξ) = t * principal x ξ
  infraredCutoff : SchwartzMap E ℂ
  infraredReal : ∀ ξ, ((infraredCutoff ξ).re : ℂ) = infraredCutoff ξ
  infraredLow : ∀ ξ : E, ‖ξ‖ ≤ 1 / 2 → fixedRadianProfile infraredCutoff ξ = 1
  infraredHigh : ∀ ξ : E, 1 < ‖ξ‖ → fixedRadianProfile infraredCutoff ξ = 0
  regularizedSmooth : ContDiff ℝ ∞ (uncurry (fun x ξ => fixedInfraredSymbol infraredCutoff 0 (principal x) ξ))
  lowerFrequencyJets : CompactBaseFrequencyJets (fun x ξ => (lower x ξ : ℂ)) univ
  lowerSeminorm : ∃ M : ℝ, 0 ≤ M ∧ CompactBaseOrderZeroBudget lower M
  kernel : E → E → ℂ
  kernelRadius : ℝ
  kernelSmooth : ContDiff ℝ 1 (uncurry kernel)
  kernelSupport : ∀ x y, x ∉ closedBall (0 : E) kernelRadius ∨
    y ∉ closedBall (0 : E) kernelRadius → kernel x y = 0

namespace CompactScalarWeylTest

variable (test : CompactScalarWeylTest)

/-- The smooth complete principal symbol with the same infrared convention
as the frozen test. -/
def regularizedPrincipal (x ξ : E) : ℝ := fixedInfraredSymbol test.infraredCutoff 0 (test.principal x) ξ

theorem regularizedPrincipal_support (x : E) (hx : x ∉ closedBall (0 : E) test.baseWindow.rIn) (ξ : E) :
    test.regularizedPrincipal x ξ = 0 := by
  simp [regularizedPrincipal, fixedInfraredSymbol, fixedRadianProfile, test.principalSupport x ξ hx]

theorem regularizedPrincipal_high (x ξ : E) (h : 1 < ‖ξ‖) :
    test.regularizedPrincipal x ξ = test.principal x ξ := by
  unfold regularizedPrincipal fixedInfraredSymbol
  rw [test.infraredHigh ξ h]
  simp [fixedRadianProfile]

theorem infrared_plateau : ∀ᶠ ξ in 𝓝 (0 : E), fixedRadianProfile test.infraredCutoff ξ = 1 := by
  filter_upwards [Metric.ball_mem_nhds (0 : E) (show 0 < (1 / 2 : ℝ) by norm_num)] with ξ hξ
  apply test.infraredLow
  have hDist : dist ξ (0 : E) < 1 / 2 := hξ
  simpa only [dist_zero_right] using hDist.le

private theorem window_support : tsupport (test.baseWindow : E → ℝ) ⊆ ball (0 : E) (test.baseWindow.rOut + 1) := by
  rw [test.baseWindow.tsupport_eq]
  exact closedBall_subset_ball (by linarith)

/-- The represented scalar test acts by the actual midpoint Weyl action
and its actual compact kernel, not by a boundedness certificate. -/
def action : SchwartzMap E ℂ → E → ℂ :=
  compactWeylFullTest (test.baseWindow.rOut + 1) test.baseWindow test.baseWindow.contDiff
    test.window_support test.infraredCutoff test.principal test.lower test.kernel

/-- Center freezing is applied to the principal symbol at the actual patch
center and uses the same infrared cutoff. -/
def frozenAction (c : E) : SchwartzMap E ℂ → E → ℂ := radianAction (test.regularizedPrincipal c)

theorem principal_symbol_data :
    CompactBaseFrequencyJets (fun x ξ => (test.principal x ξ : ℂ)) {ξ | ξ ≠ 0} ∧
      ∃ M : ℝ, 0 ≤ M ∧ CompactBaseOrderOneBudget test.principal M := by
  let a (x ξ : E) := (test.principal x ξ : ℂ)
  let β (x ξ : E) := (test.regularizedPrincipal x ξ : ℂ)
  have hβ : ContDiff ℝ ∞ (uncurry β) := Complex.ofRealCLM.contDiff.comp test.regularizedSmooth
  have off (x : E) (hx : x ∉ closedBall (0 : E) test.baseWindow.rIn) (ξ : E) : β x ξ = 0 := by
    simp [β, test.regularizedPrincipal_support x hx ξ]
  have matchHigh (x ξ : E) (h : 1 < ‖ξ‖) : β x ξ = a x ξ := by
    exact congrArg Complex.ofReal (test.regularizedPrincipal_high x ξ h)
  have hom (x : E) (t : ℝ) (ht : 0 < t) (ξ : E) : a x (t • ξ) = t • a x ξ := by
    simp only [a, test.principalHomogeneous t ht x ξ, Complex.ofReal_mul, Complex.real_smul]
  refine ⟨compact_homogeneous_symbol_punctured_jets a β hβ matchHigh hom, ?_⟩
  obtain ⟨U, _, sphereU, _, _, _, budget⟩ := compact_homogeneous_symbol_mixed_jet_budget
    a β (closedBall (0 : E) test.baseWindow.rIn) (isCompact_closedBall _ _) hβ off matchHigh hom
  obtain ⟨M, hM, bound⟩ := budget 7 8
  refine ⟨M, hM, fun n hn ξ hξ x => ?_⟩
  exact ⟨by simpa only [norm_iteratedFDeriv_zero] using bound n hn 0 (by decide) x ξ (sphereU hξ),
    bound n hn 8 le_rfl x ξ (sphereU hξ)⟩

/-- Bounds for the real frozen homogeneous multiplier at every center, using
only fixed derivatives of the actual regularized principal symbol. -/
theorem principal_sphere_jets :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ c : E, ContDiffOn ℝ ∞ (test.principal c) {ξ | ξ ≠ 0} ∧
      ∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n (test.principal c) ξ‖ ≤ D := by
  obtain ⟨U, _, sphereU, _, _, _, budget⟩ := compact_homogeneous_symbol_mixed_jet_budget
    test.principal test.regularizedPrincipal (closedBall (0 : E) test.baseWindow.rIn) (isCompact_closedBall _ _)
    test.regularizedSmooth
    test.regularizedPrincipal_support test.regularizedPrincipal_high
    (fun x t ht ξ => by simpa only [smul_eq_mul] using test.principalHomogeneous t ht x ξ)
  obtain ⟨D, hD, bound⟩ := budget 16 0
  refine ⟨D, hD, fun c => ⟨?_, fun n hn ξ hξ => ?_⟩⟩
  · have hp := (test.principal_symbol_data.1).frequencySmooth c
    simpa using Complex.reCLM.contDiff.comp_contDiffOn hp
  · simpa only [norm_iteratedFDeriv_zero] using bound n hn 0 le_rfl c ξ (sphereU hξ)

/-- The actual localized variable-minus-frozen Weyl test differs from its
localized left principal by a controlled order-zero action and first jet.
The constant at a fixed scale is chosen before the center. -/
theorem exists_center_uniform_order_zero_remainder
    (Θ : SchwartzMap E ℂ) (θ : E → SchwartzMap E ℂ) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hShape : ∀ c x, θ c x = Θ (ℓ⁻¹ • (x - c))) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ c : E, SchwartzOrderZeroJetBound (fun u => (-Complex.I) •
      (sandwichedScalarTest (θ c) (fun v => test.action v - test.frozenAction c v) u -
        radianLeftQuantization (localizedFrozenPrincipalSymbol test.principal c (θ c)) u)) K K := by
  obtain ⟨hA, M, hM, principal⟩ := test.principal_symbol_data
  obtain ⟨N, hN, lower⟩ := test.lowerSeminorm
  exact exists_compact_weyl_full_test_center_uniform_comparison_W13
    (test.baseWindow.rOut + 1) test.baseWindow.rIn
    (by linarith [test.baseWindow.rIn_pos, test.baseWindow.rIn_lt_rOut])
    (by linarith [test.baseWindow.rIn_lt_rOut]) test.baseWindow test.baseWindow.contDiff
    test.window_support (fun x hx => test.baseWindow.one_of_mem_closedBall hx)
    test.principal test.lower test.principalSupport test.lowerSupport hA test.lowerFrequencyJets
    test.principalHomogeneous M N hM hN principal lower
    test.infraredCutoff 0 test.infraredReal (fun ξ => by simp)
    test.infrared_plateau test.kernel test.kernelRadius test.kernelSmooth test.kernelSupport Θ θ ℓ hℓ hShape

end CompactScalarWeylTest

end Burnett.A03
