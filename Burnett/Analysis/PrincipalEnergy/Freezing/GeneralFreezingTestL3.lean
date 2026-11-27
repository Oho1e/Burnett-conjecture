import Burnett.Analysis.PrincipalEnergy.Freezing.CompactScalarWeylTest
import Burnett.Analysis.PrincipalEnergy.Freezing.SummedFourierAction
import Burnett.Analysis.PrincipalEnergy.Freezing.RadianLeftFullSymbol

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 5000

noncomputable section

namespace Burnett.A03.CompactScalarWeylTest

open Filter Function MeasureTheory Metric Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal Topology FourierTransform

open private window_support from Burnett.Analysis.PrincipalEnergy.Freezing.CompactScalarWeylTest

variable (test : CompactScalarWeylTest)

private def leftPrincipalAction (a : E → E → ℝ) : SchwartzMap E ℂ → E → ℂ :=
  radianLeftQuantization (fun x ξ => (a x ξ : ℂ))

private theorem exists_full_left_gap_W13 : ∃ K : ℝ≥0∞, K < ⊤ ∧
    SchwartzOrderZeroJetBound (fun u => test.action u - leftPrincipalAction test.principal u) K K := by
  obtain ⟨hA, M, hM, principal⟩ := test.principal_symbol_data
  obtain ⟨N, hN, lower⟩ := test.lowerSeminorm
  let P := test.baseWindow.rOut + 1
  let R := test.baseWindow.rIn
  let ρ := test.baseWindow
  have hP : 0 < P := by dsimp [P]; linarith [ρ.rIn_pos, ρ.rIn_lt_rOut]
  have hRP : R < P := by dsimp [R, P]; linarith [ρ.rIn_lt_rOut]
  have hOne : ∀ x ∈ closedBall (0 : E) R, ρ x = 1 := fun x hx => ρ.one_of_mem_closedBall hx
  have hS : tsupport (ρ : E → ℝ) ⊆ ball (0 : E) P := window_support test
  let Q := compactBaseFixedInfraredWeyl P ρ ρ.contDiff hS test.infraredCutoff test.principal
  let W := compactBaseModeQuantization P ρ ρ.contDiff hS (1 / 2) test.lower
  let S := compactKernelAction test.kernel
  obtain ⟨A, hA, gap⟩ := exists_compact_fixed_principal_weyl_left_gap_W13 P R hP hRP ρ ρ.contDiff
    hS hOne test.principal test.principalSupport hA test.principalHomogeneous M hM principal
    test.infraredCutoff test.infraredReal test.infrared_plateau
  obtain ⟨D, hD, mode⟩ := exists_compact_base_order_zero_mode_action_W13 P R hP hRP.le ρ ρ.contDiff
    hS test.lower test.lowerSupport test.lowerFrequencyJets N hN lower
  obtain ⟨K, hK, kernel⟩ := exists_compact_kernel_order_zero_jet_bound test.kernel test.kernelRadius
    test.kernelSmooth test.kernelSupport
  have gap' : SchwartzOrderZeroJetBound (fun u => Q u - leftPrincipalAction test.principal u) A A := gap
  have mode' : SchwartzOrderZeroJetBound W D D := mode (1 / 2)
  have eq : (fun u => test.action u - leftPrincipalAction test.principal u) =
      fun u => ((Q u - leftPrincipalAction test.principal u) + W u) + S u := by
    funext u x
    change Q u x + W u x + S u x - leftPrincipalAction test.principal u x = _
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [eq]
  exact ⟨A + D + K, ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hA,hD⟩,hK⟩,
    schwartz_order_zero_jet_bound_add _ _ _ _ _ _
      (schwartz_order_zero_jet_bound_add _ _ _ _ _ _ gap' mode') kernel⟩

private theorem exists_left_principal_gradient_bound_of_compact_symbol
    (P R : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (hOne : ∀ x ∈ closedBall (0 : E) R, ρ x = 1)
    (a : E → E → ℝ) (hSupport : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (hA : CompactBaseFrequencyJets (fun x ξ => (a x ξ : ℂ)) {ξ | ξ ≠ 0})
    (hHom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (M : ℝ) (hM : 0 ≤ M) (principal : CompactBaseOrderOneBudget a M)
    (continuousLeft : ∀ u, Continuous (leftPrincipalAction a u)) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ u : SchwartzMap E ℂ,
      MemLp (leftPrincipalAction a u) (ENNReal.ofReal 3) volume ∧
      eLpNorm (leftPrincipalAction a u) (ENNReal.ofReal 3) volume ≤ K * energyGradientNorm u := by
  obtain ⟨J, hJ, multiplier⟩ := radian_degree_one_gradient_sphere_bound 3 (by norm_num)
  let I := (Index → ℤ) × Fin 2
  let f (i : I) := compactBaseSpatialMode P ρ hρ hS i.1 i.2
  let b (i : I) := compactBaseRealMode P a i.1 i.2
  let D (i : I) := max 1 ((3 / spatialModeRate P)^8) * M / spatialLatticeWeight i.1 ^ 8
  obtain ⟨Ds, modes, reconstruction⟩ := compact_base_order_one_series_data P R hP hRP ρ hρ
    hS hOne a hSupport hA hHom M hM principal
  have hD (i : I) : 0 ≤ D i := (modes i).1
  have bM (i : I) : Measurable (b i) :=
    measurable_of_continuousOn_compl_singleton 0 (modes i).2.1.continuousOn
  have growth (i : I) (ξ : E) : ‖b i ξ‖ ≤ D i * (1 + ‖ξ‖) :=
    ((modes i).2.2.2.2 ξ).trans (mul_le_mul_of_nonneg_left (by linarith) (hD i))
  obtain ⟨U, hU, uniform⟩ := compact_base_spatial_mode_uniform_bound P ρ hρ hS
  let w (i : I) := U * D i
  have w0 (i : I) : 0 ≤ w i := mul_nonneg hU (hD i)
  have wsum : Summable w := Ds.mul_left U
  refine ⟨ENNReal.ofReal (∑' i, w i) * J, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ, ?_⟩
  intro u
  let p := ENNReal.ofReal 3
  let F := SchwartzMap.fourierTransformCLM ℂ u
  let W (ξ : E) := (1 + tau * ‖ξ‖) * ‖F ξ‖
  let G (i : I) (x : E) := f i x * radianAction (b i) u x
  have hTau : 0 ≤ tau := by unfold tau; positivity
  have WI : Integrable W volume := by
    have h := F.integrable.norm.add ((F.integrable_pow_mul volume 1).const_mul tau)
    apply h.congr
    filter_upwards with ξ
    change ‖F ξ‖ + tau * (‖ξ‖ ^ 1 * ‖F ξ‖) = W ξ
    rw [pow_one]
    dsimp only [W]
    ring
  have gMajor (i : I) (x : E) : ‖radianAction (b i) u x‖ ≤ D i * ∫ ξ, W ξ := by
    rw [radian_action_fourier_integral]
    refine (norm_integral_le_integral_norm _).trans ?_
    apply (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (WI.const_mul (D i)) ?_).trans_eq
      (integral_const_mul _ _)
    filter_upwards with ξ
    simp only [norm_mul, patch_fourier_phase_norm, one_mul, Complex.norm_real, W]
    have h := growth i (tau • ξ)
    rw [norm_smul, Real.norm_of_nonneg hTau] at h
    rw [show 𝓕 (u : E → ℂ) ξ = F ξ from rfl]
    exact (mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans_eq (by ring)
  have major (i : I) (x : E) : ‖G i x‖ ≤ w i * ∫ ξ, W ξ := by
    rw [show ‖G i x‖ = ‖f i x‖ * ‖radianAction (b i) u x‖ by simp [G]]
    exact (mul_le_mul (uniform i.1 i.2 x) (gMajor i x) (norm_nonneg _) hU).trans_eq (by dsimp only [w]; ring)
  have sum (x : E) : leftPrincipalAction a u x = ∑' i, G i x := by
    rw [leftPrincipalAction, radian_left_quantization_separated_sum _ f b bM D hD Ds growth
      U hU (fun i => uniform i.1 i.2) (fun x ξ _ => reconstruction x ξ)]
    apply tsum_congr
    intro i
    exact separated_radian_quantization_left _ (bM i) (slanted_radian_symbol_growth 0 _ (D i) (hD i) (growth i)) _ _ _
  have modeLp (i : I) : MemLp (G i) p volume ∧ eLpNorm (G i) p volume ≤
      ENNReal.ofReal (w i) * (J * energyGradientNorm u) := by
    obtain ⟨Lp, bound⟩ := multiplier (b i) (modes i).2.1 (modes i).2.2.1 (D i) (hD i)
      (fun n hn => (modes i).2.2.2.1 n (hn.trans (by decide))) u
    have sup : eLpNorm (f i : E → ℂ) ⊤ volume ≤ ENNReal.ofReal U := by
      rw [eLpNorm_exponent_top]
      exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall (uniform i.1 i.2))
    refine ⟨Lp.smul ((f i).memLp ⊤ volume), ?_⟩
    exact calc
      _ ≤ eLpNorm (f i : E → ℂ) ⊤ volume * eLpNorm (radianAction (b i) u) p volume :=
        eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm p Lp.aestronglyMeasurable (f i : E → ℂ)
      _ ≤ ENNReal.ofReal U * (J * ENNReal.ofReal (D i) * energyGradientNorm u) := mul_le_mul' sup bound
      _ = _ := by rw [show w i = U * D i from rfl, ENNReal.ofReal_mul hU]; ring
  obtain ⟨hMem,hBound⟩ := patch_summed_L3_bound G _ (continuousLeft u) sum w wsum w0 (∫ ξ, W ξ) major
    (J * energyGradientNorm u) (ENNReal.mul_lt_top hJ (energyGradientNorm_lt_top u)) modeLp
  exact ⟨hMem, hBound.trans_eq (by ring)⟩

/-- A compact homogeneous principal symbol and an order-zero gap give the value bound. -/
theorem exists_action_value_L3_bound_of_left_gap
    (P R : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (hOne : ∀ x ∈ closedBall (0 : E) R, ρ x = 1)
    (a : E → E → ℝ) (hSupport : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (hA : CompactBaseFrequencyJets (fun x ξ => (a x ξ : ℂ)) {ξ | ξ ≠ 0})
    (hHom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (M : ℝ) (hM : 0 ≤ M) (principal : CompactBaseOrderOneBudget a M)
    (B : SchwartzMap E ℂ → SchwartzMap E ℂ)
    (valueGap : ∃ D : ℝ≥0∞, D < ⊤ ∧
      SchwartzOrderZeroJetBound (fun u => (B u : E → ℂ) -
        radianLeftQuantization (fun x ξ => (a x ξ : ℂ)) u) D D) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ u : SchwartzMap E ℂ,
      eLpNorm (B u : E → ℂ) (ENNReal.ofReal 3) volume ≤
        K * (energyGradientNorm u + eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume) := by
  obtain ⟨D, hD, gap⟩ := valueGap
  let Q (u : SchwartzMap E ℂ) := (B u : E → ℂ) - leftPrincipalAction a u
  have left_eq (u : SchwartzMap E ℂ) : leftPrincipalAction a u = (B u : E → ℂ) - Q u := by
    dsimp only [Q]
    rw [sub_sub_cancel]
  have hContinuous (u : SchwartzMap E ℂ) : Continuous (leftPrincipalAction a u) := by
    rw [left_eq u]
    exact (B u).continuous.sub (gap u).2.2.1.continuous
  obtain ⟨K, hK, principal⟩ := exists_left_principal_gradient_bound_of_compact_symbol P R hP hRP ρ hρ hS
    hOne a hSupport hA hHom M hM principal hContinuous
  refine ⟨K + D, ENNReal.add_lt_top.mpr ⟨hK,hD⟩, fun u => ?_⟩
  let p := ENNReal.ofReal 3
  have full_eq : (B u : E → ℂ) = leftPrincipalAction a u + Q u := by
    rw [left_eq u, sub_add_cancel]
  rw [full_eq]
  calc
    _ ≤ eLpNorm (leftPrincipalAction a u) p volume + eLpNorm (Q u) p volume :=
      eLpNorm_add_le (principal u).1.aestronglyMeasurable (gap u).1.aestronglyMeasurable
        (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 3)
    _ ≤ K * energyGradientNorm u + D * eLpNorm (u : E → ℂ) p volume := add_le_add (principal u).2 (gap u).2.1
    _ ≤ (K + D) * (energyGradientNorm u + eLpNorm (u : E → ℂ) p volume) := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_right' (le_self_add) _) (mul_le_mul_right' (le_add_self) _)

/-- The actual represented test sends one spatial derivative to an L³
value, with the order-zero remainder paid by the value norm of the input. -/
theorem exists_action_value_L3_bound (B : SchwartzMap E ℂ → SchwartzMap E ℂ)
    (hB : ∀ u, (B u : E → ℂ) = test.action u) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ u : SchwartzMap E ℂ,
      eLpNorm (B u : E → ℂ) (ENNReal.ofReal 3) volume ≤
        K * (energyGradientNorm u + eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume) := by
  obtain ⟨hA, M, hM, principal⟩ := test.principal_symbol_data
  let ρ := test.baseWindow
  refine exists_action_value_L3_bound_of_left_gap (ρ.rOut + 1) ρ.rIn
    (by linarith [ρ.rIn_pos, ρ.rIn_lt_rOut]) (by linarith [ρ.rIn_lt_rOut])
    ρ ρ.contDiff (window_support test) (fun x hx => ρ.one_of_mem_closedBall hx)
    test.principal test.principalSupport hA test.principalHomogeneous M hM principal B ?_
  simpa only [hB, leftPrincipalAction] using test.exists_full_left_gap_W13

end Burnett.A03.CompactScalarWeylTest
