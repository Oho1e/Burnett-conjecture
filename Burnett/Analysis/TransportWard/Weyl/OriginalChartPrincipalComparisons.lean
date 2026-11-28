import Burnett.Analysis.TransportWard.Weyl.CompactPrincipalSeriesData
import Burnett.Analysis.TransportWard.Weyl.WindowedWeylLeftW13
import Burnett.Analysis.PrincipalEnergy.Freezing.AffineOriginalTestComparison
import Burnett.Analysis.PrincipalEnergy.Freezing.CutoffCommutatorOrderZero

set_option autoImplicit false
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.V03

open Filter Function MeasureTheory Metric Set Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic
open scoped ContDiff ENNReal Topology

/-- The fixed chart Weyl test supplies the actual cutoff commutator at
each patch and the uniformly centered frozen-symbol comparison. -/
theorem originalChartWeyl_cutoff_and_frozen_comparisons
    (a : E → E → ℝ) (K : Set E) (hK : IsCompact K)
    (hOff : ∀ x ∉ K, ∀ ξ, a x ξ = 0)
    (hHom : ∀ (t : ℝ), 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (cut : SchwartzMap E ℂ) (hCut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (hLow : ∀ ξ : E, ‖ξ‖ ≤ 1/2 → fixedRadianProfile cut ξ = 1)
    (hHigh : ∀ ξ : E, 1 < ‖ξ‖ → fixedRadianProfile cut ξ = 0)
    (hβ : ContDiff ℝ ∞ (uncurry (fun x ξ => (fixedInfraredSymbol cut 0 (a x) ξ : ℂ))))
    (θ : E → ℝ) (hθ : ContDiff ℝ ∞ θ) (hθS : HasCompactSupport θ) (hθK : ∀ x ∈ K, θ x = 1)
    (R : ℝ) (hAmp : CompactRadianTwoPointOrderOne
      (windowedWeylAmplitude θ (fun x ξ => (fixedInfraredSymbol cut 0 (a x) ξ : ℂ))) R R) :
    let B (u : SchwartzMap E ℂ) := firstOrderAction (windowedWeylLeftSymbol θ
      (fun x ξ => (fixedInfraredSymbol cut 0 (a x) ξ : ℂ)) R hAmp) u
    (∀ η : SchwartzMap E ℂ, ∃ C : ℝ≥0∞, C < ⊤ ∧ SchwartzOrderZeroJetBound
      (fun u x => B (energyProduct η u) x - η x * B u x) C C) ∧
    ∀ (Θ : SchwartzMap E ℂ) (η : E → SchwartzMap E ℂ) (ℓ : ℝ), 0 < ℓ →
      (∀ c x, η c x = Θ (ℓ⁻¹ • (x - c))) →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ c : E, SchwartzOrderZeroJetBound
        (fun u => (-Complex.I) •
          (sandwichedScalarTest (η c) (fun v => B v - radianAction (fixedInfraredSymbol cut 0 (a c)) v) u -
            radianLeftQuantization (localizedFrozenPrincipalSymbol a c (η c)) u)) C C := by
  intro B
  let β (x ξ : E) := (fixedInfraredSymbol cut 0 (a x) ξ : ℂ)
  have hZero (ξ : E) : fixedRadianProfile (0 : SchwartzMap E ℂ) ξ = 0 := by
    simp only [fixedRadianProfile, SchwartzMap.zero_apply, Complex.zero_re]
  have hβOff (x : E) (hx : x ∉ K) (ξ : E) : β x ξ = 0 := by
    simp only [β, fixedInfraredSymbol, hOff x hx ξ, mul_zero, hZero ξ, add_zero, Complex.ofReal_zero]
  have hMatch (x ξ : E) (h : 1 < ‖ξ‖) : β x ξ = (a x ξ : ℂ) := by
    exact congrArg Complex.ofReal (fixedInfraredSymbol_outside cut 0 (a x) ξ (hHigh ξ h) (hZero ξ))
  have hPlateau : ∀ᶠ ξ in 𝓝 (0 : E), fixedRadianProfile cut ξ = 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) (show 0 < (1 / 2 : ℝ) by norm_num)] with ξ hξ
    have h : dist ξ 0 < 1 / 2 := hξ
    rw [dist_zero_right] at h
    exact hLow ξ h.le
  obtain ⟨P,R₀,ρ,M,hP,hRP,hS,hρOne,hSupp,ha,hM0,hM⟩ :=
    exists_compact_principal_series_data_of_infrared a β K hK hβ hβOff hMatch hOff hHom
  let χ : SchwartzMap E ℂ := (hθS.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hθ)
  have hχ (x : E) : χ x = (θ x : ℂ) := rfl
  have hθPlateau (x ξ : E) (hn : a x ξ ≠ 0) : θ x = 1 :=
    hθK x (by by_contra hout; exact hn (hOff x hout ξ))
  obtain ⟨Q,A,D,hA,hD,hQ,heq⟩ := windowedWeyl_actual_left_comparison_W13
    P R₀ hP hRP ρ ρ.contDiff hS hρOne a hSupp ha hHom M hM0 hM
    cut hCut hPlateau θ χ hχ R hθPlateau hAmp
  constructor
  · intro η
    obtain ⟨C,hC,hLeft⟩ := exists_compact_principal_left_commutator_W13
      P R₀ hP hRP ρ ρ.contDiff hS hρOne a hSupp ha hHom M hM0 hM
      (patchFourierMoment 1 η) (patchFourierMoment 2 η)
      (patch_moment_nonneg _ _) (patch_moment_nonneg _ _)
    exact exists_cutoff_commutator_W13_of_left_order_zero B
      (radianLeftQuantization (fun x ξ => (a x ξ : ℂ))) Q heq η A D C C hA hD hC hC hQ
      (hLeft η le_rfl le_rfl)
  · intro Θ η ℓ hℓ hShape
    exact exists_affine_original_test_comparison_W13 P R₀ hP hRP ρ ρ.contDiff hS hρOne a hSupp
      ha hHom M hM0 hM B Q heq A D hA hD hQ cut 0 hCut
      (fun ξ => by simp only [SchwartzMap.zero_apply, Complex.zero_re, Complex.ofReal_zero])
      Θ η ℓ hℓ hShape

end Burnett.V03
