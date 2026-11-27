import Burnett.Analysis.PrincipalEnergy.Freezing.FixedTestOrderZeroAlgebra
import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedFrozenLeftDefinitions

set_option autoImplicit false
set_option maxHeartbeats 7800000
noncomputable section

namespace Burnett.A03

open MeasureTheory Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ContDiff ENNReal FourierTransform

private theorem radian_left_principal_spectrum_integrable (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0}) (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (u : SchwartzMap E ℂ) : Integrable (radianActionSpectrum b u) volume := by
  let β (ξ : E) := b (tau • ξ)
  have τp : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have βS : ContDiffOn ℝ ∞ β {ξ | ξ ≠ 0} :=
    hb.comp (contDiff_const.smul contDiff_id).contDiffOn (fun _ h => smul_ne_zero τp.ne' h)
  have βh (t : ℝ) (ht : 0 < t) (ξ : E) : β (t • ξ) = t * β ξ := by
    change b (tau • t • ξ) = t * b (tau • ξ)
    rw [smul_comm tau t ξ, hom t ht]
  exact orderOne_spectrum_integrable β βS βh u

/-- Exact comparison of the unchanged two-sided test with the literal
left quantization of the manuscript's localized frozen symbol. -/
theorem localized_frozen_left_test_exact (a : E → E → ℝ)
    (smooth : ∀ x, ContDiffOn ℝ ∞ (a x) {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (c : E) (θ : SchwartzMap E ℂ) (u : SchwartzMap E ℂ) (x : E) :
    sandwichedScalarTest θ (fun v => radianLeftQuantization (fun y ξ => (a y ξ : ℂ)) v - radianAction (a c) v) u x -
      radianLeftQuantization (localizedFrozenPrincipalSymbol a c θ) u x =
        localizedFrozenLeftCommutator a c θ u x := by
  let phase (ξ : E) := patchFourierPhase ξ x
  let arg (ξ : E) : E × E := (ξ,x)
  have ac : Continuous arg := continuous_id.prodMk continuous_const
  have pc : Continuous phase := by
    change Continuous ((fun z : E × E => patchFourierPhase z.1 z.2) ∘ arg)
    exact patch_fourier_phase_continuous.comp ac
  have one (y : E) : Integrable (fun ξ => phase ξ * radianActionSpectrum (a y) u ξ) (volume : Measure E) :=
    (radian_left_principal_spectrum_integrable (a y) (smooth y) (fun t ht => hom t ht y) u).bdd_mul
      pc.aestronglyMeasurable ⟨1, fun ξ => (patch_fourier_phase_norm ξ x).le⟩
  have left : radianLeftQuantization (fun y ξ => (a y ξ : ℂ)) u x = radianAction (a x) u x :=
    radian_left_quantization_frozen (a x) u x
  have sym : radianLeftQuantization (localizedFrozenPrincipalSymbol a c θ) u x =
      (θ x)^2 * (radianLeftQuantization (fun y ξ => (a y ξ : ℂ)) u x - radianAction (a c) u x) := by
    rw [left, radian_action_fourier_integral, radian_action_fourier_integral]
    change _ = (θ x)^2 * ((∫ ξ, phase ξ * radianActionSpectrum (a x) u ξ) -
      (∫ ξ, phase ξ * radianActionSpectrum (a c) u ξ))
    rw [← integral_sub (one x) (one c), ← integral_const_mul]
    unfold radianLeftQuantization
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [phase, radianActionSpectrum, localizedFrozenPrincipalSymbol]
    ring
  rw [sym]
  unfold sandwichedScalarTest localizedFrozenLeftCommutator radianCommutator
  change θ x * (radianLeftQuantization (fun y ξ => (a y ξ : ℂ)) (energyProduct θ u) x -
      radianAction (a c) (energyProduct θ u) x) -
      (θ x)^2 * (radianLeftQuantization (fun y ξ => (a y ξ : ℂ)) u x - radianAction (a c) u x) =
    θ x * (radianLeftQuantization (fun y ξ => (a y ξ : ℂ)) (energyProduct θ u) x -
      θ x * radianLeftQuantization (fun y ξ => (a y ξ : ℂ)) u x -
      (radianAction (a c) (energyProduct θ u) x - θ x * radianAction (a c) u x))
  ring

/-- Center-uniform consumer for a fixed scale. The original B and the original
frozen B₀ are named in the conclusion. The three inputs are the checked
order-zero full-symbol correction, the fixed infrared correction of the frozen
operator, and the actual cutoff commutator. -/
theorem sandwiched_original_test_comparison_W13
    (a : E → E → ℝ) (smooth : ∀ x, ContDiffOn ℝ ∞ (a x) {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (centers : Set E) (θ : E → SchwartzMap E ℂ)
    (B : SchwartzMap E ℂ → E → ℂ) (B₀ : E → SchwartzMap E ℂ → E → ℂ)
    (R : SchwartzMap E ℂ → E → ℂ) (R₀ : E → SchwartzMap E ℂ → E → ℂ)
    (original : ∀ u, B u = radianLeftQuantization (fun y ξ => (a y ξ : ℂ)) u + R u)
    (frozen : ∀ c ∈ centers, ∀ u, B₀ c u = radianAction (a c) u + R₀ c u)
    (A D A₀ D₀ C F P T : ℝ≥0∞)
    (value : ∀ c ∈ centers, eLpNorm (θ c : E → ℂ) ⊤ volume ≤ P)
    (jet : ∀ c ∈ centers, ∀ j : Index, eLpNorm (energyPartial j (θ c) : E → ℂ) ⊤ volume ≤ T)
    (correction : SchwartzOrderZeroJetBound R A D)
    (infrared : ∀ c ∈ centers, SchwartzOrderZeroJetBound (R₀ c) A₀ D₀)
    (commutator : ∀ c ∈ centers, SchwartzOrderZeroJetBound (localizedFrozenLeftCommutator a c (θ c)) C F) :
    ∀ c ∈ centers,
      SchwartzOrderZeroJetBound (fun u => (-Complex.I) •
        (sandwichedScalarTest (θ c) (fun v => B v - B₀ c v) u -
          radianLeftQuantization (localizedFrozenPrincipalSymbol a c (θ c)) u))
        (P^2*(A+A₀)+C) (2*P*T*(A+A₀)+P^2*(D+D₀)+F) := by
  intro c hc
  let t := θ c
  let J := sandwichedScalarTest t (fun v => R v - R₀ c v)
  let K := localizedFrozenLeftCommutator a c t
  have hR := schwartz_order_zero_jet_bound_sub R (R₀ c) A D A₀ D₀ correction (infrared c hc)
  have hJ := schwartz_order_zero_jet_bound_sandwich t _ (A+A₀) (D+D₀) P T hR (value c hc) (jet c hc)
  have hSum := schwartz_order_zero_jet_bound_add J K _ _ _ _ hJ (commutator c hc)
  have hI := schwartz_order_zero_jet_bound_const_mul _ _ _ hSum (-Complex.I)
  have un : ‖-Complex.I‖ₑ = 1 := by rw [← ofReal_norm_eq_enorm, norm_neg, Complex.norm_I, ENNReal.ofReal_one]
  rw [un, one_mul, one_mul] at hI
  have actionEq : (fun u => (-Complex.I) • (J u + K u)) =
      (fun u => (-Complex.I) •
        (sandwichedScalarTest t (fun v => B v - B₀ c v) u -
          radianLeftQuantization (localizedFrozenPrincipalSymbol a c t) u)) := by
    funext u x
    have w : K u x = _ := (localized_frozen_left_test_exact a smooth hom c t u x).symm
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, w]
    unfold J sandwichedScalarTest
    simp only [Pi.sub_apply]
    rw [original (energyProduct t u), frozen c hc (energyProduct t u)]
    simp only [Pi.add_apply, smul_eq_mul]
    ring
  rw [← actionEq]
  simpa only [add_assoc] using hI

end Burnett.A03
