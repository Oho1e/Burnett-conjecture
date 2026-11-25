import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The exact Hölder exponent and the C02 window-volume estimate. -/

set_option autoImplicit false
set_option maxHeartbeats 5400000

noncomputable section

namespace Burnett.C02

open Filter MeasureTheory Set
open scoped ENNReal Topology

def frozenErrorExponent (p : ℝ) : ℝ := 2 * (p - 3) / (3 * (p - 2))

theorem frozenErrorExponent_bounds {p : ℝ} (hp : 3 < p) :
    0 < frozenErrorExponent p ∧ frozenErrorExponent p < 1 ∧
      1 / 3 = frozenErrorExponent p / 2 + (1 - frozenErrorExponent p) / p := by
  have hd : 0 < 3 * (p - 2) := by linarith
  refine ⟨div_pos (by linarith) hd, (div_lt_one₀ hd).2 (by linarith), ?_⟩
  dsimp only [frozenErrorExponent]
  field_simp [(show p ≠ 0 by linarith), (show p - 2 ≠ 0 by linarith)]
  ring

variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V] {μ : Measure X}

/-- Hölder interpolation for the same whole-space function, including zero
norms and extended-valued seminorms. -/
theorem frozenError_interpolate {p : ℝ} (hp : 3 < p) {f : X → V} (hf : AEStronglyMeasurable f μ) :
    eLpNorm' f 3 μ ≤ (eLpNorm' f 2 μ) ^ frozenErrorExponent p *
      (eLpNorm' f p μ) ^ (1 - frozenErrorExponent p) := by
  let a := frozenErrorExponent p
  obtain ⟨ha, ha₁, hSum⟩ := frozenErrorExponent_bounds hp
  change 0 < a at ha
  change a < 1 at ha₁
  change 1 / 3 = a / 2 + (1 - a) / p at hSum
  let b : ℝ := 3 * (a / 2)
  let c : ℝ := 3 * ((1 - a) / p)
  have hb : 0 ≤ b := mul_nonneg (by norm_num) (div_nonneg ha.le (by norm_num))
  have hc : 0 ≤ c := mul_nonneg (by norm_num) (div_nonneg (sub_nonneg.mpr ha₁.le) (by linarith))
  have hbc : b + c = 1 := by dsimp [b, c]; linarith only [hSum]
  have hb' : 2 * b = 3 * a := by dsimp [b]; ring
  have hc' : p * c = 3 * (1 - a) := by dsimp [c]; field_simp [(show p ≠ 0 by linarith)]
  have h := ENNReal.lintegral_mul_norm_pow_le (hf.enorm.pow_const (2 : ℝ)) (hf.enorm.pow_const p) hb hc hbc
  simp_rw [← ENNReal.rpow_mul, hb', hc', ← ENNReal.rpow_add_of_nonneg _
    _ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) ha.le)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (sub_nonneg.mpr ha₁.le)),
    show 3 * a + 3 * (1 - a) = 3 by ring] at h
  have hRoot := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 1 / 3)
  change eLpNorm' f 3 μ ≤ (eLpNorm' f 2 μ) ^ a * (eLpNorm' f p μ) ^ (1 - a)
  rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3)] at hRoot
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hRoot ⊢
  simpa only [show b * (1 / 3) = (1 / 2) * a by dsimp [b]; ring,
    show c * (1 / 3) = (1 / p) * (1 - a) by dsimp [c]; ring] using hRoot

theorem frozenError_interpolate_toReal {p : ℝ} (hp : 3 < p) {f : X → V}
    (hf : AEStronglyMeasurable f μ) (h₂ : eLpNorm' f 2 μ < ⊤) (hₚ : eLpNorm' f p μ < ⊤) :
    (eLpNorm' f 3 μ).toReal ≤ (eLpNorm' f 2 μ).toReal ^ frozenErrorExponent p *
      (eLpNorm' f p μ).toReal ^ (1 - frozenErrorExponent p) := by
  obtain ⟨ha, ha₁, _⟩ := frozenErrorExponent_bounds hp
  have hTop : (eLpNorm' f 2 μ) ^ frozenErrorExponent p *
      (eLpNorm' f p μ) ^ (1 - frozenErrorExponent p) ≠ ⊤ :=
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ha.le h₂.ne)
      (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr ha₁.le) hₚ.ne)).ne
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] using
    ENNReal.toReal_mono hTop (frozenError_interpolate hp hf)

/-- A limsup contract in eventual-upper-bound form, with no intermediate
claims about support of the Fourier outputs or second derivatives. -/
theorem frozenError_eventually_interpolated {p : ℝ} (hp : 3 < p) (f : ℕ → X → V)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (h₂ : ∀ n, eLpNorm' (f n) 2 μ < ⊤)
    (hₚ : ∀ n, eLpNorm' (f n) p μ < ⊤) (B₂ Bₚ : ℝ)
    (hB₂ : ∀ ε > 0, ∀ᶠ n in atTop, (eLpNorm' (f n) 2 μ).toReal ≤ B₂ + ε)
    (hBₚ : ∀ ε > 0, ∀ᶠ n in atTop, (eLpNorm' (f n) p μ).toReal ≤ Bₚ + ε) :
    ∀ ε > 0, ∀ᶠ n in atTop, (eLpNorm' (f n) 3 μ).toReal ≤
      B₂ ^ frozenErrorExponent p * Bₚ ^ (1 - frozenErrorExponent p) + ε := by
  let a := frozenErrorExponent p
  obtain ⟨ha, ha₁, _⟩ := frozenErrorExponent_bounds hp
  have ha₀ : 0 ≤ a := ha.le
  have ha₁' : 0 ≤ 1 - a := sub_nonneg.mpr ha₁.le
  let F (t : ℝ) := (B₂ + t) ^ a * (Bₚ + t) ^ (1 - a)
  have hF : Continuous F := ((Real.continuous_rpow_const ha₀).comp (continuous_const.add continuous_id)).mul
    ((Real.continuous_rpow_const ha₁').comp (continuous_const.add continuous_id))
  intro ε hε
  have ht : F 0 < B₂ ^ a * Bₚ ^ (1 - a) + ε := by dsimp [F]; rw [add_zero, add_zero]; linarith
  have hδ : ∀ᶠ t in 𝓝[>] (0 : ℝ), F t < B₂ ^ a * Bₚ ^ (1 - a) + ε :=
    hF.continuousWithinAt.eventually (Iio_mem_nhds ht)
  have ht₀ : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨δ, hδ₀, hδ₁⟩ := (ht₀.and hδ).exists
  filter_upwards [hB₂ δ hδ₀, hBₚ δ hδ₀] with n hn₂ hnₚ
  exact (frozenError_interpolate_toReal hp (hf n) (h₂ n) (hₚ n)).trans
    ((mul_le_mul (Real.rpow_le_rpow ENNReal.toReal_nonneg hn₂ ha₀)
      (Real.rpow_le_rpow ENNReal.toReal_nonneg hnₚ ha₁') (Real.rpow_nonneg ENNReal.toReal_nonneg _)
      (Real.rpow_nonneg (ENNReal.toReal_nonneg.trans hn₂) _)).trans hδ₁.le)

/-- The precise window-volume power, robust also for `ℓ = 0` or zero volume. -/
theorem frozenError_window_power {p : ℝ} (hp : 3 < p) (C₂ Cₚ ℓ vol : ℝ)
    (hC₂ : 0 ≤ C₂) (hCₚ : 0 ≤ Cₚ) (hℓ : 0 ≤ ℓ) (hv : 0 ≤ vol) :
    (C₂ * ℓ * vol ^ (1 / 2 : ℝ)) ^ frozenErrorExponent p *
      (Cₚ * vol ^ (1 / p)) ^ (1 - frozenErrorExponent p) =
      C₂ ^ frozenErrorExponent p * Cₚ ^ (1 - frozenErrorExponent p) *
      ℓ ^ frozenErrorExponent p * vol ^ (1 / 3 : ℝ) := by
  let a := frozenErrorExponent p
  obtain ⟨ha, ha₁, hSum⟩ := frozenErrorExponent_bounds hp
  have hA : 0 ≤ (1 / 2 : ℝ) * a := mul_nonneg (by norm_num) ha.le
  have hP : 0 ≤ (1 / p) * (1 - a) :=
    mul_nonneg (div_nonneg (by norm_num) (by linarith)) (sub_nonneg.mpr ha₁.le)
  change (C₂ * ℓ * vol ^ (1 / 2 : ℝ)) ^ a * (Cₚ * vol ^ (1 / p)) ^ (1 - a) =
    C₂ ^ a * Cₚ ^ (1 - a) * ℓ ^ a * vol ^ (1 / 3 : ℝ)
  rw [Real.mul_rpow (mul_nonneg hC₂ hℓ) (Real.rpow_nonneg hv _), Real.mul_rpow hC₂ hℓ,
    Real.mul_rpow hCₚ (Real.rpow_nonneg hv _), ← Real.rpow_mul hv, ← Real.rpow_mul hv]
  have hs : (1 / 2 : ℝ) * a + (1 / p) * (1 - a) = 1 / 3 := by
    change (1 / 2 : ℝ) * frozenErrorExponent p + (1 / p) * (1 - frozenErrorExponent p) = 1 / 3
    simpa [div_eq_mul_inv, mul_comm] using hSum.symm
  rw [← hs, Real.rpow_add_of_nonneg hv hA hP]
  ring

/-- Direct C02 consumer of the two endpoint bounds for the same actual
sequence. The conclusion gives the sharp window power in the sense used
for the real limsup, including zero patch measure. -/
theorem frozenError_eventually_window {p : ℝ} (hp : 3 < p) (f : ℕ → X → V)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (h₂ : ∀ n, eLpNorm' (f n) 2 μ < ⊤)
    (hₚ : ∀ n, eLpNorm' (f n) p μ < ⊤) (C₂ Cₚ ℓ vol : ℝ)
    (hC₂ : 0 ≤ C₂) (hCₚ : 0 ≤ Cₚ) (hℓ : 0 ≤ ℓ) (hv : 0 ≤ vol)
    (hB₂ : ∀ ε > 0, ∀ᶠ n in atTop, (eLpNorm' (f n) 2 μ).toReal ≤ C₂ * ℓ * vol ^ (1 / 2 : ℝ) + ε)
    (hBₚ : ∀ ε > 0, ∀ᶠ n in atTop, (eLpNorm' (f n) p μ).toReal ≤ Cₚ * vol ^ (1 / p) + ε) :
    ∀ ε > 0, ∀ᶠ n in atTop, (eLpNorm' (f n) 3 μ).toReal ≤
      C₂ ^ frozenErrorExponent p * Cₚ ^ (1 - frozenErrorExponent p) *
        ℓ ^ frozenErrorExponent p * vol ^ (1 / 3 : ℝ) + ε := by
  have h := frozenError_eventually_interpolated hp f hf h₂ hₚ _ _ hB₂ hBₚ
  rwa [frozenError_window_power hp C₂ Cₚ ℓ vol hC₂ hCₚ hℓ hv] at h

/-- A bounded finite-`p` endpoint upgrades the exact strong (L²)
vanishing of the same complementary error to strong (L³). -/
theorem frozenError_strong3_of_strong2 {p : ℝ} (hp : 3 < p) (f : ℕ → X → V)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (h₂ : ∀ n, eLpNorm' (f n) 2 μ < ⊤)
    (hₚ : ∀ n, eLpNorm' (f n) p μ < ⊤)
    (hL2 : Tendsto (fun n => (eLpNorm' (f n) 2 μ).toReal) atTop (𝓝 0))
    (Cₚ : ℝ) (hBₚ : ∀ ε > 0, ∀ᶠ n in atTop, (eLpNorm' (f n) p μ).toReal ≤ Cₚ + ε) :
    Tendsto (fun n => (eLpNorm' (f n) 3 μ).toReal) atTop (𝓝 0) := by
  obtain ⟨ha, _, _⟩ := frozenErrorExponent_bounds hp
  have hb : ∀ ε > 0, ∀ᶠ n in atTop, (eLpNorm' (f n) 2 μ).toReal ≤ (0 : ℝ) + ε := by
    intro ε hε
    exact (hL2.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < 0 + ε))).mono (fun _ h => h.le)
  have h := frozenError_eventually_interpolated hp f hf h₂ hₚ 0 Cₚ hb hBₚ
  simp only [Real.zero_rpow ha.ne', zero_mul, zero_add] at h
  apply tendsto_order.2
  refine ⟨fun x hx => Eventually.of_forall (fun _ => hx.trans_le ENNReal.toReal_nonneg), ?_⟩
  intro ε hε
  exact (h (ε / 2) (half_pos hε)).mono (fun _ hn => hn.trans_lt (half_lt_self hε))

end Burnett.C02
