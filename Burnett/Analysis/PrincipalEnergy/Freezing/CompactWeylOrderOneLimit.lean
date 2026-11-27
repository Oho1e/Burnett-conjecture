import Burnett.Analysis.PrincipalEnergy.Freezing.CompactWeylFullSymbol
import Burnett.Analysis.PrincipalEnergy.Freezing.CompactOrderOneModes
import Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedInfraredStructure

set_option autoImplicit false
set_option maxHeartbeats 4900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ContDiff ENNReal FourierTransform Topology

def radianFirstFourierMass (u : SchwartzMap E ℂ) : ℝ :=
  patchFourierMoment 0 u + patchFourierMoment 1 u

private theorem radian_first_fourier_mass_nonneg (u : SchwartzMap E ℂ) :
    0 ≤ radianFirstFourierMass u :=
  add_nonneg (patch_moment_nonneg _ _) (patch_moment_nonneg _ _)

private theorem linear_fourier_mass_integral (u : SchwartzMap E ℂ) :
    Integrable (fun ξ : E => (1 + ‖ξ‖) * ‖(SchwartzMap.fourierTransformCLM ℂ u) ξ‖) volume ∧
      (∫ ξ : E, (1 + ‖ξ‖) * ‖(SchwartzMap.fourierTransformCLM ℂ u) ξ‖) = radianFirstFourierMass u := by
  let F := SchwartzMap.fourierTransformCLM ℂ u
  have eq (ξ : E) : (1+‖ξ‖) * ‖F ξ‖ = ‖F ξ‖ + ‖ξ‖^1 * ‖F ξ‖ := by rw [add_mul, one_mul, pow_one]
  change Integrable (fun ξ : E => (1 + ‖ξ‖) * ‖F ξ‖) volume ∧
    (∫ ξ : E, (1 + ‖ξ‖) * ‖F ξ‖) = _
  simp_rw [eq]
  refine ⟨F.integrable.norm.add (F.integrable_pow_mul volume 1),?_⟩
  rw [integral_add F.integrable.norm (F.integrable_pow_mul volume 1)]
  simp only [pow_zero, one_mul, radianFirstFourierMass, patchFourierMoment, F, SchwartzMap.fourierTransformCLM_apply]

private theorem radian_fourier_average_growth_mass (m : E × E → ℝ) (mM : Measurable m)
    (A : ℝ) (A0 : 0 ≤ A) (grow : ∀ η ξ : E, ‖m (η, tau • ξ)‖ ≤ A * (1 + ‖η‖) * (1 + ‖ξ‖))
    (f u : SchwartzMap E ℂ) (x : E) :
    ‖radianFourierAverage m f u x‖ ≤ A * radianFirstFourierMass f * radianFirstFourierMass u := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let U := SchwartzMap.fourierTransformCLM ℂ u
  let P := radianFirstFourierMass f
  let Q := radianFirstFourierMass u
  have hP := linear_fourier_mass_integral f
  have hQ := linear_fourier_mass_integral u
  have w (η : E) : ‖radianAction (fun ξ => m (η, ξ)) u x‖ ≤ (A * (1+‖η‖)) * Q := by
    dsimp only [Q]
    rw [radian_action_fourier_integral, ← hQ.2, ← integral_const_mul]
    apply norm_integral_le_of_norm_le (hQ.1.const_mul _)
    filter_upwards with ξ
    simp only [norm_mul, patch_fourier_phase_norm, one_mul, Complex.norm_real]
    change ‖m (η,tau • ξ)‖ * ‖U ξ‖ ≤ _
    exact (mul_le_mul_of_nonneg_right (grow η ξ) (norm_nonneg _)).trans_eq (by ring)
  rw [radian_fourier_average_eq_integral m mM ⟨A,A0,grow⟩]
  have heq : A*P*Q = ∫ η : E, (A*Q) * ((1+‖η‖)*‖F η‖) := by
    rw [integral_const_mul, hP.2]
    ring
  change (‖_‖ : ℝ) ≤ A*P*Q
  rw [heq]
  apply norm_integral_le_of_norm_le (hP.1.const_mul _)
  filter_upwards with η
  simp only [norm_mul, patch_fourier_phase_norm, one_mul]
  change ‖F η‖ * ‖radianAction (fun ξ => m (η,ξ)) u x‖ ≤ _
  exact (mul_le_mul_of_nonneg_left (w η) (norm_nonneg _)).trans_eq (by ring)

theorem slanted_radian_linear_growth_mass (σ : ℝ) (b : E → ℝ) (bM : Measurable b)
    (D : ℝ) (D0 : 0 ≤ D) (growth : ∀ ξ, ‖b ξ‖ ≤ D * (1 + ‖ξ‖))
    (f u : SchwartzMap E ℂ) (x : E) :
    ‖separatedRadianQuantization σ b f u x‖ ≤
      (D * (1+tau+tau*‖σ‖)) * radianFirstFourierMass f * radianFirstFourierMass u := by
  have τ0 : 0 ≤ tau := by unfold tau; positivity
  let C := 1+tau+tau*‖σ‖
  have C0 : 0 ≤ C := by dsimp only [C]; positivity
  have sh (η ξ : E) : ‖tau • ξ + tau • (σ • η)‖ ≤ tau*‖ξ‖+tau*‖σ‖*‖η‖ := by
    simpa only [norm_smul, Real.norm_of_nonneg τ0, mul_assoc] using norm_add_le (tau • ξ) (tau • (σ • η))
  apply radian_fourier_average_growth_mass (slantedRadianSymbol σ b)
    (slanted_radian_symbol_measurable σ b bM) (D*C) (mul_nonneg D0 C0)
  intro η ξ
  change ‖b (tau • ξ + tau • (σ • η))‖ ≤ _
  calc
    _ ≤ D * (1 + ‖tau • ξ + tau • (σ • η)‖) := growth _
    _ ≤ D * (1 + (tau*‖ξ‖+tau*‖σ‖*‖η‖)) := mul_le_mul_of_nonneg_left (add_le_add_left (sh η ξ) 1) D0
    _ ≤ D*C*(1+‖η‖)*(1+‖ξ‖) := by
      rw [mul_assoc D, mul_assoc D]
      apply mul_le_mul_of_nonneg_left _ D0
      dsimp only [C]
      nlinarith only [τ0, norm_nonneg σ, norm_nonneg η, norm_nonneg ξ,
        mul_nonneg τ0 (norm_nonneg η), mul_nonneg (mul_nonneg τ0 (norm_nonneg σ)) (norm_nonneg ξ),
        mul_nonneg (norm_nonneg η) (norm_nonneg ξ),
        mul_nonneg τ0 (mul_nonneg (norm_nonneg η) (norm_nonneg ξ)),
        mul_nonneg (mul_nonneg τ0 (norm_nonneg σ)) (mul_nonneg (norm_nonneg η) (norm_nonneg ξ))]

/-- The literal unbounded order-one midpoint quantization is obtained as
the same fixed frequency-cutoff limit of the complete physical modes.
Both weighted moments that dominate the truncations are summable. -/
theorem radian_midpoint_linear_growth_mode_limit {ι : Type} [Countable ι]
    (a : E → E → ℂ) (f : ι → SchwartzMap E ℂ) (b : ι → E → ℝ)
    (bS : ∀ i, ContDiff ℝ ∞ (b i)) (D : ι → ℝ) (D0 : ∀ i, 0 ≤ D i) (Ds : Summable D)
    (mass : Summable (fun i => D i * (patchFourierMoment 0 (f i) + patchFourierMoment 1 (f i))))
    (grow : ∀ i ξ, ‖b i ξ‖ ≤ D i * (1 + ‖ξ‖))
    (U : ℝ) (U0 : 0 ≤ U) (uniform : ∀ i x, ‖f i x‖ ≤ U)
    (rec : ∀ x ξ, ξ ≠ 0 → HasSum (fun i => f i x * (b i ξ : ℂ)) (a x ξ))
    (u : SchwartzMap E ℂ) (x : E) :
    Tendsto (fun n => radianMidpointTruncation a n u x) atTop
      (𝓝 (∑' i, separatedRadianQuantization (1/2) (b i) (f i) u x)) := by
  let F (n : ℕ) (i : ι) := ∫ y : E,
    ((SchwartzMap.fourierTransformCLE ℂ).symm (normalizedRadianCutoffProfile (b i) (bS i) n)) (x-y) *
      f i ((1/2 : ℝ) • (x+y)) * u y
  let G (i : ι) := separatedRadianQuantization (1/2) (b i) (f i) u x
  have eq (n : ℕ) : radianMidpointTruncation a n u x = ∑' i, F n i :=
    radian_midpoint_truncation_separated_sum a f b bS D D0 Ds grow U U0 uniform rec n u x
  simp only [eq]
  let σ : ℝ := 1 / 2
  let C := 1 + tau + tau*‖σ‖
  have τ0 : 0 ≤ tau := by unfold tau; positivity
  have C0 : 0 ≤ C := by dsimp only [C]; positivity
  let w (i : ι) := (D i*radianFirstFourierMass (f i))*(C*radianFirstFourierMass u)
  have ws : Summable w := mass.mul_right _
  have w0 (i : ι) : 0 ≤ w i :=
    mul_nonneg (mul_nonneg (D0 i) (radian_first_fourier_mass_nonneg _))
      (mul_nonneg C0 (radian_first_fourier_mass_nonneg _))
  have cv (i : ι) : Tendsto (fun n => F n i) atTop (𝓝 (G i)) :=
    separated_radian_weyl_is_midpoint_kernel_limit (b i) (bS i) (D i) (D0 i) (grow i) (f i) u x
  have bound (n : ℕ) (i : ι) : ‖F n i‖ ≤ w i := by
    let p := normalizedRadianCutoffProfile (b i) (bS i) n
    have pr (ξ : E) : ((p ξ).re : ℂ) = p ξ := by
      change ((↑(mikhlinBall (((n : ℝ)+1)⁻¹ • ξ) * b i (tau • ξ)) : ℂ).re : ℂ) = _
      rw [Complex.ofReal_re]
      rfl
    have growP (ξ : E) : ‖fixedRadianProfile p ξ‖ ≤ D i * (1 + ‖ξ‖) := by
      change ‖fixedRadianProfile (normalizedRadianCutoffProfile (b i) (bS i) n) ξ‖ ≤ _
      rw [normalized_radian_cutoff_apply, norm_mul, Real.norm_of_nonneg mikhlinBall.nonneg]
      exact (mul_le_of_le_one_left (norm_nonneg _) mikhlinBall.le_one).trans (grow i ξ)
    have q := separated_radian_weyl_fixed_profile_kernel p pr (f i) u x
    change separatedRadianQuantization (1/2) (fixedRadianProfile p) (f i) u x = F n i at q
    rw [← q]
    exact (slanted_radian_linear_growth_mass σ _ (fixed_radian_profile_measurable p) _ (D0 i) growP
      (f i) u x).trans_eq (by dsimp only [w, C]; ring)
  exact tendsto_countable_mode_sum F G w ws w0 bound cv

end Burnett.A03
