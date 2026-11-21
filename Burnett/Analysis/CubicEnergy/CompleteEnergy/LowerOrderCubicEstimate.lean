import Burnett.Analysis.CubicEnergy.CompleteEnergy.LowerOrderPairing
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearCoefficient

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Finset Metric Burnett.RicciSymbol
open scoped BigOperators ContDiff ComplexConjugate ENNReal

private abbrev CubicExponent : ℝ≥0∞ := ENNReal.ofReal 3
private abbrev TwoFactorExponent : ℝ≥0∞ := ENNReal.ofReal (3/2)

/-- A component W¹³ norm, using the same derivative norm as the homogeneous estimate. -/
def inhomogeneousComponentNorm (f : SchwartzMap E ℂ) : ℝ≥0∞ :=
  eLpNorm (f : E → ℂ) CubicExponent volume + energyGradientNorm f

/-- The finite field W¹³ norm as a sum of component norms. -/
def fieldInhomogeneousNorm {J : Type} [Fintype J] (f : J → SchwartzMap E ℂ) : ℝ≥0∞ :=
  ∑ j, inhomogeneousComponentNorm (f j)

private theorem partial_le_energy_gradient (j : Index) (f : SchwartzMap E ℂ) :
    eLpNorm (energyPartial j f : E → ℂ) CubicExponent volume ≤ energyGradientNorm f := by
  apply eLpNorm_mono
  intro x
  change ‖fderiv ℝ (f : E → ℂ) x (EuclideanSpace.single j 1)‖ ≤ _
  simpa using (fderiv ℝ (f : E → ℂ) x).le_opNorm (EuclideanSpace.single j 1)

theorem pair_three_cubic (A U : SchwartzMap E ℂ) (V : E → ℂ)
    (hV : MemLp V CubicExponent volume) :
    ‖∫ x, A x * U x * conj (V x)‖ₑ ≤
      eLpNorm (A : E → ℂ) CubicExponent volume * eLpNorm (U : E → ℂ) CubicExponent volume *
        eLpNorm V CubicExponent volume := by
  have h₁ : (3 : ℝ).HolderTriple 3 (3/2) := ⟨by norm_num,by norm_num,by norm_num⟩
  have h₂ : (3/2 : ℝ).HolderTriple 3 1 := ⟨by norm_num,by norm_num,by norm_num⟩
  letI : ENNReal.HolderTriple CubicExponent CubicExponent TwoFactorExponent := h₁.ennrealOfReal
  letI : ENNReal.HolderTriple TwoFactorExponent CubicExponent 1 := by
    simpa only [ENNReal.ofReal_one] using h₂.ennrealOfReal
  let B (x : E) := A x * U x
  let Z (x : E) := conj (V x)
  have ha := (A.memLp CubicExponent volume).1
  have hu := (U.memLp CubicExponent volume).1
  have hb : AEStronglyMeasurable B volume := ha.mul hu
  have hz : AEStronglyMeasurable Z volume := Complex.continuous_conj.comp_aestronglyMeasurable hV.1
  have eZ : eLpNorm Z CubicExponent volume = eLpNorm V CubicExponent volume :=
    eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => Complex.norm_conj (V x))
  have eB : eLpNorm B TwoFactorExponent volume ≤
      eLpNorm (A : E → ℂ) CubicExponent volume * eLpNorm (U : E → ℂ) CubicExponent volume :=
    eLpNorm_smul_le_mul_eLpNorm (φ := (A : E → ℂ)) (f := (U : E → ℂ))
      (p := CubicExponent) (q := CubicExponent) (r := TwoFactorExponent) hu ha
  calc
    _ ≤ ∫⁻ x, ‖B x * Z x‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun x => B x * Z x) 1 volume := eLpNorm_one_eq_lintegral_enorm.symm
    _ ≤ eLpNorm B TwoFactorExponent volume * eLpNorm Z CubicExponent volume :=
      eLpNorm_smul_le_mul_eLpNorm (φ := B) (f := Z)
        (p := TwoFactorExponent) (q := CubicExponent) (r := 1) hz hb
    _ ≤ _ := by rw [eZ]; exact mul_le_mul_right' eB _

/-- A single lower-order quasilinear pairing is controlled by moving one
derivative through the actual bounded multiplier and keeping the test slot. -/
theorem lower_order_quasilinear_component_bound (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (K : ℝ≥0∞) (bound : ∀ g : SchwartzMap E ℂ,
      MemLp (radianAction m g) CubicExponent volume ∧
      eLpNorm (radianAction m g) CubicExponent volume ≤ K * eLpNorm (g : E → ℂ) CubicExponent volume)
    (a d : Index) (A u v : SchwartzMap E ℂ) :
    ‖∫ x, A x * energyPartial a (energyPartial d u) x * conj (radianAction m v x)‖ₑ ≤
      K * (inhomogeneousComponentNorm A * (inhomogeneousComponentNorm u * inhomogeneousComponentNorm v)) := by
  rw [quasilinear_component_ibp_of_integrable_spectrum m spectrum (fun g => (bound g).1)]
  let X := ∫ x, A x * energyPartial d u x * conj (radianAction m (energyPartial a v) x)
  let Y := ∫ x, energyPartial a A x * energyPartial d u x * conj (radianAction m v x)
  let A0 := eLpNorm (A : E → ℂ) CubicExponent volume
  let V0 := eLpNorm (v : E → ℂ) CubicExponent volume
  let G := energyGradientNorm
  have hX : ‖X‖ₑ ≤ A0 * G u * (K * G v) := by
    have h := pair_three_cubic A (energyPartial d u) (radianAction m (energyPartial a v)) (bound _).1
    exact h.trans (mul_le_mul' (mul_le_mul_left' (partial_le_energy_gradient d u) _) <|
      (bound (energyPartial a v)).2.trans (mul_le_mul_left' (partial_le_energy_gradient a v) _))
  have hY : ‖Y‖ₑ ≤ G A * G u * (K * V0) := by
    have h := pair_three_cubic (energyPartial a A) (energyPartial d u) (radianAction m v) (bound _).1
    exact h.trans (mul_le_mul' (mul_le_mul' (partial_le_energy_gradient a A) (partial_le_energy_gradient d u))
      (bound v).2)
  have neg : ‖-X-Y‖ₑ ≤ ‖X‖ₑ + ‖Y‖ₑ := by
    simpa only [sub_eq_add_neg,enorm_neg] using enorm_add_le (-X) (-Y)
  have v0 : V0 ≤ inhomogeneousComponentNorm v := le_add_of_nonneg_right (zero_le (G v))
  have v1 : G v ≤ inhomogeneousComponentNorm v := le_add_of_nonneg_left (zero_le V0)
  have u1 : G u ≤ inhomogeneousComponentNorm u := le_add_of_nonneg_left
    (zero_le (eLpNorm (u : E → ℂ) CubicExponent volume))
  change ‖-X-Y‖ₑ ≤ _
  calc
    _ ≤ _ := neg.trans (add_le_add hX hY)
    _ ≤ A0 * G u * (K * inhomogeneousComponentNorm v) +
        G A * G u * (K * inhomogeneousComponentNorm v) :=
      add_le_add (mul_le_mul_left' (mul_le_mul_left' v1 K) _) (mul_le_mul_left' (mul_le_mul_left' v0 K) _)
    _ = K * (inhomogeneousComponentNorm A * (G u * inhomogeneousComponentNorm v)) := by
      change _ = K * ((A0 + G A) * (G u * inhomogeneousComponentNorm v))
      ring
    _ ≤ _ := mul_le_mul_left' (mul_le_mul_left' (mul_le_mul_right' u1 _) _) _

private def schwartzCoeAdd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    SchwartzMap E F →+ (E → F) where
  toFun f := f
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem schwartz_L3_sum_le {J F : Type*} [Fintype J] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : J → SchwartzMap E F) :
    eLpNorm ((∑ j, f j : SchwartzMap E F) : E → F) CubicExponent volume ≤
      ∑ j, eLpNorm (f j : E → F) CubicExponent volume := by
  change eLpNorm (schwartzCoeAdd (∑ j, f j)) CubicExponent volume ≤ _
  rw [map_sum]
  exact eLpNorm_sum_le (fun j _ => (f j).continuous.aestronglyMeasurable) (by norm_num)

private theorem component_sum_bound {J : Type*} [Fintype J] (f : J → SchwartzMap E ℂ) :
    inhomogeneousComponentNorm (∑ j, f j) ≤ ∑ j, inhomogeneousComponentNorm (f j) := by
  change eLpNorm ((∑ j, f j : SchwartzMap E ℂ) : E → ℂ) CubicExponent volume +
    eLpNorm (SchwartzMap.fderivCLM ℝ (∑ j, f j) : E → E →L[ℝ] ℂ) CubicExponent volume ≤
    ∑ j, (eLpNorm (f j : E → ℂ) CubicExponent volume +
      eLpNorm (SchwartzMap.fderivCLM ℝ (f j) : E → E →L[ℝ] ℂ) CubicExponent volume)
  rw [map_sum, Finset.sum_add_distrib]
  exact add_le_add (schwartz_L3_sum_le f) (schwartz_L3_sum_le (fun j => SchwartzMap.fderivCLM ℝ (f j)))

private theorem component_real_smul (r : ℝ) (f : SchwartzMap E ℂ) :
    inhomogeneousComponentNorm (r • f) = ‖r‖ₑ * inhomogeneousComponentNorm f := by
  have grad : energyGradientNorm (r • f) = ‖r‖ₑ * energyGradientNorm f := by
    change eLpNorm (SchwartzMap.fderivCLM ℝ (r • f) : E → E →L[ℝ] ℂ) CubicExponent volume = _
    rw [map_smul]
    exact eLpNorm_const_smul r (SchwartzMap.fderivCLM ℝ f : E → E →L[ℝ] ℂ) _ _
  change eLpNorm (r • (f : E → ℂ)) CubicExponent volume + energyGradientNorm (r • f) =
    ‖r‖ₑ * (eLpNorm (f : E → ℂ) CubicExponent volume + energyGradientNorm f)
  rw [grad,eLpNorm_const_smul,mul_add]

private theorem component_le_field {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ) (j : J) :
    inhomogeneousComponentNorm (u j) ≤ fieldInhomogeneousNorm u := by
  unfold fieldInhomogeneousNorm
  exact Finset.single_le_sum (f := fun i => inhomogeneousComponentNorm (u i)) (fun _ _ => zero_le _) (mem_univ j)

private def linearCoefficientMass {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ) : ℝ≥0∞ :=
  ∑ k, ∑ j, ‖c k j‖ₑ

private theorem linearCoefficientMass_finite {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ) :
    linearCoefficientMass c < ⊤ := ENNReal.sum_lt_top.mpr fun _ _ =>
  ENNReal.sum_lt_top.mpr fun _ _ => enorm_lt_top

private theorem coefficient_W13_sum {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (H : J → SchwartzMap E ℂ) :
    (∑ k, inhomogeneousComponentNorm (linearEnergyCoefficient c H k)) ≤
      linearCoefficientMass c * fieldInhomogeneousNorm H := by
  unfold linearCoefficientMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  unfold linearEnergyCoefficient
  refine (component_sum_bound _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  rw [component_real_smul]
  exact mul_le_mul_left' (component_le_field H j) _

private theorem lower_order_mixed_bound (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (K : ℝ≥0∞) (bound : ∀ g : SchwartzMap E ℂ,
      MemLp (radianAction m g) CubicExponent volume ∧
      eLpNorm (radianAction m g) CubicExponent volume ≤ K * eLpNorm (g : E → ℂ) CubicExponent volume)
    {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ) (H u v : J → SchwartzMap E ℂ) :
    ‖quasilinearMixedPairing m (linearEnergyCoefficient c H) u v‖ₑ ≤
      K * linearCoefficientMass c * (fieldInhomogeneousNorm H *
        (fieldInhomogeneousNorm u * fieldInhomogeneousNorm v)) := by
  let A := linearEnergyCoefficient c H
  let W (f : J → SchwartzMap E ℂ) := fieldInhomogeneousNorm f
  let S := W u * W v
  let X (k : EnergyIndex J) := ∫ x, A k x *
    energyPartial k.1.1 (energyPartial k.1.2 (u k.2.2)) x * conj (radianAction m (v k.2.1) x)
  have each (k : EnergyIndex J) : ‖X k‖ₑ ≤ K * (inhomogeneousComponentNorm (A k) * S) := by
    have h := lower_order_quasilinear_component_bound m spectrum K bound k.1.1 k.1.2 (A k) (u k.2.2) (v k.2.1)
    exact h.trans (mul_le_mul_left' (mul_le_mul_left'
      (mul_le_mul' (component_le_field u k.2.2) (component_le_field v k.2.1)) _) _)
  change ‖∑ k, X k‖ₑ ≤ _
  calc
    _ ≤ ∑ k, K * (inhomogeneousComponentNorm (A k) * S) :=
      (enorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => each k)
    _ = K * ((∑ k, inhomogeneousComponentNorm (A k)) * S) := by simp only [Finset.mul_sum,Finset.sum_mul]
    _ ≤ K * ((linearCoefficientMass c * W H) * S) :=
      mul_le_mul_left' (mul_le_mul_right' (coefficient_W13_sum c H) _) _
    _ = _ := by unfold S W; ring

theorem lower_order_quasilinear_W13_bound (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (K : ℝ≥0∞) (bound : ∀ g : SchwartzMap E ℂ,
      MemLp (radianAction m g) CubicExponent volume ∧
      eLpNorm (radianAction m g) CubicExponent volume ≤ K * eLpNorm (g : E → ℂ) CubicExponent volume)
    {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ) (H u v : J → SchwartzMap E ℂ) :
    ‖quasilinearSymmetricEnergy m (linearEnergyCoefficient c H) u v‖ₑ ≤
      2 * K * linearCoefficientMass c * (fieldInhomogeneousNorm H *
        (fieldInhomogeneousNorm u * fieldInhomogeneousNorm v)) := by
  let A := linearEnergyCoefficient c H
  let X := quasilinearMixedPairing m A u v
  let Y := quasilinearMixedPairing m A v u
  let G := fieldInhomogeneousNorm H * (fieldInhomogeneousNorm u * fieldInhomogeneousNorm v)
  have im : ‖(X+Y).im‖ₑ ≤ ‖X+Y‖ₑ := by
    rw [← ofReal_norm_eq_enorm,← ofReal_norm_eq_enorm,Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm (X+Y))
  have hX : ‖X‖ₑ ≤ K*linearCoefficientMass c*G := lower_order_mixed_bound m spectrum K bound c H u v
  have hY : ‖Y‖ₑ ≤ K*linearCoefficientMass c*G := by
    simpa only [Y,G,mul_comm (fieldInhomogeneousNorm v) (fieldInhomogeneousNorm u)] using
      lower_order_mixed_bound m spectrum K bound c H v u
  change ‖(X+Y).im‖ₑ ≤ _
  exact (im.trans ((enorm_add_le X Y).trans (add_le_add hX hY))).trans_eq (by ring)

/-- The actual fixed smooth additive Fourier correction satisfies the
quasilinear W¹³ estimate on the same physical pairings. -/
theorem fixed_profile_quasilinear_W13_bound (a : SchwartzMap E ℂ)
    (areal : ∀ ξ, ((a ξ).re : ℂ) = a ξ) {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ H u v : J → SchwartzMap E ℂ,
      ‖quasilinearSymmetricEnergy (fixedRadianProfile a) (linearEnergyCoefficient c H) u v‖ₑ ≤
        C * (fieldInhomogeneousNorm H * (fieldInhomogeneousNorm u * fieldInhomogeneousNorm v)) := by
  obtain ⟨K,hK,est⟩ := fixedRadianProfile_Lp a areal 3 (by norm_num)
  refine ⟨2*K*linearCoefficientMass c,ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hK)
    (linearCoefficientMass_finite c),?_⟩
  exact lower_order_quasilinear_W13_bound (fixedRadianProfile a) (fixed_profile_spectrum_integrable a areal) K est c

/-- The cutoff times the homogeneous symbol satisfies the same bound with
uniform linear dependence on the order-six sphere jet. -/
theorem fixed_cut_quasilinear_W13_sphere_bound (a : SchwartzMap E ℂ)
    (areal : ∀ ξ, ((a ξ).re : ℂ) = a ξ) {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ H u v : J → SchwartzMap E ℂ,
        ‖quasilinearSymmetricEnergy (fun ζ => fixedRadianProfile a ζ * b ζ)
          (linearEnergyCoefficient c H) u v‖ₑ ≤
          C * ENNReal.ofReal D * (fieldInhomogeneousNorm H *
            (fieldInhomogeneousNorm u * fieldInhomogeneousNorm v)) := by
  obtain ⟨K,hK,est⟩ := fixed_infrared_sphere_bound a areal 3 (by norm_num)
  refine ⟨2*K*linearCoefficientMass c,ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hK)
    (linearCoefficientMass_finite c),?_⟩
  intro b hb hom D hD jet H u v
  have bound := lower_order_quasilinear_W13_bound _ (fixed_cut_spectrum_integrable a areal b hb hom)
    (K*ENNReal.ofReal D) (est b hb hom D hD jet) c H u v
  exact bound.trans_eq (by ring)

end Burnett.A02.FrequencySplit
