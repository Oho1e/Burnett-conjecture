import Burnett.Analysis.PrincipalEnergy.Freezing.WeightedOrderZeroFourierFamily
import Burnett.Analysis.PrincipalEnergy.Freezing.CompactComplexOrderZeroLeft
import Burnett.Analysis.PrincipalEnergy.Freezing.FixedPrincipalWeylKernel

set_option autoImplicit false
set_option maxHeartbeats 4700000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ContDiff ENNReal FourierTransform Topology

/-- The difference symbol at the actual two Fourier frequencies. This
subtraction is made before integrating either of the two actions. -/
def regularizedPrincipalGapSymbol (cut : SchwartzMap E ℂ) (b : E → ℝ) (q : E × E) : ℝ :=
  slantedRadianSymbol (1/2) (fixedInfraredSymbol cut 0 b) q - slantedRadianSymbol 0 b q

private theorem radian_action_bounded_symbol_sub (a b : E → ℝ) (aM : Measurable a) (bM : Measurable b)
    (A B : ℝ) (aBound : ∀ ξ, ‖a ξ‖ ≤ A) (bBound : ∀ ξ, ‖b ξ‖ ≤ B) (u : SchwartzMap E ℂ) :
    radianAction (fun ξ => a ξ - b ξ) u = radianAction a u - radianAction b u := by
  funext x
  let p (ξ : E) := patchFourierPhase ξ x
  let args (ξ : E) : E × E := (ξ,x)
  have ac : Continuous args := continuous_id.prodMk continuous_const
  have pC : Continuous p := by
    change Continuous ((fun z : E × E => patchFourierPhase z.1 z.2) ∘ args)
    exact patch_fourier_phase_continuous.comp ac
  have h (f : E → ℝ) (hf : Measurable f) (C : ℝ) (B : ∀ ξ, ‖f ξ‖ ≤ C) :
      Integrable (fun ξ => p ξ * radianActionSpectrum f u ξ) volume :=
    (bounded_real_radian_spectrum_integrable f hf C B u).bdd_mul pC.aestronglyMeasurable
      ⟨1,fun ξ => (patch_fourier_phase_norm ξ x).le⟩
  simp only [Pi.sub_apply, radian_action_fourier_integral]
  change (∫ ξ, p ξ * radianActionSpectrum (fun q => a q - b q) u ξ) =
    (∫ ξ, p ξ * radianActionSpectrum a u ξ) - ∫ ξ, p ξ * radianActionSpectrum b u ξ
  rw [← integral_sub (h a aM A aBound) (h b bM B bBound)]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [radianActionSpectrum, Complex.ofReal_sub]
  ring

/-- Common sectionwise weighted order-zero budget for the genuine
regularized half shift minus the unregularized left principal symbol.
The only ℝ³ operator inputs are the already proved angular shift and
fixed Schwartz low-frequency estimates. -/
theorem exists_regularized_principal_gap_frequency_bound (cut : SchwartzMap E ℂ)
    (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (plateau : ∀ᶠ ζ in 𝓝 (0 : E), fixedRadianProfile cut ζ = 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} →
        (∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) →
        ∀ D : ℝ, 0 ≤ D →
        (∀ n : ℕ, n ≤ 7 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
          Measurable (regularizedPrincipalGapSymbol cut b) ∧
          (∀ η ξ : E, ‖regularizedPrincipalGapSymbol cut b (η, ξ)‖ ≤ (K*D)*(1+‖η‖)) ∧
          ∀ (η : E) (u : SchwartzMap E ℂ),
            let g := radianAction (fun ξ => regularizedPrincipalGapSymbol cut b (η,ξ)) u
            MemLp g (ENNReal.ofReal 3) volume ∧
            eLpNorm g (ENNReal.ofReal 3) volume ≤
              ENNReal.ofReal ((K*D)*(1+‖η‖)) * eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume := by
  obtain ⟨Ks,Ks0,shift⟩ := exists_radian_shift_difference_L3_bound
  obtain ⟨Kl,Klf,low⟩ := fixed_infrared_sphere_bound cut hcut 3 (by norm_num)
  have τp : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  let M := tau / 2 * max 1 Ks
  let C := tau * (SchwartzMap.seminorm ℝ 1 0) cut
  let L := max C Kl.toReal
  have M0 : 0 ≤ M := mul_nonneg (div_nonneg τp.le (by norm_num)) (zero_le_one.trans (le_max_left _ _))
  have C0 : 0 ≤ C := mul_nonneg τp.le (apply_nonneg _ _)
  have L0 : 0 ≤ L := C0.trans (le_max_left _ _)
  refine ⟨M+L,add_nonneg M0 L0,?_⟩
  intro b hb hom D D0 jets
  let lc (ξ : E) := fixedRadianProfile cut ξ * b ξ
  have bM := measurable_of_continuousOn_compl_singleton 0 hb.continuousOn
  have lM : Measurable lc := (fixed_radian_profile_measurable cut).mul bM
  have bS := fixedInfraredSymbol_smooth cut 0 b hb plateau
  have wholeM : Measurable (regularizedPrincipalGapSymbol cut b) :=
    (slanted_radian_symbol_measurable _ _ bS.continuous.measurable).sub
      (slanted_radian_symbol_measurable _ _ bM)
  have bBound (ξ : E) : ‖b ξ‖ ≤ ‖ξ‖ * D := by
    have h := norm_symbol_shift_sub_le b hb hom D D0 (jets 1 (by decide)) ξ 0
    simpa only [zero_add, homogeneous_value_zero hom, sub_zero] using h
  have lB (ξ : E) : ‖lc ξ‖ ≤ L*D := by
    let ζ := tau⁻¹ • ξ
    have scale : ‖ξ‖ = tau * ‖ζ‖ := by
      dsimp only [ζ]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr τp.le), ← mul_assoc, mul_inv_cancel₀ τp.ne', one_mul]
    have cb : ‖fixedRadianProfile cut ξ‖ * ‖ξ‖ ≤ C := by
      change ‖(cut ζ).re‖ * ‖ξ‖ ≤ C
      rw [← Complex.norm_real, hcut, scale]
      have e := SchwartzMap.norm_pow_mul_le_seminorm ℝ cut 1 ζ
      rw [pow_one] at e
      calc
        _ = tau * (‖ζ‖ * ‖cut ζ‖) := by ring
        _ ≤ C := mul_le_mul_of_nonneg_left e τp.le
    calc
      _ ≤ ‖fixedRadianProfile cut ξ‖ * (‖ξ‖*D) := by
        dsimp only [lc]
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (bBound ξ) (norm_nonneg _)
      _ ≤ C*D := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right cb D0
      _ ≤ L*D := mul_le_mul_of_nonneg_right (le_max_left _ _) D0
  let q (η : E) := (1/2 : ℝ) • η
  let Δ (η ξ : E) := b (ξ + tau • q η) - b ξ
  let ℓ (η ξ : E) := lc (ξ + tau • q η)
  have gap (η ξ : E) : regularizedPrincipalGapSymbol cut b (η,ξ) = Δ η ξ - ℓ η ξ := by
    simp only [regularizedPrincipalGapSymbol, slantedRadianSymbol, q, Δ, ℓ, lc, fixedInfraredSymbol,
      zero_smul, smul_zero, add_zero, fixedRadianProfile, SchwartzMap.zero_apply, Complex.zero_re]
    ring
  have δ (η ξ : E) : ‖Δ η ξ‖ ≤ ‖tau • q η‖ * D :=
    norm_symbol_shift_sub_le b hb hom D D0 (jets 1 (by decide)) _ _
  have scale (η : E) : ‖tau • q η‖ = (tau / 2)*‖η‖ := by
    simp only [q, norm_smul, Real.norm_of_nonneg τp.le, Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
    ring
  have plain (η : E) : ‖tau • q η‖ * D ≤ M*D*‖η‖ := by
    rw [scale η]
    have h := mul_le_mul_of_nonneg_left (le_max_left 1 Ks) (div_nonneg τp.le (by norm_num : (0:ℝ) ≤ 2))
    calc
      _ = (tau / 2 * 1 * D) * ‖η‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h D0) (norm_nonneg _)
  have shifted (η : E) : Ks*(‖tau • q η‖*D) ≤ M*D*‖η‖ := by
    rw [scale η]
    have h := mul_le_mul_of_nonneg_left (le_max_right 1 Ks) (div_nonneg τp.le (by norm_num : (0:ℝ) ≤ 2))
    calc
      _ = (((tau/2)*Ks)*D)*‖η‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h D0) (norm_nonneg _)
  have sum (η : E) : M*D*‖η‖+L*D ≤ (M+L)*D*(1+‖η‖) := by
    nlinarith only [mul_nonneg M0 D0, mul_nonneg (mul_nonneg L0 D0) (norm_nonneg η)]
  refine ⟨wholeM,fun η ξ => ?_,?_⟩
  · rw [gap]
    exact (norm_sub_le _ _).trans ((add_le_add ((δ η ξ).trans (plain η)) (lB _)).trans (sum η))
  intro η u g
  let p := ENNReal.ofReal 3
  let Y := eLpNorm (u : E → ℂ) p volume
  have lP (v : SchwartzMap E ℂ) : MemLp (radianAction lc v) p volume ∧
        eLpNorm (radianAction lc v) p volume ≤ ENNReal.ofReal (L*D)*eLpNorm (v : E → ℂ) p volume := by
    have h := low b hb hom D D0 (fun n h => jets n (h.trans (by decide))) v
    have s : Kl ≤ ENNReal.ofReal L := by
      rw [← ENNReal.ofReal_toReal Klf.ne]
      exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
    refine ⟨h.1,h.2.trans ?_⟩
    rw [ENNReal.ofReal_mul L0]
    exact mul_le_mul_right' (mul_le_mul_right' s _) _
  have low' := radian_shift_preserves_L3_bound lc (ENNReal.ofReal (L*D)) lP (q η) u
  have hi := shift b hb hom D D0 jets (tau • q η) u
  have dM : Measurable (Δ η) := (bM.comp (measurable_id.add measurable_const)).sub bM
  have llM : Measurable (ℓ η) := lM.comp (measurable_id.add measurable_const)
  have eq : g = radianAction (Δ η) u - radianAction (ℓ η) u := by
    change radianAction (fun ξ => regularizedPrincipalGapSymbol cut b (η,ξ)) u = _
    simp_rw [gap]
    exact radian_action_bounded_symbol_sub (Δ η) (ℓ η) dM llM _ _ (δ η) (fun ξ => lB _) u
  rw [eq]
  refine ⟨hi.1.sub low'.1,(eLpNorm_sub_le hi.1.1 low'.1.1 (by norm_num [p])).trans ?_⟩
  have coeff : ENNReal.ofReal (Ks*(‖tau • q η‖*D)) + ENNReal.ofReal (L*D) ≤
      ENNReal.ofReal ((M+L)*D*(1+‖η‖)) := by
    rw [← ENNReal.ofReal_add (mul_nonneg Ks0 (mul_nonneg (norm_nonneg _) D0)) (mul_nonneg L0 D0)]
    exact ENNReal.ofReal_le_ofReal ((add_le_add (shifted η) le_rfl).trans (sum η))
  exact (add_le_add hi.2 low'.2).trans (by rw [← add_mul]; exact mul_le_mul_right' coeff Y)

end Burnett.A03
