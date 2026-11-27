import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedSpatialFourierSeries
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Burnett.A03

open Metric Set Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped ContDiff RealInnerProductSpace BigOperators

private def modePhaseLinear (P : ℝ) (k : Index → ℤ) : CoordinateSpace →L[ℝ] ℝ :=
  (2 * Real.pi) • innerSL ℝ (spatialModeFrequency P k)

private theorem mode_phase_linear_apply (P : ℝ) (k : Index → ℤ) (y : CoordinateSpace) :
    modePhaseLinear P k y = spatialModePhase P k y := by
  unfold modePhaseLinear spatialModePhase
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply, real_inner_comm]

private theorem mode_phase_linear_norm (P : ℝ) (k : Index → ℤ) :
    ‖modePhaseLinear P k‖ = (|2 * Real.pi| * |(2 * P)⁻¹|) * ‖spatialLatticeVector k‖ := by
  simp only [modePhaseLinear, norm_smul, innerSL_apply_norm, spatialModeFrequency, Real.norm_eq_abs, mul_assoc]

private theorem norm_linear_trigonometric_jet (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (derivativeBound : ∀ (n : ℕ) (x : ℝ), |iteratedDeriv n g x| ≤ 1)
    (L : CoordinateSpace →L[ℝ] ℝ) (n : ℕ) (y : CoordinateSpace) :
    ‖iteratedFDeriv ℝ n (g ∘ L) y‖ ≤ ‖L‖ ^ n := by
  have hn : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  rw [L.iteratedFDeriv_comp_right hg y hn]
  have comp := (iteratedFDeriv ℝ n g (L y)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at comp
  exact comp.trans (mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (derivativeBound n (L y)))

private theorem norm_rescale_profile_jet_le (g : CoordinateSpace → ℝ) (hg : ContDiff ℝ ∞ g)
    (c : CoordinateSpace) (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) (x : CoordinateSpace) :
    ‖iteratedFDeriv ℝ n (fun y => g (ℓ⁻¹ • (y - c))) x‖ ≤
      ‖iteratedFDeriv ℝ n g (ℓ⁻¹ • (x - c))‖ * (ℓ⁻¹) ^ n := by
  let D : CoordinateSpace →L[ℝ] CoordinateSpace := ℓ⁻¹ • ContinuousLinearMap.id ℝ CoordinateSpace
  have DApply (y : CoordinateSpace) : D y = ℓ⁻¹ • y := rfl
  have DNorm : ‖D‖ ≤ ℓ⁻¹ := D.opNorm_le_bound (inv_nonneg.mpr hℓ.le) (fun y => by
    rw [DApply, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)])
  change ‖iteratedFDeriv ℝ n (fun y => (g ∘ D) (y - c)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub n c x, D.iteratedFDeriv_comp_right hg (x - c) (by exact_mod_cast le_top)]
  have comp := (iteratedFDeriv ℝ n g (D (x - c))).norm_compContinuousLinearMap_le (fun _ => D)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, DApply] at comp
  exact comp.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) DNorm _) (norm_nonneg _))

/-- The actual cosine and sine profiles have global operator-norm spatial
jets with the scaling \(\ell^{-r}(1+\|k\|_2)^r\) for \(0\le r\le2\).
One constant is chosen before the cutoff, mode, center and positive scale. -/
theorem exists_localized_spatial_mode_profile_jet_bound (P : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ρ : CoordinateSpace → ℝ), ContDiff ℝ ∞ ρ →
        ∀ B : ℝ, 0 ≤ B →
          (∀ j : ℕ, j ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ j ρ y‖ ≤ B) →
          ∀ (k : Index → ℤ) (c : CoordinateSpace) (ℓ : ℝ), 0 < ℓ →
            ∀ n : ℕ, n ≤ 2 → ∀ x : CoordinateSpace,
              ‖iteratedFDeriv ℝ n (localizedSpatialCosineProfile P k ρ c ℓ) x‖ ≤
                C * B * (ℓ⁻¹)^n * (spatialLatticeWeight k)^n ∧
              ‖iteratedFDeriv ℝ n (localizedSpatialSineProfile P k ρ c ℓ) x‖ ≤
                C * B * (ℓ⁻¹)^n * (spatialLatticeWeight k)^n := by
  let A := max 1 (|2 * Real.pi| * |(2 * P)⁻¹|)
  have hAone : 1 ≤ A := le_max_left _ _
  have hA : 0 ≤ A := zero_le_one.trans hAone
  let C := (2 * A)^2
  refine ⟨C, sq_nonneg _, ?_⟩
  intro ρ hρ B hB cutoffJets k c ℓ hℓ n hn x
  let L := modePhaseLinear P k
  let w := spatialLatticeWeight k
  have hwOne : 1 ≤ w := le_add_of_nonneg_right (norm_nonneg (spatialLatticeVector k))
  have hw : 0 ≤ w := zero_le_one.trans hwOne
  have LNorm : ‖L‖ ≤ A * w := by
    rw [show ‖L‖ = _ from mode_phase_linear_norm P k]
    calc
      _ ≤ A * ‖spatialLatticeVector k‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      _ ≤ A * w := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hA
  have awOne : 1 ≤ A * w := one_le_mul_of_one_le_of_one_le hAone hwOne
  have twoAOne : 1 ≤ 2 * A := by linarith
  have scalar (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
      (hDeriv : ∀ (n : ℕ) (y : ℝ), |iteratedDeriv n g y| ≤ 1) :
      ‖iteratedFDeriv ℝ n (fun x => ρ (ℓ⁻¹ • (x - c)) * g (L (ℓ⁻¹ • (x - c)))) x‖ ≤
        C * B * (ℓ⁻¹)^n * w^n := by
    let q : CoordinateSpace → ℝ := fun y => ρ y * g (L y)
    have hq : ContDiff ℝ ∞ q := hρ.mul (hg.comp L.contDiff)
    have nInf : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have product (y : CoordinateSpace) : ‖iteratedFDeriv ℝ n q y‖ ≤
        (2 : ℝ)^n * B * (A * w)^n := by
      have sum : (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ)) = (2 : ℝ)^n := by
        exact_mod_cast Nat.sum_range_choose n
      calc
        _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j ρ y‖ *
            ‖iteratedFDeriv ℝ (n - j) (g ∘ L) y‖ :=
          norm_iteratedFDeriv_mul_le hρ (hg.comp L.contDiff) y nInf
        _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * B * (A * w)^n := by
          apply Finset.sum_le_sum
          intro j hj
          have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          have hjg : ‖iteratedFDeriv ℝ (n - j) (g ∘ L) y‖ ≤ (A * w)^n :=
            (norm_linear_trigonometric_jet g hg hDeriv L (n - j) y).trans
              ((pow_le_pow_left₀ (norm_nonneg _) LNorm _).trans
                (pow_le_pow_right₀ awOne (Nat.sub_le _ _)))
          exact mul_le_mul (mul_le_mul_of_nonneg_left (cutoffJets j (hjn.trans hn) y) (by positivity))
            hjg (norm_nonneg _) (by positivity)
        _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, sum]
    change ‖iteratedFDeriv ℝ n (fun x => q (ℓ⁻¹ • (x - c))) x‖ ≤ _
    calc
      _ ≤ ‖iteratedFDeriv ℝ n q (ℓ⁻¹ • (x - c))‖ * (ℓ⁻¹)^n :=
        norm_rescale_profile_jet_le q hq c ℓ hℓ n x
      _ ≤ ((2 : ℝ)^n * B * (A * w)^n) * (ℓ⁻¹)^n :=
        mul_le_mul_of_nonneg_right (product _) (pow_nonneg (inv_nonneg.mpr hℓ.le) _)
      _ = (2 * A)^n * B * (ℓ⁻¹)^n * w^n := by simp only [mul_pow]; ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ twoAOne hn) hB)
            (pow_nonneg (inv_nonneg.mpr hℓ.le) _)) (pow_nonneg hw _)
  constructor
  · simpa only [L, mode_phase_linear_apply, localizedSpatialCosineProfile] using
      scalar Real.cos Real.contDiff_cos Real.abs_iteratedDeriv_cos_le_one
  · simpa only [L, mode_phase_linear_apply, localizedSpatialSineProfile] using
      scalar Real.sin Real.contDiff_sin Real.abs_iteratedDeriv_sin_le_one

end Burnett.A03
