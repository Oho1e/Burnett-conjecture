import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedModeFourierMoment
import Burnett.Analysis.SpatialFreezing.SpatialLatticeSummability

set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Set Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open Burnett.A02.FrequencySplit
open scoped BigOperators ContDiff FourierTransform

private theorem patch_moment_nonneg (r : ℕ) (f : E → ℂ) : 0 ≤ patchFourierMoment r f :=
  integral_nonneg fun _ => mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)

private theorem spatial_frequency_weight_le (P : ℝ) (hP : 0 < P) (k : Index → ℤ) :
    1 + ‖spatialModeFrequency P k‖ ≤ max 1 (2 * P)⁻¹ * spatialLatticeWeight k := by
  have hp : 0 ≤ (2 * P)⁻¹ := by positivity
  rw [spatialModeFrequency, norm_smul, Real.norm_of_nonneg hp, spatialLatticeWeight, mul_add, mul_one]
  exact add_le_add (le_max_left _ _)
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- For both actual real modes, the angular coefficient budget has a
center-uniform absolutely summable absolute Fourier moment of order at
most two. The explicit scale is `ℓ * (ℓ ^ r)⁻¹`. -/
theorem exists_summable_localized_mode_fourier_moments
    (L r : ℕ) (hL : 7 < L) (hr : r ≤ 2) (P : ℝ) (hP : 0 < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hSupport : tsupport ρ ⊆ ball (0 : E) P) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (c : E) (ℓ : ℝ) (hℓ : 0 < ℓ), ∀ M : ℝ, 0 ≤ M →
        ∀ D : (Index → ℤ) → Fin 2 → ℝ,
        (∀ k j, 0 ≤ D k j ∧ D k j ≤ M * ℓ / spatialLatticeWeight k ^ L) →
        let a (k : Index → ℤ) := ∑ j : Fin 2, D k j * patchFourierMoment r
          (localizedRealSpatialModeSchwartz P k ρ hρ hSupport c ℓ hℓ j)
        Summable a ∧ (∑' k, a k) ≤ K * M * (ℓ * (ℓ ^ r)⁻¹) := by
  let ρS := patchCutoffSchwartz P ρ hρ hSupport
  let T := 2 * ((max 1 (2 * P)⁻¹) ^ r * 2 ^ r *
    (patchFourierMoment 0 ρS + patchFourierMoment r ρS))
  let w (k : Index → ℤ) := spatialLatticeWeight k
  let W (k : Index → ℤ) := w k ^ r / w k ^ L
  have wt (k : Index → ℤ) : 0 < w k := by unfold w spatialLatticeWeight; positivity
  have hT : 0 ≤ T := by
    have hMax : 0 ≤ max 1 (2 * P)⁻¹ := le_trans zero_le_one (le_max_left _ _)
    exact mul_nonneg (by norm_num) (mul_nonneg (by positivity)
      (add_nonneg (patch_moment_nonneg _ _) (patch_moment_nonneg _ _)))
  have hW : Summable W := summable_spatial_lattice_weighted_decay L r hL hr
  have W0 (k : Index → ℤ) : 0 ≤ W k := div_nonneg (pow_nonneg (wt k).le _) (pow_nonneg (wt k).le _)
  let K := 2 * T * (∑' k, W k)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) hT) (tsum_nonneg W0)
  refine ⟨K, hK, ?_⟩
  intro c ℓ hℓ M hM D hD a
  let f (k : Index → ℤ) (j : Fin 2) := localizedRealSpatialModeSchwartz P k ρ hρ hSupport c ℓ hℓ j
  let C := 2 * M * ℓ * (ℓ ^ r)⁻¹ * T
  have C0 : 0 ≤ C := by unfold C; positivity
  have eachProfile (k : Index → ℤ) (j : Fin 2) :
      patchFourierMoment r (f k j) ≤ (ℓ ^ r)⁻¹ * T * w k ^ r := by
    have lift := pow_le_pow_left₀ (by positivity) (spatial_frequency_weight_le P hP k) r
    rw [mul_pow] at lift
    have base := localized_real_spatial_mode_fourier_moment P k ρ hρ hSupport c ℓ hℓ j r
    refine base.trans ?_
    have m0 : 0 ≤ patchFourierMoment 0 ρS + patchFourierMoment r ρS :=
      add_nonneg (patch_moment_nonneg _ _) (patch_moment_nonneg _ _)
    calc
      _ ≤ (ℓ ^ r)⁻¹ * (2 * ((max 1 (2 * P)⁻¹ ^ r * w k ^ r) * 2 ^ r *
          (patchFourierMoment 0 ρS + patchFourierMoment r ρS))) := by gcongr
      _ = _ := by dsimp only [T]; ring
  have each (k : Index → ℤ) (j : Fin 2) :
      D k j * patchFourierMoment r (f k j) ≤ (C / 2) * W k := by
    calc
      _ ≤ (M * ℓ / w k ^ L) * ((ℓ ^ r)⁻¹ * T * w k ^ r) :=
        mul_le_mul (hD k j).2 (eachProfile k j) (patch_moment_nonneg _ _)
          (div_nonneg (mul_nonneg hM hℓ.le) (pow_nonneg (wt k).le _))
      _ = _ := by dsimp only [C, W]; rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]; ring
  have an (k : Index → ℤ) : 0 ≤ a k := Finset.sum_nonneg fun j _ =>
    mul_nonneg (hD k j).1 (patch_moment_nonneg _ _)
  have upper (k : Index → ℤ) : a k ≤ C * W k := by
    calc
      _ ≤ ∑ _j : Fin 2, (C / 2) * W k := Finset.sum_le_sum fun j _ => each k j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hMajor : Summable (fun k => C * W k) := hW.mul_left C
  have ha : Summable a := Summable.of_nonneg_of_le an upper hMajor
  refine ⟨ha, (ha.tsum_le_tsum upper hMajor).trans_eq ?_⟩
  rw [tsum_mul_left]
  dsimp only [C, K]
  ring

end Burnett.A03
