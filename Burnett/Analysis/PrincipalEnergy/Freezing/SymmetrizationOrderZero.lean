import Burnett.Analysis.PrincipalEnergy.Freezing.SchwartzOrderZeroCommutator
import Burnett.Analysis.PrincipalEnergy.Freezing.SymmetrizationCoordinate
import Burnett.Analysis.PrincipalEnergy.Freezing.PatchLpDuality

set_option autoImplicit false
set_option maxHeartbeats 1900000
noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ContDiff ENNReal

/-- Quantitative W¹,³ control for the difference of the actual two placements.
The derivative bound contains at most one derivative of the field. -/
theorem exists_separated_skew_left_remainder_W13_bound :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 7 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ f u : SchwartzMap E ℂ,
        let p := ENNReal.ofReal 3
        let R := separatedSkewLeftRemainder f b u
        MemLp R p volume ∧
          eLpNorm R p volume ≤ ENNReal.ofReal (K * D * patchFourierFirstMoment f) *
            eLpNorm (u : E → ℂ) p volume ∧
          ∀ j : Index, let dR (x : E) := fderiv ℝ R x (EuclideanSpace.single j 1)
            MemLp dR p volume ∧ eLpNorm dR p volume ≤
              ENNReal.ofReal (K * D * patchFourierFirstMoment f) *
                eLpNorm (energyPartial j u : E → ℂ) p volume +
              ENNReal.ofReal (K * D * patchFourierFirstMoment (energyPartial j f)) *
                eLpNorm (u : E → ℂ) p volume := by
  obtain ⟨K, hK, estimate⟩ := exists_radian_commutator_order_zero_L3_bound
  refine ⟨K, hK, ?_⟩
  intro b hb hom D hD jet f u p R
  let c : ℂ := -Complex.I / 2
  have hcnorm : ‖c‖ₑ ≤ 1 := by
    rw [← ofReal_norm_eq_enorm]
    simp only [c, norm_div, norm_neg, Complex.norm_I, Complex.norm_ofNat]
    norm_num
  have value (g v : SchwartzMap E ℂ) :
      MemLp (separatedSkewLeftRemainder g b v) p volume ∧
        eLpNorm (separatedSkewLeftRemainder g b v) p volume ≤
          ENNReal.ofReal (K * D * patchFourierFirstMoment g) * eLpNorm (v : E → ℂ) p volume := by
    rw [separated_skew_left_remainder_eq_commutator]
    have h := estimate b hb hom D hD jet g v
    refine ⟨h.1.const_smul c, ?_⟩
    calc
      _ ≤ ‖c‖ₑ * eLpNorm (radianCommutator b g v) p volume := eLpNorm_const_smul_le
      _ ≤ _ := (mul_le_mul_right' hcnorm _).trans (by simpa only [one_mul] using h.2)
  refine ⟨(value f u).1, (value f u).2, ?_⟩
  intro j dR
  have h₁ := value f (energyPartial j u)
  have h₂ := value (energyPartial j f) u
  have same : dR = separatedSkewLeftRemainder f b (energyPartial j u) +
          separatedSkewLeftRemainder (energyPartial j f) b u :=
    funext fun x => (separated_skew_left_remainder_coordinate f b hb hom u j x).2
  rw [same]
  refine ⟨h₁.1.add h₂.1, ?_⟩
  exact (eLpNorm_add_le h₁.1.aestronglyMeasurable h₂.1.aestronglyMeasurable (by norm_num [p])).trans
    (add_le_add h₁.2 h₂.2)

/-- The actual coordinate derivative of the remainder is also its weak
derivative in the distribution pairing used by the patch L³ limit. -/
theorem separated_skew_left_remainder_weak_coordinate
    (f : SchwartzMap E ℂ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (u : SchwartzMap E ℂ) (j : Index)
    (hR : MemLp (separatedSkewLeftRemainder f b u) (ENNReal.ofReal 3) volume)
    (hd : MemLp (fun x => fderiv ℝ (separatedSkewLeftRemainder f b u) x (EuclideanSpace.single j 1))
      (ENNReal.ofReal 3) volume) :
    HasWeakCoordinateDerivative3 (hR.toLp _) (hd.toLp _) j := by
  intro φ
  let R := separatedSkewLeftRemainder f b u
  let d (x : E) := fderiv ℝ R x (EuclideanSpace.single j 1)
  let p := ENNReal.ofReal (3 / 2)
  have left : Integrable (fun x => R x * energyPartial j φ x) :=
    (energy_integral_three_three_halves hR ((energyPartial j φ).memLp p volume)).1
  have right : Integrable (fun x => d x * φ x) :=
    (energy_integral_three_three_halves hd (φ.memLp p volume)).1
  have zero : Integrable (fun x => R x * φ x) :=
    (energy_integral_three_three_halves hR (φ.memLp p volume)).1
  have hDiff : Differentiable ℝ R := fun x =>
    (separated_skew_left_remainder_coordinate f b hb hom u j x).1
  have eq := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := R) (g := (φ : E → ℂ)) (v := EuclideanSpace.single j 1)
    right left zero hDiff φ.differentiable
  rw [patch_lp_pair_toLp, patch_lp_pair_toLp]
  exact eq

end Burnett.A03
