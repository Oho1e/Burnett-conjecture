import Burnett.Analysis.CubicEnergy.HighSlotCommutator.ComparableCoefficientActualPacking
import Burnett.Analysis.PrincipalEnergy.Commutator.ParaproductCover

set_option autoImplicit false
set_option maxHeartbeats 2800000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open Burnett.Analysis.CarlesonEmbedding (finite_ball_carleson_square_le)
open MeasureTheory Metric Finset
open scoped ENNReal NNReal BigOperators

/-- The same normalized real coefficient used by the commutator yields the
weighted square estimate with any test dominated throughout the scale balls. -/
theorem exists_realAnnularCoefficient_embedded_square_bound (profile : SchwartzMap E ℂ)
    (hc : HasCompactSupport (profile : E → ℂ))
    (hAnn : ∀ ξ, profile ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) :
    ∃ C : ℝ≥0∞, C<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {t T : ℝ}, 0<t → ∀ (J : Finset ℕ), (∀ j ∈ J, dyadicScale t j≤T) →
      ∀ (G : ℕ → E → ℝ) (M : E → ℝ), (∀ j, Measurable (G j)) → (∀ j x, 0≤G j x) →
      Measurable M → (∀ x, 0≤M x) →
      (∀ j ∈ J, ∀ x y, y ∈ ball x (dyadicScale t j) → G j x ≤ M y) →
      (∑ j ∈ J, ∫⁻ x : E,
        ENNReal.ofReal (((dyadicScale t j)⁻¹*(windowTest profile D (dyadicScale t j) x).re)^2) *
          ENNReal.ofReal ((G j x)^2)) ≤
        C * (L : ℝ≥0∞)^2 * ∫⁻ x : E, ENNReal.ofReal ((M x)^2) := by
  obtain ⟨C,hC,pack⟩ := exists_realAnnularCoefficient_ball_square_packing profile hc hAnn
  refine ⟨256*C,by finiteness,?_⟩
  intro D L hL t T ht J hJ G M hG hGN hM hMN dom
  let w j (x : E) :=
    ENNReal.ofReal (((dyadicScale t j)⁻¹*(windowTest profile D (dyadicScale t j) x).re)^2)
  let ν j := (volume : Measure E).withDensity (w j)
  have hw (j : ℕ) : Measurable (w j) := by
    unfold w
    have hW := (windowTest profile D (dyadicScale t j)).continuous
    exact ((continuous_const.mul (Complex.continuous_re.comp hW)).pow 2).measurable.ennreal_ofReal
  have hfin : C*(L : ℝ≥0∞)^2 ≠ ⊤ := ENNReal.mul_ne_top hC.ne (by finiteness)
  have packν (center : E) (R : ℝ) (hR : 0<R) :
      (∑ j ∈ J.filter (fun j => dyadicScale t j≤R), ν j (ball center R)) ≤
        (C*(L : ℝ≥0∞)^2)*volume (ball center R) := by
    simp only [ν,withDensity_apply _ measurableSet_ball]
    rw [← lintegral_finset_sum _ (fun j _ => hw j)]
    exact pack D L hL center hR ht _ (fun j hj => (mem_filter.mp hj).2)
  have hs (j : ℕ) (hj : j∈J) : 0<dyadicScale t j ∧ dyadicScale t j≤T :=
    ⟨by unfold dyadicScale; positivity,hJ j hj⟩
  have h := finite_ball_carleson_square_le J (dyadicScale t) T hs ν _ hfin packν G hG hGN M hM hMN dom
  simp_rw [ν,fun j => lintegral_withDensity_eq_lintegral_mul volume (hw j)
    ((hG j).pow_const 2).ennreal_ofReal] at h
  simpa only [w,mul_assoc] using h

end Burnett.A06
