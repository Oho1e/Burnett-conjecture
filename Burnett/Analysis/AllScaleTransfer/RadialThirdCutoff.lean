import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace Burnett.Analysis.CapFourier

open MeasureTheory Set Metric Burnett.A02.FrequencySplit
open scoped ContDiff

/-- The same unit-ball bump at all scales, equal to one up to radius one. -/
def radialBallBump : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩

def radialLowCutoff (r : ℝ) (ξ : E) : ℝ := radialBallBump (r⁻¹ • ξ)

def radialAnnularCutoff (r : ℝ) (ξ : E) : ℝ := radialLowCutoff r ξ - radialLowCutoff (r/2) ξ

private theorem norm_inverse_scale {r : ℝ} (hr : 0 < r) (ξ : E) :
    ‖r⁻¹ • ξ‖ = ‖ξ‖ / r := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), div_eq_inv_mul]

theorem radialLowCutoff_eq_one {r : ℝ} (hr : 0 < r) {ξ : E} (hξ : ‖ξ‖ ≤ r) :
    radialLowCutoff r ξ = 1 := by
  apply radialBallBump.one_of_mem_closedBall
  rw [mem_closedBall, dist_zero_right, norm_inverse_scale hr]
  exact (div_le_one hr).2 hξ

theorem radialLowCutoff_eq_zero {r : ℝ} (hr : 0 < r) {ξ : E} (hξ : 2*r ≤ ‖ξ‖) :
    radialLowCutoff r ξ = 0 := by
  apply radialBallBump.zero_of_le_dist
  rw [dist_zero_right, norm_inverse_scale hr]
  exact (le_div_iff₀ hr).2 hξ

theorem radialAnnularCutoff_nonzero {r : ℝ} (hr : 0 < r) {ξ : E}
    (hξ : radialAnnularCutoff r ξ ≠ 0) : r/2 < ‖ξ‖ ∧ ‖ξ‖ < 2*r := by
  constructor
  · by_contra! h
    apply hξ
    unfold radialAnnularCutoff
    rw [radialLowCutoff_eq_one hr (by linarith), radialLowCutoff_eq_one (by positivity) h, sub_self]
  · by_contra! h
    apply hξ
    unfold radialAnnularCutoff
    rw [radialLowCutoff_eq_zero hr h, radialLowCutoff_eq_zero (by positivity) (by linarith), sub_self]

theorem radialLowCutoff_scale_le {r : ℝ} (hr : 0 < r) {s : ℕ} (hs : 3 ≤ s) :
    2 * (r/(2 : ℝ)^s) ≤ r/4 := by
  have h8 : (8 : ℝ) ≤ (2 : ℝ)^s := calc
    8 = (2 : ℝ)^3 := by norm_num
    _ ≤ (2 : ℝ)^s := pow_le_pow_right₀ (by norm_num) hs
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).2
  nlinarith [mul_nonneg hr.le (sub_nonneg.mpr h8)]

/-- The signed third frequency is in the same fixed thickened high annulus. -/
theorem signed_productFrequency_mem_annulus {r : ℝ} {p q : E} (hp : ‖p‖ ≤ r/4)
    (hq : r/2 ≤ ‖q‖ ∧ ‖q‖ ≤ 2*r) :
    r/4 ≤ ‖-(p+q)‖ ∧ ‖-(p+q)‖ ≤ (9/4)*r := by
  rw [norm_neg]
  have back := norm_sub_le (p+q) p
  rw [add_sub_cancel_left] at back
  have forward := norm_add_le p q
  exact ⟨by linarith [hq.1], by linarith [hq.2]⟩

private def productOuterBump : ContDiffBump (0 : E) := ⟨3, 4, by norm_num, by norm_num⟩

/-- One fixed smooth thick-annulus profile rescaled at the high frequency. -/
def thickProductCutoff (r : ℝ) (ξ : E) : ℝ :=
  productOuterBump (r⁻¹ • ξ) - radialLowCutoff (r/8) ξ

private theorem productOuterBump_eq_one {r : ℝ} (hr : 0 < r) {ξ : E} (hξ : ‖ξ‖ ≤ 3*r) :
    productOuterBump (r⁻¹ • ξ) = 1 := by
  apply productOuterBump.one_of_mem_closedBall
  rw [mem_closedBall, dist_zero_right, norm_inverse_scale hr]
  exact (div_le_iff₀ hr).2 hξ

theorem thickProductCutoff_eq_one {r : ℝ} (hr : 0 < r) {ξ : E}
    (hlo : r/4 ≤ ‖ξ‖) (hhi : ‖ξ‖ ≤ 3*r) : thickProductCutoff r ξ = 1 := by
  unfold thickProductCutoff
  rw [productOuterBump_eq_one hr hhi, radialLowCutoff_eq_zero (by positivity) (by linarith), sub_zero]

theorem thickProductCutoff_smooth (r : ℝ) : ContDiff ℝ ∞ (thickProductCutoff r) := by
  have scale (t : ℝ) : ContDiff ℝ ∞ (fun ξ : E => t⁻¹ • ξ) := contDiff_const.smul contDiff_id
  exact (productOuterBump.contDiff.comp (scale r)).sub
    (radialBallBump.contDiff.comp (scale (r/8)))

theorem tsupport_thickProductCutoff_subset {r : ℝ} (hr : 0 < r) :
    tsupport (thickProductCutoff r) ⊆ {ξ | r/8 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 4*r} := by
  apply closure_minimal _ ((isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const))
  intro ξ hξ
  change thickProductCutoff r ξ ≠ 0 at hξ
  have hlo : r/8 < ‖ξ‖ := by
    by_contra! h
    apply hξ
    unfold thickProductCutoff
    rw [productOuterBump_eq_one hr (by linarith), radialLowCutoff_eq_one (by positivity) h, sub_self]
  have hhi : ‖ξ‖ < 4*r := by
    by_contra! h
    apply hξ
    have hout : productOuterBump (r⁻¹ • ξ) = 0 := by
      apply productOuterBump.zero_of_le_dist
      rw [dist_zero_right, norm_inverse_scale hr]
      exact (le_div_iff₀ hr).2 h
    unfold thickProductCutoff
    rw [hout, radialLowCutoff_eq_zero (by positivity) (by linarith), sub_self]
  exact ⟨hlo.le, hhi.le⟩

/-- Insertion of the third cutoff on the actual radian Fourier integrand.
The complex coefficient can contain any remaining angular or radial symbol. -/
theorem radianWeight_mul_thickProductCutoff_eq {r : ℝ} (hr : 0 < r)
    (low high : E → ℝ) (hlow : ∀ p, low p ≠ 0 → ‖p‖ ≤ r/4)
    (hhigh : ∀ q, high q ≠ 0 → r/2 ≤ ‖q‖ ∧ ‖q‖ ≤ 2*r)
    (f g w : SchwartzMap E ℂ) :
    radianWeight (fun x => low x.1 * high x.2 * thickProductCutoff r (-(x.1+x.2))) f g w =
      radianWeight (fun x => low x.1 * high x.2) f g w := by
  funext x
  have weight : low x.1 * high x.2 * thickProductCutoff r (-(x.1 + x.2)) =
      low x.1 * high x.2 := by
    by_cases hp : low x.1 = 0
    · simp only [hp, zero_mul]
    by_cases hq : high x.2 = 0
    · simp only [hq, mul_zero, zero_mul]
    have h := signed_productFrequency_mem_annulus (hlow x.1 hp) (hhigh x.2 hq)
    rw [thickProductCutoff_eq_one hr h.1 (by linarith [h.2]), mul_one]
  simp only [radianWeight, weight]

/-- The actual normalized Fourier pairing is unchanged on the dyadic low/high
block, for either a low-pass low factor or an annular low factor. -/
theorem radianTrilinear_dyadic_thirdCutoff_eq {r : ℝ} (hr : 0 < r) {s : ℕ} (hs : 3 ≤ s)
    (low : E → ℝ) (hlow : ∀ p, low p ≠ 0 → ‖p‖ ≤ 2*(r/(2 : ℝ)^s))
    (m : Joint → ℂ) (f g w : SchwartzMap E ℂ) :
    ((tau^8)⁻¹ • ∫ x, m x *
      radianWeight (fun y => low y.1 * radialAnnularCutoff r y.2 * thickProductCutoff r (-(y.1+y.2)))
        f g w x) =
    ((tau^8)⁻¹ • ∫ x, m x * radianWeight (fun y => low y.1 * radialAnnularCutoff r y.2) f g w x) := by
  rw [radianWeight_mul_thickProductCutoff_eq hr low (radialAnnularCutoff r)
    (fun p hp => (hlow p hp).trans (radialLowCutoff_scale_le hr hs))
    (fun q hq => let h := radialAnnularCutoff_nonzero hr hq; ⟨h.1.le, h.2.le⟩)]

end Burnett.Analysis.CapFourier
