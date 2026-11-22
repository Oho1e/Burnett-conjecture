import Burnett.Analysis.AngularCaps.SmoothCapFamily
import Burnett.Analysis.Fourier.Projection

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open MeasureTheory Set Burnett.Fourier
open scoped BigOperators ENNReal

private theorem finite_cap_square_L2 (I : Finset Vec) (b : Vec → Vec → ℝ)
    (M : ↑I → BoundedSymbol Vec) (hM : ∀ w ξ, M w ξ = (b w ξ : ℂ))
    (hrange : ∀ w ∈ I, ∀ ξ, 0 ≤ b w ξ ∧ b w ξ ≤ 1)
    (L : ℝ) (hoverlap : ∀ ξ : Vec, ξ ≠ 0 → ((capSupportCenters I b ξ).card : ℝ) ≤ L)
    (f : ComplexL2 Vec) :
    (∑ w : ↑I, ‖fourierMultiplier (M w) f‖^2) ≤ L * ‖f‖^2 := by
  classical
  let g := fourierL2Equiv f
  have intg : Integrable (fun ξ => ‖g ξ‖^2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  have intw (w : ↑I) : Integrable (fun ξ => ‖M w ξ‖^2 * ‖g ξ‖^2) := by
    have h := (memLp_two_iff_integrable_sq_norm (symbol_product_memLp (M w) g).1).mp
      (symbol_product_memLp (M w) g)
    simpa only [norm_mul,mul_pow] using h
  have energy (w : ↑I) :
      ‖fourierMultiplier (M w) f‖^2 = ∫ ξ, ‖M w ξ‖^2*‖g ξ‖^2 := by
    rw [fourierMultiplier_apply,LinearIsometryEquiv.norm_map,l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [symbolL2_ae (M w) g] with ξ h
    rw [h,norm_mul,mul_pow]
  have total_energy : ‖f‖^2 = ∫ ξ, ‖g ξ‖^2 := by
    rw [← l2_norm_sq_integral,show ‖g‖ = ‖f‖ from LinearIsometryEquiv.norm_map _ _]
  simp_rw [energy]
  rw [← integral_finset_sum _ (fun w _ => intw w),total_energy,← integral_const_mul]
  apply integral_mono_ae (integrable_finset_sum _ (fun w _ => intw w)) (intg.const_mul _)
  have hne : ∀ᵐ ξ : Vec ∂volume, ξ ≠ 0 := by simp [ae_iff]
  filter_upwards [hne] with ξ hξ
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  calc
    _ ≤ ∑ w : ↑I, if ξ ∈ tsupport (b w) then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro w _
      rw [hM w,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hrange w w.property ξ).1]
      by_cases hw : ξ ∈ tsupport (b w)
      · rw [if_pos hw]
        exact pow_le_one₀ (hrange w w.property ξ).1 (hrange w w.property ξ).2
      · have hz : b w ξ = 0 := by
          by_contra h
          exact hw (subset_tsupport _ h)
        simp [if_neg hw,hz]
    _ = ((capSupportCenters I b ξ).card : ℝ) := by
      rw [Finset.univ_eq_attach,Finset.sum_attach I (fun w => if ξ ∈ tsupport (b w) then (1 : ℝ) else 0)]
      unfold capSupportCenters
      rw [← Finset.sum_filter]
      simp
    _ ≤ L := hoverlap ξ hξ

/-- Plancherel uses the actual two symbols on the same center set and the
finite closed-support overlap already proved for that family. -/
theorem actual_capMultipliers_angular_L2 {m : Form} {δ η inner outer enlarged D : ℝ}
    (S : SmoothThinConeCaps m δ η inner outer enlarged D)
    (M P : ↑S.centers → BoundedSymbol Vec)
    (hM : ∀ w ξ, M w ξ = (capMultiplier S.centers m δ η inner outer w ξ : ℂ))
    (hP : ∀ w ξ, P w ξ = (enlargedCapMultiplier m δ η outer enlarged w ξ : ℂ))
    (f : ComplexL2 Vec) :
    (∑ w : ↑S.centers, ‖fourierMultiplier (M w) f‖^2) ≤ (17:ℝ)^4*‖f‖^2 ∧
      (∑ w : ↑S.centers, ‖fourierMultiplier (P w) f‖^2) ≤ (81:ℝ)^4*‖f‖^2 :=
  ⟨finite_cap_square_L2 S.centers _ M hM S.base_range _ (fun ξ hξ => (S.support_overlap ξ hξ).1) f,
    finite_cap_square_L2 S.centers _ P hP S.enlarged_range _ (fun ξ hξ => (S.support_overlap ξ hξ).2) f⟩

end Burnett.Analysis.ProjectiveNullCaps
