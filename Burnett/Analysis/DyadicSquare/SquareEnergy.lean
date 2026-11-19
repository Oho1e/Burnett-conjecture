import Burnett.Analysis.DyadicSquare.SquareShell

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.DyadicSquare
open MeasureTheory Finset Burnett.Fourier
open scoped BigOperators

private theorem symbol_energy (a : BoundedSymbol Space) (v : ComplexL2 Space) :
    ‖symbolL2 a v‖^2 = ∫ ξ, ‖a ξ‖^2 * ‖v ξ‖^2 := by
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [symbolL2_ae a v] with ξ h
  rw [h,norm_mul,mul_pow]

private theorem integrable_energy (a : BoundedSymbol Space) (v : ComplexL2 Space) :
    Integrable (fun ξ => ‖a ξ‖^2 * ‖v ξ‖^2) := by
  have h := (memLp_two_iff_integrable_sq_norm (symbol_product_memLp a v).1).mp (symbol_product_memLp a v)
  simpa only [norm_mul,mul_pow] using h

/-- Plancherel and finite overlap give a bound independent of the number of bands for
the sum of the physical L² energies, on the entire L² space. -/
theorem annular_square_L2 (m : BoundedSymbol Space)
    (hcut : ∀ ξ, m ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) (t : ℝ) (ht : 0 < t) (I : Finset ℕ)
    (u : ComplexL2 Space) :
    (∑ k ∈ I, ‖fourierMultiplier (rescaleSymbol m ((2:ℝ)^k*t) (mul_pos (by positivity) ht)) u‖^2) ≤
      (2*m.bound^2)*‖u‖^2 := by
  let A := fun k : ℕ => rescaleSymbol m ((2:ℝ)^k*t) (mul_pos (by positivity) ht)
  let v := fourierL2Equiv u
  have hi : Integrable (fun ξ => ‖v ξ‖^2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have ev (k : ℕ) : ‖fourierMultiplier (A k) u‖^2 = ∫ ξ, ‖(A k) ξ‖^2 * ‖v ξ‖^2 := by
    rw [fourierMultiplier_apply,LinearIsometryEquiv.norm_map]
    exact symbol_energy (A k) v
  change (∑ k ∈ I, ‖fourierMultiplier (A k) u‖^2) ≤ _
  simp_rw [ev]
  rw [← integral_finset_sum _ (fun k _ => integrable_energy (A k) v)]
  have e : ‖u‖^2 = ∫ ξ, ‖v ξ‖^2 := by
    rw [← l2_norm_sq_integral,show ‖v‖ = ‖u‖ from LinearIsometryEquiv.norm_map ..]
  rw [e,← integral_const_mul]
  apply integral_mono (integrable_finset_sum _ (fun k _ => integrable_energy (A k) v)) (hi.const_mul _)
  intro ξ
  simp only [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (two_annular_scales m hcut t ht ξ I) (sq_nonneg _)

end Burnett.Analysis.DyadicSquare
