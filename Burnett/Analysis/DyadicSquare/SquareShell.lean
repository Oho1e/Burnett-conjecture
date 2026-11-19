import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Burnett.Analysis.Fourier.Projection

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.DyadicSquare

abbrev Space := EuclideanSpace ℝ (Fin 4)

open MeasureTheory Finset Burnett.Fourier
open scoped BigOperators

/-- Scale a bounded one-input symbol. Positive scales here can run on either side of one. -/
def rescaleSymbol (m : BoundedSymbol Space) (s : ℝ) (hs : 0 < s) : BoundedSymbol Space where
  toFun := fun ξ => m (s • ξ)
  bound := m.bound
  bound_nonneg := m.bound_nonneg
  norm_le ξ := m.norm_le _
  measurable := by
    have hm := m.measurable
    have he : Measure.QuasiMeasurePreserving (fun ξ : Space => s • ξ) volume volume := by
      refine ⟨(continuous_const.smul continuous_id).measurable,?_⟩
      rw [Measure.map_addHaar_smul (volume : Measure Space) hs.ne']
      exact Measure.smul_absolutelyContinuous
    exact hm.comp_quasiMeasurePreserving he

/-- At most two scales can meet this open annulus at any fixed frequency. -/
theorem two_annular_scales (m : BoundedSymbol Space)
    (hcut : ∀ ξ, m ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) (t : ℝ) (ht : 0 < t) (ξ : Space) (I : Finset ℕ) :
    ∑ k ∈ I, ‖m (((2:ℝ)^k*t) • ξ)‖^2 ≤ 2 * m.bound^2 := by
  classical
  let active := I.filter (fun k => m (((2:ℝ)^k*t) • ξ) ≠ 0)
  have eqsum : (∑ k ∈ I, ‖m (((2:ℝ)^k*t) • ξ)‖^2) =
      ∑ k ∈ active, ‖m (((2:ℝ)^k*t) • ξ)‖^2 := by
    symm
    apply sum_subset (filter_subset _ _)
    intro k hk hnot
    have eh : m (((2:ℝ)^k*t) • ξ) = 0 := by
      simpa only [active,mem_filter,hk,true_and,not_not] using hnot
    simp [eh]
  rw [eqsum]
  by_cases hempty : active.Nonempty
  · let k₀ := active.min' hempty
    have hpair : active ⊆ {k₀,k₀+1} := by
      intro k hk
      have hmin : k₀ ≤ k := min'_le active k hk
      by_contra hnot
      have hsep : k₀+2 ≤ k := by
        simp only [mem_insert,mem_singleton,not_or] at hnot
        omega
      have hA := (hcut _ (mem_filter.mp (min'_mem active hempty)).2).1
      have hB := (hcut _ (mem_filter.mp hk).2).2
      have hsize : (4 : ℝ) * ((2:ℝ)^k₀*t*‖ξ‖) ≤ (2:ℝ)^k*t*‖ξ‖ := by
        have hp : (2:ℝ)^(k₀+2) ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hsep
        calc
          _ = (2:ℝ)^(k₀+2)*t*‖ξ‖ := by rw [pow_add]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp ht.le) (norm_nonneg _)
      rw [norm_smul,Real.norm_of_nonneg (mul_nonneg (by positivity) ht.le)] at hA hB
      linarith
    calc
      _ ≤ ∑ _k ∈ active, m.bound^2 := by
        apply sum_le_sum
        intro k _
        exact (sq_le_sq₀ (norm_nonneg _) m.bound_nonneg).mpr (m.norm_le _)
      _ = (active.card : ℝ)*m.bound^2 := by simp
      _ ≤ 2*m.bound^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact_mod_cast (card_le_card hpair).trans (card_le_two)
  · rw [not_nonempty_iff_eq_empty.mp hempty,sum_empty]
    positivity

end Burnett.Analysis.DyadicSquare
