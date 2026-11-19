import Burnett.Analysis.CenteredMaximal.MaximalWeak

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.CenteredMaximal
open MeasureTheory Metric Set
open scoped ENNReal

def centeredMax (g : Space → ℝ≥0∞) (x : Space) : ℝ≥0∞ :=
  ⨆ r : {t : ℝ // 0<t}, (∫⁻ y in closedBall x r, g y) / volume (closedBall x r)

theorem centeredMax_level (g : Space → ℝ≥0∞) (level : ℝ≥0∞) (x : Space) :
    level < centeredMax g x ↔ ∃ r : ℝ, 0<r ∧
      level*volume (closedBall x r) < ∫⁻ y in closedBall x r, g y := by
  unfold centeredMax
  rw [lt_iSup_iff]
  constructor
  · rintro ⟨⟨r,hr⟩,h⟩
    exact ⟨r,hr,(ENNReal.lt_div_iff_mul_lt (.inl (measure_closedBall_pos volume x hr).ne')
      (.inl measure_closedBall_lt_top.ne)).mp h⟩
  · rintro ⟨r,hr,h⟩
    exact ⟨⟨r,hr⟩,(ENNReal.lt_div_iff_mul_lt (.inl (measure_closedBall_pos volume x hr).ne')
      (.inl measure_closedBall_lt_top.ne)).mpr h⟩

theorem centeredMax_weak_type (g : Space → ℝ≥0∞) (level : ℝ≥0∞) :
    level*volume {x | level < centeredMax g x} ≤ 256 * ∫⁻ y, g y := by
  simpa only [centeredMax_level] using centered_maximal_weak_one g level

def upperTail (g : Space → ℝ≥0∞) (a : ℝ≥0∞) (y : Space) : ℝ≥0∞ := if a < g y then g y else 0

/-- Distribution estimate with truncated input, for integrating the weak
estimate at all heights to reach the strong finite-exponent inequality. -/
theorem centeredMax_tail (g : Space → ℝ≥0∞) (a : ℝ≥0∞) :
    a * volume {x | 2*a < centeredMax g x} ≤ 256 * ∫⁻ y, upperTail g a y := by
  have sub : {x | 2*a < centeredMax g x} ⊆ {x | a < centeredMax (upperTail g a) x} := by
    intro x hx
    obtain ⟨r,hr,h⟩ := (centeredMax_level g (2*a) x).mp hx
    apply (centeredMax_level _ a x).mpr
    refine ⟨r,hr,?_⟩
    have bound (y : Space) : g y ≤ a + upperTail g a y := by
      by_cases hy : a < g y
      · simp only [upperTail,if_pos hy]; exact le_add_left le_rfl
      · simpa only [upperTail,if_neg hy,add_zero] using le_of_not_gt hy
    by_contra! hsmall
    apply (not_lt_of_ge ?_) h
    calc
      (∫⁻ y in closedBall x r, g y) ≤ ∫⁻ y in closedBall x r, a + upperTail g a y :=
        lintegral_mono bound
      _ = a*volume (closedBall x r) + ∫⁻ y in closedBall x r, upperTail g a y := by
        rw [lintegral_add_left measurable_const,lintegral_const,Measure.restrict_apply_univ]
      _ ≤ a*volume (closedBall x r) + a*volume (closedBall x r) := add_le_add_left hsmall _
      _ = 2*a*volume (closedBall x r) := by rw [two_mul,add_mul]
  exact (mul_le_mul_left' (measure_mono sub) a).trans (centeredMax_weak_type _ a)

end Burnett.Analysis.CenteredMaximal
