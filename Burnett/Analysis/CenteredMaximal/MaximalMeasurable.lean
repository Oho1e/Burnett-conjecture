import Burnett.Analysis.CenteredMaximal.MaximalTail

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.CenteredMaximal
open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

/-- Slightly enlarge a witness ball before moving its center. This proves
Borel measurability for the full real-radius supremum. -/
theorem centeredMax_open (g : Space → ℝ≥0∞) (level : ℝ≥0∞) : IsOpen {x | level < centeredMax g x} := by
  apply Metric.isOpen_iff.mpr
  intro x hx
  obtain ⟨r,hr,h⟩ := (centeredMax_level g level x).mp hx
  have hz := (measure_closedBall_pos volume x hr).ne'
  have hfinite : level ≠ ⊤ := by
    intro eq
    simp [eq,ENNReal.top_mul hz] at h
  let V := volume (ball (0:Space) 1)
  let F := fun a : ℝ => level * (ENNReal.ofReal (a^4) * V)
  have hF : Continuous F :=
    (ENNReal.continuous_const_mul hfinite).comp
      ((ENNReal.continuous_mul_const (measure_ball_lt_top.ne : V ≠ ⊤)).comp
        (ENNReal.continuous_ofReal.comp (continuous_id.pow 4)))
  have actual (a : ℝ) (ha : 0 ≤ a) (y : Space) : level * volume (closedBall y a) = F a := by
    rw [Measure.addHaar_closedBall volume y ha,show Module.finrank ℝ Space = 4 from finrank_euclideanSpace_fin]
  rw [actual r hr.le x] at h
  have he : {a | F a < ∫⁻ y in closedBall x r, g y} ∈ 𝓝 r :=
    hF.continuousAt (isOpen_Iio.mem_nhds h)
  obtain ⟨δ,hδ,hnear⟩ := Metric.mem_nhds_iff.mp he
  let R := r + δ/2
  have hR : r < R := by dsimp [R]; linarith
  have inBall : R ∈ ball r δ := by
    rw [mem_ball,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hR.le)]
    dsimp [R]; linarith
  have margin := hnear inBall
  refine ⟨R-r,sub_pos.mpr hR,?_⟩
  intro y hy
  apply (centeredMax_level g level y).mpr
  refine ⟨R,hr.trans hR,?_⟩
  rw [actual R (hr.trans hR).le y]
  apply lt_of_lt_of_le margin
  apply lintegral_mono_set
  apply closedBall_subset_closedBall'
  rw [dist_comm]
  have hd := mem_ball.mp hy
  linarith

theorem centeredMax_measurable (g : Space → ℝ≥0∞) : Measurable (centeredMax g) :=
  measurable_of_Ioi fun level => (centeredMax_open g level).measurableSet

end Burnett.Analysis.CenteredMaximal
