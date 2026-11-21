import Burnett.Analysis.PrincipalEnergy.Energy.CoordinateH1Energy
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section

namespace Burnett.Analysis.SymmetricEnergy

open Filter MeasureTheory Set
open scoped InnerProductSpace SchwartzMap BigOperators ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

def unitBallVolume : ℝ := (volume : Measure Space).real (Metric.ball 0 1)

theorem unitBallVolume_nonneg : 0 ≤ unitBallVolume := ENNReal.toReal_nonneg

omit [IsScalarTower ℝ ℂ F] in
private theorem norm_toLp_sq_eq_integral (f : 𝓢(Space, F)) :
    ‖f.toLp 2 volume‖^2 = ∫ x, ‖f x‖^2 := by
  let u := f.toLp 2 volume
  have hInt := L2.integrable_inner (𝕜 := ℂ) u u
  calc
    _ = RCLike.re (⟪u, u⟫_ℂ) := (inner_self_eq_norm_sq (𝕜 := ℂ) u).symm
    _ = ∫ x, RCLike.re (⟪u x, u x⟫_ℂ) := by rw [L2.inner_def, integral_re hInt]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [f.coeFn_toLp 2 volume] with x hx
      rw [inner_self_eq_norm_sq, show u x = f x from hx]

omit [InnerProductSpace ℂ F] [IsScalarTower ℝ ℂ F] in
private theorem norm_squares_integrable (f : 𝓢(Space, F)) :
    Integrable (fun x => ‖f x‖^2) (volume : Measure Space) :=
  (memLp_two_iff_integrable_sq_norm f.continuous.aestronglyMeasurable).mp (f.memLp 2 volume)

omit [IsScalarTower ℝ ℂ F] in
theorem schwartz_ball_norm_le (f : 𝓢(Space, F)) (c : Space) (ρ M : ℝ) (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hSupport : tsupport (f : Space → F) ⊆ Metric.closedBall c ρ) (hValue : ∀ x, ‖f x‖ ≤ M) :
    ‖f.toLp 2 volume‖ ≤ M * ρ^2 * Real.sqrt unitBallVolume := by
  let s := Metric.closedBall c ρ
  have hs : MeasurableSet s := Metric.isClosed_closedBall.measurableSet
  have hm : (volume : Measure Space).real s = ρ^4 * unitBallVolume := by
    unfold s unitBallVolume
    rw [Measure.addHaar_real_closedBall (volume : Measure Space) c hρ, finrank_euclideanSpace_fin]
  let k := s.indicator (fun _ : Space => M^2)
  have hk : Integrable k (volume : Measure Space) :=
    (integrableOn_const (measure_closedBall_lt_top.ne)).integrable_indicator hs
  have hp : ∀ x, ‖f x‖^2 ≤ k x := by
    intro x
    change ‖f x‖^2 ≤ s.indicator (fun _ : Space => M^2) x
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx]
      exact pow_le_pow_left₀ (norm_nonneg _) (hValue x) _
    · rw [indicator_of_notMem hx, show f x = 0 by
        by_contra h; exact hx (hSupport (subset_closure h)), norm_zero]
      norm_num
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ = ∫ x, ‖f x‖^2 := norm_toLp_sq_eq_integral f
    _ ≤ ∫ x, k x := integral_mono_ae (norm_squares_integrable f) hk (Eventually.of_forall hp)
    _ = M^2 * (ρ^4 * unitBallVolume) := by
      change (∫ x, s.indicator (fun _ : Space => M^2) x) = _
      rw [integral_indicator hs, setIntegral_const, hm, smul_eq_mul, mul_comm]
    _ = (M * ρ^2 * Real.sqrt unitBallVolume)^2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt unitBallVolume_nonneg]
      ring

/-- The standard pointwise first-order bump normalization gives its true
four-dimensional value L² and inhomogeneous H¹ scaling for radii at most one. -/
theorem normalizedBallTest_norms (f : 𝓢(Space, F)) (c : Space) (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ 1)
    (hSupport : tsupport (f : Space → F) ⊆ Metric.closedBall c ρ) (hValue : ∀ x, ‖f x‖ ≤ 1)
    (hDeriv : ∀ (j : Fin 4) x, ‖fderiv ℝ (⇑f) x (coordinateDirection j)‖ ≤ ρ⁻¹) :
    ‖f.toLp 2 volume‖ ≤ ρ^2 * Real.sqrt unitBallVolume ∧
      coordinateH1 f ≤ ρ * Real.sqrt (5*unitBallVolume) := by
  have h₂ : ‖f.toLp 2 volume‖ ≤ ρ^2 * Real.sqrt unitBallVolume := by
    simpa only [one_mul] using schwartz_ball_norm_le f c ρ 1 hρ.le zero_le_one hSupport hValue
  have hD (j : Fin 4) : ‖(SchwartzMap.pderivCLM ℂ (coordinateDirection j) f).toLp 2 volume‖ ≤
      ρ * Real.sqrt unitBallVolume := by
    let v := SchwartzMap.pderivCLM ℂ (coordinateDirection j) f
    have hv : tsupport (v : Space → F) ⊆ Metric.closedBall c ρ := by
      apply closure_minimal _ Metric.isClosed_closedBall
      intro z hz
      apply hSupport (support_fderiv_subset ℝ ?_)
      intro hz'
      exact hz (by simp only [v, SchwartzMap.pderivCLM_apply, hz', ContinuousLinearMap.zero_apply])
    have h := schwartz_ball_norm_le v c ρ ρ⁻¹ hρ.le (inv_nonneg.mpr hρ.le) hv
      (fun z => by simpa only [v, SchwartzMap.pderivCLM_apply] using hDeriv j z)
    simpa only [show ρ⁻¹ * ρ^2 = ρ by field_simp [hρ.ne']] using h
  refine ⟨h₂,?_⟩
  have hValueSq : ‖f.toLp 2 volume‖ ^ 2 ≤ ρ^2 * unitBallVolume := by
    have hb : ‖f.toLp 2 volume‖ ≤ ρ * Real.sqrt unitBallVolume := h₂.trans
      (mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hr hρ.le]) (Real.sqrt_nonneg _))
    have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
    simpa only [mul_pow, Real.sq_sqrt unitBallVolume_nonneg] using hs
  have hDerivSq (j : Fin 4) : ‖(SchwartzMap.pderivCLM ℂ (coordinateDirection j) f).toLp 2 volume‖^2 ≤
      ρ^2 * unitBallVolume := by
    have hs := pow_le_pow_left₀ (norm_nonneg _) (hD j) 2
    simpa only [mul_pow, Real.sq_sqrt unitBallVolume_nonneg] using hs
  have hSum : (∑ j : Fin 4, ‖(SchwartzMap.pderivCLM ℂ (coordinateDirection j) f).toLp 2 volume‖^2) ≤
      4 * (ρ^2 * unitBallVolume) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using
      (Finset.sum_le_sum fun j _ => hDerivSq j)
  unfold coordinateH1
  calc
    _ ≤ Real.sqrt (ρ^2 * unitBallVolume + 4 * (ρ^2 * unitBallVolume)) :=
      Real.sqrt_le_sqrt (add_le_add hValueSq hSum)
    _ = ρ * Real.sqrt (5*unitBallVolume) := by
      rw [show ρ^2 * unitBallVolume + 4 * (ρ^2 * unitBallVolume) = ρ^2 * (5 * unitBallVolume) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hρ.le]

end Burnett.Analysis.SymmetricEnergy
