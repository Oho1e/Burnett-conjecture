import Burnett.Analysis.AllScaleTransfer.LowRatioSplit
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Burnett.Analysis.LowRatio

open Set MeasureTheory
open scoped ContDiff Interval

theorem ratioScale_mapsTo_positiveWindow {U : Set Angles} {b t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    MapsTo (ratioScale t) (Window U 0 b) (Window U 0 b) := by
  intro z hz
  rw [ratioScale_apply]
  exact ⟨hz.1, mul_pos ht.1 hz.2.1,
    (mul_le_of_le_one_left hz.2.1.le ht.2).trans_lt hz.2.2⟩

/-- The exact remainder on the cutoff plateau at positive ratio.
Continuity at ratio zero supplies the endpoint value in the fundamental
theorem of calculus. The differentiated path lies in the positive window. -/
theorem remainder_eq_integral_on_positive_plateau {U : Set Angles} {b : ℝ} (hU : IsOpen U)
    (M : Point → ℂ) (χ : ℝ → ℝ) (hχ : χ 0 = 1)
    (hTrace : ContinuousOn M (U ×ˢ Ico (0 : ℝ) b))
    (hM : ContDiffOn ℝ 1 M (Window U 0 b)) (B : ℝ)
    (hBound : ∀ u ∈ Window U 0 b, ‖ratioDerivative M u‖ ≤ B)
    {z : Point} (hz : z ∈ Window U 0 b) (hPlateau : χ z.2 = 1) :
    remainder M χ z = ∫ t in (0 : ℝ)..1, ratioDerivative M (ratioScale t z) := by
  let D := Window U 0 b
  have hD : IsOpen D := hU.prod isOpen_Ioo
  let path (t : ℝ) : Point := ratioScale t z
  have hPath : Continuous path := ratioScale_continuous.clm_apply continuous_const
  have hTraceMap : MapsTo path (Icc (0 : ℝ) 1) (U ×ˢ Ico (0 : ℝ) b) := by
    intro t ht
    change (ratioScale t z).1 ∈ U ∧ (ratioScale t z).2 ∈ Ico (0 : ℝ) b
    rw [ratioScale_apply]
    exact ⟨hz.1, mul_nonneg ht.1 hz.2.1.le,
      (mul_le_of_le_one_left hz.2.1.le ht.2).trans_lt hz.2.2⟩
  have hCurve : ContinuousOn (fun t => M (path t)) (Icc (0 : ℝ) 1) :=
    hTrace.comp hPath.continuousOn hTraceMap
  have hPosMap : MapsTo path (Ioc (0 : ℝ) 1) D :=
    fun _ ht => ratioScale_mapsTo_positiveWindow ht hz
  have hCurveDeriv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun v => M (path v)) (z.2 • ratioDerivative M (path t)) t := by
    intro t ht
    have hw : (z.1, t * z.2) ∈ D := by
      simpa only [path, ratioScale_apply] using hPosMap (mem_Ioc_of_Ioo ht)
    have hLine : HasDerivAt (fun v : ℝ => ((z.1, v) : Point)) ((0 : Angles), (1 : ℝ)) (t * z.2) :=
      HasDerivAt.prodMk (hasDerivAt_const (t * z.2) z.1) (hasDerivAt_id (t * z.2))
    have hDiff := (hM.differentiableOn le_rfl _ hw).differentiableAt (hD.mem_nhds hw)
    have hComp : HasDerivAt (fun v : ℝ => M (z.1, v)) (ratioDerivative M (z.1, t * z.2))
        (t * z.2) :=
      hDiff.hasFDerivAt.comp_hasDerivAt _ hLine
    simpa only [path, ratioScale_apply, Function.comp_apply] using
      hComp.scomp t (hasDerivAt_mul_const z.2)
  have hSmoothDerivative : ContDiffOn ℝ 0 (ratioDerivative M) D :=
    (hM.fderiv_of_isOpen hD (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).clm_apply contDiffOn_const
  have hCont : ContinuousOn (fun t => ratioDerivative M (path t)) (Ioc (0 : ℝ) 1) :=
    hSmoothDerivative.continuousOn.comp hPath.continuousOn hPosMap
  have hBase : IntervalIntegrable (fun t => ratioDerivative M (path t)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (integrableOn_const measure_Ioc_lt_top.ne).mono'
      (hCont.aestronglyMeasurable measurableSet_Ioc)
      ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => hBound _ (hPosMap ht))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    hCurve hCurveDeriv (hBase.smul z.2)
  rw [intervalIntegral.integral_smul] at hFTC
  have hEq : z.2 • (∫ t in (0 : ℝ)..1, ratioDerivative M (ratioScale t z)) =
      M z - M (z.1, 0) := by
    simpa only [path, ratioScale_apply, one_mul, zero_mul, Prod.mk.eta] using hFTC
  have hNonzero : z.2 ≠ 0 := hz.2.1.ne'
  apply smul_right_injective ℂ hNonzero
  change z.2 • remainder M χ z = z.2 • ∫ t in (0 : ℝ)..1, ratioDerivative M (ratioScale t z)
  rw [hEq, remainder_eq_quotient M χ hχ hNonzero, numerator, hPlateau, one_smul]
  change (z.2 : ℂ) * ((M z - M (z.1, 0)) / (z.2 : ℂ)) = M z - M (z.1, 0)
  exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hNonzero)

end Burnett.Analysis.LowRatio
