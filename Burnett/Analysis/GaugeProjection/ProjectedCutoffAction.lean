import Burnett.Analysis.PrincipalEnergy.Fourier.DyadicKernel
import Burnett.Analysis.GaugeProjection.GaugeProjectionSchwartzAction

set_option autoImplicit false
set_option maxHeartbeats 2600000

noncomputable section

namespace Burnett.P01

open MeasureTheory Set Filter Burnett.Fourier
open Burnett.Microlocal.AngularDyadicKernel
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.A02.FrequencySplit (tau mikhlin_bounded_symbol radianAction radianActionSpectrum
  radianActionSpectrum_inverse)
open scoped ContDiff FourierTransform Topology InnerProduct

def gaugeDyadicAngularSymbol (a b c d : Fin 4) : BoundedSymbol E :=
  Classical.choose (mikhlin_bounded_symbol _ (gaugeProjectionSymbol_contDiffOn a b c d)
    (gaugeProjectionSymbol_scale a b c d))

theorem gaugeDyadicAngularSymbol_apply (a b c d : Fin 4) (ν : E) :
    gaugeDyadicAngularSymbol a b c d ν = (gaugeProjectionSymbol a b c d ν : ℂ) :=
  Classical.choose_spec (mikhlin_bounded_symbol _ (gaugeProjectionSymbol_contDiffOn a b c d)
    (gaugeProjectionSymbol_scale a b c d)) ν

theorem gaugeDyadicAngularSymbol_smooth (a b c d : Fin 4) :
    ContDiffOn ℝ ∞ (gaugeDyadicAngularSymbol a b c d : E → ℂ) ({0}ᶜ : Set E) := by
  simpa only [show (gaugeDyadicAngularSymbol a b c d : E → ℂ) =
    fun ν => (gaugeProjectionSymbol a b c d ν : ℂ) from
    funext (gaugeDyadicAngularSymbol_apply a b c d)] using
    Complex.ofRealCLM.contDiff.comp_contDiffOn (gaugeProjectionSymbol_contDiffOn a b c d)

theorem gaugeDyadicAngularSymbol_degreeZero (a b c d : Fin 4) :
    DegreeZero (gaugeDyadicAngularSymbol a b c d : E → ℂ) := by
  intro r hr ν
  simp only [gaugeDyadicAngularSymbol_apply, gaugeProjectionSymbol_scale _ _ _ _ r hr ν]

private theorem tau_pos : 0 < tau := mul_pos (by norm_num) Real.pi_pos

private def projectionInfraredDifference (ν : E) : ℝ :=
  gaugeProjectionInfrared (tau * ‖ν‖) - (1 - radialCore ν)

private theorem projectionInfraredDifference_eq_zero_near (ν : E)
    (hν : tau * ‖ν‖ < 1) (hν' : ‖ν‖ < 1) :
    projectionInfraredDifference ν = 0 := by
  simp [projectionInfraredDifference, gaugeProjectionInfrared_zero hν.le,
    radialCore_eq_one ν hν'.le]

private theorem projectionInfraredDifference_eq_zero_far (ν : E) (hν : 2 ≤ tau * ‖ν‖)
    (hν' : 2 ≤ ‖ν‖) : projectionInfraredDifference ν = 0 := by
  simp [projectionInfraredDifference, gaugeProjectionInfrared_one hν,
    radialCore_eq_zero ν hν']

private def projectionCorrectionSymbol (m : BoundedSymbol E) (ν : E) : ℂ :=
  (projectionInfraredDifference ν : ℂ) * m ν

private theorem projectionCorrectionSymbol_smooth (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) :
    ContDiff ℝ ∞ (projectionCorrectionSymbol m) := by
  refine contDiff_iff_contDiffAt.mpr fun ν => ?_
  by_cases hν : ν = 0
  · subst ν
    have hnear : {x : E | tau * ‖x‖ < 1} ∈ 𝓝 (0 : E) :=
      (isOpen_lt (continuous_const.mul continuous_norm) continuous_const).mem_nhds (by simp)
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hnear, Metric.ball_mem_nhds (0 : E) zero_lt_one] with x h₁ h₂
    have hx : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using h₂
    simp [projectionCorrectionSymbol, projectionInfraredDifference_eq_zero_near x h₁ hx]
  · have hχ := gaugeProjectionInfrared_contDiff.contDiffAt.comp ν
      (contDiffAt_const.mul (contDiffAt_id.norm ℝ hν) :
        ContDiffAt ℝ ∞ (fun x : E => tau * ‖x‖) ν)
    have hdiff : ContDiffAt ℝ ∞ projectionInfraredDifference ν :=
      hχ.sub ((contDiffAt_const (c := (1 : ℝ))).sub radialCore_contDiff.contDiffAt)
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp ν hdiff).mul
      (hm.contDiffAt (isOpen_compl_singleton.mem_nhds hν))

private theorem projectionCorrectionSymbol_compact (m : BoundedSymbol E) :
    HasCompactSupport (projectionCorrectionSymbol m) := by
  let R := max 2 (2 / tau)
  have hsupport : Function.support (projectionCorrectionSymbol m) ⊆
      Metric.closedBall (0 : E) R := by
    intro ν hν
    by_contra h
    rw [Metric.mem_closedBall, dist_zero_right] at h
    have hR : R < ‖ν‖ := lt_of_not_ge h
    have hlarge : 2 ≤ tau * ‖ν‖ := by
      have hdiv := (div_lt_iff₀ tau_pos).mp ((le_max_right 2 (2/tau)).trans_lt hR)
      exact hdiv.le.trans_eq (mul_comm ‖ν‖ tau)
    have hn : 2 ≤ ‖ν‖ := (le_max_left 2 (2/tau)).trans hR.le
    exact hν (by simp [projectionCorrectionSymbol, projectionInfraredDifference_eq_zero_far ν hlarge hn])
  exact (isCompact_closedBall (0 : E) R).of_isClosed_subset isClosed_closure
    (closure_minimal hsupport Metric.isClosed_closedBall)

def projectionCorrectionSchwartz (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) : SchwartzMap E ℂ :=
  (projectionCorrectionSymbol_compact m).toSchwartzMap (projectionCorrectionSymbol_smooth m hm)

def projectionCorrectionKernel (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) : SchwartzMap E ℂ :=
  (SchwartzMap.fourierTransformCLE ℂ).symm (projectionCorrectionSchwartz m hm)

private theorem gaugeProjection_recombine (a b c d : Fin 4) (ν : E) :
    projectionCorrectionSchwartz (gaugeDyadicAngularSymbol a b c d)
      (gaugeDyadicAngularSymbol_smooth a b c d) ν +
      normalizedAngularSymbol (gaugeDyadicAngularSymbol a b c d) ν =
      (regularizedGaugeProjectionSymbol a b c d (tau • ν) : ℂ) := by
  let m := gaugeDyadicAngularSymbol a b c d
  change (projectionInfraredDifference ν : ℂ) * m ν + (1 - (radialCore ((1:ℝ) • ν) : ℂ)) * m ν =
    (regularizedGaugeProjectionSymbol a b c d (tau • ν) : ℂ)
  simp only [one_smul, m, gaugeDyadicAngularSymbol_apply, projectionInfraredDifference,
    regularizedGaugeProjectionSymbol, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    norm_smul, Real.norm_of_nonneg tau_pos.le, gaugeProjectionSymbol_scale _ _ _ _ tau tau_pos ν]
  ring

/-- The actual finite infrared correction and all shells below N, in the
same standard Fourier coordinate before returning to the gauge action. -/
def projectionDyadicApproximation (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (f : SchwartzMap E ℂ)
    (N : ℕ) (x : E) : ℂ :=
  𝓕⁻ (fun ν => (projectionCorrectionSchwartz m hm ν + partialAngularSymbol m N ν) *
    𝓕 (f : E → ℂ) ν) x

theorem projectionDyadicApproximation_eq_convolution (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (f : SchwartzMap E ℂ) (N : ℕ) (x : E) :
    projectionDyadicApproximation m hm f N x = ∫ y,
      (projectionCorrectionKernel m hm (x-y) + ∑ j ∈ Finset.range N, shellKernel m hm j (x-y)) * f y := by
  let p := projectionCorrectionSchwartz m hm
  let q := partialAngularSchwartz m hm N
  have hq (ν : E) : q ν = partialAngularSymbol m N ν := partialAngularSchwartz_apply m hm hd N ν
  unfold projectionDyadicApproximation
  simp_rw [← hq]
  change 𝓕⁻ (fun ν => (p+q) ν * 𝓕 (f : E → ℂ) ν) x = _
  rw [inverseFourier_mul_fourier_eq_convolution _ _ (p+q).integrable f.integrable]
  apply integral_congr_ae
  refine Eventually.of_forall fun y => congrArg (fun k => k * f y) ?_
  let F : SchwartzMap E ℂ ≃L[ℂ] SchwartzMap E ℂ := SchwartzMap.fourierTransformCLE ℂ
  calc
    𝓕⁻ ((p + q : SchwartzMap E ℂ) : E → ℂ) (x-y) = F.symm (p+q) (x-y) :=
      congrFun (SchwartzMap.fourierTransformCLE_symm_apply ℂ (p+q)).symm (x-y)
    _ = F.symm p (x-y) + F.symm q (x-y) := by rw [map_add]; rfl
    _ = _ := by
      change projectionCorrectionKernel m hm (x-y) + F.symm q (x-y) = _
      have hI : F.symm q (x-y) = 𝓕⁻ (q : E → ℂ) (x-y) :=
        congrFun (SchwartzMap.fourierTransformCLE_symm_apply ℂ q) (x-y)
      rw [hI, show (q : E → ℂ) = partialAngularSymbol m N from funext hq,
        inverseFourier_partialAngular_eq_sum m hm hd N]

private theorem partialAngularSymbol_norm_le (m : BoundedSymbol E) (N : ℕ) (ν : E) :
    ‖partialAngularSymbol m N ν‖ ≤ 2 * m.bound := by
  let a := boundedRadialCore (dyadicScale N)⁻¹
  let b := boundedRadialCore (1 : ℝ)
  change ‖(a ν - b ν) * m ν‖ ≤ _
  rw [norm_mul]
  have hab : ‖a ν - b ν‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans (by
      have ha := a.norm_le ν
      have hb := b.norm_le ν
      change ‖a ν‖ ≤ 1 at ha
      change ‖b ν‖ ≤ 1 at hb
      linarith)
  exact mul_le_mul hab (m.norm_le ν) (norm_nonneg _) (by norm_num)

theorem projectionDyadicApproximation_tendsto (a b c d : Fin 4)
    (f : SchwartzMap E ℂ) (x : E) :
    Tendsto (fun N => projectionDyadicApproximation (gaugeDyadicAngularSymbol a b c d)
      (gaugeDyadicAngularSymbol_smooth a b c d) f N x) atTop
      (𝓝 (gaugeProjectionSchwartzComponent a b c d f x)) := by
  let m := gaugeDyadicAngularSymbol a b c d
  let p := projectionCorrectionSchwartz m (gaugeDyadicAngularSymbol_smooth a b c d)
  let K := SchwartzMap.seminorm ℝ 0 0 p
  let F := SchwartzMap.fourierTransformCLE ℂ f
  have hTarget : gaugeProjectionSchwartzComponent a b c d f x =
      𝓕⁻ (fun ν => (p ν + normalizedAngularSymbol m ν) * F ν) x := by
    rw [show gaugeProjectionSchwartzComponent a b c d f x =
      radianAction (regularizedGaugeProjectionSymbol a b c d) f x from
      congrFun (gaugeProjectionSchwartzComponent_eq_radianAction a b c d f) x,
      ← radianActionSpectrum_inverse]
    apply congrFun
    congr 1
    funext ν
    rw [gaugeProjection_recombine]
    rfl
  rw [hTarget]
  simp only [projectionDyadicApproximation, Real.fourierIntegralInv_eq]
  have hchar : Continuous (fun ν : E => Real.fourierChar (inner ℝ ν x)) :=
    Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)
  refine tendsto_integral_of_dominated_convergence
    (fun ν : E => (K + 2 * m.bound) * ‖F ν‖) ?_ (F.integrable.norm.const_mul _) ?_ ?_
  · intro N
    exact hchar.aestronglyMeasurable.smul
      ((p.continuous.aestronglyMeasurable.add (partialAngularSymbol m N).measurable).mul
        F.continuous.aestronglyMeasurable)
  · intro N
    refine Eventually.of_forall fun ν => ?_
    rw [Circle.norm_smul, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_add_le _ _).trans (add_le_add
      (by simpa only [pow_zero, one_mul] using p.norm_pow_mul_le_seminorm ℝ 0 ν)
      (partialAngularSymbol_norm_le m N ν))
  · refine Eventually.of_forall fun ν => ?_
    have hN := partialAngularSymbol_eventually_eq m ν
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hN] with N h
    change _ • ((p ν + normalizedAngularSymbol m ν) * F ν) =
      _ • ((p ν + partialAngularSymbol m N ν) * F ν)
    rw [h]

end Burnett.P01
