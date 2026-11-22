import Burnett.Analysis.GaugeProjection.ProjectedVacuumSourceOnChart
import Burnett.Analysis.GaugeProjection.ProjectedDivergenceBound
import Burnett.Analysis.GaugeProjection.LocalizedMetricSchwartzInputs

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section

namespace Burnett.P01

open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.CurvatureDifference
open Burnett.A07 (coordinateDerivative)
open MeasureTheory Set
open scoped BigOperators ContDiff NNReal


private theorem localizedMetricEntry_smooth (g g₀ : CoordinateSpace → Tensor2)
    (hg : SmoothCoordinateComponents g) (hg₀ : SmoothCoordinateComponents g₀)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (i j : Index) :
    ContDiff ℝ ∞ (localizedMetricEntry g g₀ χ i j) :=
  hχ.mul ((hg i j).sub (hg₀ i j))


private theorem coordinateDerivative_real (w : SchwartzMap CoordinateSpace ℂ)
    (f : CoordinateSpace → ℝ) (h : ∀ x, w x = (f x : ℂ)) (x : CoordinateSpace)
    (hd : DifferentiableAt ℝ f x) (a : Index) :
    coordinateDerivative a w x = (scalarPartial f a x : ℂ) := by
  rw [coordinateDerivative, SchwartzMap.pderivCLM_apply, funext h]
  have hD := (Complex.ofRealCLM.hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => (f y : ℂ)) x = _ at hD
  rw [hD]
  rfl

private theorem scalarPartial_smooth_on_chart (f : CoordinateSpace → ℝ) (a : Index)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (scalarPartial f a) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private theorem exists_cutoff_first_derivative_bound (χ : CoordinateSpace → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ tsupport χ → ‖χ x‖ ≤ C ∧ ‖scalarPartial χ a x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hχ.continuous.continuousOn
  choose D hD using fun a =>
    hc.exists_bound_of_continuousOn (scalarPartial_smooth_on_chart χ a hχ).continuous.continuousOn
  let M := max C 0 + ∑ a, max (D a) 0
  have hSum : 0 ≤ ∑ a, max (D a) 0 := Finset.sum_nonneg fun _ _ => le_max_right _ _
  refine ⟨M, add_nonneg (le_max_right _ _) hSum, fun a x hx => ⟨?_, ?_⟩⟩
  · exact (hC x hx).trans ((le_max_left _ _).trans (le_add_of_nonneg_right hSum))
  · have hLe : max (D a) 0 ≤ ∑ a, max (D a) 0 :=
      Finset.single_le_sum (fun a _ => le_max_right (D a) 0) (Finset.mem_univ a)
    exact (hD a x hx).trans ((le_max_left _ _).trans (hLe.trans
      (le_add_of_nonneg_left (le_max_right _ _))))

private theorem norm_partial_localizedMetricEntry_le
    (g g₀ inv : CoordinateSpace → Tensor2)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hg : SmoothCoordinateComponents g) (hg₀ : SmoothCoordinateComponents g₀)
    (B C : ℝ) (hC : 0 ≤ C) (a i j : Index) (x : CoordinateSpace)
    (hCut : x ∈ tsupport χ → ‖χ x‖ ≤ C ∧ ‖scalarPartial χ a x‖ ≤ C)
    (hBound : x ∈ tsupport χ → ‖localizedSourceJets inv g g₀ x‖ ≤ B) :
    ‖scalarPartial (localizedMetricEntry g g₀ χ i j) a x‖ ≤
      (tsupport χ).indicator (fun _ => 2 * C * B) x := by
  by_cases hx : x ∈ tsupport χ
  · have hb := hBound hx
    simp only [localizedSourceJets, Prod.norm_def, max_le_iff] at hb
    have hv : ‖g x i j - g₀ x i j‖ ≤ B :=
      ((norm_le_pi_norm ((g x - g₀ x) i) j).trans (norm_le_pi_norm (g x - g₀ x) i)).trans hb.2.2.2.1
    let dj := coordinateJet g x - coordinateJet g₀ x
    have hd : ‖dj a i j‖ ≤ B :=
      (((norm_le_pi_norm (dj a i) j).trans (norm_le_pi_norm (dj a) i)).trans
        (norm_le_pi_norm dj a)).trans hb.2.2.2.2.1
    have hs : scalarPartial (fun y => g y i j - g₀ y i j) a x = dj a i j := by
      simp only [scalarPartial, coordinateJet, dj, Pi.sub_apply,
        fderiv_fun_sub ((hg i j).differentiable (by simp) x) ((hg₀ i j).differentiable (by simp) x),
        ContinuousLinearMap.sub_apply]
    change ‖scalarPartial (fun y => χ y * (g y i j - g₀ y i j)) a x‖ ≤ _
    rw [scalarPartial_product _ _ _ _ (hχ.differentiable (by simp) x)
      (((hg i j).sub (hg₀ i j)).differentiable (by simp) x), hs, indicator_of_mem hx]
    calc
      _ ≤ ‖scalarPartial χ a x * (g x i j - g₀ x i j)‖ + ‖χ x * dj a i j‖ := norm_add_le _ _
      _ ≤ C * B + C * B := by
        simp only [norm_mul]
        exact add_le_add (mul_le_mul (hCut hx).2 hv (norm_nonneg _) hC)
          (mul_le_mul (hCut hx).1 hd (norm_nonneg _) hC)
      _ = _ := by ring
  · have hs : x ∉ tsupport (localizedMetricEntry g g₀ χ i j) :=
      fun h => hx (tsupport_mul_subset_left h)
    have hZero : fderiv ℝ (localizedMetricEntry g g₀ χ i j) x = 0 := by
      by_contra h
      exact hs (support_fderiv_subset ℝ h)
    simp [scalarPartial, hZero, indicator_of_notMem hx]

private theorem norm_gradientMass_localizedMetric_le
    (g g₀ inv : CoordinateSpace → Tensor2)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hg : SmoothCoordinateComponents g) (hg₀ : SmoothCoordinateComponents g₀)
    (B C : ℝ) (hC : 0 ≤ C)
    (hCut : ∀ a x, x ∈ tsupport χ → ‖χ x‖ ≤ C ∧ ‖scalarPartial χ a x‖ ≤ C)
    (hBound : ∀ x, x ∈ tsupport χ → ‖localizedSourceJets inv g g₀ x‖ ≤ B) :
    projectedSourceGradientMass (localizedMetricSchwartz g g₀ χ hχ hc hg hg₀) ≤
      4 * (eLpNorm ((tsupport χ).indicator (fun _ => 2 * C * B)) 2 volume).toReal := by
  let F := (tsupport χ).indicator (fun _ => 2 * C * B)
  have hF : MemLp F 2 volume := memLp_indicator_const 2 isClosed_closure.measurableSet _
    (Or.inr hc.measure_lt_top.ne)
  unfold projectedSourceGradientMass
  calc
    _ ≤ ∑ _ : Fin 4, (eLpNorm F 2 volume).toReal := by
      apply Finset.sum_le_sum
      intro a _
      apply (pi_norm_le_iff_of_nonneg ENNReal.toReal_nonneg).2
      intro i
      apply (pi_norm_le_iff_of_nonneg ENNReal.toReal_nonneg).2
      intro j
      change ‖(coordinateDerivative a _).toLp 2 volume‖ ≤ _
      rw [SchwartzMap.toLp, Lp.norm_toLp]
      apply ENNReal.toReal_mono hF.2.ne
      apply eLpNorm_mono_real
      intro x
      rw [coordinateDerivative_real _ (localizedMetricEntry g g₀ χ i j) (fun _ => rfl) x
        ((localizedMetricEntry_smooth g g₀ hg hg₀ χ hχ i j).differentiable (by simp) x),
        Complex.norm_real]
      exact norm_partial_localizedMetricEntry_le g g₀ inv χ hχ hg hg₀ B C hC a i j x
        (hCut a x) (hBound x)
    _ = _ := by simp [F]

/-- The coefficient in the vacuum computation and the coefficient used by the
actual whole-space nondivergence term are identical. -/
theorem projectedSourceQ_eq_localizedWaveSourceSchwartz
    (inv g g₀ : CoordinateSpace → Tensor2)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hi : SmoothCoordinateComponents inv) (hg : SmoothCoordinateComponents g)
    (hg₀ : SmoothCoordinateComponents g₀)
    (L : ℝ≥0) (hL : ∀ a b, LipschitzWith L (fun x => inv x a b)) :
    projectedSourceQ (ProjectedSourceCoefficients.ofReal (fun a b x => inv x a b) hi L hL)
      (localizedMetricSchwartz g g₀ χ hχ hc hg hg₀) =
        projectionMatrixToL2 (localizedWaveSourceSchwartz inv g g₀ χ hχ hc hi hg hg₀) := by
  apply (projectedSourceQ_eq_schwartz _ _ _ ?_).1
  intro i j x
  let z := localizedMetricEntry g g₀ χ i j
  let Z := localizedMetricSchwartz g g₀ χ hχ hc hg hg₀ i j
  have hz : ContDiff ℝ ∞ z := localizedMetricEntry_smooth g g₀ hg hg₀ χ hχ i j
  have hD (a b : Index) : coordinateDerivative a (coordinateDerivative b Z) x =
      (scalarPartial (scalarPartial z b) a x : ℂ) := by
    apply coordinateDerivative_real
    · intro y
      exact coordinateDerivative_real Z z (fun _ => rfl) y (hz.differentiable (by simp) y) b
    · exact (scalarPartial_smooth_on_chart z b hz).differentiable (by simp) x
  change (scalarWaveAt (inv x) z x : ℂ) =
    ∑ a, ∑ b, (inv x a b : ℂ) * coordinateDerivative a (coordinateDerivative b Z) x
  simp only [scalarWaveAt, Complex.ofReal_sum, Complex.ofReal_mul, hD]

/-- The original projected fluctuation satisfies a whole-space (L^2) bound
for its actual negative divergence, including the tails outside the cutoff. -/
theorem exists_wholeSpace_projectedVacuumDivergenceL2_bound
    (inv g : ℕ → CoordinateSpace → Tensor2) (g₀ : CoordinateSpace → Tensor2)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hi : ∀ n, SmoothCoordinateComponents (inv n)) (hg : ∀ n, SmoothCoordinateComponents (g n))
    (hg₀ : SmoothCoordinateComponents g₀)
    (B : ℝ) (L : ℝ≥0) (hL : ∀ n a b, LipschitzWith L (fun x => inv n x a b))
    (hInvSym : ∀ n x, x ∈ tsupport χ → IsSymmetricTensor (inv n x))
    (hSym : ∀ n x, IsSymmetricTensor (g n x))
    (hVac : ∀ n x, x ∈ tsupport χ → ∀ i j,
      coordinateRicci (fun y => christoffel (inv n y) (coordinateJet (g n) y)) x i j = 0)
    (hBound : ∀ n x, x ∈ tsupport χ → ‖localizedSourceJets (inv n) (g n) g₀ x‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      ‖projectedSourceDivergenceL2 (ProjectedSourceCoefficients.ofReal
        (fun a b x => inv n x a b) (hi n) L (hL n))
        (projectionFullSchwartz (localizedMetricSchwartz (g n) g₀ χ hχ hc (hg n) hg₀))‖ ≤ C := by
  obtain ⟨CQ, hCQ, hQ⟩ := exists_norm_projection_of_localizedVacuumSource_le
    inv g g₀ χ hχ hc hi hg hg₀ B hInvSym hSym hVac hBound
  obtain ⟨CB, hCB, hCut⟩ := exists_cutoff_first_derivative_bound χ hχ hc
  obtain ⟨C, hC, hD⟩ := exists_projectedSourceDivergenceL2_bound
  let CG := 4 * (eLpNorm ((tsupport χ).indicator (fun _ => 2 * CB * B)) 2 volume).toReal
  refine ⟨CQ + C * (L : ℝ) * CG, by positivity, fun n => ?_⟩
  let A := ProjectedSourceCoefficients.ofReal (fun a b x => inv n x a b) (hi n) L (hL n)
  let z := localizedMetricSchwartz (g n) g₀ χ hχ hc (hg n) hg₀
  have hEst := hD A z
  have he := projectedSourceQ_eq_localizedWaveSourceSchwartz (inv n) (g n) g₀ χ
    hχ hc (hi n) (hg n) hg₀ L (hL n)
  change projectedSourceQ A z = _ at he
  rw [he] at hEst
  exact hEst.trans (add_le_add (hQ n) (mul_le_mul_of_nonneg_left
    (norm_gradientMass_localizedMetric_le (g n) g₀ (inv n) χ hχ hc (hg n) hg₀ B CB hCB hCut (hBound n))
    (mul_nonneg hC L.coe_nonneg)))

end Burnett.P01
