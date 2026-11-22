import Burnett.Analysis.GaugeProjection.ProjectedDefectLocalizationError
import Burnett.Analysis.GaugeProjection.OpenChartMetricRepresentatives

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter Set
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.A07 (coordinateDerivative)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport test_memLp valueLp)
open scoped ContDiff NNReal Topology

theorem localizedMetricSchwartz_coordinateDerivative_eq_partial
    (g g₀ : CoordinateSpace → Tensor2) (χ : CoordinateSpace → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hg : SmoothCoordinateComponents g) (hg₀ : SmoothCoordinateComponents g₀)
    (i j a : Index) (x : CoordinateSpace) :
    coordinateDerivative a (localizedMetricSchwartz g g₀ χ hχ hc hg hg₀ i j) x =
      (scalarPartial (localizedMetricEntry g g₀ χ i j) a x : ℂ) := by
  rw [localizedMetricSchwartz_coordinateDerivative_real]
  change _ = (scalarPartial (fun y => χ y * (g y i j - g₀ y i j)) a x : ℂ)
  rw [scalarPartial_product _ _ _ _ (hχ.differentiable (by simp) x)
    (((hg i j).sub (hg₀ i j)).differentiable (by simp) x)]
  have hSub : scalarPartial (fun y => g y i j - g₀ y i j) a x =
      coordinateJet g x a i j - coordinateJet g₀ x a i j := by
    simp only [scalarPartial, coordinateJet,
      fderiv_fun_sub ((hg i j).differentiable (by simp) x)
        ((hg₀ i j).differentiable (by simp) x), ContinuousLinearMap.sub_apply]
  rw [hSub]
  congr 1
  ring

/-- The real representative of the actual derivative of the cutoff perturbation
is weakly zero against every original compact smooth real test. -/
theorem localizedMetricSchwartz_coordinateDerivative_test_tendsto_zero
    (g : ℕ → CoordinateSpace → Tensor2) (g₀ : CoordinateSpace → Tensor2)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hg : ∀ n, SmoothCoordinateComponents (g n)) (hg₀ : SmoothCoordinateComponents g₀)
    (i j a : Index)
    (hSmall : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      ∀ x, ‖localizedMetricSchwartz (g n) g₀ χ hχ hc (hg n) hg₀ i j x‖ < ε)
    (φ : D) :
    Tendsto (fun n => ∫ x, (coordinateDerivative a
      (localizedMetricSchwartz (g n) g₀ χ hχ hc (hg n) hg₀ i j) x).re * (φ : CoordinateSpace → ℝ) x)
      atTop (𝓝 0) := by
  let F n := localizedMetricEntry (g n) g₀ χ i j
  have hF (n : ℕ) : ContDiff ℝ ∞ (F n) := hχ.mul ((hg n i j).sub (hg₀ i j))
  have hConv (K : Set CoordinateSpace) (_ : IsCompact K) (_ : K ⊆ univ) :
      TendstoUniformlyOn F (fun _ => 0) atTop K := by
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    filter_upwards [hSmall ε hε] with n hn x _
    rw [dist_zero_left, ← Complex.norm_real (F n x)]
    exact hn x
  have h := Burnett.Analysis.LocalWeakDerivative.integral_test_directional_tendsto_zero
    (U := univ) isOpen_univ (test_smooth φ) (test_compactSupport φ) (subset_univ _)
    (fun n => (hF n).contDiffOn) hConv (EuclideanSpace.single a 1)
  refine h.congr fun n => integral_congr_ae (Eventually.of_forall fun x => ?_)
  change (φ : CoordinateSpace → ℝ) x * scalarPartial (F n) a x =
    (coordinateDerivative a (localizedMetricSchwartz (g n) g₀ χ hχ hc (hg n) hg₀ i j) x).re *
      (φ : CoordinateSpace → ℝ) x
  rw [localizedMetricSchwartz_coordinateDerivative_eq_partial, Complex.ofReal_re]
  exact mul_comm _ _

/-- One common cutoff and the real whole-space L² and test limits for the
actual derivative components used in the projected defect pairing. -/
theorem exists_localizedMetricSchwartz_coordinateDerivative_defect_inputs
    (U : Set CoordinateSpace) (hU : IsOpen U)
    (g : ℕ → CoordinateSpace → Tensor2) (g₀ : CoordinateSpace → Tensor2)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ U)
    (hg : ∀ n, SmoothCoordinateComponents (g n)) (hg₀ : SmoothCoordinateComponents g₀)
    (hConv : TendstoUniformlyOn g g₀ atTop (tsupport χ))
    (B : ℝ≥0) (hDeriv : ∀ n i j x, x ∈ tsupport χ →
      ‖fderiv ℝ (fun y => g n y i j - g₀ y i j) x‖ ≤ (B : ℝ)) :
    let z := fun n => localizedMetricSchwartz (g n) g₀ χ hχ hc (hg n) hg₀
    let f (n : ℕ) (a i j : Index) (x : CoordinateSpace) := (coordinateDerivative a (z n i j) x).re
    ∃ (θ : D) (C : ℝ), 0 ≤ C ∧
      tsupport (θ : CoordinateSpace → ℝ) ⊆ U ∧
      (θ : CoordinateSpace → ℝ) =ᶠ[𝓝ˢ (tsupport χ)] (fun _ => 1) ∧
      (∀ n a i j x, f n a i j x ≠ 0 → (θ : CoordinateSpace → ℝ) x = 1) ∧
      (∀ n a i j, ContDiff ℝ ∞ (f n a i j)) ∧
      ∃ hLp : ∀ n a i j, MemLp (f n a i j) 2 volume,
        (∀ n a i j, ‖(hLp n a i j).toLp (f n a i j)‖ ≤ C) ∧
        ∀ a i j (φ : D), Tendsto (fun n => ∫ x, f n a i j x * (φ : CoordinateSpace → ℝ) x)
          atTop (𝓝 0) := by
  let z := fun n => localizedMetricSchwartz (g n) g₀ χ hχ hc (hg n) hg₀
  let f (n : ℕ) (a i j : Index) (x : CoordinateSpace) := (coordinateDerivative a (z n i j) x).re
  let K := tsupport χ
  obtain ⟨L, hL, hSmall⟩ := localizedMetricSchwartz_uniform_inputs g g₀ hg hg₀ χ hχ hc hConv B hDeriv
  obtain ⟨η, hη, hηc, hηU, V, hV, hKV, _, hηV⟩ := exists_projectedChartCutoff hc hU hχU
  let θ : D := ⟨η, hη, hηc⟩
  have hθNear : (θ : CoordinateSpace → ℝ) =ᶠ[𝓝ˢ K] (fun _ => 1) :=
    eventually_of_mem (hV.mem_nhdsSet.mpr hKV) fun x hx => hηV hx
  have hZero (n : ℕ) (a i j : Index) (x : CoordinateSpace) (hx : x ∉ K) : f n a i j x = 0 := by
    have hSupport : tsupport (z n i j : CoordinateSpace → ℂ) ⊆ K :=
      localizedMetricSchwartz_tsupport_subset (g n) g₀ χ hχ hc (hg n) hg₀ i j
    have hz : fderiv ℝ (z n i j : CoordinateSpace → ℂ) x = 0 := by
      by_contra h
      exact hx (hSupport (support_fderiv_subset ℝ h))
    simp only [f, coordinateDerivative, SchwartzMap.pderivCLM_apply, hz,
      ContinuousLinearMap.zero_apply, Complex.zero_re]
  have hCut (n : ℕ) (a i j : Index) (x : CoordinateSpace) (hx : f n a i j x ≠ 0) :
      (θ : CoordinateSpace → ℝ) x = 1 := by
    have hmem : x ∈ K := by_contra fun h => hx (hZero n a i j x h)
    exact hηV (hKV hmem)
  have hf (n : ℕ) (a i j : Index) : ContDiff ℝ ∞ (f n a i j) :=
    Complex.reCLM.contDiff.comp ((coordinateDerivative a (z n i j)).smooth ⊤)
  have hLp (n : ℕ) (a i j : Index) : MemLp (f n a i j) 2 volume :=
    (hf n a i j).continuous.memLp_of_hasCompactSupport <|
      hc.mono' (fun x hx => by_contra fun hn => hx (hZero n a i j x hn))
  refine ⟨θ, (L : ℝ) * ‖valueLp θ‖, by positivity, hηU, hθNear, hCut, hf, hLp, ?_, ?_⟩
  · intro n a i j
    have hpoint (x : CoordinateSpace) : ‖f n a i j x‖ ≤ ‖((L : ℝ) • (θ : CoordinateSpace → ℝ)) x‖ := by
      by_cases hx : x ∈ K
      · have hθ : (θ : CoordinateSpace → ℝ) x = 1 := hηV (hKV hx)
        rw [Pi.smul_apply, smul_eq_mul, hθ, mul_one, Real.norm_of_nonneg L.coe_nonneg]
        have hOp := (fderiv ℝ (z n i j) x).le_opNorm (EuclideanSpace.single a (1 : ℝ))
        rw [EuclideanSpace.norm_single, norm_one, mul_one] at hOp
        have hD := hOp.trans (norm_fderiv_le_of_lipschitz ℝ (hL n i j))
        exact (Complex.abs_re_le_norm (coordinateDerivative a (z n i j) x)).trans
          (by simpa only [coordinateDerivative, SchwartzMap.pderivCLM_apply] using hD)
      · rw [hZero n a i j x hx, norm_zero]
        exact norm_nonneg _
    have hs := (test_memLp θ).const_smul (L : ℝ)
    have hnorm : ‖(hLp n a i j).toLp (f n a i j)‖ ≤ ‖hs.toLp ((L : ℝ) • (θ : CoordinateSpace → ℝ))‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [(hLp n a i j).coeFn_toLp, hs.coeFn_toLp] with x hx hy
      rw [hx, hy]
      exact hpoint x
    change ‖(hLp n a i j).toLp (f n a i j)‖ ≤ ‖(L : ℝ) • valueLp θ‖ at hnorm
    simpa only [norm_smul, Real.norm_of_nonneg L.coe_nonneg] using hnorm
  · intro a i j φ
    exact localizedMetricSchwartz_coordinateDerivative_test_tendsto_zero g g₀ χ hχ hc hg hg₀
      i j a (fun ε hε => (hSmall ε hε).mono fun n hn x => hn x i j) φ

end Burnett.P01
