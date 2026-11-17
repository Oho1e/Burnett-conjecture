import Burnett.Analysis.IBP.CompactIBP
import Burnett.Geometry.ManifoldMetricSequence
import Burnett.Geometry.SmoothMetricConnection
import Burnett.Geometry.ManifoldVolumeRegularity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff Topology

namespace Burnett.Analysis.LocalWeakDerivative

abbrev Space := EuclideanSpace ℝ (Fin 4)

theorem tsupport_directional_subset (ψ : Space → ℝ) (v : Space) :
    tsupport (fun x => fderiv ℝ ψ x v) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro x hx
  apply support_fderiv_subset ℝ
  intro hz
  exact hx (by simp [hz])

theorem contDiff_test_mul_local {U : Set Space} (hU : IsOpen U)
    {ψ f : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hsψ : tsupport ψ ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (fun x => ψ x * f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hψ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
  · have hxs : x ∉ tsupport ψ := fun h => hx (hsψ h)
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Space => (0 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxs] with y hy
    simp [hy]

theorem integral_directional_eq_zero {F : Space → ℝ}
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F) (v : Space) :
    (∫ x, fderiv ℝ F x v) = 0 := by
  have h := X02.CompactIBP.integral_test_directional hF hcF
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space => (1 : ℝ))) v
  simpa using h.symm

theorem fderiv_test_mul_local {U : Set Space} (hU : IsOpen U)
    {ψ f : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hsψ : tsupport ψ ⊆ U) (hf : ContDiffOn ℝ ∞ f U) (v x : Space) :
    fderiv ℝ (fun y => ψ y * f y) x v =
      fderiv ℝ ψ x v * f x + ψ x * fderiv ℝ f x v := by
  by_cases hx : x ∈ U
  · rw [fderiv_fun_mul (hψ.differentiable (by simp) x)
      ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  · have hxs : x ∉ tsupport ψ := fun h => hx (hsψ h)
    have hz : ψ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxs
    have hp : (fun y => ψ y * f y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hz] with y hy
      simp [hy]
    rw [hp.fderiv_eq, hz.fderiv_eq]
    simp [image_eq_zero_of_notMem_tsupport hxs]

theorem integral_test_directional_local {U : Set Space} (hU : IsOpen U)
    {ψ f : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ U) (hf : ContDiffOn ℝ ∞ f U) (v : Space) :
    (∫ x, ψ x * fderiv ℝ f x v) = -(∫ x, fderiv ℝ ψ x v * f x) := by
  have hDψ : ContDiff ℝ ∞ (fun x => fderiv ℝ ψ x v) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hsDψ : tsupport (fun x => fderiv ℝ ψ x v) ⊆ U :=
    (tsupport_directional_subset ψ v).trans hsψ
  have hDf : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x v) U :=
    (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hA : Integrable (fun x => fderiv ℝ ψ x v * f x) :=
    (contDiff_test_mul_local hU hDψ hsDψ hf).continuous.integrable_of_hasCompactSupport
      (hcψ.fderiv_apply ℝ v).mul_right
  have hB : Integrable (fun x => ψ x * fderiv ℝ f x v) :=
    (contDiff_test_mul_local hU hψ hsψ hDf).continuous.integrable_of_hasCompactSupport
      hcψ.mul_right
  have h := integral_directional_eq_zero (contDiff_test_mul_local hU hψ hsψ hf)
    hcψ.mul_right v
  simp_rw [fderiv_test_mul_local hU hψ hsψ hf v] at h
  rw [integral_add hA hB] at h
  linarith

theorem integral_test_local_tendsto_zero {U : Set Space} (hU : IsOpen U)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ U) {f : ℕ → Space → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) U)
    (hu : ∀ K : Set Space, IsCompact K → K ⊆ U →
      TendstoUniformlyOn f (fun _ => 0) atTop K) :
    Tendsto (fun n => ∫ x, ψ x * f n x) atTop (𝓝 0) := by
  have ht := hu (tsupport ψ) hcψ hsψ
  have hm : ∀ᶠ n in atTop, AEStronglyMeasurable (fun x => ψ x * f n x) volume :=
    Eventually.of_forall (fun n =>
      (contDiff_test_mul_local hU hψ hsψ (hf n)).continuous.aestronglyMeasurable)
  have hb : ∀ᶠ n in atTop, ∀ᵐ x : Space, ‖ψ x * f n x‖ ≤ ‖ψ x‖ := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp ht 1 (by norm_num)] with n hn
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ tsupport ψ
    · rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      simpa only [dist_zero_left] using (hn x hx).le
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hl : ∀ᵐ x : Space, Tendsto (fun n => ψ x * f n x) atTop (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ tsupport ψ
    · simpa only [mul_zero] using (ht.tendsto_at hx).const_mul (ψ x)
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]
      exact tendsto_const_nhds
  have h := tendsto_integral_filter_of_dominated_convergence (fun x => ‖ψ x‖)
    hm hb (hψ.continuous.integrable_of_hasCompactSupport hcψ).norm hl
  simpa only [integral_zero] using h

theorem integral_test_directional_tendsto_zero {U : Set Space} (hU : IsOpen U)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ U) {f : ℕ → Space → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) U)
    (hu : ∀ K : Set Space, IsCompact K → K ⊆ U →
      TendstoUniformlyOn f (fun _ => 0) atTop K) (v : Space) :
    Tendsto (fun n => ∫ x, ψ x * fderiv ℝ (f n) x v) atTop (𝓝 0) := by
  have hDψ : ContDiff ℝ ∞ (fun x => fderiv ℝ ψ x v) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have h := (integral_test_local_tendsto_zero hU hDψ (hcψ.fderiv_apply ℝ v)
    ((tsupport_directional_subset ψ v).trans hsψ) hf hu).neg
  simp only [neg_zero] at h
  exact h.congr (fun n => (integral_test_directional_local hU hψ hcψ hsψ (hf n) v).symm)

theorem integral_test_coefficient_directional_tendsto_zero {U : Set Space} (hU : IsOpen U)
    {ψ a : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ U) (ha : ContDiffOn ℝ ∞ a U) {f : ℕ → Space → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) U)
    (hu : ∀ K : Set Space, IsCompact K → K ⊆ U →
      TendstoUniformlyOn f (fun _ => 0) atTop K) (v : Space) :
    Tendsto (fun n => ∫ x, ψ x * a x * fderiv ℝ (f n) x v) atTop (𝓝 0) :=
  integral_test_directional_tendsto_zero hU (contDiff_test_mul_local hU hψ hsψ ha)
    hcψ.mul_right (tsupport_mul_subset_left.trans hsψ) hf hu v

theorem integral_test_second_directional_local {U : Set Space} (hU : IsOpen U)
    {ψ f : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ U) (hf : ContDiffOn ℝ ∞ f U) (v w : Space) :
    (∫ x, ψ x * fderiv ℝ (fun y => fderiv ℝ f y w) x v) =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ ψ y v) x w * f x := by
  have hDf : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y w) U :=
    (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hDψ : ContDiff ℝ ∞ (fun y => fderiv ℝ ψ y v) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  rw [integral_test_directional_local hU hψ hcψ hsψ hDf v,
    integral_test_directional_local hU hDψ (hcψ.fderiv_apply ℝ v)
      ((tsupport_directional_subset ψ v).trans hsψ) hf w, neg_neg]

theorem integral_test_second_directional_tendsto_zero {U : Set Space} (hU : IsOpen U)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ U) {f : ℕ → Space → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) U)
    (hu : ∀ K : Set Space, IsCompact K → K ⊆ U →
      TendstoUniformlyOn f (fun _ => 0) atTop K) (v w : Space) :
    Tendsto (fun n => ∫ x, ψ x * fderiv ℝ (fun y => fderiv ℝ (f n) y w) x v)
      atTop (𝓝 0) := by
  have hDψ : ContDiff ℝ ∞ (fun y => fderiv ℝ ψ y v) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDDψ : ContDiff ℝ ∞ (fun x => fderiv ℝ (fun y => fderiv ℝ ψ y v) x w) :=
    (hDψ.fderiv_right (by simp)).clm_apply contDiff_const
  have h := integral_test_local_tendsto_zero hU hDDψ
    ((hcψ.fderiv_apply ℝ v).fderiv_apply ℝ w)
    (((tsupport_directional_subset _ w).trans (tsupport_directional_subset ψ v)).trans hsψ)
    hf hu
  exact h.congr (fun n =>
    (integral_test_second_directional_local hU hψ hcψ hsψ (hf n) v w).symm)

theorem integral_test_coefficient_second_directional_tendsto_zero {U : Set Space}
    (hU : IsOpen U) {ψ a : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ U)
    (ha : ContDiffOn ℝ ∞ a U) {f : ℕ → Space → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) U)
    (hu : ∀ K : Set Space, IsCompact K → K ⊆ U →
      TendstoUniformlyOn f (fun _ => 0) atTop K) (v w : Space) :
    Tendsto (fun n => ∫ x, ψ x * a x *
      fderiv ℝ (fun y => fderiv ℝ (f n) y w) x v) atTop (𝓝 0) :=
  integral_test_second_directional_tendsto_zero hU (contDiff_test_mul_local hU hψ hsψ ha)
    hcψ.mul_right (tsupport_mul_subset_left.trans hsψ) hf hu v w

open Burnett.RicciSymbol
open Burnett.Geometry
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.ManifoldMetricSequence
open scoped Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem component_difference_smoothOn (g : ℕ → Field (M := M)) (g0 : Field (M := M))
    (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n)) (c : M) (i j : Index) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun y =>
      metricComponents (coordinateBilinear (g n) c) y i j -
      metricComponents (coordinateBilinear g0 c) y i j) (chartAt CoordinateSpace c).target :=
  (ManifoldBilinear.contDiffOn_metricComponents (g n) (hg n) c i j).sub
    (ManifoldBilinear.contDiffOn_metricComponents g0 h0 c i j)

theorem component_difference_uniform_of_physical_C0loc (r : Metric (M := M))
    (g : ℕ → Field (M := M)) (g0 : Field (M := M))
    (hu : LocallyUniformlyConverges r g g0) (c : M) (i j : Index)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    TendstoUniformlyOn (fun n y =>
      metricComponents (coordinateBilinear (g n) c) y i j -
      metricComponents (coordinateBilinear g0 c) y i j) (fun _ => 0) atTop K := by
  have ht := components_uniform_of_physical_C0loc r g g0 hu c K hK hKt
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp ht ε hε] with n hn
  intro y hy
  have hb : ‖(metricComponents (coordinateBilinear (g n) c) y -
      metricComponents (coordinateBilinear g0 c) y) i j‖ ≤
      ‖metricComponents (coordinateBilinear (g n) c) y -
      metricComponents (coordinateBilinear g0 c) y‖ :=
    (norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i)
  have hs : ‖metricComponents (coordinateBilinear (g n) c) y -
      metricComponents (coordinateBilinear g0 c) y‖ < ε := by
    simpa only [dist_eq_norm, norm_sub_rev] using hn y hy
  simpa only [dist_zero_left] using hb.trans_lt hs

theorem original_component_first_derivative_test (r : Metric (M := M))
    (g : ℕ → Field (M := M)) (g0 : Field (M := M))
    (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n))
    (hu : LocallyUniformlyConverges r g g0) (c : M) (i j : Index)
    {ψ a : CoordinateSpace → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target)
    (ha : ContDiffOn ℝ ∞ a (chartAt CoordinateSpace c).target) (v : CoordinateSpace) :
    Tendsto (fun n => ∫ y, ψ y * a y * fderiv ℝ (fun x =>
      metricComponents (coordinateBilinear (g n) c) x i j -
      metricComponents (coordinateBilinear g0 c) x i j) y v) atTop (𝓝 0) :=
  integral_test_coefficient_directional_tendsto_zero (chartAt CoordinateSpace c).open_target
    hψ hcψ hsψ ha (component_difference_smoothOn g g0 h0 hg c i j)
    (component_difference_uniform_of_physical_C0loc r g g0 hu c i j) v

theorem original_component_second_derivative_test (r : Metric (M := M))
    (g : ℕ → Field (M := M)) (g0 : Field (M := M))
    (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n))
    (hu : LocallyUniformlyConverges r g g0) (c : M) (i j : Index)
    {ψ a : CoordinateSpace → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target)
    (ha : ContDiffOn ℝ ∞ a (chartAt CoordinateSpace c).target) (v w : CoordinateSpace) :
    Tendsto (fun n => ∫ y, ψ y * a y * fderiv ℝ (fun z => fderiv ℝ (fun x =>
      metricComponents (coordinateBilinear (g n) c) x i j -
      metricComponents (coordinateBilinear g0 c) x i j) z w) y v) atTop (𝓝 0) :=
  integral_test_coefficient_second_directional_tendsto_zero (chartAt CoordinateSpace c).open_target
    hψ hcψ hsψ ha (component_difference_smoothOn g g0 h0 hg c i j)
    (component_difference_uniform_of_physical_C0loc r g g0 hu c i j) v w

theorem smooth_coordinate_volume_factor (g0 : Field (M := M)) (h0 : IsSmooth g0)
    (hn0 : IsNondegenerate g0) (c : M) :
    ContDiffOn ℝ ∞ (fun y => Real.sqrt
      |Matrix.det (metricComponents (coordinateBilinear g0 c) y)|)
      (chartAt CoordinateSpace c).target := by
  have hd := SmoothMetricConnection.contDiffOn_det
    (metricComponents (coordinateBilinear g0 c)) (chartAt CoordinateSpace c).target
    (ManifoldBilinear.contDiffOn_metricComponents g0 h0 c)
  have hne : ∀ y ∈ (chartAt CoordinateSpace c).target,
      Matrix.det (metricComponents (coordinateBilinear g0 c) y) ≠ 0 :=
    fun y hy => ManifoldVolumeRegularity.coordinate_det_ne_zero g0 hn0 c hy
  have ha := hd.norm ℝ hne
  simp only [Real.norm_eq_abs] at ha
  exact ha.sqrt (fun y hy => abs_ne_zero.mpr (hne y hy))

theorem original_density_connection_first_derivative_test (r : Metric (M := M))
    (g : ℕ → Field (M := M)) (g0 : Field (M := M))
    (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n)) (hn0 : IsNondegenerate g0)
    (hu : LocallyUniformlyConverges r g g0) (c : M) (i j a b d : Index)
    {ψ : CoordinateSpace → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target) (v : CoordinateSpace) :
    Tendsto (fun n => ∫ y, ψ y *
      (Real.sqrt |Matrix.det (metricComponents (coordinateBilinear g0 c) y)| *
        BackgroundConnection.computedConnection (coordinateBilinear g0 c) y a b d) *
      fderiv ℝ (fun x => metricComponents (coordinateBilinear (g n) c) x i j -
        metricComponents (coordinateBilinear g0 c) x i j) y v) atTop (𝓝 0) := by
  have hΓ := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g0 h0 hn0 c
  have hΓabd := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ a) b) d
  exact original_component_first_derivative_test r g g0 h0 hg hu c i j hψ hcψ hsψ
    ((smooth_coordinate_volume_factor g0 h0 hn0 c).mul hΓabd) v

theorem original_density_second_derivative_test (r : Metric (M := M))
    (g : ℕ → Field (M := M)) (g0 : Field (M := M))
    (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n)) (hn0 : IsNondegenerate g0)
    (hu : LocallyUniformlyConverges r g g0) (c : M) (i j : Index)
    {ψ a : CoordinateSpace → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target)
    (ha : ContDiffOn ℝ ∞ a (chartAt CoordinateSpace c).target) (v w : CoordinateSpace) :
    Tendsto (fun n => ∫ y, ψ y *
      (Real.sqrt |Matrix.det (metricComponents (coordinateBilinear g0 c) y)| * a y) *
      fderiv ℝ (fun z => fderiv ℝ (fun x =>
        metricComponents (coordinateBilinear (g n) c) x i j -
        metricComponents (coordinateBilinear g0 c) x i j) z w) y v) atTop (𝓝 0) :=
  original_component_second_derivative_test r g g0 h0 hg hu c i j hψ hcψ hsψ
    ((smooth_coordinate_volume_factor g0 h0 hn0 c).mul ha) v w

end Burnett.Analysis.LocalWeakDerivative
