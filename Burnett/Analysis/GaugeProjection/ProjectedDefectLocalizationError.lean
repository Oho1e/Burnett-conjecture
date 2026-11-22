import Burnett.Analysis.GaugeProjection.LocalizedMetricSchwartzInputs
import Burnett.Analysis.GaugeProjection.ProjectedSourceLocalization

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter Set
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Fourier
open Burnett.A07 (coordinateDerivative)
open scoped ContDiff ENNReal Topology

private theorem weight_smul_norm (w : CoordinateSpace → ℝ) (t : ℝ) :
    (eLpNorm (t • w) 2 volume).toReal = ‖t‖ * (eLpNorm w 2 volume).toReal := by
  rw [eLpNorm_const_smul, ENNReal.toReal_mul]
  change (‖t‖₊ : ℝ≥0∞).toReal * _ = _
  rfl

/-- Multiplying a uniformly small chart perturbation by a fixed compactly
supported weight produces a strongly vanishing L² error, including the
weight consisting of a derivative of the chart cutoff and a half-density. -/
theorem tendsto_weighted_localizationError_L2_zero
    (K : Set CoordinateSpace) (w : CoordinateSpace → ℝ) (hw : MemLp w 2 volume)
    (hSupp : ∀ x ∉ K, w x = 0) (f : ℕ → CoordinateSpace → ℝ)
    (hSmall : TendstoUniformlyOn f (fun _ => 0) atTop K)
    (e : ℕ → ComplexL2 CoordinateSpace)
    (hError : ∀ n, (e n : CoordinateSpace → ℂ) =ᵐ[volume] fun x => ((w x * f n x : ℝ) : ℂ)) :
    Tendsto e atTop (𝓝 0) := by
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  rw [Metric.tendsto_nhds]
  intro ε hε
  let C := (eLpNorm w 2 volume).toReal
  let δ := ε / (C + 1)
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hSmall) δ hδ] with n hn
  have hδw : eLpNorm (δ • w) 2 (volume : Measure CoordinateSpace) ≠ ⊤ :=
    (hw.const_smul δ).2.ne
  have he : eLpNorm (e n : CoordinateSpace → ℂ) 2 volume ≤ eLpNorm (δ • w) 2 volume := by
    apply eLpNorm_mono_ae
    filter_upwards [hError n] with x hx
    rw [hx, Complex.norm_real, norm_mul]
    change ‖w x‖ * ‖f n x‖ ≤ ‖δ * w x‖
    rw [norm_mul, Real.norm_of_nonneg hδ.le, mul_comm δ]
    by_cases hxK : x ∈ K
    · have hfn : ‖f n x‖ ≤ δ := by
        simpa only [dist_zero_left] using (hn x hxK).le
      exact mul_le_mul_of_nonneg_left hfn (norm_nonneg _)
    · simp [hSupp x hxK]
  have hE : ‖e n‖ ≤ δ * C := by
    rw [Lp.norm_def]
    exact (ENNReal.toReal_mono hδw he).trans_eq
      ((weight_smul_norm w δ).trans (by rw [Real.norm_of_nonneg hδ.le]))
  rw [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)]
  refine hE.trans_lt ?_
  change ε / (C + 1) * C < ε
  rw [show ε / (C + 1) * C = ε * C / (C + 1) by ring]
  exact (div_lt_iff₀ (by positivity)).2 (by nlinarith)

/-- The real part of the exact localized derivative uses the same cutoff
metric fluctuation as the whole-space source. -/
theorem localizedMetricSchwartz_coordinateDerivative_real
    (g g₀ : CoordinateSpace → Tensor2) (χ : CoordinateSpace → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hg : SmoothCoordinateComponents g) (hg₀ : SmoothCoordinateComponents g₀)
    (i j a : Index) (x : CoordinateSpace) :
    coordinateDerivative a (localizedMetricSchwartz g g₀ χ hχ hc hg hg₀ i j) x =
      ((χ x * (coordinateJet g x a i j - coordinateJet g₀ x a i j) +
        scalarPartial χ a x * (g x i j - g₀ x i j) : ℝ) : ℂ) := by
  let f := localizedMetricEntry g g₀ χ i j
  have hf : ContDiff ℝ ∞ f := hχ.mul ((hg i j).sub (hg₀ i j))
  have hd := (Complex.ofRealCLM.hasFDerivAt.comp x (hf.differentiable (by simp) x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => (f y : ℂ)) x = _ at hd
  rw [coordinateDerivative, SchwartzMap.pderivCLM_apply]
  change fderiv ℝ (fun y => (f y : ℂ)) x (EuclideanSpace.single a 1) = _
  rw [hd]
  change (scalarPartial f a x : ℂ) = _
  have hSub : scalarPartial (fun y => g y i j - g₀ y i j) a x =
      coordinateJet g x a i j - coordinateJet g₀ x a i j := by
    simp only [scalarPartial, coordinateJet,
      fderiv_fun_sub ((hg i j).differentiable (by simp) x) ((hg₀ i j).differentiable (by simp) x),
      ContinuousLinearMap.sub_apply]
  change (scalarPartial (fun y => χ y * (g y i j - g₀ y i j)) a x : ℂ) = _
  rw [scalarPartial_product _ _ _ _ (hχ.differentiable (by simp) x)
    (((hg i j).sub (hg₀ i j)).differentiable (by simp) x), hSub]
  congr 1
  ring

end Burnett.P01
