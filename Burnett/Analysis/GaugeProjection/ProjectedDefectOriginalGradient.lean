import Burnett.Analysis.GaugeProjection.ProjectedDefectLocalizationError

set_option autoImplicit false
set_option maxHeartbeats 3800000

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.A07 (coordinateDerivative)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped ContDiff Topology

/-- The half-density-weighted derivative of the actual cutoff fluctuation
differs by a strongly vanishing L² sequence from the same half-density times
the cutoff derivative field used in the original defect witness. -/
theorem localizedMetric_weighted_derivative_sub_original_tendsto_zero
    (g : ℕ → CoordinateSpace → Tensor2) (g₀ : CoordinateSpace → Tensor2)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hg : ∀ n, SmoothCoordinateComponents (g n)) (hg₀ : SmoothCoordinateComponents g₀)
    (hConv : TendstoUniformlyOn g g₀ atTop (tsupport χ))
    (d : D) (ρ : BoundedSymbol CoordinateSpace) (hρ : ∀ x, ρ x = ((d : CoordinateSpace → ℝ) x : ℂ))
    (i j a : Index) (W : ℕ → ComplexL2 CoordinateSpace)
    (hW : ∀ n, (W n : CoordinateSpace → ℂ) =ᵐ[volume] fun x =>
      ((d : CoordinateSpace → ℝ) x * χ x *
        (coordinateJet (g n) x a i j - coordinateJet g₀ x a i j) : ℝ)) :
    Tendsto (fun n => symbolCLM ρ
        ((coordinateDerivative a (localizedMetricSchwartz (g n) g₀ χ hχ hc (hg n) hg₀ i j)).toLp 2 volume) -
      W n) atTop (𝓝 0) := by
  let z n := localizedMetricSchwartz (g n) g₀ χ hχ hc (hg n) hg₀ i j
  let w (x : CoordinateSpace) := (d : CoordinateSpace → ℝ) x * scalarPartial χ a x
  let f (n : ℕ) (x : CoordinateSpace) := g n x i j - g₀ x i j
  have hwc : Continuous w :=
    (test_smooth d).continuous.mul
      ((hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hSupp (x : CoordinateSpace) (hx : x ∉ tsupport χ) : w x = 0 := by
    have hz : fderiv ℝ χ x = 0 := by
      by_contra hn
      exact hx (support_fderiv_subset ℝ hn)
    simp [w, scalarPartial, hz]
  have hwCompact : HasCompactSupport w := hc.mono' (fun x hx => by
    by_contra h
    exact hx (hSupp x h))
  have hw : MemLp w 2 volume :=
    hwc.memLp_of_hasCompactSupport hwCompact
  have hf : TendstoUniformlyOn f (fun _ => 0) atTop (tsupport χ) := by
    apply Metric.tendstoUniformlyOn_iff.2
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hConv ε hε] with n hn
    intro x hx
    rw [dist_zero_left]
    have hs := hn x hx
    rw [dist_comm, dist_eq_norm] at hs
    exact ((norm_le_pi_norm ((g n x - g₀ x) i) j).trans
      (norm_le_pi_norm (g n x - g₀ x) i)).trans_lt hs
  refine tendsto_weighted_localizationError_L2_zero (tsupport χ) w hw hSupp f
    hf (fun n => symbolCLM ρ ((coordinateDerivative a (z n)).toLp 2 volume) - W n) ?_
  intro n
  let S := (coordinateDerivative a (z n)).toLp 2 volume
  let T := symbolCLM ρ S
  filter_upwards [hW n, Lp.coeFn_sub T (W n), symbolL2_ae ρ S,
    (coordinateDerivative a (z n)).coeFn_toLp 2 volume] with x h₀ h₁ h₂ h₃
  change (T - W n) x = _
  rw [h₁, Pi.sub_apply]
  change symbolL2 ρ S x - W n x = _
  rw [h₂, h₃, hρ, h₀]
  have hD := localizedMetricSchwartz_coordinateDerivative_real (g n) g₀ χ hχ hc (hg n) hg₀ i j a x
  change coordinateDerivative a (z n) x = _ at hD
  rw [hD]
  simp only [w, f, Complex.ofReal_mul, Complex.ofReal_add]
  ring

end Burnett.P01
