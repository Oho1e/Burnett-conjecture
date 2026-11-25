import Burnett.Analysis.Microlocal.Overlap.ReceivingChartCovariantGradient
import Burnett.Geometry.MaximalChart.UniformMetric

/-! A uniform bound for the actual half-density jet by the intrinsic covariant derivative norm. -/

set_option autoImplicit false
set_option maxRecDepth 4700
set_option maxHeartbeats 4200000

noncomputable section
namespace Burnett.Microlocal.AtlasVolumeGradient

open Set Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open CovariantTensorNorm
open Burnett.Geometry.IntrinsicDhMeasure (normScalar normScalar_eq_chart)
open Burnett.Geometry.ChartVolume (derivativeMatrix)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- The intrinsic norm of the actual covariant derivative in any compatible receiving chart. -/
theorem normScalar_eq_fixedCovariantJet (r : Metric (M := M)) (H : Field (M := M))
    (hH : IsSmooth H) (c : AtlasChart M) {x : CoordinateSpace} (hx : x ∈ c.chart.target) :
    normScalar r H (c.chart.symm x) =
      norm3 (metricComponents (fixedForm r.inner c) x) (fixedCovariantJet r.inner H c x) := by
  let q := c.chart.symm x
  let d := AtlasChart.atPoint q
  let e := c.transition d
  have he : x ∈ e.source := ⟨hx, mem_chart_source CoordinateSpace q⟩
  have ht : e x ∈ (chartAt CoordinateSpace q).target := (e.mapsTo he).1
  have hi : (chartAt CoordinateSpace q).symm (e x) = q := d.chart.left_inv he.2
  rw [fixedForm_matrix_change r.inner c d he,
    fixedCovariantJet_change r.inner H (isSmooth_inner r) r.symm
      (GlobalLeviCivita.inner_nondegenerate r) hH c d x he,
    TensorCoordinateChange.norm3_pullback _ _ (fixedDerivativeMatrix_isUnit c d he),
    fixedForm_eq_preferred_components r.inner q ht, fixedCovariantJet_eq_preferred r H q ht]
  have h := normScalar_eq_chart r H hH q ((chartAt CoordinateSpace q).symm (e x))
    ((chartAt CoordinateSpace q).symm_mapsTo ht)
  rw [(chartAt CoordinateSpace q).right_inv ht, hi] at h
  exact h

/-- One fixed compact coordinate window has a uniform component bound for every smooth tensor. -/
theorem exists_fixedCovariantJet_norm_le_intrinsic (r : Metric (M := M)) (c : AtlasChart M)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKt : K ⊆ c.chart.target) :
    ∃ C > 0, ∀ (H : Field (M := M)), IsSmooth H → ∀ x ∈ K,
      ‖fixedCovariantJet r.inner H c x‖ ≤ C * normScalar r H (c.chart.symm x) := by
  let R := metricComponents (fixedForm r.inner c)
  obtain ⟨C, hC, hBound⟩ := exists_uniform_norm3_control R K hK
    (fun i => (fixedForm_components_smooth r.inner (isSmooth_inner r) c i i).continuousOn.mono hKt)
    (fun x hx => fixedRiemannian_posDef r c (hKt hx))
  refine ⟨C, hC, fun H hH x hx => ?_⟩
  rw [normScalar_eq_fixedCovariantJet r H hH c (hKt hx)]
  exact hBound x hx _

/-- The actual half-density input is bounded by the intrinsic norm times the same half-density. -/
theorem exists_fixedVolumeCovariantGradientSchwartz_pointwise_le (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hn : IsNondegenerate B) (c : AtlasChart M) (χ : D)
    (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ c.chart.target) :
    ∃ C > 0, ∀ (n : ℕ) (i : JetSlot) (x : CoordinateSpace), x ∈ tsupport (χ : CoordinateSpace → ℝ) →
      ‖fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n i x‖ ≤
        C * fixedHalfDensity B c x * normScalar r (fun m => g n m - B m) (c.chart.symm x) := by
  let S := tsupport (χ : CoordinateSpace → ℝ)
  have hS : IsCompact S := test_compactSupport χ
  obtain ⟨C₁, hC₁, hBound⟩ := exists_fixedCovariantJet_norm_le_intrinsic r c S hS hχ
  obtain ⟨C₂, hC₂, hCutoff⟩ :=
    (hS.image (test_smooth χ).continuous).isBounded.exists_pos_norm_le
  refine ⟨C₂ * C₁, mul_pos hC₂ hC₁, fun n i x hx => ?_⟩
  let J := fixedCovariantJet r.inner (fun m => g n m - B m) c x
  let D := fixedHalfDensity B c x
  let N := normScalar r (fun m => g n m - B m) (c.chart.symm x)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hCoef : ‖(χ : CoordinateSpace → ℝ) x‖ ≤ C₂ := hCutoff _ (mem_image_of_mem _ hx)
  have hJet : ‖J i.1 i.2.1 i.2.2‖ ≤ C₁ * N :=
    ((norm_le_pi_norm (J i.1 i.2.1) i.2.2).trans
      ((norm_le_pi_norm (J i.1) i.2.1).trans (norm_le_pi_norm J i.1))).trans
      (hBound _ (IntrinsicCov2.isSmooth_difference (g n) B (hg n) hB) x hx)
  rw [fixedVolumeCovariantGradientSchwartz_apply, Complex.norm_real, norm_mul, norm_mul]
  change ‖(χ : CoordinateSpace → ℝ) x‖ * ‖D‖ * ‖J i.1 i.2.1 i.2.2‖ ≤ C₂ * C₁ * D * N
  rw [Real.norm_of_nonneg hD]
  calc
    _ ≤ (C₂ * D) * (C₁ * N) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hCoef hD) hJet (norm_nonneg _) (mul_nonneg hC₂.le hD)
    _ = _ := by ring

end Burnett.Microlocal.AtlasVolumeGradient
