import Burnett.Analysis.Microlocal.Overlap.ReceivingChartVolumeInputs

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2100

noncomputable section

namespace Burnett.V03

open Set Filter MeasureTheory Burnett.Geometry ConnectionDifference
open ManifoldMetric ManifoldBilinear ManifoldMetricTransition MaximalChart
open Burnett.Microlocal.AtlasVolumeGradient
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [SecondCountableTopology M]

local notation "E₀" => CoordinateSpace

/-- The coordinate density used in the already constructed volume gradients. -/
def fixedCoordinateVolumeDensity (B : Field (M := M)) (c : AtlasChart M) (x : E₀) : ℝ :=
  Real.sqrt |Matrix.det (metricComponents (fixedForm B c) x)|

omit [IsManifold Model ∞ M] [SecondCountableTopology M] in
theorem fixedHalfDensity_sq (B : Field (M := M)) (c : AtlasChart M) (x : E₀) :
    (fixedHalfDensity B c x)^2 = fixedCoordinateVolumeDensity B c x :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

omit [SecondCountableTopology M] in
theorem fixedHalfDensity_ne_zero_on_chart (B : Field (M := M)) (hn : IsNondegenerate B) (c : AtlasChart M)
    {x : E₀} (hx : x ∈ c.chart.target) :
    fixedHalfDensity B c x ≠ 0 := by
  unfold fixedHalfDensity
  exact (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr
    (abs_pos.mpr (fixedForm_det_ne_zero B hn c hx)))).ne'

/-- Divide the original compact localization by the actual volume
half-density within its chart, leaving a smooth compact test. -/
def inverseHalfDensityWindow (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ c.chart.target) : D :=
  ⟨fun x => (χ : E₀ → ℝ) x * (fixedHalfDensity B c x)⁻¹,
    ⟨Burnett.Analysis.LocalWeakDerivative.contDiff_test_mul_local c.chart.open_target
      (test_smooth χ) hχ ((fixedHalfDensity_smooth B hB hn c).inv
        (fun _ hx => fixedHalfDensity_ne_zero_on_chart B hn c hx)),
      (test_compactSupport χ).mul_right⟩⟩

theorem inverseHalfDensityWindow_tsupport (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ c.chart.target) :
    tsupport (inverseHalfDensityWindow B hB hn c χ hχ : E₀ → ℝ) ⊆ tsupport (χ : E₀ → ℝ) :=
  tsupport_mul_subset_left

/-- The inverse-volume window in F05 gives exactly the unweighted
localized raw derivatives of the same sequence. -/
theorem fixedVolumeGradientSchwartz_inverseHalfDensityWindow
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hn : IsNondegenerate B) (c : AtlasChart M) (χ : D)
    (hχ : tsupport (χ : E₀ → ℝ) ⊆ c.chart.target) (n : ℕ) (i : JetSlot) :
    let η := inverseHalfDensityWindow B hB hn c χ hχ
    let hη := (inverseHalfDensityWindow_tsupport B hB hn c χ hχ).trans hχ
    fixedVolumeGradientSchwartz B g hB hg hn c η hη n i =
      fixedGradientSchwartz B g hB hg c χ hχ n i := by
  intro η hη
  ext x
  rw [fixedVolumeGradientSchwartz_apply, fixedGradientSchwartz_apply]
  change (((χ : E₀ → ℝ) x * (fixedHalfDensity B c x)⁻¹ * fixedHalfDensity B c x *
    coordinateJet (fixedPerturbation B (g n) c) x i.1 i.2.1 i.2.2 : ℝ) : ℂ) = _
  by_cases hx : x ∈ tsupport (χ : E₀ → ℝ)
  · rw [mul_assoc ((χ : E₀ → ℝ) x),inv_mul_cancel₀ (fixedHalfDensity_ne_zero_on_chart B hn c (hχ hx)),mul_one]
  · simp only [image_eq_zero_of_notMem_tsupport hx,zero_mul]

/-- The two matching F05 cutoffs insert exactly the reciprocal coordinate
volume density into the original operator limit. -/
theorem inverseHalfDensityWindow_pairingWeight (B : Field (M := M)) (hB : IsSmooth B)
    (hn : IsNondegenerate B) (c : AtlasChart M) (χ : D)
    (hχ : tsupport (χ : E₀ → ℝ) ⊆ c.chart.target) (x : E₀) :
    let η := inverseHalfDensityWindow B hB hn c χ hχ
    physicalCoefficient η x * physicalCoefficient η x =
      ((((χ : E₀ → ℝ) x)^2 * (fixedCoordinateVolumeDensity B c x)⁻¹ : ℝ) : ℂ) := by
  intro η
  change (((χ : E₀ → ℝ) x * (fixedHalfDensity B c x)⁻¹ : ℝ) : ℂ) *
    (((χ : E₀ → ℝ) x * (fixedHalfDensity B c x)⁻¹ : ℝ) : ℂ) =
      ((((χ : E₀ → ℝ) x)^2 * (fixedCoordinateVolumeDensity B c x)⁻¹ : ℝ) : ℂ)
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← fixedHalfDensity_sq, ← inv_pow]
  ring

end Burnett.V03
