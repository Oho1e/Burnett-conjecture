import Burnett.Analysis.AngularCaps.SmoothCapProfiles
import Burnett.Analysis.Microlocal.Overlap.AtlasAngularPhaseEncoding
import Burnett.Analysis.Microlocal.Overlap.IntrinsicRicciFiberSymbol
import Burnett.Geometry.SmoothMetricConnection
import Mathlib.Analysis.Calculus.MeanValue

/-! Freezing the actual inverse metric on a chart patch controls the relative phase. -/

set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 5600000

noncomputable section

namespace Burnett.C02

open Set Module Matrix Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian)
open Burnett.Geometry.UnitNullCompactness (dualEnergy dualEnergy_in_basis)
open Burnett.Geometry.FixedCotangentChart (inverseFrame)
open Burnett.Geometry.InverseField (matrixInverse)
open Burnett.Geometry.IntrinsicScalarEinstein (covariantForm)
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis chartTangentBasis_apply)
open Burnett.Microlocal.Overlap (atlasChartUnitCovector atlasChartUnitCovector_of_mem atlasChartUnitCovector_ne_zero)
open Burnett.Analysis.ProjectiveNullCaps (quadratic pairing rowValue thinConeProfile thinConeProfile_eq_one)
open scoped BigOperators ContDiff Manifold Topology

local notation "E" => CoordinateSpace

theorem quadratic_eq_symbolNorm (B : Tensor2) (ξ : E) :
    quadratic B ξ = symbolNorm B (fun i => ξ i) := by
  simp only [quadratic, pairing, rowValue, symbolNorm, Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem symbolNorm_sub (B C : Tensor2) (q : Covector) :
    symbolNorm B q - symbolNorm C q = symbolNorm (B - C) q := by
  simp only [symbolNorm, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- A unit Euclidean frequency costs at most a fixed four-dimensional
constant times the actual inverse-metric matrix difference. -/
theorem quadratic_sub_bound (B C : Tensor2) (ξ : E) :
    |quadratic B ξ - quadratic C ξ| ≤ 16 * ‖B - C‖ * ‖ξ‖^2 := by
  rw [quadratic_eq_symbolNorm, quadratic_eq_symbolNorm, symbolNorm_sub]
  let D := B - C
  have hEntry (i j : Index) : |D i j| ≤ ‖D‖ :=
    (Real.norm_eq_abs _ ▸ norm_le_pi_norm (D i) j).trans (norm_le_pi_norm D i)
  have hCoord (i : Index) : |ξ i| ≤ ‖ξ‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ξ i
  change |∑ i : Index, ∑ j : Index, D i j * ξ i * ξ j| ≤ 16 * ‖D‖ * ‖ξ‖^2
  calc
    _ ≤ ∑ i : Index, |∑ j : Index, D i j * ξ i * ξ j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Index, ∑ j : Index, ‖D‖ * ‖ξ‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
      rw [abs_mul, abs_mul, pow_two, ← mul_assoc]
      gcongr
      · exact hEntry i j
      · exact hCoord i
      · exact hCoord j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]; ring

/-- The degree-zero phase appearing in the gradient error. -/
def normalizedFrozenPhase (B : Tensor2) (ξ : E) : ℝ := quadratic B ξ / ‖ξ‖^2

theorem normalizedFrozenPhase_le_of_null (B C : Tensor2) (ξ : E)
    (hξ : ξ ≠ 0) (hNull : quadratic B ξ = 0) :
    |normalizedFrozenPhase C ξ| ≤ 16 * ‖B - C‖ := by
  have hDen : 0 < ‖ξ‖^2 := pow_pos (norm_pos_iff.mpr hξ) 2
  rw [normalizedFrozenPhase, abs_div, abs_of_pos hDen, div_le_iff₀ hDen]
  simpa only [hNull, zero_sub, abs_neg] using quadratic_sub_bound B C ξ

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- Actual coordinate inverse of the smooth background metric. -/
def chartInverseMetric (B : Field (M := M)) (c : AtlasChart M) (x : E) : Tensor2 :=
  matrixInverse (metricComponents (fixedForm B c) x)

theorem chartMetricComponents_in_basis (B : Field (M := M)) (c : AtlasChart M)
    (x : M) (hx : x ∈ c.chart.source) :
    metricComponents (fixedForm B c) (c.chart x) =
      FiberMetric.covariant (covariantForm B x) (chartTangentBasis c x hx) := by
  funext i j
  simp only [metricComponents, FiberMetric.covariant, chartTangentBasis_apply, covariantForm,
    fixedForm, LinearMap.mk₂_apply, fixedCoordinateBilinear, inverseFrame]
  exact congrArg (fun y => B y
      (mfderiv Model Model c.chart.symm (c.chart x) (coordinateBasis i))
      (mfderiv Model Model c.chart.symm (c.chart x) (coordinateBasis j))) (c.chart.left_inv hx)

theorem chartInverseMetric_in_basis (B : Field (M := M)) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (c : AtlasChart M) (x : M) (hx : x ∈ c.chart.source) :
    let b := chartTangentBasis c x hx
    letI : FiniteDimensional ℝ (TangentSpace Model x) := Module.Finite.of_basis b
    chartInverseMetric B c (c.chart x) = FiberMetric.contravariant (covariantForm B x) (hn x) b := by
  intro b
  letI : FiniteDimensional ℝ (TangentSpace Model x) := Module.Finite.of_basis b
  unfold chartInverseMetric
  rw [chartMetricComponents_in_basis B c x hx]
  exact Burnett.Geometry.InverseField.matrixInverse_covariant (covariantForm B x) (hn x) ⟨hs x⟩ b

theorem atlasCovector_eq_fiberCoordinates {r : Metric (M := M)}
    (c : AtlasChart M) (p : Cosphere r) (hp : projection p ∈ c.chart.source) :
    atlasChartUnitCovector c p =
      FiberMetric.covector (chartTangentBasis c (projection p) hp) p.val.2.toLinearMap := by
  funext i
  rw [atlasChartUnitCovector_of_mem c p hp i, FiberMetric.covector, chartTangentBasis_apply]
  rfl

theorem chartQuadratic_eq_two_hamiltonian {r : Metric (M := M)} (B : Field (M := M))
    (hs : IsSymmetric B) (hn : IsNondegenerate B) (c : AtlasChart M)
    (p : Cosphere r) (hp : projection p ∈ c.chart.source) :
    quadratic (chartInverseMetric B c (c.chart (projection p)))
      (WithLp.toLp 2 (atlasChartUnitCovector c p)) = 2 * hamiltonian B hn p := by
  let b := chartTangentBasis c (projection p) hp
  letI : FiniteDimensional ℝ (TangentSpace Model (projection p)) := Module.Finite.of_basis b
  have he := dualEnergy_in_basis B hn hs p.val b
  change dualEnergy B hn p.val = symbolNorm
    (matrixInverse (FiberMetric.covariant (covariantForm B (projection p)) b))
    (FiberMetric.covector b p.val.2.toLinearMap) at he
  rw [quadratic_eq_symbolNorm]
  change symbolNorm (chartInverseMetric B c (c.chart (projection p))) (atlasChartUnitCovector c p) =
    2 * (dualEnergy B hn p.val / 2)
  rw [chartInverseMetric, chartMetricComponents_in_basis B c (projection p) hp,
    atlasCovector_eq_fiberCoordinates c p hp, ← he]
  ring

theorem actualNull_chart_quadratic {r : Metric (M := M)} (B : Field (M := M))
    (hs : IsSymmetric B) (hn : IsNondegenerate B) (c : AtlasChart M)
    (p : Cosphere r) (hp : projection p ∈ c.chart.source) (hNull : hamiltonian B hn p = 0) :
    quadratic (chartInverseMetric B c (c.chart (projection p)))
      (WithLp.toLp 2 (atlasChartUnitCovector c p)) = 0 := by
  rw [chartQuadratic_eq_two_hamiltonian B hs hn c p hp, hNull, mul_zero]

variable [SecondCountableTopology M]

theorem chartInverseMetric_smooth (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (c : AtlasChart M) : ContDiffOn ℝ ∞ (chartInverseMetric B c) c.chart.target := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact SmoothMetricConnection.contDiffOn_matrixInverse _ _ (fixedForm_components_smooth B hB c)
    (fun _ hy => fixedForm_det_ne_zero B hn c hy) i j

/-- A single bound on the first derivative of the smooth background on a
compact convex chart window gives its uniform inverse-metric variation. -/
theorem exists_chartInverseMetric_lipschitz (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K)
    (hKU : K ⊆ c.chart.target) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖chartInverseMetric B c x - chartInverseMetric B c y‖ ≤ L * ‖x - y‖ := by
  let F := chartInverseMetric B c
  have hs := chartInverseMetric_smooth B hB hn c
  have hd : ContDiffOn ℝ 0 (fderiv ℝ F) c.chart.target :=
    hs.fderiv_of_isOpen c.chart.open_target (by simp)
  have hDc : ContinuousOn (fun x => fderiv ℝ F x) K := hd.continuousOn.mono hKU
  obtain ⟨L, hL, hBnd⟩ := (hK.image_of_continuousOn hDc).isBounded.exists_pos_norm_le
  refine ⟨L, hL.le, fun x hx y hy => ?_⟩
  have hDiff (q : E) (hq : q ∈ K) : DifferentiableAt ℝ F q :=
    (hs.contDiffAt (c.chart.open_target.mem_nhds (hKU hq))).differentiableAt (by simp)
  exact hConv.norm_image_sub_le_of_norm_fderiv_le hDiff
    (fun q hq => hBnd _ (mem_image_of_mem _ hq)) hy hx

/-- The actual null directions over the patch have O(ℓ) relative frozen
phase. The specified smooth thin cone is identically one on those directions. -/
theorem exists_actualNull_frozenPhaseAndThinCone {r : Metric (M := M)} (B : Field (M := M))
    (hB : IsSmooth B) (hs : IsSymmetric B) (hn : IsNondegenerate B) (c : AtlasChart M)
    (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x₀ ∈ K, ∀ (p : Cosphere r), projection p ∈ c.chart.source →
      c.chart (projection p) ∈ K → hamiltonian B hn p = 0 → ∀ ℓ : ℝ,
      ‖c.chart (projection p) - x₀‖ ≤ ℓ →
      let m := chartInverseMetric B c x₀
      let ξ : E := WithLp.toLp 2 (atlasChartUnitCovector c p)
      |normalizedFrozenPhase m ξ| ≤ L * ℓ ∧
      ∀ η inner outer : ℝ, 0 < η → 0 ≤ inner → inner < outer → L * ℓ ≤ inner * η →
        thinConeProfile m η inner outer ξ = 1 := by
  obtain ⟨C, hC, hBound⟩ := exists_chartInverseMetric_lipschitz B hB hn c K hK hConv hKU
  refine ⟨16 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro x₀ hx₀ p hp hpK hNull ℓ hℓ m ξ
  have hξ : ξ ≠ 0 := by
    intro hz
    apply atlasChartUnitCovector_ne_zero c p hp
    exact congrArg WithLp.ofLp hz
  have hPhase := normalizedFrozenPhase_le_of_null (chartInverseMetric B c (c.chart (projection p)))
    m ξ hξ (actualNull_chart_quadratic B hs hn c p hp hNull)
  have hErr : |normalizedFrozenPhase m ξ| ≤ (16 * C) * ℓ := by
    calc
      _ ≤ 16 * ‖chartInverseMetric B c (c.chart (projection p)) - chartInverseMetric B c x₀‖ := hPhase
      _ ≤ 16 * (C * ‖c.chart (projection p) - x₀‖) :=
        mul_le_mul_of_nonneg_left (hBound _ hpK _ hx₀) (by norm_num)
      _ ≤ 16 * (C * ℓ) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hℓ hC) (by norm_num)
      _ = _ := by ring
  refine ⟨hErr, fun η inner outer hη hIn hIO hSmall => ?_⟩
  have hDen : 0 < ‖ξ‖^2 := pow_pos (norm_pos_iff.mpr hξ) 2
  have hQ := hErr.trans hSmall
  rw [normalizedFrozenPhase, abs_div, abs_of_pos hDen, div_le_iff₀ hDen] at hQ
  exact thinConeProfile_eq_one hη hIn hIO hξ hQ

end Burnett.C02
