import Burnett.Analysis.TransportWard.Weyl.NormalizedTestedVacuum
import Burnett.Analysis.PrincipalEnergy.Energy.CompactActualFourier

set_option autoImplicit false
set_option maxHeartbeats 2900000

noncomputable section

namespace Burnett.V03.Palatini

open Set Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldMetricTransition ManifoldBilinear MaximalChart
open Burnett.Analysis.CarlesonEmbedding (firstOrderAction_finset_sum)
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction FrequencyOrderOne)
open Burnett.Microlocal.AtlasVolumeGradient (fixedComponent fixedPerturbation)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ContDiff Manifold Matrix.Norms.Elementwise

open private actualFirstOrderAction_smul from Burnett.Analysis.PrincipalEnergy.Energy.CompactActualFourier

local notation "E₀" => CoordinateSpace
local notation "I" => SymmetricMetricSlot

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M] [SecondCountableTopology M]

/-- The original cutoff perturbation in ordered lower indices is the exact
reassembly of the compact orthonormal input to the Weyl action. -/
theorem normalizedWeylPerturbation_reassemble_ordered
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hBs : IsSymmetric B) (hgs : ∀ n, IsSymmetric (g n))
    (c : M) (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ (chartAt E₀ c).target) (n : ℕ) (a b : Index) :
    let d := AtlasChart.atPoint c
    let w (i : I) := (symmetricMetricScale i : ℂ) • fixedWeylPerturbationSchwartz B g hB hg d χ hχ n i.val
    (∑ i, (orthonormalMetricDirection i a b : ℂ) • w i) =
      fixedWeylPerturbationSchwartz B g hB hg d χ hχ n (a,b) := by
  intro d w
  let L := assembleMetricComponents orthonormalMetricDirection
  let h := normalizedChartPerturbation B (g n) c
  have hAssemble (x : E₀) (hx : x ∈ (chartAt E₀ c).target) : L (h x) = fixedPerturbation B (g n) d x := by
    change L (normalizedChartMetric (g n) c x - normalizedChartMetric B c x) = _
    rw [map_sub, fixedPerturbation, fixedForm_eq_preferred_components (g n) c hx,
      fixedForm_eq_preferred_components B c hx]
    exact congrArg₂ (· - ·)
      (congrFun (assembledCoordinateMetric_orthonormalMetricComponents (g n) (hgs n) c) x)
      (congrFun (assembledCoordinateMetric_orthonormalMetricComponents B hBs c) x)
  ext x
  change SchwartzMap.delta ℂ ℂ x
    (∑ i, (orthonormalMetricDirection i a b : ℂ) • w i : SchwartzMap E₀ ℂ) = _
  simp only [map_sum, map_smul, SchwartzMap.delta_apply, smul_eq_mul]
  by_cases hx : x ∈ (chartAt E₀ c).target
  · have hEq (i : I) : w i x = ((χ : E₀ → ℝ) x * h x i : ℝ) := by
      change (symmetricMetricScale i : ℂ) * ((χ : E₀ → ℝ) x * fixedComponent B g d n i.val x : ℝ) = _
      unfold h
      rw [normalizedChartPerturbation_eq_fixedComponent B g c n x hx i]
      push_cast
      ring
    have hFin : (∑ i : I, h x i * orthonormalMetricDirection i a b) = fixedComponent B g d n (a,b) x := by
      have hSum := congrArg (fun v : Matrix Index Index ℝ => v a b) (hAssemble x hx)
      simpa only [L, assembleMetricComponents_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using hSum
    simp only [hEq]
    change (∑ i, (orthonormalMetricDirection i a b : ℂ) * ((χ : E₀ → ℝ) x * h x i : ℝ)) =
      Complex.ofReal ((χ : E₀ → ℝ) x * fixedComponent B g d n (a,b) x)
    rw [← hFin, Finset.mul_sum, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  · have hz : (χ : E₀ → ℝ) x = 0 := image_eq_zero_of_notMem_tsupport (fun hy => hx (hχ hy))
    have hwi (i : I) : w i x = 0 := by
      change (symmetricMetricScale i : ℂ) * ((χ : E₀ → ℝ) x * fixedComponent B g d n i.val x : ℝ) = 0
      simp only [hz, zero_mul, Complex.ofReal_zero, mul_zero]
    simp only [hwi, mul_zero, Finset.sum_const_zero]
    change (0 : ℂ) = Complex.ofReal ((χ : E₀ → ℝ) x * fixedComponent B g d n (a,b) x)
    simp only [hz, zero_mul, Complex.ofReal_zero]

/-- The same scalar Weyl operator and the factor `-I` commute with the exact
reassembly into the original lower indices used by the cubic projection. -/
theorem originalWeylRealTest_reassemble_ordered
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hBs : IsSymmetric B) (hgs : ∀ n, IsSymmetric (g n))
    (c : M) (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ (chartAt E₀ c).target)
    (p : E₀ → E₀ → ℂ) (hp : FrequencyOrderOne p) (n : ℕ) (a b : Index) (x : E₀) :
    let d := AtlasChart.atPoint c
    let w (i : I) := (symmetricMetricScale i : ℂ) • fixedWeylPerturbationSchwartz B g hB hg d χ hχ n i.val
    (∑ i, (orthonormalMetricDirection i a b : ℂ) * ((-Complex.I) * firstOrderAction p (w i) x)) =
      (-Complex.I) * firstOrderAction p (fixedWeylPerturbationSchwartz B g hB hg d χ hχ n (a,b)) x := by
  intro d w
  rw [← normalizedWeylPerturbation_reassemble_ordered B g hB hg hBs hgs c χ hχ n a b,
    firstOrderAction_finset_sum hp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let cᵢ : ℂ := orthonormalMetricDirection i a b
  change cᵢ * ((-Complex.I) * firstOrderAction p (w i) x) =
    (-Complex.I) * firstOrderAction p (cᵢ • w i : SchwartzMap E₀ ℂ) x
  rw [actualFirstOrderAction_smul hp (w i) cᵢ x]
  ring

end Burnett.V03.Palatini
