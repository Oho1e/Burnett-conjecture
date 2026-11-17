import Burnett.Geometry.ManifoldTensorNorm
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Global physical C0_loc convergence supplies actual chart conditions

The convergence input is uniform convergence to zero of the actual
physical-r norm of B_n - B_0 on each compact set of the manifold. It is not
a coordinate-component convergence field. A chart compact is pulled back
to a genuine compact base set, and the proved tensor norm identification
and compact comparison derive component convergence. Smoothness, symmetry
and nondegeneracy of the original fiber fields supply the other inputs.

Full Lorentz signature and time orientation remain uninstantiated. No
curried Hom operator norm or coordinate convergence conclusion is assumed.
-/

noncomputable section
open Bundle Set LinearMap Filter
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.ManifoldTensorNorm
open Burnett.Geometry.CovariantTensorNorm

namespace Burnett.Geometry.ManifoldMetricSequence

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]
/-- A concrete physical-r C0_loc formulation on the base manifold itself. -/
def LocallyUniformlyConverges (r : Metric (M := M)) (B : ℕ → Field (M := M))
    (B₀ : Field (M := M)) : Prop :=
  ∀ S : Set M, IsCompact S → TendstoUniformlyOn
    (fun n m => physicalNorm2 r (B n - B₀) m) (fun _ => 0) atTop S

theorem coordinateComponents_sub (B C : Field (M := M)) (c : M) (y : CoordinateSpace) :
    metricComponents (coordinateBilinear (B - C) c) y =
      metricComponents (coordinateBilinear B c) y - metricComponents (coordinateBilinear C c) y := rfl

theorem components_uniform_of_physical_C0loc (r : Metric (M := M))
    (B : ℕ → Field (M := M)) (B₀ : Field (M := M)) (hconv : LocallyUniformlyConverges r B B₀)
    (c : M) (K : Set CoordinateSpace) (hK : IsCompact K)
    (hKU : K ⊆ (chartAt CoordinateSpace c).target) :
    TendstoUniformlyOn (fun n => metricComponents (coordinateBilinear (B n) c))
      (metricComponents (coordinateBilinear B₀ c)) atTop K := by
  let R : CoordinateSpace → Matrix Index Index ℝ := metricComponents (coordinateMetric r c)
  obtain ⟨C, hC, hbound⟩ := exists_uniform_norm2_control R K hK
    (fun i => (ManifoldMetric.contDiffOn_metricComponents r c i i).continuousOn.mono hKU)
    (fun y hy => ManifoldMetric.coordinateMetric_posDef r c (hKU hy))
  have hbase : IsCompact ((chartAt CoordinateSpace c).symm '' K) :=
    hK.image_of_continuousOn ((chartAt CoordinateSpace c).continuousOn_symm.mono hKU)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hconv _ hbase) (ε / C) (div_pos hε hC)] with n hn
  intro y hy
  have hsmall : physicalNorm2 r (B n - B₀) ((chartAt CoordinateSpace c).symm y) < ε / C := by
    have h := hn _ (mem_image_of_mem _ hy)
    simpa only [dist_zero_left, Real.norm_eq_abs,
      abs_of_nonneg (physicalNorm2_nonneg r (B n - B₀) _)] using h
  rw [dist_comm, dist_eq_norm]
  have h := hbound y hy (metricComponents (coordinateBilinear (B n) c) y -
    metricComponents (coordinateBilinear B₀ c) y)
  have heq := physicalNorm2_eq_coordinate r (B n - B₀) c (hKU hy)
  rw [coordinateComponents_sub] at heq
  change ‖metricComponents (coordinateBilinear (B n) c) y - metricComponents (coordinateBilinear B₀ c) y‖ ≤
    C * norm2 (metricComponents (coordinateMetric r c) y)
      (metricComponents (coordinateBilinear (B n) c) y - metricComponents (coordinateBilinear B₀ c) y) at h
  rw [← heq] at h
  apply h.trans_lt
  calc
    _ < C * (ε / C) := mul_lt_mul_of_pos_left hsmall hC
    _ = ε := by field_simp

theorem chart_conditions_of_global (r : Metric (M := M))
    (B : ℕ → Field (M := M)) (B₀ : Field (M := M))
    (hc₀ : IsSmooth B₀) (hc : ∀ n, IsSmooth (B n))
    (hs₀ : IsSymmetric B₀) (hs : ∀ n, IsSymmetric (B n))
    (hn₀ : IsNondegenerate B₀) (hn : ∀ n, IsNondegenerate (B n))
    (hconv : LocallyUniformlyConverges r B B₀) (c : M) (K : Set CoordinateSpace)
    (hK : IsCompact K) (hKU : K ⊆ (chartAt CoordinateSpace c).target) :
    (∀ i j, ContDiffOn ℝ 1 (fun y => metricComponents (coordinateBilinear B₀ c) y i j)
      (chartAt CoordinateSpace c).target) ∧
    (∀ n i j, ContDiffOn ℝ 1 (fun y => metricComponents (coordinateBilinear (B n) c) y i j)
      (chartAt CoordinateSpace c).target) ∧
    (∀ y ∈ K, (coordinateBilinear B₀ c y).Nondegenerate) ∧
    (∀ n y, y ∈ K → (coordinateBilinear (B n) c y).Nondegenerate) ∧
    (∀ x ∈ K, ∀ᶠ y in 𝓝 x, (coordinateBilinear B₀ c y).IsSymm) ∧
    (∀ n x, x ∈ K → ∀ᶠ y in 𝓝 x, (coordinateBilinear (B n) c y).IsSymm) ∧
    TendstoUniformlyOn (fun n => metricComponents (coordinateBilinear (B n) c))
      (metricComponents (coordinateBilinear B₀ c)) atTop K := by
  refine ⟨ManifoldBilinear.contDiffOn_metricComponents_one B₀ hc₀ c,
    (fun n => ManifoldBilinear.contDiffOn_metricComponents_one (B n) (hc n) c),
    (fun y hy => coordinateBilinear_nondegenerate B₀ hn₀ c (hKU hy)),
    (fun n y hy => coordinateBilinear_nondegenerate (B n) (hn n) c (hKU hy)),
    (fun x _ => eventually_coordinateBilinear_symmetric B₀ hs₀ c x),
    (fun n x _ => eventually_coordinateBilinear_symmetric (B n) (hs n) c x), ?_⟩
  exact components_uniform_of_physical_C0loc r B B₀ hconv c K hK hKU

end Burnett.Geometry.ManifoldMetricSequence
