import Burnett.Geometry.AuxiliaryConnection
import Burnett.Geometry.CovariantTensorNorm
import Burnett.Analysis.LocalAeBound
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Burnett.Geometry.ConnectionErrorLInfinity

/-!
# Physical covariant derivative bounds in a fixed coordinate neighborhood

The auxiliary tensor norm is the explicit inverse-metric contraction, not
the component sup norm. The measure is explicit. Manifold chart pullback
and equivalence with a geometric volume measure remain separate interfaces.
-/

noncomputable section

namespace Burnett.Geometry.AuxiliaryPhysicalBound

open MeasureTheory Filter
open scoped Topology ENNReal
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.AuxiliaryConnection
open Burnett.Geometry.CovariantTensorNorm
open Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.ConnectionError
open Burnett.Analysis.LocalAeBound

theorem nondegenerate_of_posDef_components
    (r : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (hr : Matrix.PosDef (metricComponents r x)) : (r x).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero (r x) coordinateBasis
  have hm : ((BilinForm.toMatrix coordinateBasis) (r x)) = metricComponents r x := by
    ext i j
    simp only [BilinForm.toMatrix_apply, metricComponents, FiberMetric.covariant]
  rw [hm]
  exact ne_of_gt hr.det_pos

theorem symmetric_of_posDef_components
    (r : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (hr : Matrix.PosDef (metricComponents r x)) : (r x).IsSymm := by
  apply (LinearMap.BilinForm.isSymm_iff_basis coordinateBasis).mpr
  intro i j
  simpa only [star_trivial] using hr.1.apply j i

/-- Compactness constructs the comparison constant, and continuity on the
interior of the larger compact set turns its a.e. bound into a pointwise
bound on K. The measure of K itself is never used for that implication. -/
theorem exists_auxiliary_coordinate_bound_of_physical_LInfinity
    (μ : Measure CoordinateSpace)
    (U K S : Set CoordinateSpace) (hU : IsOpen U) (hS : IsCompact S)
    (hKS : K ⊆ interior S) (hSU : S ⊆ U)
    (hpos : ∀ V : Set CoordinateSpace, IsOpen V → V ⊆ U → V.Nonempty → μ V ≠ 0)
    (r g₀ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (g : ℕ → CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hrc : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents r y a b) U)
    (hrp : ∀ x ∈ S, Matrix.PosDef (metricComponents r x))
    (hc₀ : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents g₀ y a b) U)
    (hc : ∀ n a b, ContDiffOn ℝ 1 (fun y => metricComponents (g n) y a b) U)
    {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ n, eLpNorm
      (fun x => norm3 (metricComponents r x) (auxiliaryPerturbationJet r g₀ (g n) x))
      ∞ (μ.restrict S) ≤ ENNReal.ofReal D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ K → ‖auxiliaryPerturbationJet r g₀ (g n) x‖ ≤ C := by
  have hdiag : ∀ i, ContinuousOn (fun x => metricComponents r x i i) S :=
    fun i => (hrc i i).continuousOn.mono hSU
  obtain ⟨C, hC, hcontrol⟩ := exists_uniform_norm3_control (metricComponents r) S hS hdiag hrp
  refine ⟨C * D, mul_nonneg hC.le hD, ?_⟩
  intro n
  have hOS : interior S ⊆ S := interior_subset
  have hOU : interior S ⊆ U := hOS.trans hSU
  have hcJ := continuousOn_auxiliaryPerturbationJet U (interior S) hU hOU r g₀ (g n) hrc
    (fun x hx => nondegenerate_of_posDef_components r x (hrp x (hOS hx)))
    (fun x hx => symmetric_of_posDef_components r x (hrp x (hOS hx))) hc₀ (hc n)
  have hb' : ∀ᵐ x ∂μ.restrict S, ‖auxiliaryPerturbationJet r g₀ (g n) x‖ ≤ C * D := by
    filter_upwards [ae_restrict_mem hS.measurableSet, ae_norm_le_of_eLpNorm_top_le hD (hb n)]
      with x hx hbx
    have hnorm : norm3 (metricComponents r x) (auxiliaryPerturbationJet r g₀ (g n) x) ≤ D := by
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbx)
    exact (hcontrol x hx _).trans (mul_le_mul_of_nonneg_left hnorm hC.le)
  exact norm_le_on_of_ae_restrict_of_local_pos μ isOpen_interior hKS hOS
    (fun V hV hVO hne => hpos V hV (hVO.trans hOU) hne) hcJ.norm hb'

/-- The locally bounded physical auxiliary derivative supplies the actual
coordinate error convergence on every compact K in U. A larger compact
neighborhood is constructed, rather than added as a new hypothesis. -/
theorem metricConnectionError_uniform_and_LInfinity_of_local_physical_bounds
    (μ : Measure CoordinateSpace)
    (U K : Set CoordinateSpace) (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    (hpos : ∀ V : Set CoordinateSpace, IsOpen V → V ⊆ U → V.Nonempty → μ V ≠ 0)
    (r g₀ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (g : ℕ → CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hrc : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents r y a b) U)
    (hrp : ∀ x ∈ U, Matrix.PosDef (metricComponents r x))
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate)
    (hn : ∀ n x, x ∈ K → (g n x).Nondegenerate)
    (hs₀ : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, (g₀ y).IsSymm)
    (hs : ∀ n x, x ∈ K → ∀ᶠ y in 𝓝 x, (g n y).IsSymm)
    (hc₀ : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents g₀ y a b) U)
    (hc : ∀ n a b, ContDiffOn ℝ 1 (fun y => metricComponents (g n) y a b) U)
    (hb : ∀ S : Set CoordinateSpace, IsCompact S → S ⊆ U → ∃ D : ℝ, 0 ≤ D ∧
      ∀ n, eLpNorm
        (fun x => norm3 (metricComponents r x) (auxiliaryPerturbationJet r g₀ (g n) x))
        ∞ (μ.restrict S) ≤ ENNReal.ofReal D)
    (hconv : TendstoUniformlyOn (fun n => metricComponents (g n)) (metricComponents g₀) atTop K) :
    (TendstoUniformlyOn (fun n => metricConnectionErrorOn K g₀ (g n) hn₀ (hn n))
      (fun _ => 0) atTop K) ∧
    ∃ hf : ∀ n, MemLp (metricConnectionErrorOn K g₀ (g n) hn₀ (hn n)) ∞ (μ.restrict K),
      Tendsto (fun n => (hf n).toLp (metricConnectionErrorOn K g₀ (g n) hn₀ (hn n)))
        atTop (𝓝 0) := by
  obtain ⟨S, hS, hKS, hSU⟩ := exists_compact_between hK hU hKU
  obtain ⟨D, hD, hbS⟩ := hb S hS hSU
  obtain ⟨C, hC, hbound⟩ := exists_auxiliary_coordinate_bound_of_physical_LInfinity
    μ U K S hU hS hKS hSU hpos r g₀ g hrc (fun x hx => hrp x (hSU hx)) hc₀ hc hD hbS
  have hd : ∀ n x, x ∈ K → DifferentiableComponentsAt (metricComponents (g n)) x := by
    intro n x hx a b
    exact ((hc n a b).differentiableOn (by simp) x (hKU hx)).differentiableAt
      (hU.mem_nhds (hKU hx))
  have hu := metricConnectionError_uniform_of_auxiliary_coordinate_bound U K hU hKU hK r g₀ g
    hrc (fun x hx => nondegenerate_of_posDef_components r x (hrp x (hKU hx)))
    (fun x hx => symmetric_of_posDef_components r x (hrp x (hKU hx)))
    hn₀ hn hs₀ hs hc₀ hd hC (Eventually.of_forall hbound) hconv
  exact ⟨hu, ConnectionErrorLInfinity.metricConnectionError_exists_tendstoLp μ U K hU hKU hK
    g₀ g hn₀ hn (fun x hx => (hs₀ x hx).self_of_nhds)
    (fun n x hx => (hs n x hx).self_of_nhds) hc₀ hc hu⟩

end Burnett.Geometry.AuxiliaryPhysicalBound
