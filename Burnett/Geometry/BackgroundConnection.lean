import Burnett.Geometry.ConnectionDifference
import Burnett.Geometry.InverseField
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# A continuous, compactly bounded background metric connection

The background metric components are C¹ on an open coordinate set U. Actual
Frechet differentiation gives a continuous coordinate first jet there; the
computed connection is then continuous on K ⊆ U, using nondegeneracy only on K.
No regularity or nondegeneracy of a total extension outside U is asserted.
-/

noncomputable section

namespace Burnett.Geometry.BackgroundConnection

open scoped BigOperators Topology
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.InverseField

theorem continuousOn_components_of_contDiffOn
    (A : CoordinateSpace → Tensor2) (U : Set CoordinateSpace)
    (hc : ∀ a b, ContDiffOn ℝ 1 (fun x => A x a b) U) : ContinuousOn A U := by
  apply continuousOn_pi.mpr
  intro a
  apply continuousOn_pi.mpr
  intro b
  exact (hc a b).continuousOn

/-- C¹ regularity on an open coordinate set gives continuity of the actual
ambient Frechet derivative jet, not an independently supplied jet field. -/
theorem continuousOn_coordinateJet (A : CoordinateSpace → Tensor2)
    (U : Set CoordinateSpace) (hU : IsOpen U)
    (hc : ∀ a b, ContDiffOn ℝ 1 (fun x => A x a b) U) :
    ContinuousOn (coordinateJet A) U := by
  apply continuousOn_pi.mpr
  intro d
  apply continuousOn_pi.mpr
  intro a
  apply continuousOn_pi.mpr
  intro b
  exact ((hc a b).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const

theorem continuousOn_christoffel {X : Type*} [TopologicalSpace X]
    (A : X → Tensor2) (J : X → FirstJet) (K : Set X)
    (hA : ContinuousOn A K) (hJ : ContinuousOn J K) :
    ContinuousOn (fun x => christoffel (A x) (J x)) K := by
  have hAc (a d : Index) : ContinuousOn (fun x => A x a d) K :=
    continuousOn_pi.mp (continuousOn_pi.mp hA a) d
  have hJc (d a b : Index) : ContinuousOn (fun x => J x d a b) K :=
    continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_pi.mp hJ d) a) b
  apply continuousOn_pi.mpr
  intro a
  apply continuousOn_pi.mpr
  intro b
  apply continuousOn_pi.mpr
  intro c
  exact continuousOn_finset_sum Finset.univ (fun d _ =>
    (hAc a d).mul ((((hJc b c d).add (hJc c b d)).sub (hJc d b c)).div_const 2))

/-- A total coordinate expression. Its values outside the specified geometric
set are immaterial; it agrees with the actual metric connection on K. -/
def computedConnection
    (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) : Connection :=
  christoffel (matrixInverse (metricComponents g x)) (coordinateJet (metricComponents g) x)

theorem computedConnection_eq_metricConnection
    (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (hn : (g x).Nondegenerate) (hs : (g x).IsSymm) :
    computedConnection g x = metricConnection g x hn := by
  simp only [computedConnection, metricConnection, metricInverse, metricComponents,
    matrixInverse_covariant (g x) hn hs coordinateBasis]

/-- Background connection continuity follows from C¹ metric components and
pointwise symmetric nondegeneracy on K. No inverse regularity is assumed. -/
theorem continuousOn_computedConnection
    (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (U K : Set CoordinateSpace) (hU : IsOpen U) (hKU : K ⊆ U)
    (hc : ∀ a b, ContDiffOn ℝ 1 (fun x => metricComponents g x a b) U)
    (hn : ∀ x ∈ K, (g x).Nondegenerate) (hs : ∀ x ∈ K, (g x).IsSymm) :
    ContinuousOn (computedConnection g) K := by
  have hcomp := continuousOn_components_of_contDiffOn (metricComponents g) U hc
  have hinv := continuousOn_inverseMetric g coordinateBasis K (hcomp.mono hKU) hn hs
  exact continuousOn_christoffel _ _ K hinv
    ((continuousOn_coordinateJet (metricComponents g) U hU hc).mono hKU)

theorem continuous_metricConnection_restrict
    (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (U K : Set CoordinateSpace) (hU : IsOpen U) (hKU : K ⊆ U)
    (hc : ∀ a b, ContDiffOn ℝ 1 (fun x => metricComponents g x a b) U)
    (hn : ∀ x ∈ K, (g x).Nondegenerate) (hs : ∀ x ∈ K, (g x).IsSymm) :
    Continuous (fun x : K => metricConnection g x (hn x x.property)) := by
  have hcont := (continuousOn_computedConnection g U K hU hKU hc hn hs).restrict
  have heq : (fun x : K => computedConnection g x) =
      (fun x : K => metricConnection g x (hn x x.property)) := by
    funext x
    exact computedConnection_eq_metricConnection g x (hn x x.property) (hs x x.property)
  exact heq ▸ hcont

/-- Compactness supplies a positive uniform bound for the actual computed
background connection, with no bound or connection continuity as an input. -/
theorem exists_pos_bound_metricConnection
    (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (U K : Set CoordinateSpace) (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    (hc : ∀ a b, ContDiffOn ℝ 1 (fun x => metricComponents g x a b) U)
    (hn : ∀ x ∈ K, (g x).Nondegenerate) (hs : ∀ x ∈ K, (g x).IsSymm) :
    ∃ G > 0, ∀ x (hx : x ∈ K), ‖metricConnection g x (hn x hx)‖ ≤ G := by
  obtain ⟨G, hG, hb⟩ := (hK.image_of_continuousOn
    (continuousOn_computedConnection g U K hU hKU hc hn hs)).isBounded.exists_pos_norm_le
  refine ⟨G, hG, fun x hx => ?_⟩
  simpa only [computedConnection_eq_metricConnection g x (hn x hx) (hs x hx)] using
    hb _ (Set.mem_image_of_mem _ hx)

end Burnett.Geometry.BackgroundConnection
