import Burnett.Geometry.InversePerturbation
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Continuous inverse metric components on a fixed set

The total matrix inverse is used only at points where its determinant is
nonzero. Nondegeneracy and continuity are local to the specified set; no
nondegenerate extension of a chart metric is asserted.
-/

noncomputable section

namespace Burnett.Geometry.InverseField

open scoped Topology
open Filter
open Burnett.RicciSymbol
open Burnett.Geometry.FiberMetric
open Burnett.Geometry.InversePerturbation
open Module

/-- Actual matrix inverse, explicitly distinguished from componentwise inverse
on the function type used for tensor components. -/
def matrixInverse (A : Tensor2) : Tensor2 :=
  @Inv.inv (Matrix Index Index ℝ) Matrix.inv A

theorem matrixInverse_eq_of_right_inverse (A inv : Tensor2)
    (hi : compose A inv = identity) : matrixInverse A = inv :=
  Matrix.inv_eq_right_inv (A := A) (B := inv) hi

theorem det_ne_zero_of_right_inverse (A inv : Tensor2)
    (hi : compose A inv = identity) : Matrix.det A ≠ 0 :=
  Matrix.det_ne_zero_of_right_inverse (A := A) (B := inv) hi

theorem continuousAt_matrixInverse (A : Tensor2)
    (hA : Matrix.det A ≠ 0) : ContinuousAt matrixInverse A := by
  exact continuousAt_matrix_inv A (by
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hA))

theorem continuousOn_matrixInverse {X : Type*} [TopologicalSpace X]
    (A : X → Tensor2) (K : Set X) (hc : ContinuousOn A K)
    (hn : ∀ x ∈ K, Matrix.det (A x) ≠ 0) :
    ContinuousOn (fun x => matrixInverse (A x)) K := by
  intro x hx
  exact (continuousAt_matrixInverse (A x) (hn x hx)).comp_continuousWithinAt (hc x hx)

theorem exists_pos_bound_matrixInverse {X : Type*} [TopologicalSpace X]
    (A : X → Tensor2) (K : Set X) (hK : IsCompact K) (hc : ContinuousOn A K)
    (hn : ∀ x ∈ K, Matrix.det (A x) ≠ 0) :
    ∃ B > 0, ∀ x ∈ K, ‖matrixInverse (A x)‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := (hK.image_of_continuousOn
    (continuousOn_matrixInverse A K hc hn)).isBounded.exists_pos_norm_le
  exact ⟨B, hB, fun x hx => hb _ (Set.mem_image_of_mem _ hx)⟩

theorem compose_matrixInverse (A : Tensor2) (hn : Matrix.det A ≠ 0) :
    compose A (matrixInverse A) = identity :=
  Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hn)

theorem matrixInverse_compose (A : Tensor2) (hn : Matrix.det A ≠ 0) :
    compose (matrixInverse A) A = identity :=
  Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hn)

/-- An actual uniform convergence hypothesis supplies one eventual smallness
witness simultaneously for every point of the specified set. -/
theorem eventually_small_perturbation {ι X : Type*} (p : Filter ι)
    (A : X → Tensor2) (Aₙ : ι → X → Tensor2) (K : Set X)
    {B : ℝ} (hB : 0 < B) (hu : TendstoUniformlyOn Aₙ A p K) :
    ∀ᶠ n in p, ∀ x ∈ K, 16 * ‖Aₙ n x - A x‖ * B ≤ 1 / 2 := by
  have hδ : 0 < 1 / (32 * B) := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu _ hδ] with n hn x hx
  have hh : ‖Aₙ n x - A x‖ < 1 / (32 * B) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hn x hx
  have hm := (lt_div_iff₀ (by positivity : 0 < 32 * B)).mp hh
  nlinarith

/-- Both the eventual bound and the quantitative inverse difference are
derived from uniform convergence and a bound for the background inverse. -/
theorem eventually_matrixInverse_estimates {ι X : Type*} (p : Filter ι)
    (A : X → Tensor2) (Aₙ : ι → X → Tensor2) (K : Set X)
    (hn : ∀ x ∈ K, Matrix.det (A x) ≠ 0)
    (hnₙ : ∀ n x, x ∈ K → Matrix.det (Aₙ n x) ≠ 0)
    {B : ℝ} (hB : 0 < B) (hb : ∀ x ∈ K, ‖matrixInverse (A x)‖ ≤ B)
    (hu : TendstoUniformlyOn Aₙ A p K) :
    ∀ᶠ n in p, ∀ x ∈ K,
      ‖matrixInverse (Aₙ n x)‖ ≤ 2 * B ∧
      ‖matrixInverse (Aₙ n x) - matrixInverse (A x)‖ ≤
        32 * B ^ 2 * ‖Aₙ n x - A x‖ := by
  filter_upwards [eventually_small_perturbation p A Aₙ K hB hu] with n hs x hx
  have hsmall : 16 * ‖Aₙ n x - A x‖ * ‖matrixInverse (A x)‖ ≤ 1 / 2 := by
    calc
      _ ≤ 16 * ‖Aₙ n x - A x‖ * B := by gcongr; exact hb x hx
      _ ≤ 1 / 2 := hs x hx
  have hi₀ := compose_matrixInverse (A x) (hn x hx)
  have hi₁ := matrixInverse_compose (Aₙ n x) (hnₙ n x hx)
  constructor
  · exact (norm_inverse_le_of_small _ _ _ _ hi₀ hi₁ hsmall).trans
      (by gcongr; exact hb x hx)
  · exact (norm_inverse_sub_le_of_small _ _ _ _ hi₀ hi₁ hsmall).trans
      (by gcongr; exact hb x hx)

theorem tendstoUniformlyOn_matrixInverse_of_bound {ι X : Type*} (p : Filter ι)
    (A : X → Tensor2) (Aₙ : ι → X → Tensor2) (K : Set X)
    (hn : ∀ x ∈ K, Matrix.det (A x) ≠ 0)
    (hnₙ : ∀ n x, x ∈ K → Matrix.det (Aₙ n x) ≠ 0)
    {B : ℝ} (hB : 0 < B) (hb : ∀ x ∈ K, ‖matrixInverse (A x)‖ ≤ B)
    (hu : TendstoUniformlyOn Aₙ A p K) :
    TendstoUniformlyOn (fun n x => matrixInverse (Aₙ n x))
      (fun x => matrixInverse (A x)) p K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hδ : 0 < ε / (32 * B ^ 2) := by positivity
  filter_upwards [eventually_matrixInverse_estimates p A Aₙ K hn hnₙ hB hb hu,
    Metric.tendstoUniformlyOn_iff.mp hu _ hδ] with n hinv hd x hx
  have hdiff : ‖Aₙ n x - A x‖ < ε / (32 * B ^ 2) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hd x hx
  have hmul := (lt_div_iff₀ (by positivity : 0 < 32 * B ^ 2)).mp hdiff
  calc
    dist (matrixInverse (A x)) (matrixInverse (Aₙ n x)) =
        ‖matrixInverse (Aₙ n x) - matrixInverse (A x)‖ := by
      rw [dist_eq_norm, norm_sub_rev]
    _ ≤ 32 * B ^ 2 * ‖Aₙ n x - A x‖ := (hinv x hx).2
    _ < ε := by nlinarith

/-- Compactness and continuity provide the background bound used by the
uniform inverse theorem. No inverse bound or inverse continuity is assumed. -/
theorem compact_uniform_inverse {ι X : Type*} [TopologicalSpace X] (p : Filter ι)
    (A : X → Tensor2) (Aₙ : ι → X → Tensor2) (K : Set X)
    (hK : IsCompact K) (hc : ContinuousOn A K)
    (hn : ∀ x ∈ K, Matrix.det (A x) ≠ 0)
    (hnₙ : ∀ n x, x ∈ K → Matrix.det (Aₙ n x) ≠ 0)
    (hu : TendstoUniformlyOn Aₙ A p K) :
    ∃ B > 0, (∀ x ∈ K, ‖matrixInverse (A x)‖ ≤ B) ∧
      (∀ᶠ n in p, ∀ x ∈ K,
        ‖matrixInverse (Aₙ n x)‖ ≤ 2 * B ∧
        ‖matrixInverse (Aₙ n x) - matrixInverse (A x)‖ ≤
          32 * B ^ 2 * ‖Aₙ n x - A x‖) ∧
      TendstoUniformlyOn (fun n x => matrixInverse (Aₙ n x))
        (fun x => matrixInverse (A x)) p K := by
  obtain ⟨B, hB, hb⟩ := exists_pos_bound_matrixInverse A K hK hc hn
  exact ⟨B, hB, hb, eventually_matrixInverse_estimates p A Aₙ K hn hnₙ hB hb hu,
    tendstoUniformlyOn_matrixInverse_of_bound p A Aₙ K hn hnₙ hB hb hu⟩

section MetricFibers

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem matrixInverse_covariant (g : LinearMap.BilinForm ℝ V)
    (hn : g.Nondegenerate) (hs : g.IsSymm) (b : Basis Index ℝ V) :
    matrixInverse (covariant g b) = contravariant g hn b :=
  matrixInverse_eq_of_right_inverse _ _ (covariant_compose_contravariant g hn hs b)

theorem det_covariant_ne_zero (g : LinearMap.BilinForm ℝ V)
    (hn : g.Nondegenerate) (hs : g.IsSymm) (b : Basis Index ℝ V) :
    Matrix.det (covariant g b) ≠ 0 :=
  det_ne_zero_of_right_inverse _ _ (covariant_compose_contravariant g hn hs b)

/-- Continuity of the actual inverse components is a conclusion from
continuity of the covariant components and pointwise metric nondegeneracy. -/
theorem continuousOn_inverseMetric {X : Type*} [TopologicalSpace X]
    (g : X → LinearMap.BilinForm ℝ V) (b : Basis Index ℝ V) (K : Set X)
    (hc : ContinuousOn (fun x => covariant (g x) b) K)
    (hn : ∀ x ∈ K, (g x).Nondegenerate) (hs : ∀ x ∈ K, (g x).IsSymm) :
    ContinuousOn (fun x => matrixInverse (covariant (g x) b)) K :=
  continuousOn_matrixInverse _ K hc (fun x hx => det_covariant_ne_zero _ (hn x hx) (hs x hx) b)

/-- A compact-set bound for the genuine inverse lowering map. The bound is
derived from continuity and compactness rather than supplied as a field. -/
theorem exists_pos_bound_inverseMetric {X : Type*} [TopologicalSpace X]
    (g : X → LinearMap.BilinForm ℝ V) (b : Basis Index ℝ V) (K : Set X)
    (hK : IsCompact K) (hc : ContinuousOn (fun x => covariant (g x) b) K)
    (hn : ∀ x ∈ K, (g x).Nondegenerate) (hs : ∀ x ∈ K, (g x).IsSymm) :
    ∃ B > 0, ∀ x (hx : x ∈ K), ‖contravariant (g x) (hn x hx) b‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_pos_bound_matrixInverse _ K hK hc
    (fun x hx => det_covariant_ne_zero _ (hn x hx) (hs x hx) b)
  refine ⟨B, hB, fun x hx => ?_⟩
  rw [← matrixInverse_covariant (g x) (hn x hx) (hs x hx) b]
  exact hb x hx

end MetricFibers

end Burnett.Geometry.InverseField
