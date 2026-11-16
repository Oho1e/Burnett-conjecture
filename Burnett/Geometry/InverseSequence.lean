import Burnett.Geometry.InverseField

/-!
# Actual inverse metric fields for a uniformly convergent metric sequence

All nondegeneracy and symmetry hypotheses are restricted to the fixed set K.
The uniform convergence of the inverse lowering maps is stated on the subtype
K, so no inverse field or nondegenerate extension outside K is required.
-/

noncomputable section

namespace Burnett.Geometry.InverseSequence

open scoped Topology
open Filter Module
open Burnett.RicciSymbol
open Burnett.Geometry.FiberMetric
open Burnett.Geometry.InverseField

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Continuity of the genuine inverse lowering map on K with its subspace
topology, derived from continuity of the covariant components on K. -/
theorem continuous_inverseMetric_restrict {X : Type*} [TopologicalSpace X]
    (g : X → LinearMap.BilinForm ℝ V) (b : Basis Index ℝ V) (K : Set X)
    (hc : ContinuousOn (fun x => covariant (g x) b) K)
    (hn : ∀ x ∈ K, (g x).Nondegenerate) (hs : ∀ x ∈ K, (g x).IsSymm) :
    Continuous (fun x : K => contravariant (g x) (hn x x.property) b) := by
  have hcont := (continuousOn_inverseMetric g b K hc hn hs).restrict
  have heq : (fun x : K => matrixInverse (covariant (g x) b)) =
      (fun x : K => contravariant (g x) (hn x x.property) b) := by
    funext x
    exact matrixInverse_covariant (g x) (hn x x.property) (hs x x.property) b
  exact heq ▸ hcont

/-- One background bound B and one eventual set of indices work for all
points of K. The conclusion concerns the actual FiberMetric inverses and
also gives their uniform convergence. Neither inverse continuity nor an
inverse bound is an input. -/
theorem compact_uniform_inverseMetric {ι X : Type*} [TopologicalSpace X]
    (p : Filter ι) (g : X → LinearMap.BilinForm ℝ V)
    (gₙ : ι → X → LinearMap.BilinForm ℝ V) (b : Basis Index ℝ V) (K : Set X)
    (hK : IsCompact K) (hc : ContinuousOn (fun x => covariant (g x) b) K)
    (hn : ∀ x ∈ K, (g x).Nondegenerate) (hs : ∀ x ∈ K, (g x).IsSymm)
    (hnₙ : ∀ n x, x ∈ K → (gₙ n x).Nondegenerate)
    (hsₙ : ∀ n x, x ∈ K → (gₙ n x).IsSymm)
    (hu : TendstoUniformlyOn (fun n x => covariant (gₙ n x) b)
      (fun x => covariant (g x) b) p K) :
    ∃ B > 0, (∀ x (hx : x ∈ K), ‖contravariant (g x) (hn x hx) b‖ ≤ B) ∧
      (∀ᶠ n in p, ∀ x (hx : x ∈ K),
        16 * ‖covariant (gₙ n x) b - covariant (g x) b‖ *
            ‖contravariant (g x) (hn x hx) b‖ ≤ 1 / 2 ∧
        ‖contravariant (gₙ n x) (hnₙ n x hx) b‖ ≤ 2 * B ∧
        ‖contravariant (gₙ n x) (hnₙ n x hx) b - contravariant (g x) (hn x hx) b‖ ≤
          32 * B ^ 2 * ‖covariant (gₙ n x) b - covariant (g x) b‖) ∧
      TendstoUniformly
        (fun n (x : K) => contravariant (gₙ n x) (hnₙ n x x.property) b)
        (fun x : K => contravariant (g x) (hn x x.property) b) p := by
  have hdet : ∀ x ∈ K, Matrix.det (covariant (g x) b) ≠ 0 :=
    fun x hx => det_covariant_ne_zero (g x) (hn x hx) (hs x hx) b
  have hdetₙ : ∀ n x, x ∈ K → Matrix.det (covariant (gₙ n x) b) ≠ 0 :=
    fun n x hx => det_covariant_ne_zero (gₙ n x) (hnₙ n x hx) (hsₙ n x hx) b
  obtain ⟨B, hB, hb, hest, huni⟩ := compact_uniform_inverse p
    (fun x => covariant (g x) b) (fun n x => covariant (gₙ n x) b) K hK hc hdet hdetₙ hu
  refine ⟨B, hB, ?_, ?_, ?_⟩
  · intro x hx
    simpa only [matrixInverse_covariant (g x) (hn x hx) (hs x hx) b] using hb x hx
  · filter_upwards [hest, eventually_small_perturbation p _ _ K hB hu] with n he hsmall
    intro x hx
    have hb₀ := hb x hx
    rw [matrixInverse_covariant (g x) (hn x hx) (hs x hx) b] at hb₀
    have he₀ := he x hx
    rw [matrixInverse_covariant (g x) (hn x hx) (hs x hx) b,
      matrixInverse_covariant (gₙ n x) (hnₙ n x hx) (hsₙ n x hx) b] at he₀
    refine ⟨?_, he₀.1, he₀.2⟩
    calc
      _ ≤ 16 * ‖covariant (gₙ n x) b - covariant (g x) b‖ * B := by
        gcongr
      _ ≤ 1 / 2 := hsmall x hx
  · have huni' := tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp huni
    change TendstoUniformly
      (fun n (x : K) => matrixInverse (covariant (gₙ n x) b))
      (fun x : K => matrixInverse (covariant (g x) b)) p at huni'
    have heqₙ : (fun n (x : K) => matrixInverse (covariant (gₙ n x) b)) =
        (fun n (x : K) => contravariant (gₙ n x) (hnₙ n x x.property) b) := by
      funext n x
      exact matrixInverse_covariant (gₙ n x) (hnₙ n x x.property) (hsₙ n x x.property) b
    have heq : (fun x : K => matrixInverse (covariant (g x) b)) =
        (fun x : K => contravariant (g x) (hn x x.property) b) := by
      funext x
      exact matrixInverse_covariant (g x) (hn x x.property) (hs x x.property) b
    rwa [heqₙ, heq] at huni'

end Burnett.Geometry.InverseSequence
