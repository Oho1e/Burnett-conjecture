import Burnett.Geometry.FiberMetric
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Inverse metric perturbations in the actual component sup norm

No bound on the perturbed inverse is an input to the small-perturbation
estimate. Both inverse identities are later supplied by actual metric fibers.
The norms here are the usual finite-function sup norms on ordered components.
-/

noncomputable section

namespace Burnett.Geometry.InversePerturbation

open scoped BigOperators
open Burnett.RicciSymbol

/-- Matrix composition, explicitly distinguished from pointwise multiplication
of the function type used for the existing tensor components. -/
def compose (A B : Tensor2) : Tensor2 := fun i j => ∑ k, A i k * B k j

def identity : Tensor2 := fun i j => if i = j then 1 else 0

theorem compose_identity (A : Tensor2) : compose A identity = A := by
  funext i j
  simp [compose, identity, mul_ite]

theorem identity_compose (A : Tensor2) : compose identity A = A := by
  funext i j
  simp [compose, identity, ite_mul]

theorem compose_assoc (A B C : Tensor2) :
    compose (compose A B) C = compose A (compose B C) :=
  Matrix.mul_assoc A B C

theorem compose_sub_left (A B C : Tensor2) :
    compose (A - B) C = compose A C - compose B C := by
  funext i j
  simp [compose, sub_mul, Finset.sum_sub_distrib]

theorem compose_sub_right (A B C : Tensor2) :
    compose A (B - C) = compose A B - compose A C := by
  funext i j
  simp [compose, mul_sub, Finset.sum_sub_distrib]

/-- The resolvent identity is derived from the two relevant inverse laws. -/
theorem inverse_sub_inverse (g₀ g₁ inv₀ inv₁ : Tensor2)
    (hi₀ : compose g₀ inv₀ = identity) (hi₁ : compose inv₁ g₁ = identity) :
    inv₁ - inv₀ = compose (compose inv₁ (g₀ - g₁)) inv₀ := by
  symm
  rw [compose_sub_right, compose_sub_left, compose_assoc, hi₀, hi₁,
    compose_identity, identity_compose]

theorem abs_entry_le_norm (A : Tensor2) (i j : Index) : |A i j| ≤ ‖A‖ := by
  simpa only [Real.norm_eq_abs] using
    (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

theorem norm_le_of_entries_le (A : Tensor2) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i j, |A i j| ≤ C) : ‖A‖ ≤ C := by
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro j
  simpa only [Real.norm_eq_abs] using h i j

/-- Four terms in each component give this dimension-dependent bound. -/
theorem norm_compose_le (A B : Tensor2) : ‖compose A B‖ ≤ 4 * ‖A‖ * ‖B‖ := by
  apply norm_le_of_entries_le _ (by positivity)
  intro i j
  have hs := norm_sum_le Finset.univ (fun k : Index => A i k * B k j)
  simp only [Real.norm_eq_abs, abs_mul] at hs
  calc
    |compose A B i j| ≤ ∑ k, |A i k| * |B k j| := hs
    _ ≤ ∑ _ : Index, ‖A‖ * ‖B‖ := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul (abs_entry_le_norm A i k) (abs_entry_le_norm B k j)
        (abs_nonneg _) (norm_nonneg _)
    _ = 4 * ‖A‖ * ‖B‖ := by simp; ring

theorem norm_inverse_sub_le (g₀ g₁ inv₀ inv₁ : Tensor2)
    (hi₀ : compose g₀ inv₀ = identity) (hi₁ : compose inv₁ g₁ = identity) :
    ‖inv₁ - inv₀‖ ≤ 16 * ‖inv₁‖ * ‖g₁ - g₀‖ * ‖inv₀‖ := by
  rw [inverse_sub_inverse g₀ g₁ inv₀ inv₁ hi₀ hi₁]
  calc
    _ ≤ 4 * ‖compose inv₁ (g₀ - g₁)‖ * ‖inv₀‖ := norm_compose_le _ _
    _ ≤ 4 * (4 * ‖inv₁‖ * ‖g₀ - g₁‖) * ‖inv₀‖ := by
      gcongr
      exact norm_compose_le _ _
    _ = _ := by rw [norm_sub_rev g₀ g₁]; ring

/-- A small metric perturbation bounds the actual new inverse, rather than
assuming that bound. Nondegeneracy is needed only through its inverse law. -/
theorem norm_inverse_le_of_small (g₀ g₁ inv₀ inv₁ : Tensor2)
    (hi₀ : compose g₀ inv₀ = identity) (hi₁ : compose inv₁ g₁ = identity)
    (hsmall : 16 * ‖g₁ - g₀‖ * ‖inv₀‖ ≤ 1 / 2) : ‖inv₁‖ ≤ 2 * ‖inv₀‖ := by
  have hdiff := norm_inverse_sub_le g₀ g₁ inv₀ inv₁ hi₀ hi₁
  have htri : ‖inv₁‖ ≤ ‖inv₁ - inv₀‖ + ‖inv₀‖ := by
    simpa only [sub_add_cancel] using norm_add_le (inv₁ - inv₀) inv₀
  have hbound := mul_le_mul_of_nonneg_left hsmall (norm_nonneg inv₁)
  nlinarith

theorem norm_inverse_sub_le_of_small (g₀ g₁ inv₀ inv₁ : Tensor2)
    (hi₀ : compose g₀ inv₀ = identity) (hi₁ : compose inv₁ g₁ = identity)
    (hsmall : 16 * ‖g₁ - g₀‖ * ‖inv₀‖ ≤ 1 / 2) :
    ‖inv₁ - inv₀‖ ≤ 32 * ‖inv₀‖ ^ 2 * ‖g₁ - g₀‖ := by
  calc
    _ ≤ 16 * ‖inv₁‖ * ‖g₁ - g₀‖ * ‖inv₀‖ :=
      norm_inverse_sub_le g₀ g₁ inv₀ inv₁ hi₀ hi₁
    _ ≤ 16 * (2 * ‖inv₀‖) * ‖g₁ - g₀‖ * ‖inv₀‖ := by
      gcongr
      exact norm_inverse_le_of_small g₀ g₁ inv₀ inv₁ hi₀ hi₁ hsmall
    _ = _ := by ring

section MetricFibers

open Module
open Burnett.Geometry.FiberMetric

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem covariant_sub (g₀ g₁ : LinearMap.BilinForm ℝ V) (b : Basis Index ℝ V) :
    covariant (g₀ - g₁) b = covariant g₀ b - covariant g₁ b := rfl

theorem covariant_compose_contravariant (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (hs : g.IsSymm) (b : Basis Index ℝ V) :
    compose (covariant g b) (contravariant g hg b) = identity := by
  funext i j
  exact covariant_mul_contravariant g hg hs b i j

theorem contravariant_compose_covariant (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (hs : g.IsSymm) (b : Basis Index ℝ V) :
    compose (contravariant g hg b) (covariant g b) = identity := by
  funext i j
  exact contravariant_mul_covariant g hg hs b i j

/-- The inverse difference for the inverse lowering maps of genuine symmetric,
nondegenerate bilinear forms, in one given basis. -/
theorem fiber_inverse_sub_inverse (g₀ g₁ : LinearMap.BilinForm ℝ V)
    (hn₀ : g₀.Nondegenerate) (hn₁ : g₁.Nondegenerate)
    (hs₀ : g₀.IsSymm) (hs₁ : g₁.IsSymm) (b : Basis Index ℝ V) :
    contravariant g₁ hn₁ b - contravariant g₀ hn₀ b =
      compose (compose (contravariant g₁ hn₁ b) (covariant (g₀ - g₁) b))
        (contravariant g₀ hn₀ b) := by
  rw [covariant_sub]
  exact inverse_sub_inverse _ _ _ _
    (covariant_compose_contravariant g₀ hn₀ hs₀ b)
    (contravariant_compose_covariant g₁ hn₁ hs₁ b)

/-- Pointwise bounds for actual inverse metrics. The only smallness condition
uses the background inverse and the covariant metric difference. -/
theorem fiber_inverse_estimates (g₀ g₁ : LinearMap.BilinForm ℝ V)
    (hn₀ : g₀.Nondegenerate) (hn₁ : g₁.Nondegenerate)
    (hs₀ : g₀.IsSymm) (hs₁ : g₁.IsSymm) (b : Basis Index ℝ V)
    (hsmall : 16 * ‖covariant g₁ b - covariant g₀ b‖ *
      ‖contravariant g₀ hn₀ b‖ ≤ 1 / 2) :
    ‖contravariant g₁ hn₁ b‖ ≤ 2 * ‖contravariant g₀ hn₀ b‖ ∧
    ‖contravariant g₁ hn₁ b - contravariant g₀ hn₀ b‖ ≤
      32 * ‖contravariant g₀ hn₀ b‖ ^ 2 * ‖covariant g₁ b - covariant g₀ b‖ := by
  have hi₀ := covariant_compose_contravariant g₀ hn₀ hs₀ b
  have hi₁ := contravariant_compose_covariant g₁ hn₁ hs₁ b
  exact ⟨norm_inverse_le_of_small _ _ _ _ hi₀ hi₁ hsmall,
    norm_inverse_sub_le_of_small _ _ _ _ hi₀ hi₁ hsmall⟩

/-- Uniform estimates on a specified set, including any fixed compact chart
set. Nondegeneracy and symmetry are required only at points of that set.
The background inverse bound and covariant perturbation bound are explicit
inputs; the perturbed inverse bound is derived. No global extension is used. -/
theorem fiber_inverse_estimates_on {X : Type*} (K : Set X)
    (g₀ g₁ : X → LinearMap.BilinForm ℝ V)
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate)
    (hn₁ : ∀ x ∈ K, (g₁ x).Nondegenerate)
    (hs₀ : ∀ x ∈ K, (g₀ x).IsSymm) (hs₁ : ∀ x ∈ K, (g₁ x).IsSymm)
    (b : Basis Index ℝ V) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hbase : ∀ x (hx : x ∈ K), ‖contravariant (g₀ x) (hn₀ x hx) b‖ ≤ B)
    (hdiff : ∀ x ∈ K, ‖covariant (g₁ x) b - covariant (g₀ x) b‖ ≤ ε)
    (hsmall : 16 * ε * B ≤ 1 / 2) :
    ∀ x (hx : x ∈ K),
      ‖contravariant (g₁ x) (hn₁ x hx) b‖ ≤ 2 * B ∧
      ‖contravariant (g₁ x) (hn₁ x hx) b - contravariant (g₀ x) (hn₀ x hx) b‖ ≤
        32 * B ^ 2 * ε := by
  intro x hx
  have hpoint : 16 * ‖covariant (g₁ x) b - covariant (g₀ x) b‖ *
      ‖contravariant (g₀ x) (hn₀ x hx) b‖ ≤ 1 / 2 := by
    calc
      _ ≤ 16 * ε * B := by
        gcongr
        · exact hdiff x hx
        · exact hbase x hx
      _ ≤ 1 / 2 := hsmall
  obtain ⟨hinv, hdelta⟩ := fiber_inverse_estimates (g₀ x) (g₁ x)
    (hn₀ x hx) (hn₁ x hx) (hs₀ x hx) (hs₁ x hx) b hpoint
  constructor
  · exact hinv.trans (by gcongr; exact hbase x hx)
  · apply hdelta.trans
    gcongr
    · exact hbase x hx
    · exact hdiff x hx

end MetricFibers

end Burnett.Geometry.InversePerturbation
