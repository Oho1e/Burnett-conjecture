import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.UrysohnsLemma

/-!
# Local order-unit bounds for positive real functionals

These are fixed-support bounds on genuine compactly supported continuous
tests, including subspaces that can later be instantiated by smooth tests.
Positivity is an explicit input; no pseudodifferential positivity or defect
measure existence is asserted here.
-/

noncomputable section

open Set
open scoped CompactlySupported ZeroAtInfty

namespace Burnett.Microlocal.PositiveFunctional

variable {X : Type*} [TopologicalSpace X]

/-- Pointwise order-unit control implies scalar control for a positive real
linear functional on an actual subspace of compactly supported tests. -/
theorem abs_apply_le_of_pointwise_order_unit_subspace
    (S : Submodule ℝ C_c(X, ℝ)) (L : S →ₗ[ℝ] ℝ)
    (hpos : ∀ g : S, (∀ x, 0 ≤ (g : C_c(X, ℝ)) x) → 0 ≤ L g)
    (f e : S) (c : ℝ)
    (hbound : ∀ x, |(f : C_c(X, ℝ)) x| ≤ c * (e : C_c(X, ℝ)) x) :
    |L f| ≤ c * L e := by
  have hl := hpos (c • e + f) (fun x => by
    change 0 ≤ c * (e : C_c(X, ℝ)) x + (f : C_c(X, ℝ)) x
    have h := add_le_add_left (abs_le.mp (hbound x)).1 (c * (e : C_c(X, ℝ)) x)
    simpa only [add_neg_cancel] using h)
  have hu := hpos (c • e + (-1 : ℝ) • f) (fun x => by
    change 0 ≤ c * (e : C_c(X, ℝ)) x + (-1) * (f : C_c(X, ℝ)) x
    simpa only [neg_one_mul, sub_eq_add_neg] using
      sub_nonneg.mpr (abs_le.mp (hbound x)).2)
  simp only [L.map_add, L.map_smul, smul_eq_mul] at hl
  simp only [L.map_add, L.map_smul, smul_eq_mul, neg_one_mul] at hu
  apply abs_le.mpr
  constructor
  · have h := add_le_add_left hl (-(c * L e))
    simpa only [add_zero, ← add_assoc, neg_add_cancel, zero_add] using h
  · exact sub_nonneg.mp (by simpa only [sub_eq_add_neg] using hu)

/-- The actual supremum norm, through the canonical map into `C₀`, controls
the functional on tests supported where a fixed nonnegative cutoff is one. -/
theorem abs_apply_le_of_supported_subspace
    (S : Submodule ℝ C_c(X, ℝ)) (L : S →ₗ[ℝ] ℝ)
    (hpos : ∀ g : S, (∀ x, 0 ≤ (g : C_c(X, ℝ)) x) → 0 ≤ L g)
    (f e : S) (K : Set X)
    (he : ∀ x, 0 ≤ (e : C_c(X, ℝ)) x)
    (heK : ∀ x ∈ K, (e : C_c(X, ℝ)) x = 1)
    (hfK : Function.support (f : C_c(X, ℝ)) ⊆ K) :
    |L f| ≤ ‖((f : C_c(X, ℝ)) : C₀(X, ℝ))‖ * L e := by
  apply abs_apply_le_of_pointwise_order_unit_subspace S L hpos f e
    ‖((f : C_c(X, ℝ)) : C₀(X, ℝ))‖
  intro x
  by_cases hx : x ∈ K
  · rw [heK x hx, mul_one]
    simpa only [Real.norm_eq_abs, ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using
      (((f : C_c(X, ℝ)) : C₀(X, ℝ)).toBCF.norm_coe_le_norm x)
  · have hfx : (f : C_c(X, ℝ)) x = 0 := by
      by_contra hne
      exact hx (hfK hne)
    rw [hfx, abs_zero]
    exact mul_nonneg (norm_nonneg _) (he x)

/-- Fixed-cutoff local supremum bound for a positive functional on all
compactly supported continuous real tests. -/
theorem abs_apply_le_of_supported
    (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) (f e : C_c(X, ℝ)) (K : Set X)
    (he : ∀ x, 0 ≤ e x) (heK : ∀ x ∈ K, e x = 1)
    (hfK : Function.support f ⊆ K) :
    |Λ f| ≤ ‖(f : C₀(X, ℝ))‖ * Λ e := by
  let S : Submodule ℝ C_c(X, ℝ) := ⊤
  let L : S →ₗ[ℝ] ℝ := Λ.toLinearMap.comp S.subtype
  let fS : S := ⟨f, Submodule.mem_top⟩
  let eS : S := ⟨e, Submodule.mem_top⟩
  have hpos (g : S) (hg : ∀ x, 0 ≤ (g : C_c(X, ℝ)) x) : 0 ≤ L g :=
    Λ.map_nonneg hg
  exact abs_apply_le_of_supported_subspace S L hpos fS eS K he heK hfK

/-- On every compact set in a locally compact Hausdorff space there is an
actual finite nonnegative bound for all tests supported in that set. -/
theorem exists_nonneg_bound_on_compact [T2Space X] [LocallyCompactSpace X]
    (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) (K : Set X) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : C_c(X, ℝ), Function.support f ⊆ K →
      |Λ f| ≤ C * ‖(f : C₀(X, ℝ))‖ := by
  obtain ⟨e, heK, _, hec, he01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  let eC : C_c(X, ℝ) := ⟨e, hec⟩
  have he (x : X) : 0 ≤ eC x := (he01 x).1
  refine ⟨Λ eC, Λ.map_nonneg he, ?_⟩
  intro f hfK
  simpa only [mul_comm] using abs_apply_le_of_supported Λ f eC K he heK hfK

end Burnett.Microlocal.PositiveFunctional
