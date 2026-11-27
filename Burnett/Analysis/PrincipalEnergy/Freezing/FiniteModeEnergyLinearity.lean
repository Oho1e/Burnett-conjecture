import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedModeEnergy

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace Burnett.A03

open MeasureTheory Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped ContDiff BigOperators

/-- Vary the original field in the direction of the actual test output. -/
def principalPatchTestEnergy {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (w : J → E → ℂ) : ℂ :=
  deriv (fun t : ℝ => principalCubicAction C (fun i x => z i x + t • w i x)) 0

private theorem bounded_coordinate_jet_add {u v : E → ℂ} (hu : BoundedCoordinateJet u)
    (hv : BoundedCoordinateJet v) : BoundedCoordinateJet (u + v) := by
  have hDiff : Differentiable ℝ (u + v) := hu.1.add hv.1
  obtain ⟨A, hA, hValU⟩ := hu.2.1
  obtain ⟨B, hB, hValV⟩ := hv.2.1
  refine ⟨hDiff, ⟨A+B, add_nonneg hA hB, fun x =>
    (norm_add_le _ _).trans (add_le_add (hValU x) (hValV x))⟩, ?_⟩
  intro a
  obtain ⟨M, hM, hU⟩ := hu.2.2 a
  obtain ⟨N, hN, hV⟩ := hv.2.2 a
  refine ⟨M+N, add_nonneg hM hN, fun x => ?_⟩
  rw [fderiv_add (hu.1 x) (hv.1 x), ContinuousLinearMap.add_apply]
  exact (norm_add_le _ _).trans (add_le_add (hU x) (hV x))

private theorem bounded_coordinate_jet_zero : BoundedCoordinateJet (0 : E → ℂ) := by
  refine ⟨differentiable_const (0 : ℂ), ⟨0, le_rfl, by simp⟩, fun _ => ⟨0, le_rfl, ?_⟩⟩
  intro x
  simp

private theorem principal_variation_density_integrable {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (w : J → E → ℂ) (hw : ∀ i, BoundedCoordinateJet (w i)) :
    Integrable (principalVariationDensity (fun a d i j k => C a d i j k) z w) := by
  let u (i : J) : E → ℂ := z i
  have hu (i : J) : BoundedCoordinateJet (u i) := schwartz_bounded_coordinate_jet (z i)
  rw [← principal_cubic_linear_density_eq_variation (fun a d i j k => C a d i j k) z w]
  exact ((principal_cubic_mixed_integrable C w u u hw hu hu).add
    (principal_cubic_mixed_integrable C u w u hu hw hu)).add
    (principal_cubic_mixed_integrable C u u w hu hu hw)

private theorem principal_variation_density_add {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (u v : J → E → ℂ) (hu : ∀ i, Differentiable ℝ (u i)) (hv : ∀ i, Differentiable ℝ (v i)) :
    principalVariationDensity (fun a d i j k => C a d i j k) z (u + v) =
      principalVariationDensity (fun a d i j k => C a d i j k) z u +
        principalVariationDensity (fun a d i j k => C a d i j k) z v := by
  funext x
  have variation (i : J) (a : Index) :
      fderiv ℝ (u i + v i) x (EuclideanSpace.single a 1) =
        fderiv ℝ (u i) x (EuclideanSpace.single a 1) +
          fderiv ℝ (v i) x (EuclideanSpace.single a 1) := by
    rw [fderiv_add (hu i x) (hv i x), ContinuousLinearMap.add_apply]
  simp only [principalVariationDensity, Pi.add_apply, variation, add_mul, mul_add, Finset.sum_add_distrib]
  abel

private theorem principal_patch_test_energy_add {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (u v : J → E → ℂ) (hu : ∀ i, BoundedCoordinateJet (u i)) (hv : ∀ i, BoundedCoordinateJet (v i)) :
    principalPatchTestEnergy C z (u + v) = principalPatchTestEnergy C z u + principalPatchTestEnergy C z v := by
  unfold principalPatchTestEnergy
  rw [(principal_variation_action_derivatives C z (u+v) (fun i => bounded_coordinate_jet_add (hu i) (hv i))).1.deriv,
    (principal_variation_action_derivatives C z u hu).1.deriv,
    (principal_variation_action_derivatives C z v hv).1.deriv,
    principal_variation_density_add C z u v (fun i => (hu i).1) (fun i => (hv i).1)]
  exact integral_add (principal_variation_density_integrable C z u hu)
    (principal_variation_density_integrable C z v hv)

/-- The action variation of a finite sum of actual outputs equals the sum
of the individual action variations. -/
theorem principal_patch_test_energy_finset_sum {J I : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (w : I → J → E → ℂ) (modes : Finset I) (h : ∀ k ∈ modes, ∀ i, BoundedCoordinateJet (w k i)) :
    (∀ i, BoundedCoordinateJet ((∑ k ∈ modes, w k) i)) ∧
    principalPatchTestEnergy C z (∑ k ∈ modes, w k) =
      ∑ k ∈ modes, principalPatchTestEnergy C z (w k) := by
  classical
  induction modes using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, Pi.zero_apply]
      exact ⟨fun _ => bounded_coordinate_jet_zero, by simp [principalPatchTestEnergy]⟩
  | insert k modes hkm ih =>
      have hk := h k (Finset.mem_insert_self k modes)
      obtain ⟨hw, energy⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      rw [Finset.sum_insert hkm, Finset.sum_insert hkm]
      refine ⟨fun i => bounded_coordinate_jet_add (hk i) (hw i), ?_⟩
      rw [principal_patch_test_energy_add C z (w k) (∑ j ∈ modes, w j) hk hw, energy]

/-- Both real phases of each actual Fourier mode enter the same finite
directional derivative of the original cubic action. -/
theorem finite_mode_energy_eq_sum {J I : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (modes : Finset I) (f : I → Fin 2 → SchwartzMap E ℂ) (b : I → Fin 2 → E → ℝ)
    (hb : ∀ k j, ContDiffOn ℝ ∞ (b k j) {ξ | ξ ≠ 0})
    (hom : ∀ k j (t : ℝ), 0 < t → ∀ ξ, b k j (t • ξ) = t * b k j ξ) :
    principalPatchTestEnergy C z (fun i x =>
      ∑ k ∈ modes, ∑ j : Fin 2, separatedSkewAction (f k j) (b k j) (z i) x) =
      ∑ k ∈ modes, ∑ j : Fin 2, separatedModeEnergy C z (f k j) (b k j) := by
  let w (k : I) (j : Fin 2) (i : J) := separatedSkewAction (f k j) (b k j) (z i)
  have innerJet (k : I) : ∀ j ∈ Finset.univ, ∀ i, BoundedCoordinateJet (w k j i) :=
    fun j _ i => separated_skew_bounded_coordinate_jet (f k j) (b k j) (hb k j) (hom k j) (z i)
  have inner (k : I) := principal_patch_test_energy_finset_sum C z (w k) Finset.univ (innerJet k)
  have outer := principal_patch_test_energy_finset_sum C z (fun k => ∑ j, w k j) modes (fun k _ => (inner k).1)
  have eq : (fun i x => ∑ k ∈ modes, ∑ j : Fin 2, separatedSkewAction (f k j) (b k j) (z i) x) =
      ∑ k ∈ modes, ∑ j : Fin 2, w k j := by
    funext i x
    simp only [w, Finset.sum_apply]
  rw [eq, outer.2]
  apply Finset.sum_congr rfl
  intro k _
  exact (inner k).2

end Burnett.A03
