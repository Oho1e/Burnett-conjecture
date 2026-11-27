import Burnett.Analysis.PrincipalEnergy.Freezing.PatchLpDuality
import Burnett.Analysis.PrincipalEnergy.Freezing.FiniteModeEnergyLinearity

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace Burnett.A03

open MeasureTheory Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal BigOperators Burnett.A03

abbrev PatchFieldLpJet (J : Type) := (J → PatchLp3) × (Index × J → PatchLp3)

private def patchValueComponent (J : Type) (i : J) : PatchFieldLpJet J →L[ℂ] PatchLp3 :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ (J → PatchLp3) (Index × J → PatchLp3))

private def patchDerivativeComponent (J : Type) (i : Index × J) : PatchFieldLpJet J →L[ℂ] PatchLp3 :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ (J → PatchLp3) (Index × J → PatchLp3))

/-- The three slots of the original action are continuous on the (L^3)
test value and coordinate derivative arrays for a fixed coefficient and field. -/
def principalCubicLpFunctional {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ) :
    PatchFieldLpJet J →L[ℂ] ℂ :=
  let U (i : Index × J) := energyPartial i.1 (z i.2)
  let R := principalCoefficientContraction C z
  (∑ p : (Index × J) × (Index × J), ∑ i : J,
    (patchLpPair (energyProduct (C p.1.1 p.2.1 i p.1.2 p.2.2)
      (energyProduct (U p.1) (U p.2)))).comp (patchValueComponent J i)) +
  (∑ p : (Index × J) × (Index × J),
    ((patchLpPair (energyProduct (R p) (U p.2))).comp (patchDerivativeComponent J p.1) +
      (patchLpPair (energyProduct (R p) (U p.1))).comp (patchDerivativeComponent J p.2)))

private theorem patch_slot_integrable {u : E → ℂ}
    (h : MemLp u (ENNReal.ofReal 3) volume) (A : SchwartzMap E ℂ) :
    Integrable (fun x => u x * A x) :=
  (energy_integral_three_three_halves h (A.memLp (ENNReal.ofReal (3 / 2)) volume)).1

theorem principal_cubic_Lp_functional_eq_action {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (w : J → E → ℂ) (hJet : ∀ i, BoundedCoordinateJet (w i))
    (hV : ∀ i, MemLp (w i) (ENNReal.ofReal 3) volume)
    (hD : ∀ p : Index × J,
      MemLp (fun x => fderiv ℝ (w p.2) x (EuclideanSpace.single p.1 1)) (ENNReal.ofReal 3) volume) :
    principalCubicLpFunctional C z (fun i => (hV i).toLp _, fun p => (hD p).toLp _) =
      principalPatchTestEnergy C z w := by
  classical
  let T := Index × J
  let S := T × T
  let U (i : T) := energyPartial i.1 (z i.2)
  let R (p : S) := principalCoefficientContraction C z p
  let D (p : T) (x : E) := fderiv ℝ (w p.2) x (EuclideanSpace.single p.1 1)
  let V (p : S) (i : J) := energyProduct (C p.1.1 p.2.1 i p.1.2 p.2.2)
    (energyProduct (U p.1) (U p.2))
  let A (p : S) := energyProduct (R p) (U p.2)
  let B (p : S) := energyProduct (R p) (U p.1)
  have vIntegrable (p : S) (i : J) : Integrable (fun x => w i x * V p i x) :=
    patch_slot_integrable (hV i) (V p i)
  have aIntegrable (p : S) : Integrable (fun x => D p.1 x * A p x) :=
    patch_slot_integrable (hD p.1) (A p)
  have bIntegrable (p : S) : Integrable (fun x => D p.2 x * B p x) :=
    patch_slot_integrable (hD p.2) (B p)
  have density :
      (fun x => principalVariationDensity (fun a d i j k => C a d i j k) z w x) =
        fun x => (∑ p : S, ∑ i, w i x * V p i x) +
          ∑ p : S, (D p.1 x * A p x + D p.2 x * B p x) := by
    funext x
    rw [principal_variation_density_contracted C z w x]
    refine congrArg₂ (· + ·) ?_ ?_
    · apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro i _
      simp only [V, energyProduct_apply, U]
      ring
    · apply Finset.sum_congr rfl
      intro p _
      simp only [D, A, B, U, R, energyProduct_apply]
      ring
  unfold principalPatchTestEnergy
  rw [(principal_variation_action_derivatives C z w hJet).1.deriv, density]
  have intSplit : (∫ x, (∑ p : S, ∑ i, w i x * V p i x) +
        ∑ p : S, (D p.1 x * A p x + D p.2 x * B p x)) =
      (∫ x, ∑ p : S, ∑ i, w i x * V p i x) + ∫ x, ∑ p : S, (D p.1 x * A p x + D p.2 x * B p x) := by
    exact integral_add
      (integrable_finset_sum Finset.univ (fun p _ => integrable_finset_sum Finset.univ (fun i _ => vIntegrable p i)))
      (integrable_finset_sum Finset.univ (fun p _ => (aIntegrable p).add (bIntegrable p)))
  rw [intSplit]
  have intD : (∫ x, ∑ p : S, (D p.1 x * A p x + D p.2 x * B p x)) =
      ∑ p : S, ∫ x, (D p.1 x * A p x + D p.2 x * B p x) :=
    integral_finset_sum Finset.univ (fun p _ => (aIntegrable p).add (bIntegrable p))
  rw [integral_finset_sum Finset.univ (fun p _ => integrable_finset_sum Finset.univ (fun i _ => vIntegrable p i)), intD]
  simp only [principalCubicLpFunctional, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, patchValueComponent, patchDerivativeComponent,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.proj_apply,
    patch_lp_pair_toLp]
  refine congrArg₂ (· + ·) ?_ ?_
  · apply Finset.sum_congr rfl
    intro p _
    exact (integral_finset_sum Finset.univ (fun i _ => vIntegrable p i)).symm
  · apply Finset.sum_congr rfl
    intro p _
    exact (integral_add (aIntegrable p) (bIntegrable p)).symm

/-- Assemble the actual mode's value and Fréchet derivative representatives. -/
def separatedModeFieldLpJet {J : Type}
    (f : SchwartzMap E ℂ) (b : E → ℝ) (z : J → SchwartzMap E ℂ)
    (h : ∀ i, SeparatedModeLpJet f b (z i)) : PatchFieldLpJet J :=
  (fun i => (h i).valueLp, fun p => (h p.2).coordinateLp p.1)

theorem principal_cubic_Lp_functional_mode {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (f : SchwartzMap E ℂ) (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (h : ∀ i, SeparatedModeLpJet f b (z i)) :
    principalCubicLpFunctional C z (separatedModeFieldLpJet f b z h) = separatedModeEnergy C z f b :=
  principal_cubic_Lp_functional_eq_action C z _ (fun i => separated_skew_bounded_coordinate_jet f b hb hom (z i))
    (fun i => (h i).value) (fun p => (h p.2).coordinate p.1)

end Burnett.A03
