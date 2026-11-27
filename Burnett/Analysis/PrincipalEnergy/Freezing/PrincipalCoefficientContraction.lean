import Burnett.Analysis.TransportWard.Weyl.Amplitude.LocalizedPrincipalTest

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.RicciSymbol
open scoped BigOperators

/-- Contract the coefficient array with the undifferentiated slot of the
same field, keeping the result in the Schwartz test class. -/
def principalCoefficientContraction {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ)
    (z : J → SchwartzMap E ℂ) (k : (Index × J) × (Index × J)) : SchwartzMap E ℂ :=
  ∑ i, energyProduct (C k.1.1 k.2.1 i k.1.2 k.2.2) (z i)

theorem principalCoefficientContraction_apply {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ)
    (z : J → SchwartzMap E ℂ) (k : (Index × J) × (Index × J)) (x : E) :
    principalCoefficientContraction C z k x = ∑ i, C k.1.1 k.2.1 i k.1.2 k.2.2 x * z i x := by
  let eval : SchwartzMap E ℂ →+ ℂ :=
    {toFun := fun u => u x, map_zero' := rfl, map_add' := fun _ _ => rfl}
  change eval (∑ i, energyProduct (C k.1.1 k.2.1 i k.1.2 k.2.2) (z i)) = _
  exact map_sum eval _ _

theorem principalCoefficientContraction_symm {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ)
    (z : J → SchwartzMap E ℂ)
    (symm : ∀ a d i j k, C a d i j k = C d a i k j) (u v : Index × J) :
    principalCoefficientContraction C z (u,v) = principalCoefficientContraction C z (v,u) := by
  unfold principalCoefficientContraction
  apply Finset.sum_congr rfl
  intro i _
  rw [symm u.1 v.1 i u.2 v.2]

private theorem sum_coordinate_slots {J : Type} [Fintype J]
    (F : Index → Index → J → J → J → ℂ) :
    (∑ a, ∑ d, ∑ i, ∑ j, ∑ k, F a d i j k) =
      ∑ p : (Index × J) × (Index × J), ∑ i, F p.1.1 p.2.1 i p.1.2 p.2.2 := by
  let e : Index × Index × J × J × J ≃ ((Index × J) × (Index × J)) × J :=
    {toFun := fun p => (((p.1,p.2.2.2.1),(p.2.1,p.2.2.2.2)),p.2.2.1),
     invFun := fun p => (p.1.1.1,p.1.2.1,p.2,p.1.1.2,p.1.2.2),
     left_inv := fun _ => rfl, right_inv := fun _ => rfl}
  calc
    _ = ∑ p : Index × Index × J × J × J, F p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ p : ((Index × J) × (Index × J)) × J, F p.1.1.1 p.1.2.1 p.2 p.1.1.2 p.1.2.2 :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_prod_type _

/-- Regroup the two differentiated test slots in the principal density using
the actual coefficient contraction. The undifferentiated test stays in its
original slot. -/
theorem principal_variation_density_contracted {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ)
    (z : J → SchwartzMap E ℂ) (w : J → E → ℂ) (x : E) :
    let U (i : Index × J) := energyPartial i.1 (z i.2) x
    let D (i : Index × J) := fderiv ℝ (w i.2) x (EuclideanSpace.single i.1 1)
    let R (k : (Index × J) × (Index × J)) := principalCoefficientContraction C z k x
    principalVariationDensity (fun a d i j k => C a d i j k) z w x =
      (∑ p : (Index × J) × (Index × J),
        ∑ i, C p.1.1 p.2.1 i p.1.2 p.2.2 x * (w i x * U p.1 * U p.2)) +
      (∑ p : (Index × J) × (Index × J), (D p.1 * R p * U p.2 + U p.1 * R p * D p.2)) := by
  dsimp only
  rw [principalVariationDensity, sum_coordinate_slots, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp only [principalCoefficientContraction_apply, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Burnett.A02.FrequencySplit
