import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedSkewPlacement
import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedSkewDifferentiation

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate ContDiff

/-- The two test derivatives in the principal variation reduce to a coefficient
commutator and the spatial-profile derivative. All derivatives are those of the
same scalar action applied to the components of the same real field. -/
theorem separated_skew_both_derivative_terms {J : Type} [Fintype J]
    (f : SchwartzMap E ℂ) (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (hf : ∀ x, conj (f x) = f x) (hodd : ∀ ξ, b (-ξ) = -b ξ)
    (R : (Index × J) × (Index × J) → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (symm : ∀ i j, R (i,j) = R (j,i)) (hz : ∀ j x, conj (z j x) = z j x) :
    let U (i : Index × J) := energyPartial i.1 (z i.2)
    let D (i : Index × J) (x : E) :=
      fderiv ℝ (separatedSkewAction f b (z i.2)) x (EuclideanSpace.single i.1 1)
    let F (i : Index × J) := separatedSkewAction (energyPartial i.1 f) b (z i.2)
    (∑ k : (Index × J) × (Index × J), ∫ x, D k.1 x * R k x * U k.2 x) +
      (∑ k : (Index × J) × (Index × J), ∫ x, U k.1 x * R k x * D k.2 x) =
      -(∑ k : (Index × J) × (Index × J), ∫ x,
        U k.1 x * separatedSkewCommutator f b (R k) (U k.2) x) +
      2 * (∑ k : (Index × J) × (Index × J), ∫ x, U k.1 x * R k x * F k.2 x) := by
  let T := Index × J
  let U (i : T) := energyPartial i.1 (z i.2)
  let D (i : T) (x : E) :=
    fderiv ℝ (separatedSkewAction f b (z i.2)) x (EuclideanSpace.single i.1 1)
  let F (i : T) := separatedSkewAction (energyPartial i.1 f) b (z i.2)
  let P (i : T) := separatedSkewAction f b (U i)
  let W (k : T × T) := ∫ x, U k.1 x * R k x * D k.2 x
  let A (k : T × T) := ∫ x, U k.1 x * R k x * P k.2 x
  let B (k : T × T) := ∫ x, U k.1 x * R k x * F k.2 x
  have derivative (i : T) (x : E) : D i x = P i x + F i x := by
    have h := (separated_skew_coordinate_commutator f b hb hom (z i.2) x i.1).2
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  have placement (k : T × T) : (∫ x, D k.1 x * R k x * U k.2 x) = W k.swap := by
    rcases k with ⟨i,j⟩
    apply integral_congr_ae
    filter_upwards with x
    simp only [Prod.swap, symm i j]
    ring
  have sumSwap : (∑ k : T × T, W k.swap) = ∑ k, W k :=
    Fintype.sum_equiv (Equiv.prodComm T T) _ _ (fun _ => rfl)
  have sumSplit (k : T × T) : W k = A k + B k := by
    have first : Integrable (fun x => U k.1 x * R k x * P k.2 x) :=
      ((energyProduct (U k.1) (R k)).memLp 2 volume).integrable_mul
        (separatedSkewAction_memLp_two f b hb hom (U k.2))
    have second : Integrable (fun x => U k.1 x * R k x * F k.2 x) :=
      ((energyProduct (U k.1) (R k)).memLp 2 volume).integrable_mul
        (separatedSkewAction_memLp_two (energyPartial k.2.1 f) b hb hom (z k.2.2))
    change (∫ x, U k.1 x * R k x * D k.2 x) = A k + B k
    simp_rw [derivative, mul_add]
    exact integral_add first second
  change (∑ k : T × T, ∫ x, D k.1 x * R k x * U k.2 x) + (∑ k : T × T, W k) =
    -(∑ k : T × T, ∫ x, U k.1 x * separatedSkewCommutator f b (R k) (U k.2) x) +
      2 * (∑ k : T × T, B k)
  simp_rw [placement, sumSwap, sumSplit, Finset.sum_add_distrib]
  rw [← coordinate_separated_skew_placement f b hb hom hf hodd R z symm hz]
  change ((∑ k, A k) + ∑ k, B k) + ((∑ k, A k) + ∑ k, B k) =
    2 * (∑ k, A k) + 2 * (∑ k, B k)
  ring

end Burnett.A02.FrequencySplit
