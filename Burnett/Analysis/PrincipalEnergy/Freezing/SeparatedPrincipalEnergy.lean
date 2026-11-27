import Burnett.Analysis.PrincipalEnergy.Freezing.PrincipalCoefficientContraction
import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedSkewEnergyPlacement

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate ContDiff

/-- The principal cubic test has the three terms of the freezing identity
for the actual separated Fourier action on a single field. -/
theorem separated_principal_variation_formula {J : Type} [Fintype J]
    (f : SchwartzMap E ℂ) (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (hf : ∀ x, conj (f x) = f x) (hodd : ∀ ξ, b (-ξ) = -b ξ)
    (C : Index → Index → J → J → J → SchwartzMap E ℂ)
    (z : J → SchwartzMap E ℂ)
    (symm : ∀ a d i j k, C a d i j k = C d a i k j) (hz : ∀ j x, conj (z j x) = z j x) :
    let U (i : Index × J) := energyPartial i.1 (z i.2)
    let Qz (i : J) := separatedSkewAction f b (z i)
    let R := principalCoefficientContraction C z
    let V (x : E) := ∑ p : (Index × J) × (Index × J),
      ∑ i, C p.1.1 p.2.1 i p.1.2 p.2.2 x * (Qz i x * U p.1 x * U p.2 x)
    (∫ x, principalVariationDensity (fun a d i j k => C a d i j k) z Qz x) =
      (∫ x, V x) -
        (∑ p : (Index × J) × (Index × J), ∫ x,
          U p.1 x * separatedSkewCommutator f b (R p) (U p.2) x) +
        2 * (∑ p : (Index × J) × (Index × J), ∫ x, U p.1 x * R p x *
          separatedSkewAction (energyPartial p.2.1 f) b (z p.2.2) x) := by
  intro U Qz R V
  let T := Index × J
  let D (i : T) (x : E) := fderiv ℝ (Qz i.2) x (EuclideanSpace.single i.1 1)
  let L (p : T × T) (x : E) := D p.1 x * R p x * U p.2 x
  let M (p : T × T) (x : E) := U p.1 x * R p x * D p.2 x
  have derivativeLp (i : T) : MemLp (D i) 2 volume := by
    have eq : D i = fun x => separatedSkewAction f b (U i) x +
        separatedSkewAction (energyPartial i.1 f) b (z i.2) x := by
      funext x
      have h := (separated_skew_coordinate_commutator f b hb hom (z i.2) x i.1).2
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
    rw [eq]
    exact (separatedSkewAction_memLp_two f b hb hom (U i)).add
      (separatedSkewAction_memLp_two (energyPartial i.1 f) b hb hom (z i.2))
  have valueTerm (p : T × T) (i : J) :
      Integrable (fun x => C p.1.1 p.2.1 i p.1.2 p.2.2 x * (Qz i x * U p.1 x * U p.2 x)) := by
    let G := energyProduct (energyProduct (C p.1.1 p.2.1 i p.1.2 p.2.2) (U p.1)) (U p.2)
    have h : Integrable (fun x => G x * Qz i x) :=
      (G.memLp 2 volume).integrable_mul (separatedSkewAction_memLp_two f b hb hom (z i))
    refine h.congr ?_
    filter_upwards with x
    simp only [G, energyProduct_apply]
    ring
  have leftTerm (p : T × T) : Integrable (L p) := by
    have h : Integrable (fun x => energyProduct (R p) (U p.2) x * D p.1 x) :=
      ((energyProduct (R p) (U p.2)).memLp 2 volume).integrable_mul (derivativeLp p.1)
    refine h.congr ?_
    filter_upwards with x
    simp only [L, energyProduct_apply]
    ring
  have rightTerm (p : T × T) : Integrable (M p) :=
    ((energyProduct (U p.1) (R p)).memLp 2 volume).integrable_mul (derivativeLp p.2)
  have hv : Integrable V :=
    integrable_finset_sum Finset.univ (fun p _ =>
      integrable_finset_sum Finset.univ (fun i _ => valueTerm p i))
  have hl : Integrable (fun x => ∑ p, L p x) :=
    integrable_finset_sum Finset.univ (fun p _ => leftTerm p)
  have hm : Integrable (fun x => ∑ p, M p x) :=
    integrable_finset_sum Finset.univ (fun p _ => rightTerm p)
  have split : (fun x => principalVariationDensity (fun a d i j k => C a d i j k) z Qz x) =
      fun x => V x + ((∑ p, L p x) + ∑ p, M p x) := by
    funext x
    rw [← Finset.sum_add_distrib]
    exact principal_variation_density_contracted C z Qz x
  have pairEq := separated_skew_both_derivative_terms f b hb hom hf hodd R z
    (principalCoefficientContraction_symm C z symm) hz
  change (∑ p, ∫ x, L p x) + (∑ p, ∫ x, M p x) = _ at pairEq
  have hboth : Integrable (fun x => (∑ p, L p x) + ∑ p, M p x) := hl.add hm
  rw [split, integral_add hv hboth, integral_add hl hm,
    integral_finset_sum Finset.univ (fun p _ => leftTerm p),
    integral_finset_sum Finset.univ (fun p _ => rightTerm p), pairEq]
  ring

end Burnett.A02.FrequencySplit
