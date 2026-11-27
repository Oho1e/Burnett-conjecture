import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedSpatialSkew

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate ContDiff

/-- The two symmetric derivative placements combine into the coefficient
commutator for a scalar test with finite L² action and a real skew pairing. -/
theorem symmetric_skew_action_placement {I : Type} [Fintype I]
    (Q : SchwartzMap E ℂ → E → ℂ) (hQ : ∀ v, MemLp (Q v) 2 volume)
    (skew : ∀ (u v : SchwartzMap E ℂ), (∀ x, conj (v x) = v x) →
      (∫ x, Q u x * v x) = -∫ x, u x * Q v x)
    (R : I × I → SchwartzMap E ℂ) (U : I → SchwartzMap E ℂ)
    (symm : ∀ i j, R (i,j) = R (j,i)) (realU : ∀ i x, conj (U i x) = U i x) :
    2 * (∑ k : I × I, ∫ x, U k.1 x * R k x * Q (U k.2) x) =
      -(∑ k : I × I, ∫ x, U k.1 x * (Q (energyProduct (R k) (U k.2)) x -
        R k x * Q (U k.2) x)) := by
  let W (k : I × I) := ∫ x, U k.1 x * R k x * Q (U k.2) x
  let P (k : I × I) := energyProduct (R k) (U k.2)
  have flip (k : I × I) : (∫ x, U k.1 x * Q (P k) x) = -W k.swap := by
    rcases k with ⟨i,j⟩
    rw [show (fun x => U i x * Q (P (i,j)) x) =
      (fun x => Q (P (i,j)) x * U i x) from funext fun _ => mul_comm _ _,
      skew (P (i,j)) (U i) (realU i)]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    simp only [P, Prod.swap, energyProduct_apply, symm i j]
    ring
  have each (k : I × I) :
      (∫ x, U k.1 x * (Q (P k) x - R k x * Q (U k.2) x)) = -W k.swap - W k := by
    have left : Integrable (fun x => U k.1 x * Q (P k) x) :=
      ((U k.1).memLp 2 volume).integrable_mul (hQ (P k))
    have right : Integrable (fun x => energyProduct (U k.1) (R k) x * Q (U k.2) x) :=
      ((energyProduct (U k.1) (R k)).memLp 2 volume).integrable_mul (hQ (U k.2))
    have eq (x : E) : U k.1 x * (Q (P k) x - R k x * Q (U k.2) x) =
        U k.1 x * Q (P k) x - energyProduct (U k.1) (R k) x * Q (U k.2) x := by
      rw [energyProduct_apply]
      ring
    simp_rw [eq]
    rw [integral_sub left right, flip]
    rfl
  have reindex : (∑ k : I × I, W k.swap) = ∑ k, W k :=
    Fintype.sum_equiv (Equiv.prodComm I I) _ _ (fun _ => rfl)
  change 2 * (∑ k, W k) = -(∑ k, ∫ x, U k.1 x * (Q (P k) x - R k x * Q (U k.2) x))
  simp_rw [each, Finset.sum_sub_distrib, Finset.sum_neg_distrib, reindex]
  ring

/-- The actual separated Fourier test satisfies the skew placement identity
on the first coordinate derivatives of the same real field. -/
theorem coordinate_separated_skew_placement {J : Type} [Fintype J]
    (f : SchwartzMap E ℂ) (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (hf : ∀ x, conj (f x) = f x) (hodd : ∀ ξ, b (-ξ) = -b ξ)
    (R : (Index × J) × (Index × J) → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (symm : ∀ i j, R (i,j) = R (j,i)) (hz : ∀ j x, conj (z j x) = z j x) :
    let U (i : Index × J) := energyPartial i.1 (z i.2)
    2 * (∑ k : (Index × J) × (Index × J),
      ∫ x, U k.1 x * R k x * separatedSkewAction f b (U k.2) x) =
      -(∑ k : (Index × J) × (Index × J),
        ∫ x, U k.1 x * separatedSkewCommutator f b (R k) (U k.2) x) :=
  symmetric_skew_action_placement (separatedSkewAction f b)
    (separatedSkewAction_memLp_two f b hb hom) (separatedSkewAction_real_pairing f b hb hom hf hodd)
    R (fun i => energyPartial i.1 (z i.2)) symm
    (fun i => energyPartial_preserves_real i.1 (z i.2) (hz i.2))

end Burnett.A02.FrequencySplit
