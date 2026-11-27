import Burnett.Analysis.PrincipalEnergy.Freezing.RealSkewTest
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearIBP
import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianCommutator

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate ContDiff

theorem radianSkewAction_real_pairing (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (hodd : ∀ ξ, b (-ξ) = -b ξ) (f g : SchwartzMap E ℂ) (hg : ∀ x, conj (g x) = g x) :
    (∫ x, radianSkewAction b f x * g x) = -∫ x, f x * radianSkewAction b g x := by
  simpa only [hg, radianSkewAction_preserves_real b hodd g hg] using
    radianSkewAction_skew_adjoint b hb hom f g

private theorem skew_test_integrable (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (hodd : ∀ ξ, b (-ξ) = -b ξ) (f g : SchwartzMap E ℂ)
    (hg : ∀ x, conj (g x) = g x) : Integrable (fun x => f x * radianSkewAction b g x) := by
  have eq (x : E) : f x * radianSkewAction b g x =
      Complex.I * (f x * conj (radianAction b g x)) := by
    rw [← radianSkewAction_preserves_real b hodd g hg x]
    simp only [radianSkewAction, map_mul, map_neg, Complex.conj_I, neg_neg]
    ring
  rw [show (fun x => f x * radianSkewAction b g x) = _ from funext eq]
  exact (radian_order_one_test_integrable b hb hom f g).const_mul _

/-- The paired derivative slots in the freezing identity cancel into the
actual commutator after the common index exchange. -/
theorem symmetric_skew_placement_identity {I : Type} [Fintype I]
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (hodd : ∀ ξ, b (-ξ) = -b ξ)
    (R : I × I → SchwartzMap E ℂ) (U : I → SchwartzMap E ℂ)
    (hsymm : ∀ i j, R (i,j) = R (j,i))
    (hR : ∀ k x, conj (R k x) = R k x) (hU : ∀ i x, conj (U i x) = U i x) :
    2 * (∑ k : I × I, ∫ x, U k.1 x * R k x * radianSkewAction b (U k.2) x) =
      -(∑ k : I × I, ∫ x, U k.1 x * (-Complex.I * radianCommutator b (R k) (U k.2) x)) := by
  let W (k : I × I) := ∫ x, U k.1 x * R k x * radianSkewAction b (U k.2) x
  let P (k : I × I) := energyProduct (R k) (U k.2)
  have hP (k : I × I) : ∀ x, conj (P k x) = P k x := by
    intro x
    simp only [P, energyProduct_apply, map_mul, hR, hU]
  have flip (k : I × I) :
      (∫ x, U k.1 x * radianSkewAction b (P k) x) = -W k.swap := by
    rcases k with ⟨i,j⟩
    rw [show (fun x => U i x * radianSkewAction b (P (i,j)) x) =
      (fun x => radianSkewAction b (P (i,j)) x * U i x) from funext fun _ => mul_comm _ _]
    rw [radianSkewAction_real_pairing b hb hom hodd (P (i,j)) (U i) (hU i)]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    simp only [P, Prod.swap, energyProduct_apply, hsymm i j]
    ring
  have each (k : I × I) :
      (∫ x, U k.1 x * (-Complex.I * radianCommutator b (R k) (U k.2) x)) =
        -W k.swap - W k := by
    have hFirst := skew_test_integrable b hb hom hodd (U k.1) (P k) (hP k)
    have hSecond := skew_test_integrable b hb hom hodd (energyProduct (U k.1) (R k)) (U k.2) (hU k.2)
    have same (x : E) : U k.1 x * (-Complex.I * radianCommutator b (R k) (U k.2) x) =
        U k.1 x * radianSkewAction b (P k) x -
          energyProduct (U k.1) (R k) x * radianSkewAction b (U k.2) x := by
      change U k.1 x * (-Complex.I * (radianAction b (P k) x -
        R k x * radianAction b (U k.2) x)) =
        U k.1 x * (-Complex.I * radianAction b (P k) x) -
          energyProduct (U k.1) (R k) x * (-Complex.I * radianAction b (U k.2) x)
      rw [energyProduct_apply]
      ring
    simp_rw [same]
    rw [integral_sub hFirst hSecond, flip]
    rfl
  have reindex : (∑ k : I × I, W k.swap) = ∑ k, W k :=
    Fintype.sum_equiv (Equiv.prodComm I I) _ _ (fun _ => rfl)
  change 2 * (∑ k, W k) = _
  simp_rw [each, Finset.sum_sub_distrib, Finset.sum_neg_distrib, reindex]
  ring

theorem energyPartial_preserves_real (j : Index) (u : SchwartzMap E ℂ)
    (hu : ∀ x, conj (u x) = u x) (x : E) :
    conj (energyPartial j u x) = energyPartial j u x := by
  let C : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap
  have hC : C ∘ (u : E → ℂ) = (u : E → ℂ) := funext hu
  have hD : HasFDerivAt (C ∘ (u : E → ℂ)) (C.comp (fderiv ℝ u x)) x :=
    C.hasFDerivAt.comp x (u.differentiable x).hasFDerivAt
  rw [hC] at hD
  change C (fderiv ℝ u x (EuclideanSpace.single j 1)) =
    fderiv ℝ u x (EuclideanSpace.single j 1)
  exact congrArg (fun d : E →L[ℝ] ℂ => d (EuclideanSpace.single j 1)) hD.fderiv.symm

/-- Specialize the symmetric placement identity to the actual first
coordinate derivatives of a single real field. -/
theorem coordinate_skew_placement_identity {J : Type} [Fintype J]
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (hodd : ∀ ξ, b (-ξ) = -b ξ)
    (R : (Index × J) × (Index × J) → SchwartzMap E ℂ)
    (z : J → SchwartzMap E ℂ)
    (hsymm : ∀ i j, R (i,j) = R (j,i))
    (hR : ∀ k x, conj (R k x) = R k x) (hz : ∀ j x, conj (z j x) = z j x) :
    let U (i : Index × J) := energyPartial i.1 (z i.2)
    2 * (∑ k : (Index × J) × (Index × J),
      ∫ x, U k.1 x * R k x * radianSkewAction b (U k.2) x) =
      -(∑ k : (Index × J) × (Index × J),
        ∫ x, U k.1 x * (-Complex.I * radianCommutator b (R k) (U k.2) x)) :=
  symmetric_skew_placement_identity b hb hom hodd R
    (fun i => energyPartial i.1 (z i.2)) hsymm hR
    (fun i => energyPartial_preserves_real i.1 (z i.2) (hz i.2))

end Burnett.A02.FrequencySplit
