import Burnett.Analysis.CubicEnergy.AngularHarmonics.SpherePolynomialLaplacian
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

set_option autoImplicit false
set_option maxHeartbeats 3600000

noncomputable section

namespace Burnett.A06

open MvPolynomial

abbrev SphereHomogeneous (d : ℕ) :=
  ↥(homogeneousSubmodule (Fin 4) ℝ d)

abbrev SphereMonomialIndex (d : ℕ) := {s : Fin 4 →₀ ℕ // s.degree = d}

private def sphereMonomialIndexEquivSym (d : ℕ) : SphereMonomialIndex d ≃ Sym (Fin 4) d where
  toFun m := ⟨Finsupp.toMultiset m.val, (Finsupp.card_toMultiset _).trans m.property⟩
  invFun s := ⟨Multiset.toFinsupp s.val, (Multiset.toFinsupp_sum_eq s.val).trans s.property⟩
  left_inv m := Subtype.ext (Finsupp.toMultiset_toFinsupp m.val)
  right_inv s := Subtype.ext (Multiset.toFinsupp_toMultiset s.val)

instance sphereMonomialIndexFintype (d : ℕ) : Fintype (SphereMonomialIndex d) :=
  Fintype.ofEquiv (Sym (Fin 4) d) (sphereMonomialIndexEquivSym d).symm

/-- The ordinary coefficient basis restricted to monomials of total degree d. -/
def sphereHomogeneousMonomialBasis (d : ℕ) :
    Module.Basis (SphereMonomialIndex d) ℝ (SphereHomogeneous d) :=
  Finsupp.basisSingleOne.map
    ((LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported (Fin 4) ℝ d)).trans
      (Finsupp.supportedEquivFinsupp (R := ℝ) {s : Fin 4 →₀ ℕ | s.degree = d})).symm

theorem sphereHomogeneousMonomialBasis_apply (d : ℕ) (m : SphereMonomialIndex d) :
    (sphereHomogeneousMonomialBasis d m : SpherePolynomial) = monomial m.val 1 := by
  rw [sphereHomogeneousMonomialBasis, Module.Basis.map_apply, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply,
    Finsupp.coe_basisSingleOne]
  change ((Finsupp.supportedEquivFinsupp (R := ℝ)
      ({s | s.degree = d} : Set (Fin 4 →₀ ℕ))).symm (Finsupp.single m (1 : ℝ)) :
        (Fin 4 →₀ ℕ) →₀ ℝ) = Finsupp.single (m : Fin 4 →₀ ℕ) (1 : ℝ)
  exact Finsupp.supportedEquivFinsupp_symm_single (R := ℝ) (M := ℝ)
    ({s | s.degree = d} : Set (Fin 4 →₀ ℕ)) m (1 : ℝ)

instance sphereHomogeneousFiniteDimensional (d : ℕ) : FiniteDimensional ℝ (SphereHomogeneous d) :=
  FiniteDimensional.of_fintype_basis (sphereHomogeneousMonomialBasis d)

theorem sphereHomogeneous_finrank (d : ℕ) :
    Module.finrank ℝ (SphereHomogeneous d) = (d+3).choose 3 := by
  rw [Module.finrank_eq_card_basis (sphereHomogeneousMonomialBasis d),
    Fintype.card_congr (sphereMonomialIndexEquivSym d), Sym.card_sym_eq_choose, Fintype.card_fin]
  rw [show 4+d-1 = d+3 by omega]
  exact Nat.choose_symm_of_eq_add (n := d+3) (a := d) (b := 3) rfl

end Burnett.A06
