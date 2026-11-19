import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring

/-!
# Four-test polarization for ordered matrix entries

An ordered complex matrix entry is recovered from four quadratic
tests with the conjugate in the first slot.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.MatrixPolarization

variable {ι : Type*} [Fintype ι]

def form (A : Matrix ι ι ℂ) (u v : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, star (u i) * v j * A i j

def quadratic (A : Matrix ι ι ℂ) (v : ι → ℂ) : ℂ := form A v v

private theorem quadratic_add_smul (A : Matrix ι ι ℂ) (u v : ι → ℂ) (c : ℂ) :
    quadratic A (u + c • v) =
      quadratic A u + c * form A u v + star c * form A v u +
        (star c * c) * quadratic A v := by
  have h (i j : ι) :
      star ((u + c • v) i) * (u + c • v) j * A i j =
        star (u i) * u j * A i j + c * (star (u i) * v j * A i j) +
          star c * (star (v i) * u j * A i j) +
            (star c * c) * (star (v i) * v j * A i j) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add, star_mul]
    ring
  simp only [quadratic, form, h, Finset.sum_add_distrib, Finset.mul_sum]

/-- Four quadratic tests recover each bilinear coefficient with the
complex-conjugate-first convention, without a Hermitian premise. -/
theorem form_eq_quadratic_polarization (A : Matrix ι ι ℂ) (u v : ι → ℂ) :
    form A u v =
      (quadratic A (u + (1 : ℂ) • v) - quadratic A (u + (-1 : ℂ) • v) -
        Complex.I * (quadratic A (u + Complex.I • v) - quadratic A (u + (-Complex.I) • v))) / 4 := by
  simp only [quadratic_add_smul, star_one, star_neg, Complex.star_def, Complex.conj_I]
  have hi : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [show (-Complex.I) * Complex.I = 1 by rw [neg_mul, hi, neg_neg],
    show (-(-Complex.I)) * (-Complex.I) = 1 by rw [neg_neg, mul_neg, hi, neg_neg]]
  have hcross : Complex.I *
        (quadratic A u + Complex.I * form A u v + -Complex.I * form A v u +
            1 * quadratic A v -
          (quadratic A u + -Complex.I * form A u v + - -Complex.I * form A v u +
            1 * quadratic A v)) =
      -2 * form A u v + 2 * form A v u := by
    calc
      _ = (Complex.I * Complex.I) * (2 * form A u v - 2 * form A v u) := by ring
      _ = _ := by rw [hi]; ring
  rw [hcross]
  ring

theorem form_single_single [DecidableEq ι] (A : Matrix ι ι ℂ) (i j : ι) :
    form A (Pi.single i 1) (Pi.single j 1) = A i j := by
  simp only [form, Pi.single_apply, apply_ite, star_one, star_zero, ite_mul,
    one_mul, zero_mul, mul_one, mul_zero]
  simp

end Burnett.Microlocal.MatrixPolarization
