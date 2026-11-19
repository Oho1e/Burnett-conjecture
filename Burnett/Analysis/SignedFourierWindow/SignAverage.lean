import Burnett.Analysis.DyadicSquare.SquareEnergy

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.DyadicSquare hiding Space
open Finset MeasureTheory
open scoped ENNReal

/-- The uniform average over all sign words of length n, exposing the first
coordinate. The same words will be used at every spatial point. -/
def signAverage : (n : ℕ) → ((Fin n → Bool) → ℝ) → ℝ
  | 0, F => F Fin.elim0
  | n+1, F => (signAverage n (fun s => F (Fin.cons false s)) +
      signAverage n (fun s => F (Fin.cons true s)))/2

theorem signAverage_mono {n : ℕ} {F G : (Fin n → Bool) → ℝ} (h : ∀ s, F s ≤ G s) :
    signAverage n F ≤ signAverage n G := by
  induction n with
  | zero => exact h _
  | succ n ih =>
    exact div_le_div_of_nonneg_right
      (add_le_add (ih (fun s => h (Fin.cons false s))) (ih (fun s => h (Fin.cons true s)))) (by norm_num)

theorem signAverage_const (n : ℕ) (c : ℝ) : signAverage n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [signAverage,ih]; ring

theorem signAverage_add (n : ℕ) (F G : (Fin n → Bool) → ℝ) :
    signAverage n (fun s => F s+G s) = signAverage n F + signAverage n G := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [signAverage]
    rw [ih (fun s => F (Fin.cons false s)) (fun s => G (Fin.cons false s)),
      ih (fun s => F (Fin.cons true s)) (fun s => G (Fin.cons true s))]
    ring

theorem signAverage_mul (n : ℕ) (c : ℝ) (F : (Fin n → Bool) → ℝ) :
    signAverage n (fun s => c*F s) = c*signAverage n F := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [signAverage,ih]
    ring

def signValue (b : Bool) : ℂ := if b then 1 else -1

def signedVector {n : ℕ} (v : Fin n → ℂ) (s : Fin n → Bool) : ℂ := ∑ j, signValue (s j)*v j

def vectorEnergy {n : ℕ} (v : Fin n → ℂ) : ℝ := ∑ j, ‖v j‖^2

theorem sign_moments {n : ℕ} (v : Fin n → ℂ) :
    signAverage n (fun s => ‖signedVector v s‖^2) = vectorEnergy v ∧
    signAverage n (fun s => ‖signedVector v s‖^4) ≤ 3*(vectorEnergy v)^2 := by
  have second (z w : ℂ) : (‖-z+w‖^2+‖z+w‖^2)/2 = ‖z‖^2+‖w‖^2 := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.neg_re,Complex.neg_im]
    ring
  have fourth (z w : ℂ) : (‖-z+w‖^4+‖z+w‖^4)/2 ≤
      ‖z‖^4 + 6*‖z‖^2*‖w‖^2 + ‖w‖^4 := by
    simp only [show ∀ x : ℝ, x^4=(x^2)^2 from fun x => by ring,Complex.sq_norm,Complex.normSq_apply,
      Complex.add_re,Complex.add_im,Complex.neg_re,Complex.neg_im]
    nlinarith only [sq_nonneg (z.re*w.im-z.im*w.re)]
  induction n with
  | zero => simp [signAverage,signedVector,vectorEnergy]
  | succ n ih =>
    let u := fun j : Fin n => v j.succ
    let z := v 0
    let w := signedVector u
    have plus (s : Fin n → Bool) : signedVector v (Fin.cons true s) = z+w s := by
      simp [signedVector,Fin.sum_univ_succ,signValue,z,w,u]
    have minus (s : Fin n → Bool) : signedVector v (Fin.cons false s) = -z+w s := by
      simp [signedVector,Fin.sum_univ_succ,signValue,z,w,u]
    have energy : vectorEnergy v = ‖z‖^2+vectorEnergy u := Fin.sum_univ_succ _
    have avg (F : ℂ → ℝ) : signAverage (n+1) (fun s => F (signedVector v s)) =
        signAverage n (fun s => (F (-z+w s)+F (z+w s))/2) := by
      simp only [signAverage,minus,plus,div_eq_inv_mul,signAverage_mul,signAverage_add]
    obtain ⟨h₂,h₄⟩ := ih u
    constructor
    · rw [avg (fun x => ‖x‖^2),energy]
      simp only [second,signAverage_add,signAverage_const,w,h₂]
    · rw [avg (fun x => ‖x‖^4),energy]
      have major := signAverage_mono (fun s => fourth z (w s))
      simp only [signAverage_add,signAverage_const,signAverage_mul,w,h₂] at major
      nlinarith [major,h₄,sq_nonneg (‖z‖^2)]

end Burnett.Analysis.SignedFourierWindow
