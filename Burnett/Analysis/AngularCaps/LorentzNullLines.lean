import Burnett.Analysis.AngularCaps.ProjectiveWedgeGeometry
import Burnett.Algebra.TensorFrame
import Burnett.Algebra.MinkowskiNull

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open scoped BigOperators
open Burnett.RicciSymbol

private theorem rowValue_add (m : Form) (x y : Vec) (j : Fin 4) :
    rowValue m (x+y) j = rowValue m x j+rowValue m y j := by
  simp only [rowValue, PiLp.add_apply, mul_add, Finset.sum_add_distrib]

private theorem rowValue_sub (m : Form) (x y : Vec) (j : Fin 4) :
    rowValue m (x-y) j = rowValue m x j-rowValue m y j := by
  simp only [rowValue, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem pairing_add_left (m : Form) (x y z : Vec) :
    pairing m (x+y) z = pairing m x z+pairing m y z := by
  simp only [pairing, rowValue_add, add_mul, Finset.sum_add_distrib]

theorem pairing_add_right (m : Form) (x y z : Vec) :
    pairing m x (y+z) = pairing m x y+pairing m x z := by
  simp only [pairing, PiLp.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairing_sub_left (m : Form) (x y z : Vec) :
    pairing m (x-y) z = pairing m x z-pairing m y z := by
  simp only [pairing, rowValue_sub, sub_mul, Finset.sum_sub_distrib]

theorem pairing_sub_right (m : Form) (x y z : Vec) :
    pairing m x (y-z) = pairing m x y-pairing m x z := by
  simp only [pairing, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem pairing_smul_left (m : Form) (t : ℝ) (x y : Vec) :
    pairing m (t • x) y = t*pairing m x y := by
  simp only [pairing, rowValue_smul, Finset.mul_sum, mul_assoc]

theorem pairing_smul_right (m : Form) (t : ℝ) (x y : Vec) :
    pairing m x (t • y) = t*pairing m x y := by
  simp only [pairing, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem pairing_neg_right (m : Form) (x y : Vec) : pairing m x (-y) = -pairing m x y := by
  simpa only [neg_one_smul, neg_one_mul] using pairing_smul_right m (-1) x y

theorem quadratic_neg (m : Form) (x : Vec) : quadratic m (-x) = quadratic m x := by
  simpa using quadratic_smul m (-1) x

theorem quadratic_add {m : Form} (hm : Symmetric m) (x y : Vec) :
    quadratic m (x+y) = quadratic m x+quadratic m y+2*pairing m x y := by
  simp only [quadratic, pairing_add_left, pairing_add_right, pairing_symm hm y x]
  ring

theorem quadratic_sub {m : Form} (hm : Symmetric m) (x y : Vec) :
    quadratic m (x-y) = quadratic m x+quadratic m y-2*pairing m x y := by
  simp only [quadratic, pairing_sub_left, pairing_sub_right, pairing_symm hm y x]
  ring

theorem pairing_sum_difference {m : Form} (hm : Symmetric m) (x y : Vec) :
    pairing m (x+y) (x-y) = quadratic m x-quadratic m y := by
  simp only [quadratic, pairing_add_left, pairing_sub_right, pairing_symm hm y x]
  ring

/-- On a Lorentz form the only null directions in the orthogonal space of
a nonzero null vector are in its own line. -/
def NullLinesUnique (m : Form) : Prop :=
  ∀ x y : Vec, x ≠ 0 → quadratic m x = 0 → quadratic m y = 0 →
    pairing m x y = 0 → ∃ a : ℝ, y = a • x

theorem lorentzFrame_symm {m : Form} (f : TensorFrame.LorentzFrame m) : Symmetric m := by
  intro i j
  rw [← f.inverseMetric_eq]
  unfold TensorFrame.inverseMetric
  exact Finset.sum_congr rfl fun _ _ => by ring

private theorem quadratic_eq_symbolNorm (m : Form) (x : Vec) :
    quadratic m x = symbolNorm m (fun i => x i) := by
  simp only [quadratic, pairing, rowValue, symbolNorm, Finset.sum_mul]
  exact Finset.sum_comm

private def frameVector {m : Form} (f : TensorFrame.LorentzFrame m) (x : Vec) : Covector :=
  TensorFrame.covector f.components (fun i => x i)

private theorem frameVector_ne_zero {m : Form} (f : TensorFrame.LorentzFrame m) {x : Vec}
    (hx : x ≠ 0) : frameVector f x ≠ 0 := by
  apply TensorFrame.covector_ne_zero _ f.isBasis.1
  intro h
  apply hx
  ext i
  exact congrFun h i

private theorem frame_quadratic {m : Form} (f : TensorFrame.LorentzFrame m) (x : Vec) :
    quadratic m x = symbolNorm NullScreen.minkowskiInverse (frameVector f x) := by
  conv_lhs => rw [quadratic_eq_symbolNorm, ← f.inverseMetric_eq, TensorFrame.symbolNorm_transform]
  rfl

private theorem frameVector_sub_smul {m : Form} (f : TensorFrame.LorentzFrame m)
    (y x : Vec) (a : ℝ) (j : Fin 4) :
    frameVector f (y-a • x) j = frameVector f y j-a*frameVector f x j := by
  simp only [frameVector, TensorFrame.covector, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem lorentzFrame_nullLinesUnique {m : Form} (f : TensorFrame.LorentzFrame m) :
    NullLinesUnique m := by
  intro x y hx hQx hQy hPair
  have htX := MinkowskiNull.temporal_component_ne_zero (frameVector f x)
    (frameVector_ne_zero f hx) ((frame_quadratic f x).symm.trans hQx)
  let a := frameVector f y 0 / frameVector f x 0
  let z := y-a • x
  have hQz : quadratic m z = 0 := by
    simp only [z, quadratic_sub (lorentzFrame_symm f), quadratic_smul, pairing_smul_right,
      pairing_symm (lorentzFrame_symm f) y x, hQx, hQy, hPair, mul_zero, zero_add, sub_zero]
  have htZ : frameVector f z 0 = 0 := by
    change frameVector f (y-a • x) 0 = 0
    rw [frameVector_sub_smul]
    dsimp only [a]
    rw [div_mul_cancel₀ _ htX, sub_self]
  refine ⟨a,sub_eq_zero.mp ?_⟩
  show z = 0
  by_contra hz
  exact (MinkowskiNull.temporal_component_ne_zero (frameVector f z)
    (frameVector_ne_zero f hz) ((frame_quadratic f z).symm.trans hQz)) htZ

end Burnett.Analysis.ProjectiveNullCaps
