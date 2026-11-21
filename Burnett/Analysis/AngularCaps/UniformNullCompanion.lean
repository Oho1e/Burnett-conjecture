import Burnett.Analysis.AngularCaps.ThinConeRowBounds
import Burnett.Analysis.AngularCaps.ParabolicCapAlgebra

set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set Metric Finset
open scoped BigOperators

theorem continuous_pairing_family {X : Type*} [TopologicalSpace X] {m : X → Form} {u v : X → Vec}
    (hm : Continuous m) (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun x => pairing (m x) (u x) (v x)) := by
  unfold pairing rowValue
  apply continuous_finset_sum
  intro j _
  refine (continuous_finset_sum _ (fun i _ => ?_)).mul
    ((PiLp.continuous_apply 2 (fun _ : Index => ℝ) j).comp hv)
  have hi : Continuous fun x => m x i := (continuous_apply i).comp hm
  exact ((continuous_apply j).comp hi).mul ((PiLp.continuous_apply 2 (fun _ : Index => ℝ) i).comp hu)

theorem exists_uniform_pairing_norm_bound {K : Set Form} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ∈ K, ∀ x y : Vec, |pairing m x y| ≤ C*‖x‖*‖y‖ := by
  let S : Set (Form × Vec × Vec) := K ×ˢ (sphere (0:Vec) 1 ×ˢ sphere (0:Vec) 1)
  have hS : IsCompact S := hK.prod ((isCompact_sphere _ _).prod (isCompact_sphere _ _))
  have hCont : Continuous (fun z : Form × Vec × Vec => pairing z.1 z.2.1 z.2.2) :=
    continuous_pairing_family continuous_fst continuous_snd.fst continuous_snd.snd
  obtain ⟨C,hC,hBound⟩ := (hS.image hCont).isBounded.exists_pos_norm_le
  refine ⟨C,hC,?_⟩
  intro m hm x y
  by_cases hx : x = 0
  · simp [hx,pairing,rowValue]
  by_cases hy : y = 0
  · simp [hy,pairing]
  have hs (u : Vec) (hu : u ≠ 0) : ‖u‖ • unitRep u = u := by
    rw [unitRep,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu),one_smul]
  have hMem : (m,unitRep x,unitRep y) ∈ S :=
    ⟨hm,by simpa only [mem_sphere,dist_zero_right] using norm_unitRep x hx,
         by simpa only [mem_sphere,dist_zero_right] using norm_unitRep y hy⟩
  have hBound' : |pairing m (unitRep x) (unitRep y)| ≤ C := by
    rw [← Real.norm_eq_abs]
    exact hBound _ ⟨(m,unitRep x,unitRep y),hMem,rfl⟩
  have hp : pairing m x y = ‖x‖ * (‖y‖ * pairing m (unitRep x) (unitRep y)) := by
    calc
      _ = pairing m (‖x‖ • unitRep x) (‖y‖ • unitRep y) := by rw [hs x hx,hs y hy]
      _ = _ := by rw [pairing_smul_left,pairing_smul_right]
  rw [hp,abs_mul ‖x‖,abs_mul ‖y‖,abs_of_nonneg (norm_nonneg x),abs_of_nonneg (norm_nonneg y)]
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBound' (norm_nonneg y))
    (norm_nonneg x)).trans_eq (by ring)

def complementaryNullAxis (m : Form) (w n : Vec) : Prop :=
  quadratic m n = 0 ∧ pairing m w n = -1/2

/-- For each true unit null center, choose a complementary null axis with
`m(w,n) = -1/2`. The axis has one Euclidean upper norm bound over the compact
family, including the choice among transverse coordinate directions. -/
theorem exists_uniform_complementaryNullAxis {K : Set Form} (hK : IsCompact K)
    (hSym : ∀ m ∈ K, Symmetric m) (hND : ∀ m ∈ K, Nondegenerate m) :
    ∃ L : ℝ, 0 < L ∧ ∀ m ∈ K, ∀ w ∈ unitNull m,
      ∃ n : Vec, complementaryNullAxis m w n ∧ ‖n‖ ≤ L := by
  obtain ⟨a,ha,hA⟩ := exists_uniform_unit_rowLower hK hND
  obtain ⟨B,hB,hUpper⟩ := exists_uniform_unitAxis_quadratic_upper hK
  let A : ℝ := 1/(2*a)
  have hA0 : 0 < A := one_div_pos.mpr (mul_pos zero_lt_two ha)
  refine ⟨A+A^2*B,add_pos_of_pos_of_nonneg hA0 (mul_nonneg (sq_nonneg _) hB.le),?_⟩
  intro m hm w hw
  obtain ⟨j,hj⟩ := hA m hm w hw.1
  let b := rowValue m w j
  let r : ℝ := (-1)/(2*b)
  let v := r • unitAxis j
  let n := v+quadratic m v • w
  have hb : b ≠ 0 := abs_pos.mp (ha.trans_le hj)
  have hrb : r*b = -1/2 := by
    dsimp only [r]
    field_simp [hb]
  have hr : |r| ≤ A := by
    change |(-1:ℝ)/(2*b)| ≤ 1/(2*a)
    rw [abs_div,abs_neg,abs_one,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ 2 from zero_le_two)]
    exact one_div_le_one_div_of_le (mul_pos zero_lt_two ha)
      (mul_le_mul_of_nonneg_left hj zero_le_two)
  have hwv : pairing m w v = -1/2 := by
    change pairing m w (r • unitAxis j) = _
    rw [pairing_smul_right,pairing_unitAxis_right]
    exact hrb
  have hvw : pairing m v w = -1/2 := (pairing_symm (hSym m hm) v w).trans hwv
  have hww : pairing m w w = 0 := hw.2
  have hnQ : quadratic m n = 0 := by
    simp only [n,quadratic_add (hSym m hm),quadratic_smul,pairing_smul_right,hw.2,hvw,mul_zero,add_zero]
    ring
  have hPair : pairing m w n = -1/2 := by
    simp only [n,pairing_add_right,pairing_smul_right,hwv,hww,mul_zero,add_zero]
  have hVnorm : ‖v‖ = |r| := by
    change ‖r • unitAxis j‖ = _
    rw [norm_smul,Real.norm_eq_abs,norm_unitAxis,mul_one]
  have hQv : |quadratic m v| ≤ A^2*B := by
    change |quadratic m (r • unitAxis j)| ≤ _
    rw [quadratic_smul,abs_mul,abs_sq]
    have hR2 : r^2 ≤ A^2 := by
      rw [← sq_abs r]
      exact pow_le_pow_left₀ (abs_nonneg _) hr 2
    exact mul_le_mul hR2 (hUpper m hm j) (abs_nonneg _) (sq_nonneg A)
  refine ⟨n,⟨hnQ,hPair⟩,?_⟩
  calc
    _ ≤ ‖v‖ + ‖quadratic m v • w‖ := norm_add_le _ _
    _ = |r| + |quadratic m v| := by rw [hVnorm,norm_smul,Real.norm_eq_abs,hw.1,mul_one]
    _ ≤ _ := add_le_add hr hQv

end Burnett.Analysis.ProjectiveNullCaps
