import Burnett.Analysis.AngularCaps.ThinConeRowBounds
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option maxHeartbeats 6500000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set

private theorem norm_unitRep_sub_self {z : Vec} (hz : z ≠ 0) :
    ‖unitRep z-z‖ = |1-‖z‖| := by
  have hVector : unitRep z-z = (‖z‖⁻¹-1) • z := by rw [unitRep,sub_smul,one_smul]
  calc
    _ = |‖z‖⁻¹-1| * ‖z‖ := by rw [hVector,norm_smul,Real.norm_eq_abs]
    _ = |(‖z‖⁻¹-1)*‖z‖| := by rw [abs_mul,abs_of_nonneg (norm_nonneg z)]
    _ = _ := by rw [sub_mul,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz),one_mul]

private theorem norm_sub_unitRep_le {x z : Vec} (hx : ‖x‖ = 1) (hz : z ≠ 0) :
    ‖x-unitRep z‖ ≤ 2*‖z-x‖ := by
  have hn := abs_norm_sub_norm_le x z
  rw [hx,norm_sub_rev x z] at hn
  calc
    _ ≤ ‖x-z‖+‖z-unitRep z‖ := by simpa only [dist_eq_norm] using dist_triangle x z (unitRep z)
    _ ≤ _ := by
      rw [norm_sub_rev x z,norm_sub_rev z (unitRep z),norm_unitRep_sub_self hz]
      linarith only [hn]

private theorem exists_unitNull_near_unit {m : Form} (hm : Symmetric m)
    {x : Vec} (hx : ‖x‖ = 1) {a B ε : ℝ} (ha : 0 < a) (hB : 0 < B)
    (hε₁ : ε ≤ a/2) (hε₂ : ε ≤ a^2/B) (hQ : |quadratic m x| ≤ ε)
    (j : Index) (hRow : a ≤ |rowValue m x j|) (hAxis : |quadratic m (unitAxis j)| ≤ B) :
    ∃ v ∈ unitNull m, ‖x-v‖ ≤ (2/a)*ε := by
  let q := quadratic m x
  let b := rowValue m x j
  let t := -q/b
  have hb : b ≠ 0 := abs_pos.mp (ha.trans_le hRow)
  have ht : |t| * |b| = |q| := by
    dsimp only [t]
    rw [abs_div,abs_neg,div_mul_cancel₀ _ (abs_pos.mpr hb).ne']
  have htNear : |t| * a ≤ ε :=
    (mul_le_mul_of_nonneg_left hRow (abs_nonneg t)).trans (ht.le.trans hQ)
  have htB : |t| * B ≤ a := by
    apply (mul_le_mul_iff_left₀ ha).mp
    calc
      _ = (|t| * a)*B := by ring
      _ ≤ ε*B := mul_le_mul_of_nonneg_right htNear hB.le
      _ ≤ a^2 := (le_div_iff₀ hB).mp hε₂
      _ = a*a := by ring
  have hErr : |t^2*quadratic m (unitAxis j)| ≤ |q| := by
    calc
      _ = |t| * (|t| * |quadratic m (unitAxis j)|) := by
        rw [abs_mul,abs_of_nonneg (sq_nonneg t),← sq_abs t]
        ring
      _ ≤ |t| * (|t| * B) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hAxis (abs_nonneg t)) (abs_nonneg t)
      _ ≤ |t| * a := mul_le_mul_of_nonneg_left htB (abs_nonneg t)
      _ ≤ |t| * |b| := mul_le_mul_of_nonneg_left hRow (abs_nonneg t)
      _ = _ := ht
  let f (s : ℝ) := quadratic m (x+(s*t) • unitAxis j)
  have hCont : Continuous f := (continuous_quadratic_fixed m).comp
    (continuous_const.add ((continuous_id.mul continuous_const).smul continuous_const))
  have hF0 : f 0 = q := by simp only [f,q,zero_mul,zero_smul,add_zero]
  have hF1 : f 1 = -q+t^2*quadratic m (unitAxis j) := by
    have htq : t*b = -q := div_mul_cancel₀ _ hb
    simp only [f,one_mul,quadratic_add hm,quadratic_smul,pairing_smul_right,pairing_unitAxis_right]
    change q+t^2*quadratic m (unitAxis j)+2*(t*b) = -q+t^2*quadratic m (unitAxis j)
    rw [htq]
    ring
  have hRoot : (0 : ℝ) ∈ f '' Icc 0 1 := by
    rcases le_total 0 q with h | h
    · apply intermediate_value_Icc' zero_le_one hCont.continuousOn
      constructor
      · have hf := (abs_le.mp hErr).2
        rw [abs_of_nonneg h] at hf
        rw [hF1]
        linarith only [hf]
      · rwa [hF0]
    · apply intermediate_value_Icc zero_le_one hCont.continuousOn
      constructor
      · rwa [hF0]
      · have hf := (abs_le.mp hErr).1
        rw [abs_of_nonpos h] at hf
        rw [hF1]
        linarith only [hf]
  obtain ⟨s,hs,h0⟩ := hRoot
  let z := x+(s*t) • unitAxis j
  have hzQuad : quadratic m z = 0 := h0
  have hzNear : ‖z-x‖ ≤ ε/a := by
    have hVector : z-x = (s*t) • unitAxis j := by dsimp only [z]; abel
    rw [hVector,norm_smul,Real.norm_eq_abs,norm_unitAxis,mul_one,abs_mul,abs_of_nonneg hs.1]
    have h := mul_le_mul_of_nonneg_right hs.2 (abs_nonneg t)
    exact (by simpa only [one_mul] using h : s * |t| ≤ |t|).trans ((le_div_iff₀ ha).mpr htNear)
  have hHalf : ε/a ≤ 1/2 := (div_le_iff₀ ha).mpr (by linarith only [hε₁])
  have hz : z ≠ 0 := by
    intro hz
    have h := hzNear.trans hHalf
    rw [hz,zero_sub,norm_neg,hx] at h
    norm_num at h
  refine ⟨unitRep z,unitRep_mem_unitNull (norm_pos_iff.mpr hz) hzQuad,?_⟩
  have h := norm_sub_unitRep_le hx hz
  calc
    _ ≤ 2*(ε/a) := h.trans (mul_le_mul_of_nonneg_left hzNear zero_le_two)
    _ = _ := by ring

/-- One fixed compact symmetric nondegenerate family admits signed quantitative
projection from its relative thin cone to the actual unit null cone. -/
theorem exists_uniform_unitNull_projection {K : Set Form} (hK : IsCompact K)
    (hSym : ∀ m ∈ K, Symmetric m) (hND : ∀ m ∈ K, Nondegenerate m) :
    ∃ A ε₀ : ℝ, 0 < A ∧ 0 < ε₀ ∧ ∀ m ∈ K, ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
      ∀ ξ : Vec, ξ ≠ 0 → |quadratic m ξ| ≤ ε*‖ξ‖^2 →
        ∃ v ∈ unitNull m, ‖unitRep ξ-v‖ ≤ A*ε := by
  obtain ⟨a,ha,hLower⟩ := exists_uniform_unit_rowLower hK hND
  obtain ⟨B,hB,hUpper⟩ := exists_uniform_unitAxis_quadratic_upper hK
  refine ⟨2/a,min (a/2) (a^2/B),div_pos zero_lt_two ha,
    lt_min (div_pos ha zero_lt_two) (div_pos (pow_pos ha _) hB),?_⟩
  intro m hm ε _ hε ξ hξ hQuad
  let x := unitRep ξ
  have hx : ‖x‖ = 1 := norm_unitRep ξ hξ
  have hxscale : ‖ξ‖ • x = ξ := by
    change ‖ξ‖ • unitRep ξ = ξ
    rw [unitRep,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hξ),one_smul]
  have hScale : |quadratic m ξ| = ‖ξ‖^2 * |quadratic m x| := by
    calc
      _ = |quadratic m (‖ξ‖ • x)| := by rw [hxscale]
      _ = _ := by rw [quadratic_smul,abs_mul,abs_of_nonneg (sq_nonneg ‖ξ‖)]
  have hQx : |quadratic m x| ≤ ε := by
    apply (mul_le_mul_iff_right₀ (pow_pos (norm_pos_iff.mpr hξ) 2)).mp
    rw [← hScale,mul_comm (‖ξ‖^2) ε]
    exact hQuad
  obtain ⟨j,hj⟩ := hLower m hm x hx
  exact exists_unitNull_near_unit (hSym m hm) hx ha hB (hε.trans (min_le_left _ _))
    (hε.trans (min_le_right _ _)) hQx j (hj) (hUpper m hm j)

end Burnett.Analysis.ProjectiveNullCaps
