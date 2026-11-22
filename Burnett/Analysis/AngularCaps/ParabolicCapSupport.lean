import Burnett.Analysis.AngularCaps.ParabolicCapAlgebra

set_option autoImplicit false
set_option maxHeartbeats 9500000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

private theorem vector_eq_norm_smul_unitRep {x : Vec} (hx : x ≠ 0) :
    ‖x‖ • unitRep x = x := by
  rw [unitRep,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]

private theorem choose_close_signed_center {x w : Vec} (hx : x ≠ 0) (hw : ‖w‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) (h : projectiveWedgeSq x w ≤ r^2) :
    ∃ a : ℝ, |a| = 1 ∧ ‖unitRep x-a • w‖ ≤ 2*r := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have hRep : unitRep w = w := by simp [unitRep,hw]
  have hClose := projectiveDist_unitRep_le_of_wedgeSq_le hx hw0 hr h
  rw [hRep] at hClose
  rcases min_le_iff.mp hClose with hPos | hNeg
  · exact ⟨1,abs_one,by simpa only [one_smul] using hPos⟩
  · exact ⟨-1,by norm_num,by simpa only [neg_one_smul,sub_neg_eq_add] using hNeg⟩

private theorem unit_coordinate_screen_bound {m : Form} {w x : Vec} (F : NullCapChart m w)
    {B r : ℝ} (hB : ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B) (hr : 0 ≤ r)
    (hSmall : 4*B*r ≤ 1) (hw : ‖w‖ = 1) (hx : x ≠ 0) (hW : projectiveWedgeSq x w ≤ r^2) :
    1/2 ≤ |(F.toFrequency.symm (unitRep x)).1| ∧
      ‖(F.toFrequency.symm (unitRep x)).2.2‖ ≤ 2*B*r := by
  obtain ⟨a,ha,hSigned⟩ := choose_close_signed_center hx hw hr hW
  let u := F.toFrequency.symm (unitRep x)
  have hAxis : F.toFrequency.symm w = nullAxis :=
    (congrArg F.toFrequency.symm F.center_eq.symm).trans (F.toFrequency.symm_apply_apply nullAxis)
  have hDiff : F.toFrequency.symm (unitRep x-a • w) = u-a • nullAxis := by
    rw [map_sub,map_smul,hAxis]
  have hNear : ‖u-a • nullAxis‖ ≤ 2*B*r := by
    have hn := F.toFrequency.symm.toContinuousLinearMap.le_opNorm (unitRep x-a • w)
    rw [show F.toFrequency.symm.toContinuousLinearMap (unitRep x-a • w) =
      F.toFrequency.symm (unitRep x-a • w) from rfl,hDiff] at hn
    calc
      _ ≤ ‖F.toFrequency.symm.toContinuousLinearMap‖ * ‖unitRep x-a • w‖ := hn
      _ ≤ B*(2*r) := mul_le_mul hB hSigned (norm_nonneg _) ((norm_nonneg _).trans hB)
      _ = _ := by ring
  have hFirst : |u.1-a| ≤ 2*B*r := by
    calc
      _ = ‖(u-a • nullAxis).1‖ := by simp [nullAxis,Real.norm_eq_abs]
      _ ≤ ‖u-a • nullAxis‖ := norm_fst_le _
      _ ≤ _ := hNear
  have hLower : 1 ≤ |u.1-a|+|u.1| := by
    simpa only [sub_zero,ha,abs_sub_comm a u.1] using abs_sub_le a u.1 0
  refine ⟨by linarith only [hFirst,hLower,hSmall],?_⟩
  calc
    _ = ‖(u-a • nullAxis).2.2‖ := by simp [u,nullAxis]
    _ ≤ ‖(u-a • nullAxis).2‖ := norm_snd_le _
    _ ≤ ‖u-a • nullAxis‖ := norm_snd_le _
    _ ≤ _ := hNear

/-- On a nonzero thin angular cap, the radial coordinate stays comparable to
the original Euclidean norm. The screen and conjugate null coordinates have
their actual first and second parabolic scales. -/
theorem parabolic_cap_coordinate_bounds {m : Form} {w x : Vec} (F : NullCapChart m w)
    {B R δ ε : ℝ} (hB : ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B)
    (hR : 0 ≤ R) (hδ : 0 < δ) (hε : 0 ≤ ε) (hSmall : 4*B*(R*δ) ≤ 1)
    (hw : ‖w‖ = 1) (hx : x ≠ 0)
    (hW : projectiveWedgeSq x w ≤ (R*δ)^2)
    (hCone : |quadratic m x| ≤ ε*δ^2*‖x‖^2) :
    let u := F.toFrequency.symm x
    ‖x‖ ≤ 2*|u.1| ∧ |u.1| ≤ B*‖x‖ ∧
      ‖u.2.2‖ ≤ (4*B*R)*δ*|u.1| ∧
      |u.2.1| ≤ ((4*B*R)^2+4*ε)*δ^2*|u.1| := by
  let u := F.toFrequency.symm x
  let v := F.toFrequency.symm (unitRep x)
  have ⟨hvS,hvZ⟩ := unit_coordinate_screen_bound F hB (mul_nonneg hR hδ.le) hSmall hw hx hW
  have hScale : u = ‖x‖ • v := by
    have h := congrArg F.toFrequency.symm (vector_eq_norm_smul_unitRep hx)
    simpa only [u,v,map_smul] using h.symm
  have hScaleS : |u.1| = ‖x‖ * |v.1| := by
    rw [hScale]
    simp [abs_mul,abs_of_nonneg (norm_nonneg x)]
  have hScaleZ : ‖u.2.2‖ = ‖x‖ * ‖v.2.2‖ := by
    rw [hScale]
    simp [norm_smul]
  have hRadial : ‖x‖ ≤ 2*|u.1| := by
    rw [hScaleS]
    have h := mul_le_mul_of_nonneg_left hvS (norm_nonneg x)
    linarith only [h]
  have hRadial' : |u.1| ≤ B*‖x‖ := by
    calc
      _ = ‖u.1‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖u‖ := norm_fst_le _
      _ ≤ _ := (F.toFrequency.symm.toContinuousLinearMap.le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hB (norm_nonneg x))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hZ : ‖u.2.2‖ ≤ (4*B*R)*δ*|u.1| := by
    calc
      _ = ‖x‖ * ‖v.2.2‖ := hScaleZ
      _ ≤ ‖x‖ * (2*B*(R*δ)) := mul_le_mul_of_nonneg_left hvZ (norm_nonneg x)
      _ ≤ (2*|u.1|)*(2*B*(R*δ)) := mul_le_mul_of_nonneg_right hRadial
        (mul_nonneg (mul_nonneg zero_le_two hB0) (mul_nonneg hR hδ.le))
      _ = _ := by ring
  have hQuad : quadratic m x = -(u.1*u.2.1)+‖u.2.2‖^2 := by
    have h := F.quadratic_eq u
    rwa [show F.toFrequency u = x from F.toFrequency.apply_symm_apply x] at h
  have hCone' : |quadratic m x| ≤ ε*δ^2*(2*|u.1|)^2 :=
    hCone.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg x) hRadial 2)
      (mul_nonneg hε (sq_nonneg δ)))
  have hProd : |u.1| * |u.2.1| ≤ ‖u.2.2‖^2 + |quadratic m x| := by
    have hEq : u.1*u.2.1 = ‖u.2.2‖^2-quadratic m x := by linarith only [hQuad]
    rw [← abs_mul,hEq]
    have hb : |‖u.2.2‖ ^ (2 : ℕ)| = ‖u.2.2‖ ^ (2 : ℕ) :=
      abs_of_nonneg (pow_nonneg (norm_nonneg _) 2)
    have h := abs_add_le (‖u.2.2‖ ^ (2 : ℕ)) (-quadratic m x)
    rw [hb,abs_neg] at h
    simpa only [sub_eq_add_neg] using h
  have hs : 0 < |u.1| := by linarith only [hRadial,norm_pos_iff.mpr hx]
  have hT : |u.2.1| ≤ ((4*B*R)^2+4*ε)*δ^2*|u.1| := by
    apply (mul_le_mul_iff_right₀ hs).mp
    calc
      _ ≤ ‖u.2.2‖^2 + |quadratic m x| := hProd
      _ ≤ ((4*B*R)*δ*|u.1|)^2 + ε*δ^2*(2*|u.1|)^2 :=
        add_le_add (pow_le_pow_left₀ (norm_nonneg _) hZ 2) hCone'
      _ = _ := by ring
  exact ⟨hRadial,hRadial',hZ,hT⟩

def parabolicRescale (δ : ℝ) (u : NullFrequencyCoordinates) : NullFrequencyCoordinates :=
  (u.1,u.2.1/δ^2,δ⁻¹ • u.2.2)

theorem parabolicDilation_rescale {δ : ℝ} (hδ : δ ≠ 0) (u : NullFrequencyCoordinates) :
    parabolicDilation δ (parabolicRescale δ u) = u := by
  rcases u with ⟨s,t,z⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · simp only [parabolicDilation,parabolicRescale]
      rw [mul_comm,div_mul_cancel₀ _ (pow_ne_zero _ hδ)]
    · simp [parabolicDilation,parabolicRescale,smul_smul,hδ]

/-- This expresses the whole closed angular and thin-cone support in the
fixed-shape coordinates used by the normalized derivative estimate. -/
theorem scaled_cap_coordinate_bounds {m : Form} {w x : Vec} (F : NullCapChart m w)
    {B R δ ε : ℝ} (hB : ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B)
    (hR : 0 ≤ R) (hδ : 0 < δ) (hε : 0 ≤ ε) (hSmall : 4*B*(R*δ) ≤ 1)
    (hw : ‖w‖ = 1) (hx : x ≠ 0)
    (hW : projectiveWedgeSq x w ≤ (R*δ)^2)
    (hCone : |quadratic m x| ≤ ε*δ^2*‖x‖^2) :
    let u := parabolicRescale δ (F.toFrequency.symm x)
    ‖x‖ ≤ 2*|u.1| ∧ |u.1| ≤ B*‖x‖ ∧
      ‖u.2.2‖ ≤ (4*B*R)*|u.1| ∧
      |u.2.1| ≤ ((4*B*R)^2+4*ε)*|u.1| := by
  let a := F.toFrequency.symm x
  have ⟨hS,hS',hZ,hT⟩ := parabolic_cap_coordinate_bounds F hB hR hδ hε hSmall hw hx hW hCone
  change ‖x‖ ≤ 2*|a.1| ∧ |a.1| ≤ B*‖x‖ ∧
    ‖δ⁻¹ • a.2.2‖ ≤ (4*B*R)*|a.1| ∧
    |a.2.1/δ^2| ≤ ((4*B*R)^2+4*ε)*|a.1|
  refine ⟨hS,hS',?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hδ.le),inv_mul_eq_div]
    apply (div_le_iff₀ hδ).mpr
    refine hZ.trans_eq ?_
    ring
  · rw [abs_div,abs_of_nonneg (sq_nonneg δ)]
    apply (div_le_iff₀ (pow_pos hδ 2)).mpr
    refine hT.trans_eq ?_
    ring

end Burnett.Analysis.ProjectiveNullCaps
