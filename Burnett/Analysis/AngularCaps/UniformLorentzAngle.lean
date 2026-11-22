import Burnett.Analysis.AngularCaps.LorentzNullLines
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option maxHeartbeats 6500000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set Metric
open scoped BigOperators RealInnerProductSpace

private abbrev OrthoData := Form × Vec × Vec

private def orthogonalUnitPairs (K : Set Form) : Set OrthoData :=
  (K ×ˢ (sphere (0 : Vec) 1 ×ˢ sphere (0 : Vec) 1)) ∩ {z | ⟪z.2.1,z.2.2⟫ = 0}

private theorem continuous_data_pairing :
    Continuous fun z : OrthoData => pairing z.1 z.2.1 z.2.2 := by
  unfold pairing rowValue
  apply continuous_finset_sum
  intro j _
  apply Continuous.mul
  · apply continuous_finset_sum
    intro i _
    apply Continuous.mul
    · have hi : Continuous fun z : OrthoData => z.1 i := (continuous_apply i).comp continuous_fst
      exact (continuous_apply j).comp hi
    · exact (PiLp.continuous_apply 2 (fun _ : Index => ℝ) i).comp
        (continuous_fst.comp continuous_snd)
  · exact (PiLp.continuous_apply 2 (fun _ : Index => ℝ) j).comp
      (continuous_snd.comp continuous_snd)

private def absFormSize (z : OrthoData) : ℝ :=
  |quadratic z.1 z.2.1| + |pairing z.1 z.2.1 z.2.2| + |quadratic z.1 z.2.2|

private theorem continuous_absFormSize : Continuous absFormSize := by
  have hFirst : Continuous fun z : OrthoData => quadratic z.1 z.2.1 :=
    continuous_data_pairing.comp (continuous_fst.prodMk
      ((continuous_fst.comp continuous_snd).prodMk (continuous_fst.comp continuous_snd)))
  have hSecond : Continuous fun z : OrthoData => quadratic z.1 z.2.2 :=
    continuous_data_pairing.comp (continuous_fst.prodMk
      ((continuous_snd.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd)))
  exact (hFirst.abs.add continuous_data_pairing.abs).add hSecond.abs

private theorem orthogonalUnitPairs_compact {K : Set Form} (hK : IsCompact K) :
    IsCompact (orthogonalUnitPairs K) := by
  have hc : Continuous fun z : OrthoData => ⟪z.2.1,z.2.2⟫ :=
    continuous_inner.comp continuous_snd
  exact (hK.prod ((isCompact_sphere _ _).prod (isCompact_sphere _ _))).inter_right
    (isClosed_eq hc continuous_const)

private theorem orthogonalUnitPairs_absFormSize_pos {K : Set Form}
    (hUnique : ∀ m ∈ K, NullLinesUnique m) {z : OrthoData} (hz : z ∈ orthogonalUnitPairs K) :
    0 < absFormSize z := by
  obtain ⟨m,x,y⟩ := z
  have hm : m ∈ K := hz.1.1
  have hX : ‖x‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hz.1.2.1
  have hY : ‖y‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hz.1.2.2
  have hOrth : ⟪x,y⟫ = 0 := hz.2
  have hx : x ≠ 0 := by intro he; simp [he] at hX
  by_contra! hBad
  change |quadratic m x| + |pairing m x y| + |quadratic m y| ≤ 0 at hBad
  have hQX : quadratic m x = 0 := abs_nonpos_iff.mp (by
    linarith only [hBad,abs_nonneg (pairing m x y),abs_nonneg (quadratic m y)])
  have hPair : pairing m x y = 0 := abs_nonpos_iff.mp (by
    linarith only [hBad,abs_nonneg (quadratic m x),abs_nonneg (quadratic m y)])
  have hQY : quadratic m y = 0 := abs_nonpos_iff.mp (by
    linarith only [hBad,abs_nonneg (quadratic m x),abs_nonneg (pairing m x y)])
  obtain ⟨a,ha⟩ := hUnique m hm x y hx hQX hQY hPair
  rw [ha,real_inner_smul_right,real_inner_self_eq_norm_sq,hX,one_pow,mul_one] at hOrth
  have h0 : y = 0 := by simpa only [hOrth,zero_smul] using ha
  simp [h0] at hY

/-- On a fixed compact family, two Euclidean-orthogonal unit covectors cannot
simultaneously have both quadratic values and their mixed value approach zero. -/
theorem exists_uniform_orthogonal_absFormSize {K : Set Form} (hK : IsCompact K)
    (hUnique : ∀ m ∈ K, NullLinesUnique m) :
    ∃ a : ℝ, 0 < a ∧ ∀ m ∈ K, ∀ x y : Vec, ‖x‖ = 1 → ‖y‖ = 1 → ⟪x,y⟫ = 0 →
      a ≤ |quadratic m x|+|pairing m x y|+|quadratic m y| := by
  by_cases h : (orthogonalUnitPairs K).Nonempty
  · obtain ⟨z,hz,hMin⟩ := (orthogonalUnitPairs_compact hK).exists_isMinOn h
      continuous_absFormSize.continuousOn
    refine ⟨absFormSize z,orthogonalUnitPairs_absFormSize_pos hUnique hz,?_⟩
    intro m hm x y hx hy hOrth
    have hmem : (m,x,y) ∈ orthogonalUnitPairs K :=
      ⟨⟨hm,by simpa only [mem_sphere,dist_zero_right] using hx,
         by simpa only [mem_sphere,dist_zero_right] using hy⟩,hOrth⟩
    exact (isMinOn_iff.mp hMin) (m,x,y) hmem
  · refine ⟨1,zero_lt_one,?_⟩
    intro m hm x y hx hy hOrth
    have hmem : (m,x,y) ∈ orthogonalUnitPairs K :=
      ⟨⟨hm,by simpa only [mem_sphere,dist_zero_right] using hx,
         by simpa only [mem_sphere,dist_zero_right] using hy⟩,hOrth⟩
    exact (h ⟨(m,x,y),hmem⟩).elim

private theorem norm_smul_unitRep (x : Vec) (hx : x ≠ 0) : ‖x‖ • unitRep x = x := by
  rw [unitRep,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]

private theorem absQuadratic_cancel_unitRep (m : Form) (x : Vec) (hx : x ≠ 0) :
    ‖x‖^2*|quadratic m (unitRep x)| = |quadratic m x| := by
  conv_rhs => rw [← norm_smul_unitRep x hx,quadratic_smul,abs_mul,abs_of_nonneg (sq_nonneg ‖x‖)]

private theorem absPairing_cancel_unitRep (m : Form) (x y : Vec) (hx : x ≠ 0) (hy : y ≠ 0) :
    (‖x‖*‖y‖)*|pairing m (unitRep x) (unitRep y)| = |pairing m x y| := by
  calc
    _ = |‖x‖*(‖y‖*pairing m (unitRep x) (unitRep y))| := by
      rw [abs_mul ‖x‖,abs_mul ‖y‖,abs_of_nonneg (norm_nonneg x),abs_of_nonneg (norm_nonneg y)]
      ring
    _ = _ := by
      rw [← pairing_smul_right,← pairing_smul_left,norm_smul_unitRep x hx,norm_smul_unitRep y hy]

private theorem orthogonal_absFormSize_scaled {m : Form} {a : ℝ}
    (hBound : ∀ x y : Vec, ‖x‖ = 1 → ‖y‖ = 1 → ⟪x,y⟫ = 0 →
      a ≤ |quadratic m x|+|pairing m x y|+|quadratic m y|)
    (s d : Vec) (hOrth : ⟪s,d⟫ = 0) (hOrder : ‖d‖ ≤ ‖s‖) :
    a*‖d‖^2 ≤ |quadratic m s|+|pairing m s d|+|quadratic m d| := by
  by_cases hd : d = 0
  · have hZero : a*‖d‖^2 = 0 := by simp [hd]
    rw [hZero]
    positivity
  · have hdPos := norm_pos_iff.mpr hd
    have hs := norm_pos_iff.mp (hdPos.trans_le hOrder)
    have ho : ⟪unitRep s,unitRep d⟫ = 0 := by
      simp only [unitRep,real_inner_smul_left,real_inner_smul_right,hOrth,mul_zero]
    have hNorm := hBound (unitRep s) (unitRep d) (norm_unitRep s hs) (norm_unitRep d hd) ho
    have hScale := mul_le_mul_of_nonneg_right hNorm (sq_nonneg ‖d‖)
    have hSub := pow_le_pow_left₀ (norm_nonneg d) hOrder 2
    have hMix := mul_le_mul_of_nonneg_right hOrder (norm_nonneg d)
    have hTermS := mul_le_mul_of_nonneg_left hSub (abs_nonneg (quadratic m (unitRep s)))
    have hTermM := mul_le_mul_of_nonneg_left hMix (abs_nonneg (pairing m (unitRep s) (unitRep d)))
    have hS := absQuadratic_cancel_unitRep m s hs
    have hM := absPairing_cancel_unitRep m s d hs hd
    have hD := absQuadratic_cancel_unitRep m d hd
    nlinarith only [hScale,hTermS,hTermM,hS,hM,hD]

private theorem abs_two_mul (z : ℝ) : |2*z| = 2*|z| := by
  rw [abs_mul,abs_of_nonneg zero_le_two]

private theorem near_null_wedge_oriented {m : Form} (hm : Symmetric m) {a e : ℝ} (ha : 0 ≤ a)
    (hBound : ∀ x y : Vec, ‖x‖ = 1 → ‖y‖ = 1 → ⟪x,y⟫ = 0 →
      a ≤ |quadratic m x|+|pairing m x y|+|quadratic m y|)
    {x y : Vec} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hSign : 0 ≤ ⟪x,y⟫) (hQx : |quadratic m x| ≤ e) (hQy : |quadratic m y| ≤ e) :
    a*projectiveWedgeSq x y ≤ 6*(e+|pairing m x y|) := by
  have hOrth : ⟪x+y,x-y⟫ = 0 := by
    simp only [inner_add_left,inner_sub_right,real_inner_comm x y,real_inner_self_eq_norm_sq,hx,hy]
    ring
  have hOrder : ‖x-y‖ ≤ ‖x+y‖ := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
    rw [norm_add_sq_real,norm_sub_sq_real]
    linarith only [hSign])
  have hScale := orthogonal_absFormSize_scaled hBound (x+y) (x-y) hOrth hOrder
  rw [quadratic_add hm,quadratic_sub hm,pairing_sum_difference hm] at hScale
  have hPlus : |quadratic m x+quadratic m y+2*pairing m x y| ≤
      |quadratic m x|+|quadratic m y|+2*|pairing m x y| := by
    rw [← abs_two_mul]
    exact (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
  have hMinus : |quadratic m x+quadratic m y-2*pairing m x y| ≤
      |quadratic m x|+|quadratic m y|+2*|pairing m x y| := by
    rw [← abs_two_mul]
    have h : |quadratic m x+quadratic m y-2*pairing m x y| ≤
        |quadratic m x+quadratic m y|+|2*pairing m x y| := by
      simpa only [sub_eq_add_neg,abs_neg] using
        abs_add_le (quadratic m x+quadratic m y) (-(2*pairing m x y))
    exact h.trans (add_le_add_right (abs_add_le _ _) _)
  have hMix : |quadratic m x-quadratic m y| ≤ |quadratic m x|+|quadratic m y| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (quadratic m x) (-quadratic m y)
  have hAngle : projectiveWedgeSq x y ≤ ‖x-y‖^2 := by
    have h := (coordinateWedgeSq_compare_projectiveDist hx hy).2
    simpa only [projectiveWedgeSq,hx,hy,one_pow,mul_one,div_one,projectiveDist,min_eq_left hOrder] using h
  have hA := mul_le_mul_of_nonneg_left hAngle ha
  linarith only [hA,hScale,hPlus,hMinus,hMix,hQx,hQy,abs_nonneg (pairing m x y)]

private theorem near_null_wedge_unit {m : Form} (hm : Symmetric m) {a e : ℝ} (ha : 0 ≤ a)
    (hBound : ∀ x y : Vec, ‖x‖ = 1 → ‖y‖ = 1 → ⟪x,y⟫ = 0 →
      a ≤ |quadratic m x|+|pairing m x y|+|quadratic m y|)
    {x y : Vec} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hQx : |quadratic m x| ≤ e) (hQy : |quadratic m y| ≤ e) :
    a*projectiveWedgeSq x y ≤ 6*(e+|pairing m x y|) := by
  by_cases hSign : 0 ≤ ⟪x,y⟫
  · exact near_null_wedge_oriented hm ha hBound hx hy hSign hQx hQy
  · have hSign' : 0 ≤ ⟪x,-y⟫ := by
      rw [inner_neg_right]
      linarith only [lt_of_not_ge hSign]
    have h := near_null_wedge_oriented hm ha hBound hx (by simpa only [norm_neg] using hy)
      hSign' hQx (by simpa only [quadratic_neg] using hQy)
    simpa only [projectiveWedgeSq_neg_right,pairing_neg_right,abs_neg] using h

/-- Uniform quantitative control of the original projective angle by the
absolute Lorentz product on any two near-null sheets. -/
theorem exists_uniform_projectiveWedgeSq_le_nearNullPairing {K : Set Form} (hK : IsCompact K)
    (hFrame : ∀ m ∈ K, Nonempty (Burnett.RicciSymbol.TensorFrame.LorentzFrame m)) :
    ∃ A : ℝ, 0 < A ∧ ∀ m ∈ K, ∀ x y : Vec, x ≠ 0 → y ≠ 0 →
      ∀ e : ℝ, |quadratic m x| ≤ e*‖x‖^2 → |quadratic m y| ≤ e*‖y‖^2 →
      projectiveWedgeSq x y ≤ A*(e+|pairing m x y|/(‖x‖*‖y‖)) := by
  obtain ⟨a,ha,hB⟩ := exists_uniform_orthogonal_absFormSize hK
    (fun m hm => (hFrame m hm).elim lorentzFrame_nullLinesUnique)
  refine ⟨6/a,div_pos (by norm_num) ha,?_⟩
  intro m hm x y hx hy e hQx hQy
  have hs := (hFrame m hm).elim lorentzFrame_symm
  have hNormQ (u : Vec) (hu : u ≠ 0) (hQu : |quadratic m u| ≤ e*‖u‖^2) :
      |quadratic m (unitRep u)| ≤ e := by
    have he : 0 < ‖u‖^2 := pow_pos (norm_pos_iff.mpr hu) _
    apply (mul_le_mul_iff_right₀ he).mp
    rw [absQuadratic_cancel_unitRep m u hu,mul_comm (‖u‖^2) e]
    exact hQu
  have hWedge : projectiveWedgeSq (unitRep x) (unitRep y) = projectiveWedgeSq x y := by
    rw [projectiveWedgeSq_eq_unitRep hx hy,projectiveWedgeSq,norm_unitRep x hx,norm_unitRep y hy]
    norm_num
  have hPair : |pairing m (unitRep x) (unitRep y)| = |pairing m x y|/(‖x‖*‖y‖) := by
    have hpos := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)
    apply (eq_div_iff hpos.ne').2
    rw [mul_comm]
    exact absPairing_cancel_unitRep m x y hx hy
  have h := near_null_wedge_unit hs ha.le (hB m hm) (norm_unitRep x hx) (norm_unitRep y hy)
    (hNormQ x hx hQx) (hNormQ y hy hQy)
  rw [hWedge,hPair] at h
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ ha).mpr
  rwa [mul_comm]

end Burnett.Analysis.ProjectiveNullCaps
