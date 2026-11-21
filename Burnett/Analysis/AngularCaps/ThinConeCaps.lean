import Burnett.Analysis.AngularCaps.ThinConeProjection
import Burnett.Analysis.AngularCaps.ProjectiveWedgeCaps

set_option autoImplicit false
set_option maxHeartbeats 6500000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set Finset

private theorem normalized_center {w : Vec} (hw : ‖w‖ = 1) : w ≠ 0 ∧ unitRep w = w := by
  constructor
  · intro h
    simp [h] at hw
  · simp [unitRep,hw]

/-- The same signed cap centers cover all relative widths up to the outer cone
width, with an angular margin and overlap bounds independent of frequency.
In particular, any designated inner cone band uses the same centers. -/
theorem exists_uniform_thinCone_wedge_caps {K : Set Form} (hK : IsCompact K)
    (hSym : ∀ m ∈ K, Symmetric m) (hND : ∀ m ∈ K, Nondegenerate m)
    (Cout : ℝ) (hOut : 0 ≤ Cout) :
    ∃ D c₀ : ℝ, 0 < D ∧ 0 < c₀ ∧ ∀ m ∈ K, ∀ κ : ℝ, 0 < κ → κ < 1/16 →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∃ t : Finset Vec, (↑t : Set Vec) ⊆ unitNull m ∧ (t.card : ℝ) ≤ D/δ^2 ∧
        (↑t : Set Vec).Pairwise (fun x y => δ/4 < projectiveDist x y) ∧
        (∀ ε : ℝ, 0 ≤ ε → ε ≤ Cout*(c*κ*δ^2) →
          ∀ ξ : Vec, ξ ≠ 0 → |quadratic m ξ| ≤ ε*‖ξ‖^2 →
          ∃ w ∈ t,
            (‖unitRep ξ-w‖ < 3*δ/4 ∨ ‖unitRep ξ+w‖ < 3*δ/4) ∧
              projectiveWedgeSq ξ w < (3*δ/4)^2) ∧
        ∀ R : ℝ, 0 ≤ R → ∀ ξ : Vec, ξ ≠ 0 →
          ((wedgeCentersMeeting t ξ (R*δ)).card : ℝ) ≤ (16*R+1)^4 := by
  obtain ⟨A,ε₀,hA,hε₀,hProject⟩ := exists_uniform_unitNull_projection hK hSym hND
  obtain ⟨C,hC,hFamily⟩ := exists_uniform_projective_null_caps hK hSym hND
  let eMax := min ε₀ (1/(4*A))
  let c₀ := eMax/(1+Cout)
  have hOneC : 0 < 1+Cout := by linarith only [hOut]
  have hMax : 0 < eMax := lt_min hε₀ (one_div_pos.mpr (mul_pos (by norm_num) hA))
  refine ⟨4*C,c₀,mul_pos (by norm_num) hC,div_pos hMax hOneC,?_⟩
  intro m hm κ hκ hκsmall δ hδ hδone c hc hcUpper
  have hδh : 0 < δ/2 := div_pos hδ zero_lt_two
  obtain ⟨t,ht,hCard,hCover,hSep,hOverlap⟩ := hFamily m hm (δ/2) hδh (by linarith only [hδone])
  have hCard' : (t.card : ℝ) ≤ 4*C/δ^2 := hCard.trans_eq (by
    field_simp [hδ.ne']
    ring)
  have hSep' : (↑t : Set Vec).Pairwise (fun x y => δ/4 < projectiveDist x y) := by
    intro x hx y hy hxy
    linarith only [hSep hx hy hxy]
  refine ⟨t,ht,hCard',hSep',?_,?_⟩
  · intro ε hε hεOuter ξ hξ hQuad
    have hCoeff : Cout*c*κ ≤ eMax := by
      calc
        _ ≤ Cout*c*1 := mul_le_mul_of_nonneg_left (by linarith only [hκsmall]) (mul_nonneg hOut hc.le)
        _ ≤ (1+Cout)*c := by linarith only [hc]
        _ ≤ (1+Cout)*c₀ := mul_le_mul_of_nonneg_left hcUpper hOneC.le
        _ = eMax := by
          rw [mul_comm]
          exact div_mul_cancel₀ _ hOneC.ne'
    have hThick : ε ≤ eMax*δ^2 := hεOuter.trans (by
      rw [show Cout*(c*κ*δ^2) = (Cout*c*κ)*δ^2 by ring]
      exact mul_le_mul_of_nonneg_right hCoeff (sq_nonneg _))
    have hDeltaSq : δ^2 ≤ δ := by
      rw [pow_two]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hδone hδ.le
    have hThin : ε ≤ ε₀ := hThick.trans
      ((mul_le_of_le_one_right hMax.le (hDeltaSq.trans hδone)).trans (min_le_left _ _))
    have hAε : A*ε ≤ δ/4 := by
      have hAFour : A*eMax ≤ 1/4 :=
        (mul_le_mul_of_nonneg_left (min_le_right ε₀ (1/(4*A))) hA.le).trans_eq (by
          field_simp [hA.ne'])
      calc
        _ ≤ A*(eMax*δ^2) := mul_le_mul_of_nonneg_left hThick hA.le
        _ = (A*eMax)*δ^2 := by ring
        _ ≤ (1/4)*δ^2 := mul_le_mul_of_nonneg_right hAFour (sq_nonneg _)
        _ ≤ (1/4)*δ := mul_le_mul_of_nonneg_left hDeltaSq (by norm_num)
        _ = _ := by ring
    obtain ⟨v,hv,hV⟩ := hProject m hm ε hε hThin ξ hξ hQuad
    obtain ⟨w,hw,hW⟩ := hCover v hv
    have hXV : projectiveDist (unitRep ξ) v ≤ A*ε :=
      (min_le_left _ _).trans hV
    have hClose : projectiveDist (unitRep ξ) w < 3*δ/4 :=
      (projectiveDist_triangle (unitRep ξ) v w).trans_lt (by linarith only [hXV,hW,hAε])
    have hOpen : ‖unitRep ξ-w‖ < 3*δ/4 ∨ ‖unitRep ξ+w‖ < 3*δ/4 :=
      min_lt_iff.mp hClose
    have ⟨hw0,hwu⟩ := normalized_center (ht hw).1
    have hUpper := (projectiveWedgeSq_compare_unitRep_dist hξ hw0).2
    rw [hwu] at hUpper
    refine ⟨w,hw,hOpen,hUpper.trans_lt ?_⟩
    exact (sq_lt_sq₀ (projectiveDist_nonneg _ _) (by positivity)).mpr hClose
  · intro R hR ξ hξ
    have hIncl : wedgeCentersMeeting t ξ (R*δ) ⊆ centersMeeting t (unitRep ξ) ((4*R)*(δ/2)) := by
      classical
      intro w hw
      simp only [wedgeCentersMeeting,Finset.mem_filter] at hw
      simp only [centersMeeting,Finset.mem_filter]
      obtain ⟨hw0,hwu⟩ := normalized_center (ht hw.1).1
      have h := projectiveDist_unitRep_le_of_wedgeSq_le hξ hw0 (mul_nonneg hR hδ.le) hw.2
      rw [hwu,show 2*(R*δ) = (4*R)*(δ/2) by ring] at h
      exact ⟨hw.1,h⟩
    have hMonotone : ((wedgeCentersMeeting t ξ (R*δ)).card : ℝ) ≤
        ((centersMeeting t (unitRep ξ) ((4*R)*(δ/2))).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hIncl)
    have hPack := hOverlap (4*R) (mul_nonneg (by norm_num) hR) (unitRep ξ)
    exact (hMonotone.trans hPack).trans_eq (by
      congr 1
      ring)

end Burnett.Analysis.ProjectiveNullCaps
