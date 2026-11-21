import Burnett.Analysis.AngularCaps.UniformProjectiveNullCaps
import Burnett.Analysis.AngularCaps.ProjectiveWedgeGeometry

set_option autoImplicit false
set_option maxHeartbeats 4500000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Finset Set

/-- Comparison of the manuscript angle with the projective metric on normalized
representatives of arbitrary nonzero covectors. -/
theorem projectiveWedgeSq_compare_unitRep_dist {x y : Vec} (hx : x ≠ 0) (hy : y ≠ 0) :
    projectiveDist (unitRep x) (unitRep y)^2/2 ≤ projectiveWedgeSq x y ∧
      projectiveWedgeSq x y ≤ projectiveDist (unitRep x) (unitRep y)^2 := by
  rw [projectiveWedgeSq_eq_unitRep hx hy]
  exact coordinateWedgeSq_compare_projectiveDist (norm_unitRep x hx) (norm_unitRep y hy)

private theorem unitRep_of_norm_one {x : Vec} (hx : ‖x‖ = 1) : unitRep x = x := by
  simp [unitRep, hx]

private theorem nonzero_of_norm_one {x : Vec} (hx : ‖x‖ = 1) : x ≠ 0 := by
  intro hz
  simp [hz] at hx

theorem projectiveDist_unitRep_le_of_wedgeSq_le {x y : Vec} (hx : x ≠ 0) (hy : y ≠ 0)
    {a : ℝ} (ha : 0 ≤ a) (hAngle : projectiveWedgeSq x y ≤ a^2) :
    projectiveDist (unitRep x) (unitRep y) ≤ 2*a := by
  apply (sq_le_sq₀ (projectiveDist_nonneg _ _) (mul_nonneg zero_le_two ha)).mp
  have hLower := (projectiveWedgeSq_compare_unitRep_dist hx hy).1
  nlinarith only [hLower, hAngle, sq_nonneg a]

noncomputable def wedgeCentersMeeting (t : Finset Vec) (ξ : Vec) (δ : ℝ) : Finset Vec := by
  classical
  exact t.filter fun w => projectiveWedgeSq ξ w ≤ δ^2

/-- The same finite set of true null directions covers all nonzero null
covectors in the manuscript's own squared wedge angle. Every fixed enlargement
has uniformly bounded overlap at any nonzero frequency. -/
theorem exists_uniform_projective_wedge_null_caps {K : Set Form} (hK : IsCompact K)
    (hs : ∀ m ∈ K, Symmetric m) (hND : ∀ m ∈ K, Nondegenerate m) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ t : Finset Vec, (↑t : Set Vec) ⊆ unitNull m ∧ (t.card : ℝ) ≤ C/δ^2 ∧
        (∀ ξ : Vec, ξ ≠ 0 → quadratic m ξ = 0 →
          ∃ w ∈ t, projectiveWedgeSq ξ w < δ^2) ∧
        (↑t : Set Vec).Pairwise (fun x y => δ/2 < projectiveDist x y) ∧
        ∀ R : ℝ, 0 ≤ R → ∀ ξ : Vec, ξ ≠ 0 →
          ((wedgeCentersMeeting t ξ (R*δ)).card : ℝ) ≤ (8*R+1)^4 := by
  obtain ⟨C,hC,hFamily⟩ := exists_uniform_projective_null_caps hK hs hND
  refine ⟨C,hC,fun m hm δ hδ hδone => ?_⟩
  obtain ⟨t,ht,hCard,hCover,hSep,hOverlap⟩ := hFamily m hm δ hδ hδone
  refine ⟨t,ht,hCard,?_,hSep,?_⟩
  · intro ξ hξ hQuad
    obtain ⟨w,hw,hClose⟩ := hCover (unitRep ξ)
      (unitRep_mem_unitNull (norm_pos_iff.mpr hξ) hQuad)
    have hwunit : ‖w‖ = 1 := (ht hw).1
    have hUpper := (projectiveWedgeSq_compare_unitRep_dist hξ (nonzero_of_norm_one hwunit)).2
    rw [unitRep_of_norm_one hwunit] at hUpper
    exact ⟨w,hw,hUpper.trans_lt
      ((sq_lt_sq₀ (projectiveDist_nonneg _ _) hδ.le).mpr hClose)⟩
  · intro R hR ξ hξ
    have hSubset : wedgeCentersMeeting t ξ (R*δ) ⊆ centersMeeting t (unitRep ξ) ((2*R)*δ) := by
      classical
      intro w hw
      simp only [wedgeCentersMeeting, Finset.mem_filter] at hw
      simp only [centersMeeting, Finset.mem_filter]
      refine ⟨hw.1,?_⟩
      have hwunit : ‖w‖ = 1 := (ht hw.1).1
      have hDist := projectiveDist_unitRep_le_of_wedgeSq_le hξ (nonzero_of_norm_one hwunit)
        (mul_nonneg hR hδ.le) hw.2
      rwa [unitRep_of_norm_one hwunit, ← mul_assoc] at hDist
    have hCount : ((wedgeCentersMeeting t ξ (R*δ)).card : ℝ) ≤
        ((centersMeeting t (unitRep ξ) ((2*R)*δ)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hSubset)
    have hPack := hOverlap (2*R) (mul_nonneg zero_le_two hR) (unitRep ξ)
    refine (hCount.trans hPack).trans_eq ?_
    congr 1
    ring

/-- The manuscript angular cutoff for a single designated low slot. -/
def angularNearWeight (ϑ : ℝ → ℝ) (δ : ℝ) (p q r : Vec) : ℝ :=
  ϑ (projectiveWedgeSq p q/δ^2) * ϑ (projectiveWedgeSq p r/δ^2)

theorem angularNearWeight_nonzero_edges {ϑ : ℝ → ℝ}
    (hCut : ∀ s : ℝ, 1 ≤ s → ϑ s = 0) {δ : ℝ} (hδ : 0 < δ) {p q r : Vec}
    (hNear : angularNearWeight ϑ δ p q r ≠ 0) :
    projectiveWedgeSq p q < δ^2 ∧ projectiveWedgeSq p r < δ^2 := by
  have h (z : Vec) (hz : ϑ (projectiveWedgeSq p z/δ^2) ≠ 0) :
      projectiveWedgeSq p z < δ^2 := by
    have hp : 0 < δ^2 := pow_pos hδ _
    have hx : projectiveWedgeSq p z/δ^2 < 1 :=
      lt_of_not_ge fun h => hz (hCut _ h)
    simpa only [one_mul] using (div_lt_iff₀ hp).mp hx
  have hFactors := mul_ne_zero_iff.mp hNear
  exact ⟨h q hFactors.1, h r hFactors.2⟩

/-- One designated angular cap suffices for both other near directions.
Weak inequalities include the angular boundary. -/
theorem near_wedge_slots_same_wedge_enlargement {δ : ℝ} (hδ : 0 < δ)
    {p q r w : Vec} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hw : w ≠ 0)
    (hCap : projectiveWedgeSq p w ≤ δ^2)
    (hPQ : projectiveWedgeSq p q ≤ δ^2) (hPR : projectiveWedgeSq p r ≤ δ^2) :
    projectiveWedgeSq q w ≤ (4*δ)^2 ∧ projectiveWedgeSq r w ≤ (4*δ)^2 := by
  have hPW := projectiveDist_unitRep_le_of_wedgeSq_le hp hw hδ.le hCap
  have hStep (z : Vec) (hz : z ≠ 0) (hPZ : projectiveWedgeSq p z ≤ δ^2) :
      projectiveWedgeSq z w ≤ (4*δ)^2 := by
    have hd := projectiveDist_unitRep_le_of_wedgeSq_le hp hz hδ.le hPZ
    rw [projectiveDist_comm] at hd
    have hTri := projectiveDist_triangle (unitRep z) (unitRep p) (unitRep w)
    have hZBound : projectiveDist (unitRep z) (unitRep w) ≤ 4*δ := by linarith only [hd,hPW,hTri]
    exact (projectiveWedgeSq_compare_unitRep_dist hz hw).2.trans
      ((sq_le_sq₀ (projectiveDist_nonneg _ _) (mul_nonneg (by norm_num) hδ.le)).mpr hZBound)
  exact ⟨hStep q hq hPQ,hStep r hr hPR⟩

theorem angularNearWeight_slots_same_wedge_enlargement {ϑ : ℝ → ℝ}
    (hCut : ∀ s : ℝ, 1 ≤ s → ϑ s = 0) {δ : ℝ} (hδ : 0 < δ)
    {p q r w : Vec} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hw : w ≠ 0)
    (hCap : projectiveWedgeSq p w ≤ δ^2) (hNear : angularNearWeight ϑ δ p q r ≠ 0) :
    projectiveWedgeSq q w ≤ (4*δ)^2 ∧ projectiveWedgeSq r w ≤ (4*δ)^2 := by
  obtain ⟨hPQ,hPR⟩ := angularNearWeight_nonzero_edges hCut hδ hNear
  exact near_wedge_slots_same_wedge_enlargement hδ hp hq hr hw hCap hPQ.le hPR.le

end Burnett.Analysis.ProjectiveNullCaps
