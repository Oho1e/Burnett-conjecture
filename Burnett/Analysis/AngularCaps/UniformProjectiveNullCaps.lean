import Burnett.Analysis.AngularCaps.ProjectiveNullCover
import Burnett.Analysis.AngularCaps.AmbientBallPacking

set_option autoImplicit false
set_option maxHeartbeats 5500000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Finset Set Metric
open scoped BigOperators

def centersMeeting (t : Finset Vec) (v : Vec) (r : ℝ) : Finset Vec := by
  classical
  exact t.filter (fun x => projectiveDist v x ≤ r)

private def signedRepresentative (v : Vec) (r : ℝ) (x : Vec) : Vec :=
  if dist x v ≤ r then x else -x

private theorem signedRepresentative_near {v x : Vec} {r : ℝ} (hx : projectiveDist v x ≤ r) :
    dist (signedRepresentative v r x) v ≤ r := by
  by_cases h : dist x v ≤ r
  · simpa only [signedRepresentative, if_pos h] using h
  · rw [signedRepresentative, if_neg h, dist_eq_norm, show -x-v = -(v+x) by abel, norm_neg]
    refine (min_le_iff.mp hx).resolve_left ?_
    intro h'
    apply h
    rw [dist_comm, dist_eq_norm]
    exact h'

private theorem projectiveDist_le_signedRepresentative_dist (v x y : Vec) (r : ℝ) :
    projectiveDist x y ≤ dist (signedRepresentative v r x) (signedRepresentative v r y) := by
  by_cases hx : dist x v ≤ r
  · by_cases hy : dist y v ≤ r
    · simpa only [signedRepresentative, if_pos hx, if_pos hy] using projectiveDist_le_dist x y
    · simp only [signedRepresentative, if_pos hx, if_neg hy]
      rw [dist_eq_norm, sub_neg_eq_add]
      exact min_le_right _ _
  · by_cases hy : dist y v ≤ r
    · simp only [signedRepresentative, if_neg hx, if_pos hy]
      rw [dist_eq_norm, show -x-y = -(x+y) by abel, norm_neg]
      exact min_le_right _ _
    · simp only [signedRepresentative, if_neg hx, if_neg hy]
      rw [dist_eq_norm, show -x - -y = -(x-y) by abel, norm_neg]
      exact min_le_left _ _

/-- Every fixed enlargement of the same separated caps has bounded overlap.
The test direction can be anywhere in the ambient four-dimensional space. -/
theorem projectiveCaps_bounded_overlap {t : Finset Vec} {δ : ℝ} (hδ : 0 < δ)
    (hSep : (↑t : Set Vec).Pairwise (fun x y => δ/2 < projectiveDist x y))
    (R : ℝ) (hR : 0 ≤ R) (v : Vec) :
    ((centersMeeting t v (R*δ)).card : ℝ) ≤ (4*R+1)^4 := by
  let s := centersMeeting t v (R*δ)
  let c := signedRepresentative v (R*δ)
  have hMem (x : Vec) (hx : x ∈ s) : x ∈ t ∧ projectiveDist v x ≤ R*δ := by
    simpa only [s, centersMeeting, Finset.mem_filter] using hx
  have hNear (x : Vec) (hx : x ∈ s) : dist (c x) v ≤ R*δ :=
    signedRepresentative_near (hMem x hx).2
  have hF (x : Vec) (hx : x ∈ s) (y : Vec) (hy : y ∈ s) (hxy : x ≠ y) :
      2*(δ/4) ≤ dist (c x) (c y) := by
    have hOne := (hSep (hMem x hx).1 (hMem y hy).1 hxy).le.trans
      (projectiveDist_le_signedRepresentative_dist v x y (R*δ))
    linarith only [hOne]
  have hPacked := card_ambientBall_packing_le s c v (show 0 < δ/4 from div_pos hδ (by norm_num))
    (mul_nonneg hR hδ.le) hNear hF
  refine hPacked.trans_eq ?_
  have hRatio : (R*δ+δ/4)/(δ/4) = 4*R+1 := by
    apply (div_eq_iff (show δ/4 ≠ 0 from (div_pos hδ (by norm_num)).ne')).2
    ring
  rw [hRatio]

/-- The actual projective null directions of each form in a fixed compact
Lorentz family are covered by a single separated family of true null caps.
The cardinality is of order δ⁻² and the enlarged overlaps are uniform. -/
theorem exists_uniform_projective_null_caps {K : Set Form} (hK : IsCompact K)
    (hs : ∀ m ∈ K, Symmetric m) (hND : ∀ m ∈ K, Nondegenerate m) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ t : Finset Vec,
        (↑t : Set Vec) ⊆ unitNull m ∧ (t.card : ℝ) ≤ C/δ^2 ∧
        (∀ v ∈ unitNull m, ∃ w ∈ t, projectiveDist v w < δ) ∧
        (↑t : Set Vec).Pairwise (fun x y => δ/2 < projectiveDist x y) ∧
        ∀ R : ℝ, 0 ≤ R → ∀ v : Vec, ((centersMeeting t v (R*δ)).card : ℝ) ≤ (4*R+1)^4 := by
  obtain ⟨C, hC, hGrid⟩ := exists_compactFamily_gridNullCover hK hs hND
  refine ⟨C,hC,fun m hm δ hδ hδone => ?_⟩
  obtain ⟨c, hc, hCard, hCover⟩ := hGrid m hm δ hδ hδone
  obtain ⟨t, htc, hSep, hTCover⟩ := exists_projectiveSeparated_subcover c
    (show 0 ≤ δ/2 from div_nonneg hδ.le zero_le_two)
  have ht : (↑t : Set Vec) ⊆ unitNull m := fun x hx => hc (htc hx)
  have hCount : (t.card : ℝ) ≤ C/δ^2 :=
    (Nat.cast_le.mpr (Finset.card_le_card htc)).trans hCard
  refine ⟨t, ht, hCount, ?_, hSep, fun R hR v => projectiveCaps_bounded_overlap hδ hSep R hR v⟩
  intro v hv
  obtain ⟨y, hy, hvy⟩ := hCover v hv
  obtain ⟨z, hz, hyz⟩ := hTCover y hy
  refine ⟨z,hz,(projectiveDist_triangle v y z).trans_lt ?_⟩
  linarith only [hvy, hyz, hδ]

end Burnett.Analysis.ProjectiveNullCaps
