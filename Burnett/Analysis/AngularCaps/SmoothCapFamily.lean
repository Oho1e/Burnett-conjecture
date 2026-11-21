import Burnett.Analysis.AngularCaps.SmoothCapSupport

set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set Function
open scoped ContDiff BigOperators

/-- A family of the actual base and enlarged smooth cap symbols, with one
common center set and the geometric properties needed by the near terms. -/
structure SmoothThinConeCaps (m : Form) (δ η inner outer enlarged D : ℝ) where
  centers : Finset Vec
  centers_null : (↑centers : Set Vec) ⊆ unitNull m
  count_bound : (centers.card : ℝ) ≤ D/δ^2
  centers_separated : (↑centers : Set Vec).Pairwise (fun x y => δ/4 < projectiveDist x y)
  smoothness : ∀ w ∈ centers,
    ContDiffOn ℝ ∞ (capMultiplier centers m δ η inner outer w) puncturedFrequency ∧
    ContDiffOn ℝ ∞ (enlargedCapMultiplier m δ η outer enlarged w) puncturedFrequency
  degree_zero : ∀ w ∈ centers,
    DegreeZero (capMultiplier centers m δ η inner outer w) ∧
    DegreeZero (enlargedCapMultiplier m δ η outer enlarged w)
  base_range : ∀ w ∈ centers, ∀ ξ,
    0 ≤ capMultiplier centers m δ η inner outer w ξ ∧ capMultiplier centers m δ η inner outer w ξ ≤ 1
  enlarged_range : ∀ w ∈ centers, ∀ ξ,
    0 ≤ enlargedCapMultiplier m δ η outer enlarged w ξ ∧ enlargedCapMultiplier m δ η outer enlarged w ξ ≤ 1
  partition_inner : ∀ ξ, ξ ≠ 0 → |quadratic m ξ| ≤ inner*η*‖ξ‖^2 →
    ∑ w ∈ centers, capMultiplier centers m δ η inner outer w ξ = 1
  base_support : ∀ w ∈ centers, ∀ ξ, ξ ≠ 0 → ξ ∈ tsupport (capMultiplier centers m δ η inner outer w) →
    projectiveWedgeSq ξ w ≤ δ^2 ∧ |quadratic m ξ| ≤ outer*η*‖ξ‖^2
  enlarged_support : ∀ w ∈ centers, ∀ ξ, ξ ≠ 0 → ξ ∈ tsupport (enlargedCapMultiplier m δ η outer enlarged w) →
    projectiveWedgeSq ξ w ≤ (5*δ)^2 ∧ |quadratic m ξ| ≤ enlarged*η*‖ξ‖^2
  support_overlap : ∀ ξ, ξ ≠ 0 →
    ((capSupportCenters centers (capMultiplier centers m δ η inner outer) ξ).card : ℝ) ≤ 17^4 ∧
    ((capSupportCenters centers (enlargedCapMultiplier m δ η outer enlarged) ξ).card : ℝ) ≤ 81^4
  enlarged_plateau : ∀ w ∈ centers, ∀ ξ, ξ ≠ 0 →
    projectiveWedgeSq ξ w ≤ (4*δ)^2 → |quadratic m ξ| ≤ outer*η*‖ξ‖^2 →
    enlargedCapMultiplier m δ η outer enlarged w ξ = 1
  enlarged_on_three_nearSlots : ∀ w ∈ centers, ∀ p q r : Vec, p ≠ 0 → q ≠ 0 → r ≠ 0 →
    p ∈ tsupport (capMultiplier centers m δ η inner outer w) →
    projectiveWedgeSq p q ≤ δ^2 → projectiveWedgeSq p r ≤ δ^2 →
    |quadratic m q| ≤ outer*η*‖q‖^2 → |quadratic m r| ≤ outer*η*‖r‖^2 →
    enlargedCapMultiplier m δ η outer enlarged w p = 1 ∧
      enlargedCapMultiplier m δ η outer enlarged w q = 1 ∧
      enlargedCapMultiplier m δ η outer enlarged w r = 1

/-- Explicit smooth partitions on the whole inner thin cone, with bounded
overlap and a single family of genuine centers for the enlarged multipliers. -/
theorem exists_smooth_thinCone_capMultipliers {K : Set Form} (hK : IsCompact K)
    (hSym : ∀ m ∈ K, Symmetric m) (hND : ∀ m ∈ K, Nondegenerate m)
    {inner outer enlarged : ℝ} (hIn : 0 ≤ inner) (hIO : inner < outer) (hOE : outer < enlarged) :
    ∃ D c₀ : ℝ, 0 < D ∧ 0 < c₀ ∧ ∀ m ∈ K, ∀ κ : ℝ, 0 < κ → κ < 1/16 →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ c : ℝ, 0 < c → c ≤ c₀ →
        Nonempty (SmoothThinConeCaps m δ (c*κ*δ^2) inner outer enlarged D) := by
  have hOut := hIn.trans hIO.le
  obtain ⟨D,c₀,hD,hc₀,hFamily⟩ :=
    exists_uniform_thinCone_wedge_caps hK hSym hND enlarged (hOut.trans hOE.le)
  refine ⟨D,c₀,hD,hc₀,?_⟩
  intro m hm κ hκ hκsmall δ hδ hδone c hc hc₀'
  let η := c*κ*δ^2
  have hη : 0 < η := mul_pos (mul_pos hc hκ) (pow_pos hδ 2)
  obtain ⟨t,ht,hCard,hSep,hCover,hOverlap⟩ := hFamily m hm κ hκ hκsmall δ hδ hδone c hc hc₀'
  have hwNZ (w : Vec) (hw : w ∈ t) : w ≠ 0 := by
    intro h
    have hNorm : ‖w‖ = 1 := (ht hw).1
    simp [h] at hNorm
  have hBaseSup (w : Vec) (hw : w ∈ t) (ξ : Vec) (hξ : ξ ≠ 0)
      (hs : ξ ∈ tsupport (capMultiplier t m δ η inner outer w)) :
      projectiveWedgeSq ξ w ≤ δ^2 ∧ |quadratic m ξ| ≤ outer*η*‖ξ‖^2 :=
    capMultiplier_tsupport_bounds hδ hη hIn hIO (hwNZ w hw) hξ hs
  have hLargeSup (w : Vec) (hw : w ∈ t) (ξ : Vec) (hξ : ξ ≠ 0)
      (hs : ξ ∈ tsupport (enlargedCapMultiplier m δ η outer enlarged w)) :
      projectiveWedgeSq ξ w ≤ (5*δ)^2 ∧ |quadratic m ξ| ≤ enlarged*η*‖ξ‖^2 :=
    enlargedCapMultiplier_tsupport_bounds hδ hη hOut hOE (hwNZ w hw) hξ hs
  refine ⟨{
    centers := t
    centers_null := ht
    count_bound := hCard
    centers_separated := hSep
    smoothness := fun w hw => ⟨capMultiplier_contDiffOn hwNZ m δ hη inner outer (hwNZ w hw),
      enlargedCapMultiplier_contDiffOn m δ hη outer enlarged (hwNZ w hw)⟩
    degree_zero := fun w _ => ⟨capMultiplier_degreeZero t m δ η inner outer w,
      enlargedCapMultiplier_degreeZero m δ η outer enlarged w⟩
    base_range := fun _ hw ξ => capMultiplier_range m δ η inner outer hw ξ
    enlarged_range := fun w _ ξ => enlargedCapMultiplier_range m δ η outer enlarged w ξ
    partition_inner := ?_
    base_support := hBaseSup
    enlarged_support := hLargeSup
    support_overlap := ?_
    enlarged_plateau := fun _ _ _ hξ hAngle hCone =>
      enlargedCapMultiplier_eq_one m hδ hη hOut hOE hξ hAngle hCone
    enlarged_on_three_nearSlots := fun w hw _ _ _ hp hq hr hCap hPQ hPR hQ hR =>
      enlargedCapMultiplier_eq_one_on_three_nearSlots hδ hη hIn hIO hOE
        (hwNZ w hw) hp hq hr hCap hPQ hPR hQ hR
  }⟩
  · intro ξ hξ hCone
    apply capMultiplier_partition_eq_one t m hδ hη hIn hIO hξ hCone
    obtain ⟨w,hw,_,hW⟩ := hCover (inner*η) (mul_nonneg hIn hη.le)
      (mul_le_mul_of_nonneg_right (hIO.trans hOE).le hη.le) ξ hξ hCone
    have he : 3*δ/4 = (3/4)*δ := by ring
    rw [he] at hW
    exact ⟨w,hw,hW.le⟩
  · intro ξ hξ
    have hBase := capSupportCenters_card_le_wedge (t := t)
      (σ := capMultiplier t m δ η inner outer) (ξ := ξ) (radius := δ)
      (fun w hw hs => (hBaseSup w hw ξ hξ hs).1)
    have hEnlarged := capSupportCenters_card_le_wedge (t := t)
      (σ := enlargedCapMultiplier m δ η outer enlarged) (ξ := ξ) (radius := 5*δ)
      (fun w hw hs => (hLargeSup w hw ξ hξ hs).1)
    refine ⟨hBase.trans ?_,hEnlarged.trans ?_⟩
    · simpa only [one_mul,show (16:ℝ)*1+1 = 17 by norm_num] using hOverlap 1 zero_le_one ξ hξ
    · simpa only [show (16:ℝ)*5+1 = 81 by norm_num] using hOverlap 5 (by norm_num) ξ hξ

end Burnett.Analysis.ProjectiveNullCaps
