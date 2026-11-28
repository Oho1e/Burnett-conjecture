import Burnett.Analysis.FrozenTransport.Ward.WardAllScalePurePhysicalDecomposition
import Burnett.Analysis.AngularCaps.SmoothCapFamily
import Burnett.Analysis.AngularCaps.ComparableTriadAngle

set_option autoImplicit false
set_option maxHeartbeats 11000000

noncomputable section

namespace Burnett.C02

open Set Burnett.Analysis.ProjectiveNullCaps
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.RicciSymbol

private theorem wardWedge_comm (x y : E) :
    projectiveWedgeSq x y = projectiveWedgeSq y x := by
  simp only [projectiveWedgeSq,coordinateWedgeSq_eq_gram,real_inner_comm x y,
    mul_comm (‖x‖^2) (‖y‖^2)]

private theorem wardLowNear_three_edges {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) {κ δ : ℝ}
    (hκ : 0 < κ) (hκsmall : κ < 1/16) (hδ : 0 < δ)
    {p q r : E} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hSum : p+q+r = 0) (hLow : lowSlotWeight ϑ κ p q r ≠ 0)
    (hNear : angularNearWeight ϑ δ p q r ≠ 0) :
    projectiveWedgeSq p q ≤ δ^2 ∧ projectiveWedgeSq q r ≤ δ^2 ∧
      projectiveWedgeSq r p ≤ δ^2 := by
  obtain ⟨hPQ,hPR⟩ := angularNearWeight_nonzero_edges hCut hδ hNear
  have hPerm : p+r+q = 0 := by simpa only [add_right_comm] using hSum
  have hLow' : lowSlotWeight ϑ κ p r q ≠ 0 := by rwa [lowSlotWeight_swap_high]
  have hSmall := lowSlotWeight_nonzero_small hCut hκ hκsmall hPerm hr hLow'
  have hPsmall : ‖p‖ ≤ ‖r‖ := hSmall.trans (by
    have e := mul_le_mul_of_nonneg_right (show 2*κ ≤ 1 by linarith only [hκsmall]) (norm_nonneg r)
    simpa only [one_mul] using e)
  have hRatio : ‖p‖^2/‖r‖^2 ≤ 1 := by
    apply (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hr) 2)).mpr
    simpa only [one_mul] using pow_le_pow_left₀ (norm_nonneg p) hPsmall 2
  have hPerm' : q+p+r = 0 := by simpa only [add_comm p q] using hSum
  refine ⟨hPQ.le,?_,by rw [wardWedge_comm r p]; exact hPR.le⟩
  rw [projectiveWedgeSq_third_eq_of_triad hPerm' hq hp hr,wardWedge_comm q p]
  exact ((mul_le_mul_of_nonneg_right hRatio (projectiveWedgeSq_nonneg _ _)).trans_eq
    (one_mul _)).trans hPQ.le

/-- The unchanged full near coefficient puts all three signed frequencies
within the same projective angle. On a low term the high-high edge follows
from the signed identity, and on the comparable term the true cone does so. -/
theorem exists_wardPurePhysicalNearWeight_all_edges {K : Set Form} (hK : IsCompact K)
    (hFrame : ∀ m ∈ K, Nonempty (TensorFrame.LorentzFrame m))
    (out : ℝ) (hOut : 0 ≤ out) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ m ∈ K, ∀ {ϑ : ℝ → ℝ}
      (_ : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (_ : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
      {κ δ c : ℝ}, 0 < κ → κ < 1/16 → 0 < δ → 0 < c → c ≤ c₀ →
      ∀ x : Joint, let p := x.1; let q := x.2; let r := -(p+q)
      p ≠ 0 → q ≠ 0 → r ≠ 0 →
      InRelativeCone m (out*(c*κ*δ^2)) p → InRelativeCone m (out*(c*κ*δ^2)) q →
      InRelativeCone m (out*(c*κ*δ^2)) r →
      wardPurePhysicalNearWeight ϑ κ δ x ≠ 0 →
      projectiveWedgeSq p q ≤ δ^2 ∧ projectiveWedgeSq q r ≤ δ^2 ∧
        projectiveWedgeSq r p ≤ δ^2 := by
  obtain ⟨B,hB,hComp⟩ := exists_uniform_comparable_nearNull_wedge hK hFrame
  let c₀ := 1/(B*(out+1))
  have hDen : 0 < B*(out+1) := mul_pos hB (by linarith only [hOut])
  refine ⟨c₀,one_div_pos.mpr hDen,?_⟩
  intro m hm ϑ hCut hFlat κ δ c hκ hκsmall hδ hc hc₀ x p q r hp hq hr hP hQ hR hNear
  have hSum : p+q+r = 0 := add_neg_cancel (p+q)
  have hRot : q+r+p = 0 := by
    calc
      _ = p+q+r := by abel
      _ = 0 := hSum
  have hRot' : r+p+q = 0 := by
    calc
      _ = p+q+r := by abel
      _ = 0 := hSum
  by_cases hComparable : comparableSlotWeight ϑ κ p q r = 0
  · by_cases hFirst : lowSlotWeight ϑ κ p q r * angularNearWeight ϑ δ p q r = 0
    · by_cases hSecond : lowSlotWeight ϑ κ q r p * angularNearWeight ϑ δ q r p = 0
      · have hThird : lowSlotWeight ϑ κ r p q * angularNearWeight ϑ δ r p q ≠ 0 := by
          intro he
          apply hNear
          change comparableSlotWeight ϑ κ p q r +
            lowSlotWeight ϑ κ p q r * angularNearWeight ϑ δ p q r +
            lowSlotWeight ϑ κ q r p * angularNearWeight ϑ δ q r p +
            lowSlotWeight ϑ κ r p q * angularNearWeight ϑ δ r p q = 0
          simp only [hComparable,hFirst,hSecond,he,add_zero]
        obtain ⟨h₁,h₂,h₃⟩ := wardLowNear_three_edges hCut hκ hκsmall hδ hr hp hq hRot'
          (mul_ne_zero_iff.mp hThird).1 (mul_ne_zero_iff.mp hThird).2
        exact ⟨h₂,h₃,h₁⟩
      · obtain ⟨h₁,h₂,h₃⟩ := wardLowNear_three_edges hCut hκ hκsmall hδ hq hr hp hRot
          (mul_ne_zero_iff.mp hSecond).1 (mul_ne_zero_iff.mp hSecond).2
        exact ⟨h₃,h₁,h₂⟩
    · exact wardLowNear_three_edges hCut hκ hκsmall hδ hp hq hr hSum
        (mul_ne_zero_iff.mp hFirst).1 (mul_ne_zero_iff.mp hFirst).2
  · obtain ⟨h₁,h₂,h₃⟩ := hComp m hm κ hκ hκsmall (out*(c*κ*δ^2)) (by positivity)
      ϑ hCut hFlat p q r hSum hp hq hr hP hQ hR hComparable
    have hC : B*out*c ≤ 1 := calc
      _ ≤ (B*(out+1))*c := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hB.le) hc.le
      _ ≤ (B*(out+1))*c₀ := mul_le_mul_of_nonneg_left hc₀ hDen.le
      _ = 1 := by rw [show c₀ = (B*(out+1))⁻¹ from one_div _,
          mul_inv_cancel₀ hDen.ne']
    have hScaled : B*(out*(c*κ*δ^2))/κ ≤ δ^2 := calc
      _ = (B*out*c)*δ^2 := by field_simp [hκ.ne']
      _ ≤ 1*δ^2 := mul_le_mul_of_nonneg_right hC (sq_nonneg δ)
      _ = δ^2 := one_mul _
    exact ⟨h₁.trans hScaled,h₂.trans hScaled,h₃.trans hScaled⟩

/-- The actual cap multiplier is one on all three inputs of a nonzero
localized near weight, with cap inner width containing the physical screen. -/
theorem wardNear_capPlateaux {m : Form} {δ η inn out enlarged D screenOut : ℝ}
    (S : SmoothThinConeCaps m δ η inn out enlarged D)
    (hη : 0 < η) (hWidth : screenOut ≤ inn) (hIO : inn ≤ out)
    (γ : ↑S.centers) {p q r : E} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hP : InRelativeCone m (screenOut*η) p) (hQ : InRelativeCone m (screenOut*η) q)
    (hR : InRelativeCone m (screenOut*η) r)
    (hPQ : projectiveWedgeSq p q ≤ δ^2) (hRP : projectiveWedgeSq r p ≤ δ^2)
    (hCap : capMultiplier S.centers m δ η inn out γ p ≠ 0) :
    |quadratic m p| ≤ inn*η*‖p‖^2 ∧
      enlargedCapMultiplier m δ η out enlarged γ p = 1 ∧
      enlargedCapMultiplier m δ η out enlarged γ q = 1 ∧
      enlargedCapMultiplier m δ η out enlarged γ r = 1 := by
  have hSupport : p ∈ tsupport (capMultiplier S.centers m δ η inn out γ) :=
    subset_tsupport _ hCap
  have hQ' : |quadratic m q| ≤ out*η*‖q‖^2 :=
    hQ.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hWidth.trans hIO) hη.le) (sq_nonneg ‖q‖))
  have hR' : |quadratic m r| ≤ out*η*‖r‖^2 :=
    hR.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hWidth.trans hIO) hη.le) (sq_nonneg ‖r‖))
  refine ⟨hP.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hWidth hη.le) (sq_nonneg ‖p‖)),?_⟩
  have hPR : projectiveWedgeSq p r ≤ δ^2 := by rwa [wardWedge_comm]
  exact S.enlarged_on_three_nearSlots γ γ.property p q r hp hq hr hSupport hPQ hPR hQ' hR'

end Burnett.C02
