import Burnett.Analysis.FrozenTransport.NormalizedFarReciprocal

set_option autoImplicit false
set_option maxHeartbeats 5600000
set_option maxRecDepth 4000

noncomputable section

namespace Burnett.V10

open Set Metric Burnett.Analysis.ProjectiveNullCaps
open scoped ContDiff RealInnerProductSpace

def farHighOutput (x : FarProfilePoint) : Vec := x.2.2 + x.2.1

def farLowArgument (κ : ℝ) (x : FarProfilePoint) : ℝ :=
  ⟪x.2.1, x.2.1⟫ / (κ ^ 2 * (1 + ⟪farHighOutput x, farHighOutput x⟫))

def farIncomingAngle (x : FarProfilePoint) : ℝ := 1 - ⟪x.1, x.2.2⟫ ^ 2

def farOutgoingAngle (x : FarProfilePoint) : ℝ :=
  1 - ⟪x.1, farHighOutput x⟫ ^ 2 / ⟪farHighOutput x, farHighOutput x⟫

/-- The actual designated low-slot far weight extended in the three independent variables. -/
def farCutoffExtension (ϑ : ℝ → ℝ) (κ δ : ℝ) (x : FarProfilePoint) : ℝ :=
  ϑ (farLowArgument κ x) *
    (1 - ϑ (farIncomingAngle x / δ ^ 2) * ϑ (farOutgoingAngle x / δ ^ 2))

def farProfileOpenDomain : Set FarProfilePoint := {x | farHighOutput x ≠ 0}

private theorem farHighOutput_contDiff : ContDiff ℝ ∞ farHighOutput :=
  (contDiff_snd.comp contDiff_snd).add (contDiff_fst.comp contDiff_snd)

theorem farProfileOpenDomain_isOpen : IsOpen farProfileOpenDomain :=
  isClosed_singleton.isOpen_compl.preimage farHighOutput_contDiff.continuous

theorem farCutoffExtension_contDiffOn {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ ∞ ϑ)
    {κ : ℝ} (hκ : 0 < κ) (δ : ℝ) :
    ContDiffOn ℝ ∞ (farCutoffExtension ϑ κ δ) farProfileOpenDomain := by
  have hω : ContDiff ℝ ∞ (fun x : FarProfilePoint => x.1) := contDiff_fst
  have hz : ContDiff ℝ ∞ (fun x : FarProfilePoint => x.2.1) := contDiff_fst.comp contDiff_snd
  have hθ : ContDiff ℝ ∞ (fun x : FarProfilePoint => x.2.2) := contDiff_snd.comp contDiff_snd
  have hOut := farHighOutput_contDiff
  have hDen := hOut.inner ℝ hOut
  have hl : ContDiff ℝ ∞ (farLowArgument κ) := by
    apply (hz.inner ℝ hz).div (contDiff_const.mul (contDiff_const.add hDen))
    intro x
    change κ ^ 2 * (1 + ⟪farHighOutput x, farHighOutput x⟫) ≠ 0
    rw [real_inner_self_eq_norm_sq]
    exact mul_ne_zero (pow_ne_zero _ hκ.ne') (by positivity)
  have hi : ContDiff ℝ ∞ farIncomingAngle := contDiff_const.sub ((hω.inner ℝ hθ).pow 2)
  have ho : ContDiffOn ℝ ∞ farOutgoingAngle farProfileOpenDomain := by
    refine contDiffOn_const.sub (((hω.inner ℝ hOut).pow 2).contDiffOn.div hDen.contDiffOn ?_)
    intro x hx
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hAngularOut : ContDiffOn ℝ ∞ (fun x => ϑ (farOutgoingAngle x / δ ^ 2)) farProfileOpenDomain :=
    hϑ.comp_contDiffOn (ho.div_const _)
  exact ((hϑ.comp hl).contDiffOn).mul
    (contDiffOn_const.sub (((hϑ.comp (hi.div_const _)).contDiffOn).mul hAngularOut))

private theorem normalizedAngle_of_unit_left {w y : Vec} (hw : ‖w‖ = 1) (hy : y ≠ 0) :
    1 - ⟪w, y⟫ ^ 2 / ‖y‖ ^ 2 = projectiveWedgeSq w y := by
  rw [projectiveWedgeSq, coordinateWedgeSq_eq_gram, hw, one_pow, one_mul, sub_div,
    div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr hy))]

private theorem projectiveWedgeSq_smul_right_of_nonzero {t : ℝ} (ht : t ≠ 0)
    {x y : Vec} (hx : x ≠ 0) (hy : y ≠ 0) :
    projectiveWedgeSq x (t • y) = projectiveWedgeSq x y := by
  simp only [projectiveWedgeSq, coordinateWedgeSq_eq_gram, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp [ht, norm_ne_zero_iff.mpr hx, norm_ne_zero_iff.mpr hy]

theorem farCutoffExtension_eq_physical {κ : ℝ} (hκ : 0 < κ)
    (ϑ : ℝ → ℝ) (δ : ℝ) {p q r : Vec}
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hSum : p + q + r = 0) :
    farCutoffExtension ϑ κ δ (physicalFarProfilePoint p q) =
      lowSlotWeight ϑ κ p q r * (1 - angularNearWeight ϑ δ p q r) := by
  let x := physicalFarProfilePoint p q
  have hnq : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hnq' : ‖q‖⁻¹ ≠ 0 := inv_ne_zero hnq
  have hR := triad_third_eq_neg_add hSum
  have hOut : farHighOutput x = ‖q‖⁻¹ • (p + q) := by
    simp only [x, farHighOutput, physicalFarProfilePoint, unitRep, smul_add, add_comm]
  have hPQ : p + q ≠ 0 := by
    intro h
    exact hr (by simpa only [h, neg_zero] using hR)
  have hOutNZ : farHighOutput x ≠ 0 := by
    rw [hOut]
    exact smul_ne_zero hnq' hPQ
  have hNorm (y : Vec) : ‖‖q‖⁻¹ • y‖ = ‖q‖⁻¹ * ‖y‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg q))]
  have hLow : farLowArgument κ x = ‖p‖ ^ 2 / (κ ^ 2 * (‖q‖ ^ 2 + ‖r‖ ^ 2)) := by
    rw [farLowArgument, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hOut, hR, norm_neg]
    change ‖‖q‖⁻¹ • p‖ ^ 2 / (κ ^ 2 * (1 + ‖‖q‖⁻¹ • (p + q)‖ ^ 2)) = _
    rw [hNorm p, hNorm (p + q)]
    have hSumPos : 0 < ‖q‖ ^ 2 + ‖p + q‖ ^ 2 :=
      add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.mpr hq) _) (sq_nonneg _)
    field_simp [hκ.ne', hnq, hSumPos.ne']
  have hW : unitRep p ≠ 0 := norm_ne_zero_iff.mp (by rw [norm_unitRep p hp]; norm_num)
  have hIn : farIncomingAngle x = projectiveWedgeSq p q := by
    rw [projectiveWedgeSq_eq_unitRep hp hq, coordinateWedgeSq_eq_gram, norm_unitRep p hp, norm_unitRep q hq]
    simp [farIncomingAngle, x, physicalFarProfilePoint]
  have hOutAngle : farOutgoingAngle x = projectiveWedgeSq p r := by
    rw [farOutgoingAngle, real_inner_self_eq_norm_sq]
    change 1 - ⟪unitRep p, farHighOutput x⟫ ^ 2 / ‖farHighOutput x‖ ^ 2 = _
    rw [normalizedAngle_of_unit_left (norm_unitRep p hp) hOutNZ, hOut,
      projectiveWedgeSq_smul_right_of_nonzero hnq' hW hPQ, unitRep,
      projectiveWedgeSq_smul_left _ (inv_ne_zero (norm_ne_zero_iff.mpr hp)),
      hR, projectiveWedgeSq_neg_right]
  change farCutoffExtension ϑ κ δ x = _
  rw [farCutoffExtension, lowSlotWeight, angularNearWeight, hLow, hIn, hOutAngle]

/-- The compact extension window admits independent variation of all three coordinates. -/
def farProfileCompactDomain : Set FarProfilePoint :=
  closedBall (0 : Vec) 2 ×ˢ (closedBall (0 : Vec) (1 / 4) ×ˢ
    (closedBall (0 : Vec) 2 ∩ {θ | 1 / 2 ≤ ‖θ‖}))

theorem farProfileCompactDomain_isCompact : IsCompact farProfileCompactDomain :=
  (isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)))

theorem farProfileCompactDomain_subset : farProfileCompactDomain ⊆ farProfileOpenDomain := by
  intro x hx hZero
  have hSmall : ‖x.2.1‖ ≤ 1 / 4 := by simpa only [mem_closedBall, dist_zero_right] using hx.2.1
  have hLarge : 1 / 2 ≤ ‖x.2.2‖ := hx.2.2.2
  have hNeg : x.2.2 = -x.2.1 := eq_neg_of_add_eq_zero_left hZero
  rw [hNeg, norm_neg] at hLarge
  linarith

theorem physicalFarProfilePoint_mem_compactDomain {ϑ : ℝ → ℝ} {κ δ : ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1)
    (hκ : 0 < κ) (hκ' : κ < 1 / 16) (hδ : 0 < δ) {p q r : Vec}
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hSupport : InLowFarTriadSupport ϑ κ δ p q r) :
    physicalFarProfilePoint p q ∈ farProfileCompactDomain := by
  have hQ : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hSmall := (lowFarTriadSupport_separated hCut hFlat hκ hκ' hδ hp hq hr hSupport).1
  have hz : ‖‖q‖⁻¹ • p‖ ≤ 1 / 4 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hQ.le), inv_mul_eq_div]
    apply (div_le_iff₀ hQ).mpr
    exact hSmall.trans (mul_le_mul_of_nonneg_right (by linarith) hQ.le)
  change unitRep p ∈ closedBall _ _ ∧ ‖q‖⁻¹ • p ∈ closedBall _ _ ∧
    unitRep q ∈ closedBall _ _ ∩ {θ : Vec | 1 / 2 ≤ ‖θ‖}
  simp only [mem_closedBall, dist_zero_right, mem_inter_iff, mem_setOf_eq, norm_unitRep p hp,
    norm_unitRep q hq]
  exact ⟨by norm_num, hz, by norm_num, by norm_num⟩

end Burnett.V10
