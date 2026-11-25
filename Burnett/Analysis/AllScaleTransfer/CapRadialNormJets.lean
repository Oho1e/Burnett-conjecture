import Burnett.Analysis.AngularCaps.CapFrequencyCoordinates
import Burnett.Analysis.AngularCaps.ParabolicProfileJets
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.Analysis.CapFourier

open Set Metric Burnett.Analysis.ProjectiveNullCaps
open scoped BigOperators ContDiff

abbrev RadialFrequencyMap := Space →L[ℝ] Space

/-- The manuscript's degree-zero radial factor. -/
def capRadialFactor (A : RadialFrequencyMap) (p : Space) : ℝ := ‖A p‖ / ‖p‖

/-- The physical ratio of two transformed frequencies. -/
def physicalRadialRatio (A : RadialFrequencyMap) (pq : Space × Space) : ℝ :=
  ‖A pq.1‖ / ‖A pq.2‖

def radialJetAnnulus (lo hi : ℝ) : Set Space := {p | lo ≤ ‖p‖ ∧ ‖p‖ ≤ hi}

theorem capRadialFactor_pos_smul (A : RadialFrequencyMap) {r : ℝ} (hr : 0 < r)
    (p : Space) : capRadialFactor A (r • p) = capRadialFactor A p := by
  rw [capRadialFactor, map_smul, norm_smul, norm_smul, Real.norm_of_nonneg hr.le]
  exact mul_div_mul_left _ _ hr.ne'

/-- The physical and transformed radial ratios differ by the quotient of the two angular factors. -/
theorem physicalRadialRatio_eq_normalized (A : RadialFrequencyMap) {p q : Space}
    (hp : p ≠ 0) (hq : q ≠ 0) (hAq : A q ≠ 0) :
    physicalRadialRatio A (p,q) =
      (‖p‖ / ‖q‖) * (capRadialFactor A (‖p‖⁻¹ • p) / capRadialFactor A (‖q‖⁻¹ • q)) := by
  have hp' : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hq' : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hAq' : 0 < ‖A q‖ := norm_pos_iff.mpr hAq
  rw [capRadialFactor_pos_smul A (inv_pos.mpr hp'), capRadialFactor_pos_smul A (inv_pos.mpr hq')]
  unfold capRadialFactor physicalRadialRatio
  dsimp only
  field_simp [hp'.ne', hq'.ne', hAq'.ne']

private def radialDomain : Set (RadialFrequencyMap × Space) :=
  {z | z.2 ≠ 0 ∧ z.1 z.2 ≠ 0}

private theorem radialDomain_open : IsOpen radialDomain :=
  (isOpen_ne_fun continuous_snd continuous_const).inter
    (isOpen_ne_fun (continuous_fst.clm_apply continuous_snd) continuous_const)

private theorem radialFactor_joint_contDiffOn :
    ContDiffOn ℝ ∞ (fun z : RadialFrequencyMap × Space => capRadialFactor z.1 z.2) radialDomain := by
  have hp : ContDiffOn ℝ ∞ (fun z : RadialFrequencyMap × Space => ‖z.2‖) radialDomain :=
    contDiff_snd.contDiffOn.norm ℝ (fun _ hz => hz.1)
  have hA : ContDiffOn ℝ ∞ (fun z : RadialFrequencyMap × Space => ‖z.1 z.2‖) radialDomain :=
    (contDiff_fst.clm_apply contDiff_snd).contDiffOn.norm ℝ (fun _ hz => hz.2)
  exact hA.div hp (fun _ hz => norm_ne_zero_iff.mpr hz.1)

private theorem radialFactorInv_joint_contDiffOn :
    ContDiffOn ℝ ∞ (fun z : RadialFrequencyMap × Space => (capRadialFactor z.1 z.2)⁻¹) radialDomain :=
  radialFactor_joint_contDiffOn.inv (fun _ hz =>
    div_ne_zero (norm_ne_zero_iff.mpr hz.2) (norm_ne_zero_iff.mpr hz.1))

private def radialPairDomain : Set (RadialFrequencyMap × (Space × Space)) :=
  {z | z.1 z.2.1 ≠ 0 ∧ z.1 z.2.2 ≠ 0}

private theorem radialPairDomain_open : IsOpen radialPairDomain :=
  (isOpen_ne_fun (continuous_fst.clm_apply continuous_snd.fst) continuous_const).inter
    (isOpen_ne_fun (continuous_fst.clm_apply continuous_snd.snd) continuous_const)

private theorem physicalRatio_joint_contDiffOn :
    ContDiffOn ℝ ∞ (fun z : RadialFrequencyMap × (Space × Space) => physicalRadialRatio z.1 z.2)
      radialPairDomain := by
  have hp : ContDiffOn ℝ ∞ (fun z : RadialFrequencyMap × (Space × Space) => ‖z.1 z.2.1‖)
      radialPairDomain :=
    (contDiff_fst.clm_apply contDiff_snd.fst).contDiffOn.norm ℝ (fun _ hz => hz.1)
  have hq : ContDiffOn ℝ ∞ (fun z : RadialFrequencyMap × (Space × Space) => ‖z.1 z.2.2‖)
      radialPairDomain :=
    (contDiff_fst.clm_apply contDiff_snd.snd).contDiffOn.norm ℝ (fun _ hz => hz.2)
  exact hp.div hq (fun _ hz => norm_ne_zero_iff.mpr hz.2)

theorem physicalRadialRatio_contDiffAt (A : RadialFrequencyMap) {p q : Space}
    (hp : A p ≠ 0) (hq : A q ≠ 0) : ContDiffAt ℝ ∞ (physicalRadialRatio A) (p,q) := by
  have h : (A,(p,q)) ∈ radialPairDomain := ⟨hp,hq⟩
  exact (physicalRatio_joint_contDiffOn.contDiffAt (radialPairDomain_open.mem_nhds h)).comp
    (p,q) (contDiffAt_const.prodMk contDiffAt_id)

/-- A closed collection of map-frequency pairs with the lower bound tested at the listed frequency. -/
private def radialData (M L lo hi : ℝ) : Set (RadialFrequencyMap × Space) :=
  {z | ‖z.1‖ ≤ M ∧ z.2 ∈ radialJetAnnulus lo hi ∧ L * ‖z.2‖ ≤ ‖z.1 z.2‖}

private theorem radialData_isCompact (M L lo hi : ℝ) : IsCompact (radialData M L lo hi) := by
  have hAnnulus : IsClosed (radialJetAnnulus lo hi) :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  have hClosed : IsClosed (radialData M L lo hi) :=
    (isClosed_le continuous_fst.norm continuous_const).inter
      ((hAnnulus.preimage continuous_snd).inter (isClosed_le (continuous_const.mul continuous_snd.norm)
        (continuous_fst.clm_apply continuous_snd).norm))
  refine ((isCompact_closedBall (0 : RadialFrequencyMap) M).prod
    (isCompact_closedBall (0 : Space) hi)).of_isClosed_subset hClosed ?_
  intro z hz
  exact ⟨mem_closedBall_zero_iff.mpr hz.1, mem_closedBall_zero_iff.mpr hz.2.1.2⟩

private theorem radialData_subset_domain {M L lo hi : ℝ} (hL : 0 < L) (hlo : 0 < lo) :
    radialData M L lo hi ⊆ radialDomain := by
  intro z hz
  have hnorm : 0 < ‖z.2‖ := hlo.trans_le hz.2.1.1
  exact ⟨norm_pos_iff.mp hnorm, norm_pos_iff.mp ((mul_pos hL hnorm).trans_le hz.2.2)⟩

private def radialPairData (M L lo hi : ℝ) : Set (RadialFrequencyMap × (Space × Space)) :=
  {z | (z.1,z.2.1) ∈ radialData M L lo hi ∧ (z.1,z.2.2) ∈ radialData M L lo hi}

private theorem radialPairData_isCompact (M L lo hi : ℝ) : IsCompact (radialPairData M L lo hi) := by
  have hOne := (radialData_isCompact M L lo hi).isClosed
  have hClosed : IsClosed (radialPairData M L lo hi) :=
    (hOne.preimage (continuous_fst.prodMk continuous_snd.fst)).inter
      (hOne.preimage (continuous_fst.prodMk continuous_snd.snd))
  have hBox := (isCompact_closedBall (0 : RadialFrequencyMap) M).prod
    ((isCompact_closedBall (0 : Space) hi).prod (isCompact_closedBall (0 : Space) hi))
  refine hBox.of_isClosed_subset hClosed ?_
  intro z hz
  exact ⟨mem_closedBall_zero_iff.mpr hz.1.1, mem_closedBall_zero_iff.mpr hz.1.2.1.2,
    mem_closedBall_zero_iff.mpr hz.2.2.1.2⟩

private theorem radialPairData_subset_domain {M L lo hi : ℝ} (hL : 0 < L) (hlo : 0 < lo) :
    radialPairData M L lo hi ⊆ radialPairDomain := by
  intro z hz
  exact ⟨(radialData_subset_domain hL hlo hz.1).2, (radialData_subset_domain hL hlo hz.2).2⟩

/-- Every order up to the prescribed one has a common bound on the controlled annuli.
Maps are allowed to have kernels away from the chosen frequencies. -/
theorem exists_uniform_radial_norm_jets (M L lo hi : ℝ) (hL : 0 < L) (hlo : 0 < lo)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ A : RadialFrequencyMap, ‖A‖ ≤ M →
      (∀ j ≤ n, ∀ p ∈ radialJetAnnulus lo hi, L * ‖p‖ ≤ ‖A p‖ →
        ‖iteratedFDeriv ℝ j (capRadialFactor A) p‖ ≤ C ∧
        ‖iteratedFDeriv ℝ j (fun x => (capRadialFactor A x)⁻¹) p‖ ≤ C) ∧
      (∀ j ≤ n, ∀ p ∈ radialJetAnnulus lo hi, ∀ q ∈ radialJetAnnulus lo hi,
        L * ‖p‖ ≤ ‖A p‖ → L * ‖q‖ ≤ ‖A q‖ →
        ‖iteratedFDeriv ℝ j (physicalRadialRatio A) (p,q)‖ ≤ C) := by
  have hK := radialData_isCompact M L lo hi
  have hDom := radialData_subset_domain (M := M) (hi := hi) hL hlo
  have hK₂ := radialPairData_isCompact M L lo hi
  have hDom₂ := radialPairData_subset_domain (M := M) (hi := hi) hL hlo
  choose Cb hb cb using fun j : Fin (n + 1) =>
    exists_uniform_right_slice_iteratedFDeriv radialDomain_open radialFactor_joint_contDiffOn hK hDom j.val
  choose Ci hi' ci using fun j : Fin (n + 1) =>
    exists_uniform_right_slice_iteratedFDeriv radialDomain_open radialFactorInv_joint_contDiffOn hK hDom j.val
  choose Cr hr cr using fun j : Fin (n + 1) =>
    exists_uniform_right_slice_iteratedFDeriv radialPairDomain_open physicalRatio_joint_contDiffOn hK₂ hDom₂ j.val
  let term (j : Fin (n + 1)) := Cb j + Ci j + Cr j
  let C := 1 + ∑ j, term j
  have hn (j : Fin (n + 1)) : 0 ≤ term j := by
    dsimp only [term]
    linarith only [hb j, hi' j, hr j]
  have bound (j : Fin (n + 1)) : Cb j ≤ C ∧ Ci j ≤ C ∧ Cr j ≤ C := by
    have hterm : term j ≤ ∑ k, term k := Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ j)
    dsimp only [term] at hterm
    dsimp only [C]
    exact ⟨by linarith only [hterm, hi' j, hr j], by linarith only [hterm, hb j, hr j],
      by linarith only [hterm, hb j, hi' j]⟩
  refine ⟨C, add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun j _ => hn j)), ?_⟩
  intro A hA
  constructor
  · intro j hj p hp hAp
    let k : Fin (n + 1) := ⟨j,Nat.lt_succ_of_le hj⟩
    have hData : (A,p) ∈ radialData M L lo hi := ⟨hA,hp,hAp⟩
    exact ⟨(cb k (A,p) hData).trans (bound k).1, (ci k (A,p) hData).trans (bound k).2.1⟩
  · intro j hj p hp q hq hAp hAq
    let k : Fin (n + 1) := ⟨j,Nat.lt_succ_of_le hj⟩
    have hData : (A,(p,q)) ∈ radialPairData M L lo hi := ⟨⟨hA,hp,hAp⟩,⟨hA,hq,hAq⟩⟩
    exact (cr k (A,(p,q)) hData).trans (bound k).2.2

end Burnett.Analysis.CapFourier
