import Burnett.Analysis.AllScaleTransfer.CapAxialChartBudget
import Burnett.Analysis.AllScaleTransfer.ActualCapSignedBoxes
import Burnett.Analysis.AllScaleTransfer.FixedAnnularCutoff
import Burnett.Analysis.AllScaleTransfer.CapRadialNormJets

set_option autoImplicit false
set_option maxHeartbeats 3900000
noncomputable section

namespace Burnett.A05

open Set Metric Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier
open scoped ContDiff

/-- The existing signed angular domain, with a radial annulus and an open
axial margin for the true physical ratio. -/
def capCorrectionSlot (α R : ℝ) : Set E :=
  {p | (1 / 4 : ℝ) < ‖p‖ ∧ ‖p‖ < 3 ∧ (α/4)*‖p‖ < |p 0|} ∩
    {p | endpointTail (endpointDirection p) ∈ ball (0 : EndpointAngle) R}

def capCorrectionDomain (α R : ℝ) : Set BoxSpace :=
  boxToPair ⁻¹' (capCorrectionSlot α R ×ˢ capCorrectionSlot α R)

private theorem capCorrectionSlot_open (α R : ℝ) : IsOpen (capCorrectionSlot α R) := by
  let C : Set E := {p | (1 / 4 : ℝ) < ‖p‖ ∧ ‖p‖ < 3 ∧ (α/4)*‖p‖ < |p 0|}
  have axis : Continuous (fun p : E => p 0) := frequencyCoordinates.continuous.fst
  have hC : IsOpen C := (isOpen_lt continuous_const continuous_norm).inter
    ((isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt (continuous_const.mul continuous_norm) axis.abs))
  have direction : ContinuousOn endpointDirection C :=
    endpointDirection_contDiffOn.continuousOn.mono (fun _ hz =>
      norm_pos_iff.mp ((by norm_num : (0:ℝ) < 1/4).trans hz.1))
  exact (endpointTail.continuous.comp_continuousOn direction).isOpen_inter_preimage hC isOpen_ball

theorem capCorrectionDomain_open (α R : ℝ) : IsOpen (capCorrectionDomain α R) :=
  ((capCorrectionSlot_open α R).prod (capCorrectionSlot_open α R)).preimage boxToPair.continuous

theorem capCorrectionDomain_left_right {α R : ℝ} {z : BoxSpace} (hz : z ∈ capCorrectionDomain α R) :
    firstInput z ∈ capCorrectionSlot α R ∧ secondInput z ∈ capCorrectionSlot α R := hz

theorem capCorrectionSlot_ne_zero {α R : ℝ} {p : E} (hp : p ∈ capCorrectionSlot α R) : p ≠ 0 :=
  norm_pos_iff.mp ((by norm_num : (0:ℝ) < 1/4).trans hp.1.1)

private theorem correction_unit_axis {p : E} (hp : p ≠ 0) {a : ℝ} (ha : a*‖p‖ ≤ |p 0|) :
    a ≤ |endpointDirection p 0| := by
  have hn := norm_pos_iff.mpr hp
  change a ≤ |‖p‖⁻¹ * p 0|
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr hn.le),inv_mul_eq_div]
  exact (le_div_iff₀ hn).mpr ha

/-- A single fixed box cutoff is one on every active two-window pair. It
uses the angular margin already supplied by the actual axial window. -/
theorem exists_capCorrection_domain_cutoff (α r R : ℝ) (hα : 0 < α) (hrR : r < R)
    (tail : ∀ x ∈ sphere (0 : E) 1, α/2 ≤ |x 0| → ‖endpointTail x‖ ≤ r) :
    ∃ β : BoxSpace → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ capCorrectionDomain α R ∧
      ∀ p q : E, endpointHighProfile p ≠ 0 → endpointHighProfile q ≠ 0 →
        axialCapPairWindow α (p,q) ≠ 0 → β (joinedInputs p q) = 1 := by
  let K : Set E := radialJetAnnulus (1/2) 2 ∩ {p | (α/2)*‖p‖ ≤ |p 0|}
  let V := capCorrectionSlot α R
  have axis : Continuous (fun p : E => p 0) := frequencyCoordinates.continuous.fst
  have closedK : IsClosed K :=
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)).inter
      (isClosed_le (continuous_const.mul continuous_norm) axis.abs)
  have compactK : IsCompact K := (isCompact_closedBall (0 : E) 2).of_isClosed_subset closedK
    (fun _ hz => mem_closedBall_zero_iff.mpr hz.1.2)
  have hs : IsOpen V := capCorrectionSlot_open α R
  have KV : K ⊆ V := by
    intro p hp
    have hn : 0 < ‖p‖ := (by norm_num : (0:ℝ) < 1/2).trans_le hp.1.1
    have htail := tail _ (endpointDirection_mem_sphere (norm_pos_iff.mp hn))
      (correction_unit_axis (norm_pos_iff.mp hn) hp.2)
    exact ⟨⟨(by norm_num : (1/4:ℝ) < 1/2).trans_le hp.1.1, hp.1.2.trans_lt (by norm_num),
      (mul_lt_mul_of_pos_right (by linarith only [hα] : α/4 < α/2) hn).trans_le hp.2⟩,
      mem_ball_zero_iff.mpr (htail.trans_lt hrR)⟩
  obtain ⟨β₀, smooth, compactβ₀, suppβ₀, one⟩ := exists_fixed_annular_cutoff
    (compactK.prod compactK) (hs.prod hs) (Set.prod_mono KV KV)
  let β : BoxSpace → ℝ := β₀ ∘ boxToPair
  let supportBox := boxToPair.symm '' tsupport β₀
  have hCompact : IsCompact supportBox := compactβ₀.image boxToPair.symm.continuous
  have suppBox : tsupport β ⊆ supportBox := by
    apply closure_minimal ?_ hCompact.isClosed
    intro z hz
    exact ⟨boxToPair z,subset_tsupport _ hz,boxToPair.symm_apply_apply z⟩
  have inDomain : supportBox ⊆ capCorrectionDomain α R := by
    rintro z ⟨p,hp,rfl⟩
    change boxToPair (boxToPair.symm p) ∈ V ×ˢ V
    rw [boxToPair.apply_symm_apply]
    exact suppβ₀ hp
  refine ⟨β,smooth.comp boxToPair.contDiff,
    hCompact.of_isClosed_subset isClosed_closure suppBox,suppBox.trans inDomain,?_⟩
  intro p q hp hq hw
  have hpR := endpointHighProfile_properties.2.2 p hp
  have hqR := endpointHighProfile_properties.2.2 q hq
  have hpC := (axialCapWindow_nonzero_cone hα (left_ne_zero_of_mul hw)).2.le
  have hqC := (axialCapWindow_nonzero_cone hα (right_ne_zero_of_mul hw)).2.le
  change β₀ (boxToPair (joinedInputs p q)) = 1
  rw [boxToPair_joined]
  exact one (p,q) ⟨⟨⟨hpR.1.le,hpR.2.le⟩,hpC⟩,⟨⟨hqR.1.le,hqR.2.le⟩,hqC⟩⟩

end Burnett.A05
