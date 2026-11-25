import Burnett.Analysis.AllScaleTransfer.ActualCapBoxExtension
import Burnett.Analysis.AllScaleTransfer.EndpointAngularTraceSeries

set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section

namespace Burnett.A05.BoxFourier

open Set Metric Burnett.Analysis CapFourier

abbrev CapSigns := Bool × Bool

/-- The positive axial coordinate on either signed sheet. -/
def signedAxis (positive : Bool) (x : Frequency) : ℝ := if positive then x 0 else -(x 0)

private theorem continuous_signedAxis (positive : Bool) : Continuous (signedAxis positive) := by
  have hc : Continuous (fun x : Frequency => x 0) := frequencyCoordinates.continuous.fst
  cases positive
  · exact hc.neg
  · exact hc

theorem signedAxis_le_abs (positive : Bool) (x : Frequency) : signedAxis positive x ≤ |x 0| := by
  cases positive
  · exact neg_le_abs _
  · exact le_abs_self _

/-- The compact sector for one normalized annular input. -/
def signedClosedAnnulus (α : ℝ) (positive : Bool) : Set Frequency :=
  {x | ((1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2) ∧ α * ‖x‖ ≤ signedAxis positive x}

/-- The fixed open annulus and smaller cone margin for the same sign. -/
def signedOpenAnnulus (α : ℝ) (positive : Bool) : Set Frequency :=
  {x | ((1 / 4 : ℝ) < ‖x‖ ∧ ‖x‖ < 3) ∧ (α / 2) * ‖x‖ < signedAxis positive x}

def signedPairK (α : ℝ) (signs : CapSigns) : Set FrequencyPair :=
  signedClosedAnnulus α signs.1 ×ˢ signedClosedAnnulus α signs.2

def signedPairV (α : ℝ) (signs : CapSigns) : Set FrequencyPair :=
  signedOpenAnnulus α signs.1 ×ˢ signedOpenAnnulus α signs.2

private theorem isCompact_signedClosedAnnulus (α : ℝ) (positive : Bool) :
    IsCompact (signedClosedAnnulus α positive) := by
  have hc : IsClosed (signedClosedAnnulus α positive) :=
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)).inter
      (isClosed_le (continuous_const.mul continuous_norm) (continuous_signedAxis positive))
  exact (isCompact_closedBall (0 : Frequency) 2).of_isClosed_subset hc
    (fun _ hx => mem_closedBall_zero_iff.mpr hx.1.2)

private theorem isOpen_signedOpenAnnulus (α : ℝ) (positive : Bool) :
    IsOpen (signedOpenAnnulus α positive) :=
  ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)).inter
    (isOpen_lt (continuous_const.mul continuous_norm) (continuous_signedAxis positive))

private theorem signedClosedAnnulus_subset_open {α : ℝ} (hα : 0 < α) (positive : Bool) :
    signedClosedAnnulus α positive ⊆ signedOpenAnnulus α positive := by
  intro x hx
  have hp := (show (0 : ℝ) < 1 / 2 by norm_num).trans_le hx.1.1
  exact ⟨⟨(by norm_num : (1 / 4 : ℝ) < 1 / 2).trans_le hx.1.1,
    hx.1.2.trans_lt (by norm_num)⟩,
    (mul_lt_mul_of_pos_right (half_lt_self hα) hp).trans_le hx.2⟩

private theorem signedOpenAnnulus_subset_fixedCone (α : ℝ) (positive : Bool) :
    signedOpenAnnulus α positive ⊆ fixedConeAnnulus (1 / 4) 3 (α / 2) := by
  intro x hx
  exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, hx.2.le.trans (signedAxis_le_abs positive x)⟩

private theorem unit_axis_ge {x : Frequency} (hx : x ≠ 0) {α : ℝ} (hα : α * ‖x‖ ≤ |x 0|) :
    α ≤ |endpointDirection x 0| := by
  have hn := norm_pos_iff.mpr hx
  change α ≤ |‖x‖⁻¹ * x 0|
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_eq_div]
  exact (le_div_iff₀ hn).mpr hα

/-- Four fixed compact and open radial chart pairs, with one common angular
margin in both slots. -/
theorem exists_signed_annular_box_charts {α : ℝ} (hα : 0 < α) (hαone : α ≤ 1) :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧ R < 1 ∧
      ∀ signs : CapSigns,
        IsCompact (signedPairK α signs) ∧ IsOpen (signedPairV α signs) ∧
        signedPairK α signs ⊆ signedPairV α signs ∧
        signedPairV α signs ⊆
          fixedConeAnnulus (1 / 4) 3 (α / 2) ×ˢ fixedConeAnnulus (1 / 4) 3 (α / 2) ∧
        MapsTo (normalizedPairAngles endpointTail endpointTail) (signedPairV α signs)
          (ball (0 : EndpointAngle) R ×ˢ ball (0 : EndpointAngle) R) := by
  have hαhalf : 0 < α / 2 := half_pos hα
  obtain ⟨r, R, hr, hrR, hR, bounds⟩ :=
    exists_endpointTail_radii hαhalf (by linarith only [hα, hαone] : α / 2 ≤ 1)
  have angles (positive : Bool) (x : Frequency) (hx : x ∈ signedOpenAnnulus α positive) :
      endpointTail (endpointDirection x) ∈ ball (0 : EndpointAngle) R := by
    have hxne : x ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 4).trans hx.1.1)
    have ha : (α / 2) * ‖x‖ ≤ |x 0| := hx.2.le.trans (signedAxis_le_abs positive x)
    have hRadius := (bounds _ (endpointDirection_mem_sphere hxne) (unit_axis_ge hxne ha)).trans_lt hrR
    exact mem_ball_zero_iff.mpr hRadius
  refine ⟨r, R, hr, hrR, hR, fun signs => ?_⟩
  exact ⟨(isCompact_signedClosedAnnulus α signs.1).prod (isCompact_signedClosedAnnulus α signs.2),
    (isOpen_signedOpenAnnulus α signs.1).prod (isOpen_signedOpenAnnulus α signs.2),
    Set.prod_mono (signedClosedAnnulus_subset_open hα signs.1) (signedClosedAnnulus_subset_open hα signs.2),
    Set.prod_mono (signedOpenAnnulus_subset_fixedCone α signs.1)
      (signedOpenAnnulus_subset_fixedCone α signs.2),
    fun pq hpq => ⟨angles signs.1 pq.1 hpq.1, angles signs.2 pq.2 hpq.2⟩⟩

private theorem existsUnique_signedClosedAnnulus {α : ℝ} (hα : 0 < α) {x : Frequency}
    (hlo : (1 / 2 : ℝ) ≤ ‖x‖) (hhi : ‖x‖ ≤ 2) (ha : α * ‖x‖ ≤ |x 0|) :
    ∃! sign : Bool, x ∈ signedClosedAnnulus α sign := by
  have hAxis : 0 < α * ‖x‖ := mul_pos hα ((by norm_num : (0 : ℝ) < 1 / 2).trans_le hlo)
  by_cases hx : 0 ≤ x 0
  · refine ⟨true, ⟨⟨hlo, hhi⟩, ?_⟩, fun sign hsign => ?_⟩
    · change α * ‖x‖ ≤ x 0
      rwa [abs_of_nonneg hx] at ha
    · cases sign
      · have h := hsign.2
        change α * ‖x‖ ≤ -(x 0) at h
        exfalso
        linarith only [h, hx, hAxis]
      · rfl
  · have hneg := lt_of_not_ge hx
    refine ⟨false, ⟨⟨hlo, hhi⟩, ?_⟩, fun sign hsign => ?_⟩
    · change α * ‖x‖ ≤ -(x 0)
      rwa [abs_of_neg hneg] at ha
    · cases sign
      · rfl
      · have h := hsign.2
        change α * ‖x‖ ≤ x 0 at h
        exfalso
        linarith only [h, hneg, hAxis]

theorem existsUnique_signedPairK {α : ℝ} (hα : 0 < α) {x y : Frequency}
    (hx : (1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2) (hy : (1 / 2 : ℝ) ≤ ‖y‖ ∧ ‖y‖ ≤ 2)
    (hxa : α * ‖x‖ ≤ |x 0|) (hya : α * ‖y‖ ≤ |y 0|) :
    ∃! signs : CapSigns, (x, y) ∈ signedPairK α signs := by
  obtain ⟨sx, hxs, ux⟩ := existsUnique_signedClosedAnnulus hα hx.1 hx.2 hxa
  obtain ⟨sy, hys, uy⟩ := existsUnique_signedClosedAnnulus hα hy.1 hy.2 hya
  exact ⟨(sx, sy), ⟨hxs, hys⟩, fun signs hs => Prod.ext (ux signs.1 hs.1) (uy signs.2 hs.2)⟩

/-- Inverse angular coordinates in the signed hemisphere. -/
def signedChartLift (positive : Bool) (u : EndpointAngle) : Frequency :=
  WithLp.toLp 2 (Fin.cases
    (if positive then Real.sqrt (1 - ‖u‖^2) else -Real.sqrt (1 - ‖u‖^2))
    (fun i : Fin 3 => u i))

theorem endpointTail_signedChartLift (positive : Bool) (u : EndpointAngle) :
    endpointTail (signedChartLift positive u) = u := by
  ext i
  rfl

theorem signedChartLift_endpointTail (positive : Bool) {x : Frequency}
    (hSphere : x ∈ sphere (0 : Frequency) 1) (hSign : 0 < signedAxis positive x) :
    signedChartLift positive (endpointTail x) = x := by
  have head := endpointTail_head_abs hSphere
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · cases positive
    · change 0 < -(x 0) at hSign
      change -Real.sqrt (1 - ‖endpointTail x‖^2) = x 0
      rw [← head, abs_of_neg (neg_pos.mp hSign), neg_neg]
    · change 0 < x 0 at hSign
      change Real.sqrt (1 - ‖endpointTail x‖^2) = x 0
      rw [← head, abs_of_pos hSign]
  · rfl

theorem signedChartLift_unitSphere (positive : Bool) {u : EndpointAngle} (hu : ‖u‖ < 1) :
    signedChartLift positive u ∈ sphere (0 : Frequency) 1 ∧
      0 < signedAxis positive (signedChartLift positive u) := by
  have hsq : ‖u‖^2 < (1 : ℝ)^2 := (sq_lt_sq₀ (norm_nonneg _) zero_le_one).mpr hu
  have hPos : 0 < 1 - ‖u‖^2 := sub_pos.mpr (hsq.trans_le (by norm_num))
  let x := signedChartLift positive u
  have tail : endpointTail x = u := endpointTail_signedChartLift positive u
  have head : (x 0)^2 = 1 - ‖u‖^2 := by
    cases positive
    · change (-Real.sqrt (1 - ‖u‖^2))^2 = _
      rw [neg_sq, Real.sq_sqrt hPos.le]
    · exact Real.sq_sqrt hPos.le
  have hNorm := endpointTail_norm_sq x
  rw [tail, head] at hNorm
  have hn : ‖x‖^2 = (1 : ℝ)^2 := by linarith only [hNorm]
  refine ⟨mem_sphere_zero_iff_norm.mpr ((sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hn), ?_⟩
  cases positive
  · change 0 < -(-Real.sqrt (1 - ‖u‖^2))
    rw [neg_neg]
    exact Real.sqrt_pos.2 hPos
  · exact Real.sqrt_pos.2 hPos

/-- The angular variables in the same joined box are the tails of the
directions of the unscaled annular inputs. -/
theorem normalized_signed_box_angles (i j : ℤ) (p q : Frequency) :
    let z := joinedInputs (((2 : ℝ)^(-i)) • p) (((2 : ℝ)^(-j)) • q)
    normalizedPairAngles endpointTail endpointTail (boxToPair z) =
      (endpointTail (endpointDirection p), endpointTail (endpointDirection q)) := by
  intro z
  dsimp only [z]
  rw [boxToPair_joined]
  change (endpointTail (endpointDirection (((2 : ℝ)^(-i)) • p)),
    endpointTail (endpointDirection (((2 : ℝ)^(-j)) • q))) = _
  rw [endpointDirection_pos_smul _ (by positivity), endpointDirection_pos_smul _ (by positivity)]

end Burnett.A05.BoxFourier
