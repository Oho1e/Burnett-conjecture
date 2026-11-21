import Burnett.Analysis.AngularCaps.SmoothCapProfiles

set_option autoImplicit false
set_option maxHeartbeats 6500000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set Finset
open scoped ContDiff BigOperators

def capAngularMass (t : Finset Vec) (δ : ℝ) (ξ : Vec) : ℝ :=
  ∑ w ∈ t, capAngularProfile δ (3/4) 1 w ξ

/-- The normalization is positive even for frequencies outside every cap. -/
def capDenominator (t : Finset Vec) (δ : ℝ) (ξ : Vec) : ℝ :=
  capAngularMass t δ ξ + descendingProfile (1/4) (1/2) (capAngularMass t δ ξ)

theorem capAngularMass_nonneg (t : Finset Vec) (δ : ℝ) (ξ : Vec) :
    0 ≤ capAngularMass t δ ξ :=
  Finset.sum_nonneg fun w _ => (capAngularProfile_range _ _ _ w ξ).1

theorem capAngularProfile_le_mass {t : Finset Vec} (δ : ℝ) {w : Vec} (hw : w ∈ t) (ξ : Vec) :
    capAngularProfile δ (3/4) 1 w ξ ≤ capAngularMass t δ ξ :=
  Finset.single_le_sum (fun v _ => (capAngularProfile_range _ _ _ v ξ).1) hw

theorem capAngularMass_le_denominator (t : Finset Vec) (δ : ℝ) (ξ : Vec) :
    capAngularMass t δ ξ ≤ capDenominator t δ ξ := by
  exact le_add_of_nonneg_right (descendingProfile_range _ _ _).1

theorem capDenominator_uniform_pos (t : Finset Vec) (δ : ℝ) (ξ : Vec) :
    1/4 ≤ capDenominator t δ ξ := by
  by_cases h : capAngularMass t δ ξ ≤ 1/4
  · rw [capDenominator,descendingProfile_eq_one (by norm_num) h]
    linarith only [capAngularMass_nonneg t δ ξ]
  · exact (lt_of_not_ge h).le.trans (capAngularMass_le_denominator t δ ξ)

theorem capDenominator_eq_mass_of_one_le {t : Finset Vec} {δ : ℝ} {ξ : Vec}
    (h : 1 ≤ capAngularMass t δ ξ) : capDenominator t δ ξ = capAngularMass t δ ξ := by
  rw [capDenominator,descendingProfile_eq_zero (by norm_num)
    (show 1/2 ≤ capAngularMass t δ ξ by linarith only [h]),add_zero]

theorem capAngularMass_degreeZero (t : Finset Vec) (δ : ℝ) : DegreeZero (capAngularMass t δ) := by
  intro a ha ξ
  exact Finset.sum_congr rfl fun w _ => capAngularProfile_degreeZero _ _ _ w a ha ξ

theorem capDenominator_degreeZero (t : Finset Vec) (δ : ℝ) : DegreeZero (capDenominator t δ) := by
  intro a ha ξ
  rw [capDenominator,capDenominator,capAngularMass_degreeZero t δ a ha ξ]

theorem capDenominator_contDiffOn {t : Finset Vec} (hw : ∀ w ∈ t, w ≠ 0) (δ : ℝ) :
    ContDiffOn ℝ ∞ (capDenominator t δ) puncturedFrequency := by
  have hMass : ContDiffOn ℝ ∞ (capAngularMass t δ) puncturedFrequency :=
    ContDiffOn.sum fun w hwt => capAngularProfile_contDiffOn _ _ _ (hw w hwt)
  exact hMass.add ((descendingProfile_contDiff _ _).comp_contDiffOn hMass)

/-- The actual cap symbol on the punctured frequency space. Its assigned value
at the origin is zero. -/
def capMultiplier (t : Finset Vec) (m : Form) (δ η inner outer : ℝ) (w ξ : Vec) : ℝ := by
  classical
  exact if ξ = 0 then 0 else
    thinConeProfile m η inner outer ξ * (capAngularProfile δ (3/4) 1 w ξ/capDenominator t δ ξ)

/-- The enlarged angular cap is one through radius `4δ` and zero from
radius `5δ`. Its relative cone band is enlarged independently. -/
def enlargedCapMultiplier (m : Form) (δ η outer enlarged : ℝ) (w ξ : Vec) : ℝ := by
  classical
  exact if ξ = 0 then 0 else
    thinConeProfile m η outer enlarged ξ * capAngularProfile δ 4 5 w ξ

theorem capMultiplier_at_nonzero (t : Finset Vec) (m : Form) (δ η inner outer : ℝ) (w : Vec)
    {ξ : Vec} (hξ : ξ ≠ 0) :
    capMultiplier t m δ η inner outer w ξ =
      thinConeProfile m η inner outer ξ * (capAngularProfile δ (3/4) 1 w ξ/capDenominator t δ ξ) := by
  classical
  exact if_neg hξ

theorem enlargedCapMultiplier_at_nonzero (m : Form) (δ η outer enlarged : ℝ) (w : Vec)
    {ξ : Vec} (hξ : ξ ≠ 0) :
    enlargedCapMultiplier m δ η outer enlarged w ξ =
      thinConeProfile m η outer enlarged ξ * capAngularProfile δ 4 5 w ξ := by
  classical
  exact if_neg hξ

@[simp] theorem capMultiplier_zero (t : Finset Vec) (m : Form) (δ η inner outer : ℝ) (w : Vec) :
    capMultiplier t m δ η inner outer w 0 = 0 := by
  classical
  simp [capMultiplier]

@[simp] theorem enlargedCapMultiplier_zero (m : Form) (δ η outer enlarged : ℝ) (w : Vec) :
    enlargedCapMultiplier m δ η outer enlarged w 0 = 0 := by
  classical
  simp [enlargedCapMultiplier]

theorem capMultiplier_contDiffOn {t : Finset Vec} (ht : ∀ w ∈ t, w ≠ 0)
    (m : Form) (δ : ℝ) {η : ℝ} (hη : 0 < η) (inner outer : ℝ) {w : Vec} (hw : w ≠ 0) :
    ContDiffOn ℝ ∞ (capMultiplier t m δ η inner outer w) puncturedFrequency := by
  have hDen := capDenominator_contDiffOn ht δ
  have hPos (ξ : Vec) : 0 < capDenominator t δ ξ :=
    (show (0 : ℝ) < 1/4 by norm_num).trans_le (capDenominator_uniform_pos t δ ξ)
  have hCore := (thinConeProfile_contDiffOn m hη inner outer).mul
    ((capAngularProfile_contDiffOn δ (3/4) 1 hw).div hDen (fun ξ _ => (hPos ξ).ne'))
  exact hCore.congr fun ξ hξ => capMultiplier_at_nonzero t m δ η inner outer w hξ

theorem enlargedCapMultiplier_contDiffOn (m : Form) (δ : ℝ) {η : ℝ} (hη : 0 < η)
    (outer enlarged : ℝ) {w : Vec} (hw : w ≠ 0) :
    ContDiffOn ℝ ∞ (enlargedCapMultiplier m δ η outer enlarged w) puncturedFrequency := by
  have hCore := (thinConeProfile_contDiffOn m hη outer enlarged).mul (capAngularProfile_contDiffOn δ 4 5 hw)
  exact hCore.congr fun ξ hξ => enlargedCapMultiplier_at_nonzero m δ η outer enlarged w hξ

theorem capMultiplier_degreeZero (t : Finset Vec) (m : Form) (δ η inner outer : ℝ) (w : Vec) :
    DegreeZero (capMultiplier t m δ η inner outer w) := by
  intro a ha ξ
  by_cases hξ : ξ = 0
  · simp [hξ]
  · simp only [capMultiplier_at_nonzero _ _ _ _ _ _ w (smul_ne_zero ha hξ),
      capMultiplier_at_nonzero _ _ _ _ _ _ w hξ, thinConeProfile_degreeZero m η inner outer a ha ξ,
      capAngularProfile_degreeZero δ (3/4) 1 w a ha ξ, capDenominator_degreeZero t δ a ha ξ]

theorem enlargedCapMultiplier_degreeZero (m : Form) (δ η outer enlarged : ℝ) (w : Vec) :
    DegreeZero (enlargedCapMultiplier m δ η outer enlarged w) := by
  intro a ha ξ
  by_cases hξ : ξ = 0
  · simp [hξ]
  · simp only [enlargedCapMultiplier_at_nonzero m δ η outer enlarged w (smul_ne_zero ha hξ),
      enlargedCapMultiplier_at_nonzero m δ η outer enlarged w hξ, thinConeProfile_degreeZero m η outer enlarged a ha ξ,
      capAngularProfile_degreeZero δ 4 5 w a ha ξ]

theorem capMultiplier_range {t : Finset Vec} (m : Form) (δ η inner outer : ℝ) {w : Vec}
    (hw : w ∈ t) (ξ : Vec) :
    0 ≤ capMultiplier t m δ η inner outer w ξ ∧ capMultiplier t m δ η inner outer w ξ ≤ 1 := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  · rw [capMultiplier_at_nonzero t m δ η inner outer w hξ]
    have hPos := (show (0 : ℝ) < 1/4 by norm_num).trans_le (capDenominator_uniform_pos t δ ξ)
    have hCone := thinConeProfile_range m η inner outer ξ
    have hA := capAngularProfile_range δ (3/4) 1 w ξ
    have hR := div_nonneg hA.1 hPos.le
    have hUpper := (div_le_one hPos).mpr
      ((capAngularProfile_le_mass δ hw ξ).trans (capAngularMass_le_denominator t δ ξ))
    exact ⟨mul_nonneg hCone.1 hR,by simpa only [one_mul] using mul_le_mul hCone.2 hUpper hR zero_le_one⟩

theorem enlargedCapMultiplier_range (m : Form) (δ η outer enlarged : ℝ) (w ξ : Vec) :
    0 ≤ enlargedCapMultiplier m δ η outer enlarged w ξ ∧ enlargedCapMultiplier m δ η outer enlarged w ξ ≤ 1 := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  · rw [enlargedCapMultiplier_at_nonzero m δ η outer enlarged w hξ]
    have hCone := thinConeProfile_range m η outer enlarged ξ
    have hAng := capAngularProfile_range δ 4 5 w ξ
    exact ⟨mul_nonneg hCone.1 hAng.1,by simpa only [one_mul] using mul_le_mul hCone.2 hAng.2 hAng.1 zero_le_one⟩

theorem capMultiplier_partition_eq_one (t : Finset Vec) (m : Form) {δ η inner outer : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hIn : 0 ≤ inner) (hIO : inner < outer) {ξ : Vec} (hξ : ξ ≠ 0)
    (hCone : |quadratic m ξ| ≤ inner*η*‖ξ‖^2)
    (hCover : ∃ w ∈ t, projectiveWedgeSq ξ w ≤ ((3/4)*δ)^2) :
    ∑ w ∈ t, capMultiplier t m δ η inner outer w ξ = 1 := by
  obtain ⟨w,hw,hAngle⟩ := hCover
  have hOne := capAngularProfile_eq_one hδ (show (0 : ℝ) ≤ 3/4 by norm_num)
    (show (3/4 : ℝ) < 1 by norm_num) hAngle
  have hMass := capAngularProfile_le_mass δ hw ξ
  rw [hOne] at hMass
  calc
    _ = ∑ w ∈ t, thinConeProfile m η inner outer ξ *
        (capAngularProfile δ (3/4) 1 w ξ/capDenominator t δ ξ) :=
      Finset.sum_congr rfl fun z _ => capMultiplier_at_nonzero t m δ η inner outer z hξ
    _ = thinConeProfile m η inner outer ξ * (capAngularMass t δ ξ/capDenominator t δ ξ) := by
      simp only [capAngularMass,Finset.mul_sum,Finset.sum_div]
    _ = 1 := by
      rw [thinConeProfile_eq_one hη hIn hIO hξ hCone,capDenominator_eq_mass_of_one_le hMass,
        div_self ((zero_lt_one.trans_le hMass).ne'),mul_one]

theorem enlargedCapMultiplier_eq_one (m : Form) {δ η outer enlarged : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hOut : 0 ≤ outer) (hOE : outer < enlarged)
    {w ξ : Vec} (hξ : ξ ≠ 0) (hAngle : projectiveWedgeSq ξ w ≤ (4*δ)^2)
    (hCone : |quadratic m ξ| ≤ outer*η*‖ξ‖^2) :
    enlargedCapMultiplier m δ η outer enlarged w ξ = 1 := by
  rw [enlargedCapMultiplier_at_nonzero m δ η outer enlarged w hξ,
    thinConeProfile_eq_one hη hOut hOE hξ hCone,
    capAngularProfile_eq_one hδ (by norm_num) (by norm_num) hAngle,one_mul]

end Burnett.Analysis.ProjectiveNullCaps
