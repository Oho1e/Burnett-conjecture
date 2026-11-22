import Burnett.Analysis.AngularCaps.ThinConeCaps
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set
open scoped ContDiff BigOperators RealInnerProductSpace

def puncturedFrequency : Set Vec := {ξ | ξ ≠ 0}

theorem isOpen_puncturedFrequency : IsOpen puncturedFrequency :=
  isOpen_compl_singleton

def DegreeZero (b : Vec → ℝ) : Prop :=
  ∀ (t : ℝ), t ≠ 0 → ∀ ξ, b (t • ξ) = b ξ

/-- A fixed smooth profile which is one below its lower threshold and zero
above its upper threshold. -/
def descendingProfile (lower upper x : ℝ) : ℝ :=
  Real.smoothTransition ((upper-x)/(upper-lower))

theorem descendingProfile_contDiff (lower upper : ℝ) :
    ContDiff ℝ ∞ (descendingProfile lower upper) := by
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)

theorem descendingProfile_range (lower upper x : ℝ) :
    0 ≤ descendingProfile lower upper x ∧ descendingProfile lower upper x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem descendingProfile_eq_one {lower upper x : ℝ} (h : lower < upper) (hx : x ≤ lower) :
    descendingProfile lower upper x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (sub_pos.mpr h)).mpr
  linarith only [hx]

theorem descendingProfile_eq_zero {lower upper x : ℝ} (h : lower < upper) (hx : upper ≤ x) :
    descendingProfile lower upper x = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx)
    (sub_nonneg.mpr h.le))

theorem descendingProfile_nonzero_lt {lower upper x : ℝ} (h : lower < upper)
    (hx : descendingProfile lower upper x ≠ 0) : x < upper :=
  lt_of_not_ge fun h' => hx (descendingProfile_eq_zero h h')

theorem projectiveWedgeSq_smul_left (t : ℝ) (ht : t ≠ 0) (x y : Vec) :
    projectiveWedgeSq (t • x) y = projectiveWedgeSq x y := by
  have hw : coordinateWedgeSq (t • x) y = t^2 * coordinateWedgeSq x y := by
    simp only [coordinateWedgeSq_eq_gram,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,real_inner_smul_left]
    ring
  unfold projectiveWedgeSq
  rw [hw,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,mul_assoc,mul_div_mul_left _ _ (pow_ne_zero _ ht)]

def scaledConeRatio (m : Form) (η : ℝ) (ξ : Vec) : ℝ :=
  quadratic m ξ/(η*‖ξ‖^2)

theorem scaledConeRatio_smul (m : Form) (η t : ℝ) (ht : t ≠ 0) (ξ : Vec) :
    scaledConeRatio m η (t • ξ) = scaledConeRatio m η ξ := by
  unfold scaledConeRatio
  simp only [quadratic_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [show η*(t^2*‖ξ‖^2) = t^2*(η*‖ξ‖^2) by ring,
    mul_div_mul_left _ _ (pow_ne_zero _ ht)]

private theorem coord_contDiff (j : Index) : ContDiff ℝ ∞ (fun x : Vec => x j) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Index => ℝ) j).contDiff

theorem quadratic_contDiff (m : Form) : ContDiff ℝ ∞ (quadratic m) := by
  unfold quadratic pairing rowValue
  exact ContDiff.sum fun j _ =>
    (ContDiff.sum fun i _ => contDiff_const.mul (coord_contDiff i)).mul (coord_contDiff j)

theorem projectiveWedgeSq_contDiffOn_left {w : Vec} (hw : w ≠ 0) :
    ContDiffOn ℝ ∞ (fun ξ => projectiveWedgeSq ξ w) puncturedFrequency := by
  have hNorm : ContDiff ℝ ∞ (fun ξ : Vec => ‖ξ‖^2*‖w‖^2) :=
    (contDiff_id.norm_sq ℝ).mul contDiff_const
  have hInner : ContDiff ℝ ∞ (fun ξ : Vec => ⟪ξ,w⟫) :=
    contDiff_id.inner ℝ contDiff_const
  simp only [projectiveWedgeSq,coordinateWedgeSq_eq_gram]
  exact (hNorm.sub (hInner.pow 2)).contDiffOn.div hNorm.contDiffOn (fun ξ hξ =>
    mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr hξ)) (pow_ne_zero _ (norm_ne_zero_iff.mpr hw)))

theorem scaledConeRatio_contDiffOn (m : Form) {η : ℝ} (hη : 0 < η) :
    ContDiffOn ℝ ∞ (scaledConeRatio m η) puncturedFrequency := by
  exact (quadratic_contDiff m).contDiffOn.div (contDiff_const.mul (contDiff_id.norm_sq ℝ)).contDiffOn
    (fun ξ hξ => mul_ne_zero hη.ne' (pow_ne_zero _ (norm_ne_zero_iff.mpr hξ)))

/-- The angular factor uses the manuscript's normalized squared wedge angle. -/
def capAngularProfile (δ inner outer : ℝ) (w ξ : Vec) : ℝ :=
  descendingProfile (inner^2) (outer^2) (projectiveWedgeSq ξ w/δ^2)

/-- Squaring the relative quadratic value preserves smoothness at the real cone. -/
def thinConeProfile (m : Form) (η inner outer : ℝ) (ξ : Vec) : ℝ :=
  descendingProfile (inner^2) (outer^2) ((scaledConeRatio m η ξ)^2)

theorem capAngularProfile_degreeZero (δ inner outer : ℝ) (w : Vec) :
    DegreeZero (capAngularProfile δ inner outer w) := by
  intro t ht ξ
  rw [capAngularProfile,capAngularProfile,projectiveWedgeSq_smul_left t ht]

theorem thinConeProfile_degreeZero (m : Form) (η inner outer : ℝ) :
    DegreeZero (thinConeProfile m η inner outer) := by
  intro t ht ξ
  rw [thinConeProfile,thinConeProfile,scaledConeRatio_smul m η t ht]

theorem capAngularProfile_contDiffOn (δ inner outer : ℝ) {w : Vec} (hw : w ≠ 0) :
    ContDiffOn ℝ ∞ (capAngularProfile δ inner outer w) puncturedFrequency :=
  (descendingProfile_contDiff _ _).comp_contDiffOn ((projectiveWedgeSq_contDiffOn_left hw).div_const _)

theorem thinConeProfile_contDiffOn (m : Form) {η : ℝ} (hη : 0 < η) (inner outer : ℝ) :
    ContDiffOn ℝ ∞ (thinConeProfile m η inner outer) puncturedFrequency :=
  (descendingProfile_contDiff _ _).comp_contDiffOn ((scaledConeRatio_contDiffOn m hη).pow 2)

theorem capAngularProfile_range (δ inner outer : ℝ) (w ξ : Vec) :
    0 ≤ capAngularProfile δ inner outer w ξ ∧ capAngularProfile δ inner outer w ξ ≤ 1 :=
  descendingProfile_range _ _ _

theorem thinConeProfile_range (m : Form) (η inner outer : ℝ) (ξ : Vec) :
    0 ≤ thinConeProfile m η inner outer ξ ∧ thinConeProfile m η inner outer ξ ≤ 1 :=
  descendingProfile_range _ _ _

theorem capAngularProfile_eq_one {δ inner outer : ℝ} (hδ : 0 < δ)
    (hIn : 0 ≤ inner) (hIO : inner < outer) {w ξ : Vec}
    (hAngle : projectiveWedgeSq ξ w ≤ (inner*δ)^2) : capAngularProfile δ inner outer w ξ = 1 := by
  apply descendingProfile_eq_one ((sq_lt_sq₀ hIn (hIn.trans hIO.le)).mpr hIO)
  apply (div_le_iff₀ (pow_pos hδ 2)).mpr
  exact hAngle.trans_eq (mul_pow _ _ _)

theorem capAngularProfile_nonzero_angle {δ inner outer : ℝ} (hδ : 0 < δ)
    (hIn : 0 ≤ inner) (hIO : inner < outer) {w ξ : Vec}
    (hNZ : capAngularProfile δ inner outer w ξ ≠ 0) : projectiveWedgeSq ξ w < (outer*δ)^2 := by
  have h := descendingProfile_nonzero_lt ((sq_lt_sq₀ hIn (hIn.trans hIO.le)).mpr hIO) hNZ
  rw [mul_pow]
  exact (div_lt_iff₀ (pow_pos hδ 2)).mp h

theorem thinConeProfile_eq_one {m : Form} {η inner outer : ℝ} (hη : 0 < η)
    (hIn : 0 ≤ inner) (hIO : inner < outer) {ξ : Vec} (hξ : ξ ≠ 0)
    (hCone : |quadratic m ξ| ≤ inner*η*‖ξ‖^2) : thinConeProfile m η inner outer ξ = 1 := by
  apply descendingProfile_eq_one ((sq_lt_sq₀ hIn (hIn.trans hIO.le)).mpr hIO)
  have hDen := mul_pos hη (pow_pos (norm_pos_iff.mpr hξ) 2)
  have h : |scaledConeRatio m η ξ| ≤ inner := by
    rw [scaledConeRatio,abs_div,abs_of_pos hDen]
    exact (div_le_iff₀ hDen).mpr (by simpa only [mul_assoc] using hCone)
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hIn).mpr h

theorem thinConeProfile_nonzero_cone {m : Form} {η inner outer : ℝ} (hη : 0 < η)
    (hIn : 0 ≤ inner) (hIO : inner < outer) {ξ : Vec} (hξ : ξ ≠ 0)
    (hNZ : thinConeProfile m η inner outer ξ ≠ 0) : |quadratic m ξ| < outer*η*‖ξ‖^2 := by
  have h := descendingProfile_nonzero_lt ((sq_lt_sq₀ hIn (hIn.trans hIO.le)).mpr hIO) hNZ
  have hDen := mul_pos hη (pow_pos (norm_pos_iff.mpr hξ) 2)
  have h' := (sq_lt_sq₀ (abs_nonneg (scaledConeRatio m η ξ)) (hIn.trans hIO.le)).mp
    (by simpa only [sq_abs] using h)
  rw [scaledConeRatio,abs_div,abs_of_pos hDen] at h'
  simpa only [mul_assoc] using (div_lt_iff₀ hDen).mp h'

end Burnett.Analysis.ProjectiveNullCaps
