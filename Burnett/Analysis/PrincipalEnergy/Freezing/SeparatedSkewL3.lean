import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedSpatialSkew
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeRadianDegreeOne
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearEstimate

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit

open MeasureTheory Metric
open scoped ContDiff ENNReal

private theorem energyProduct_gradientL3_le (f u : SchwartzMap E ℂ) :
    energyGradientNorm (energyProduct f u) ≤
      eLpNorm (f : E → ℂ) ⊤ volume * energyGradientNorm u +
        eLpNorm (fderiv ℝ (f : E → ℂ)) ⊤ volume * eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume := by
  let P := ENNReal.ofReal 3
  let df := fderiv ℝ (f : E → ℂ)
  let du := fderiv ℝ (u : E → ℂ)
  let A := (f : E → ℂ) • du
  let B := (u : E → ℂ) • df
  have hdf : Continuous df := (SchwartzMap.fderivCLM ℝ f).continuous
  have hdu : Continuous du := (SchwartzMap.fderivCLM ℝ u).continuous
  have hA : Continuous A := f.continuous.smul hdu
  have hB : Continuous B := u.continuous.smul hdf
  have shape : (energyProduct f u : E → ℂ) = (f : E → ℂ) * (u : E → ℂ) :=
    funext (energyProduct_apply f u)
  have derivative : fderiv ℝ (energyProduct f u : E → ℂ) = A + B := by
    funext x
    rw [shape]
    exact fderiv_mul (f.differentiable x) (u.differentiable x)
  have boundA : eLpNorm A P volume ≤ eLpNorm (f : E → ℂ) ⊤ volume * eLpNorm du P volume :=
    eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm P hdu.aestronglyMeasurable (f : E → ℂ)
  have boundB : eLpNorm B P volume ≤ eLpNorm df ⊤ volume * eLpNorm (u : E → ℂ) P volume := by
    let n : E → ℝ := fun x => ‖df x‖
    calc
      _ ≤ eLpNorm (n • (u : E → ℂ)) P volume := by
        apply eLpNorm_mono
        intro x
        change ‖u x • df x‖ ≤ ‖‖df x‖ • u x‖
        simp only [norm_smul, Real.norm_of_nonneg (norm_nonneg (df x)), mul_comm]
        exact le_rfl
      _ ≤ _ := by
        simpa only [n, eLpNorm_norm] using eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
          P u.continuous.aestronglyMeasurable n
  unfold energyGradientNorm
  rw [derivative]
  exact (eLpNorm_add_le hA.aestronglyMeasurable hB.aestronglyMeasurable
    (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 3)).trans (add_le_add boundA boundB)

/-- A common sphere-jet constant controls the actual separated Fourier test.
The test and its gradient input use the physical Euclidean Lebesgue norms. -/
theorem separated_skew_action_L3_sphere_bound :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ f u : SchwartzMap E ℂ,
        MemLp (separatedSkewAction f b u) (ENNReal.ofReal 3) volume ∧
        eLpNorm (separatedSkewAction f b u) (ENNReal.ofReal 3) volume ≤ C * ENNReal.ofReal D *
          (eLpNorm (f : E → ℂ) ⊤ volume * energyGradientNorm u +
            eLpNorm (fderiv ℝ (f : E → ℂ)) ⊤ volume * eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume) := by
  obtain ⟨C, hC, multiplier⟩ := radian_degree_one_gradient_sphere_bound 3 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro b hb hom D hD jet f u
  let P := ENNReal.ofReal 3
  let c := C * ENNReal.ofReal D
  let F := eLpNorm (f : E → ℂ) ⊤ volume
  let G := eLpNorm (fderiv ℝ (f : E → ℂ)) ⊤ volume
  let U := eLpNorm (u : E → ℂ) P volume
  let W := c * (F * energyGradientNorm u + G * U)
  have skew (v : SchwartzMap E ℂ) : MemLp (radianSkewAction b v) P volume ∧
      eLpNorm (radianSkewAction b v) P volume ≤ c * energyGradientNorm v := by
    obtain ⟨hLp, bound⟩ := multiplier b hb hom D hD
      (fun n hn => jet n (hn.trans (by norm_num))) v
    refine ⟨hLp.const_mul (-Complex.I), ?_⟩
    change eLpNorm ((-Complex.I) • radianAction b v) P volume ≤ _
    have hI : ‖(-Complex.I : ℂ)‖ₑ = 1 := by
      rw [← ofReal_norm_eq_enorm, norm_neg, Complex.norm_I, ENNReal.ofReal_one]
    rw [eLpNorm_const_smul, hI, one_mul]
    exact bound
  let A := (f : E → ℂ) • radianSkewAction b u
  let B := radianSkewAction b (energyProduct f u)
  have hA : MemLp A P volume := (skew u).1.smul (f.memLp ⊤ volume)
  have hB : MemLp B P volume := (skew (energyProduct f u)).1
  have boundA : eLpNorm A P volume ≤ W := calc
    _ ≤ F * eLpNorm (radianSkewAction b u) P volume :=
      eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm P (skew u).1.aestronglyMeasurable (f : E → ℂ)
    _ ≤ F * (c * energyGradientNorm u) := mul_le_mul_left' (skew u).2 _
    _ = c * (F * energyGradientNorm u) := by ring
    _ ≤ W := mul_le_mul_left' (le_add_of_nonneg_right (zero_le _)) _
  have boundB : eLpNorm B P volume ≤ W :=
    (skew (energyProduct f u)).2.trans (mul_le_mul_left' (energyProduct_gradientL3_le f u) _)
  have form : separatedSkewAction f b u = (2 : ℂ)⁻¹ • (A + B) := by
    funext x
    simp only [separatedSkewAction, div_eq_inv_mul, Pi.smul_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul, A, B]
  have half : ‖(2 : ℂ)⁻¹‖ₑ = (2 : ℝ≥0∞)⁻¹ := by
    rw [← ofReal_norm_eq_enorm, norm_inv, Complex.norm_two,
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  rw [form]
  refine ⟨(hA.add hB).const_smul _, ?_⟩
  change eLpNorm ((2 : ℂ)⁻¹ • (A+B)) P volume ≤ W
  rw [eLpNorm_const_smul, half]
  calc
    _ ≤ (2 : ℝ≥0∞)⁻¹ * (eLpNorm A P volume + eLpNorm B P volume) :=
      mul_le_mul_left' (eLpNorm_add_le hA.aestronglyMeasurable hB.aestronglyMeasurable
        (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 3)) _
    _ ≤ (2 : ℝ≥0∞)⁻¹ * (W + W) := mul_le_mul_left' (add_le_add boundA boundB) _
    _ = ((2 : ℝ≥0∞)⁻¹ * 2) * W := by ring
    _ = W := by rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp), one_mul]

end Burnett.A02.FrequencySplit
