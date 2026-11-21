import Burnett.Analysis.CubicEnergy.CompleteEnergy.CompleteCubicContinuity
import Burnett.Analysis.CubicEnergy.CompleteEnergy.EuclideanFieldGradient

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.RicciSymbol
open scoped BigOperators ContDiff ENNReal

/-- The finite real L³ norm of the full gradient with the manuscript's
fixed Euclidean fiber metric. -/
def euclideanFieldGradientL3 {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ) : ℝ :=
  (euclideanFieldGradientNorm u).toReal

/-- Transfer a three-factor cubic difference estimate from component norms to
the common Euclidean gradient, checking finiteness before taking real norms. -/
theorem euclidean_cubic_difference_of_component_bound {J : Type} [Fintype J]
    (F : RealEnergyField J → ℝ) (C : ℝ≥0∞) (hC : C < ⊤)
    (bound : ∀ u v : RealEnergyField J, ‖F u - F v‖ₑ ≤
      C * fieldEnergyGradientNorm (↑(u-v) : J → SchwartzMap E ℂ) *
        (fieldEnergyGradientNorm (u : J → SchwartzMap E ℂ) +
          fieldEnergyGradientNorm (v : J → SchwartzMap E ℂ))^2)
    (u v : RealEnergyField J) :
      |F u - F v| ≤ (C * ((Fintype.card J : ℝ≥0∞) * Fintype.card Index)^3).toReal *
        euclideanFieldGradientL3 (↑(u-v) : J → SchwartzMap E ℂ) *
        (euclideanFieldGradientL3 (u : J → SchwartzMap E ℂ) +
          euclideanFieldGradientL3 (v : J → SchwartzMap E ℂ))^2 := by
  let M : ℝ≥0∞ := (Fintype.card J : ℝ≥0∞) * Fintype.card Index
  let K := C * M^3
  have hM : M < ⊤ := ENNReal.mul_lt_top (by simp) (by simp)
  have hK : K < ⊤ := ENNReal.mul_lt_top hC (by
    rw [pow_succ, pow_two]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hM hM) hM)
  let S (w : RealEnergyField J) := fieldEnergyGradientNorm (w : J → SchwartzMap E ℂ)
  let G (w : RealEnergyField J) := euclideanFieldGradientNorm (w : J → SchwartzMap E ℂ)
  have comp (w : RealEnergyField J) : S w ≤ M * G w :=
    fieldEnergyGradientNorm_le_euclidean (w : J → SchwartzMap E ℂ)
  have gfinite (w : RealEnergyField J) : G w < ⊤ := euclideanFieldGradientNorm_lt_top _
  have pair : S u + S v ≤ M * (G u + G v) := by
    rw [mul_add]
    exact add_le_add (comp u) (comp v)
  have e : ‖F u - F v‖ₑ ≤ K * G (u - v) * (G u + G v)^2 := calc
    _ ≤ C * S (u-v) * (S u + S v)^2 := bound u v
    _ ≤ C * (M * G (u-v)) * (M * (G u + G v))^2 :=
      mul_le_mul' (mul_le_mul_left' (comp (u-v)) C) (pow_le_pow_left' pair 2)
    _ = _ := by dsimp only [K]; ring
  have hpair : G u + G v < ⊤ := ENNReal.add_lt_top.mpr ⟨gfinite u, gfinite v⟩
  have finite : K * G (u-v) * (G u + G v)^2 < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top hK (gfinite (u-v))) (by rw [pow_two]; exact ENNReal.mul_lt_top hpair hpair)
  have real := ENNReal.toReal_mono finite.ne e
  change _ ≤ K.toReal * _ * _
  simpa only [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg (F u - F v)),
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_add (gfinite u).ne (gfinite v).ne,
    euclideanFieldGradientL3, G] using real

/-- The homogeneous continuity inequality for the actual complete cubic energy,
in the manuscript's real Euclidean gradient norms. -/
theorem complete_cubic_energy_difference_euclidean {J : Type} [Fintype J]
    (c : EnergyIndex J → J → ℝ) (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l)
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u v : RealEnergyField J,
      |completeCubicEnergy c q b u - completeCubicEnergy c q b v| ≤
        K * euclideanFieldGradientL3 (↑(u-v) : J → SchwartzMap E ℂ) *
          (euclideanFieldGradientL3 (u : J → SchwartzMap E ℂ) +
            euclideanFieldGradientL3 (v : J → SchwartzMap E ℂ))^2 := by
  obtain ⟨C, hC, bound⟩ := complete_cubic_energy_difference_bound c hc q b hb hom
  refine ⟨(C * ((Fintype.card J : ℝ≥0∞) * Fintype.card Index)^3).toReal, ENNReal.toReal_nonneg, ?_⟩
  exact euclidean_cubic_difference_of_component_bound (completeCubicEnergy c q b) C hC bound

end Burnett.A02.FrequencySplit
