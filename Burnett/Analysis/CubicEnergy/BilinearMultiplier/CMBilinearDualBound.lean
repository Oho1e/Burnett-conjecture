import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDual
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualFourier
import Burnett.Analysis.CubicEnergy.JointMultiplier.JointTrilinearSeminorm

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow

open MeasureTheory Metric Burnett.RicciSymbol
open scoped ContDiff ENNReal

private theorem triBalance_of_output_exponent {p s r : ℝ} (hp : 1 < p) (hs : 1 < s) (hr : 1 < r)
    (he : r⁻¹ = p⁻¹ + s⁻¹) : triBalance p s (Real.conjExponent r) := by
  have ht : p.HolderTriple s r := ⟨he.symm, zero_lt_one.trans hp, zero_lt_one.trans hs⟩
  letI : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal s) (ENNReal.ofReal r) := ht.ennrealOfReal
  rw [triBalance, ENNReal.HolderTriple.inv_add_inv_eq_inv (ENNReal.ofReal p) (ENNReal.ofReal s) (ENNReal.ofReal r)]
  exact (Real.HolderConjugate.conjExponent hr).inv_add_inv_ennreal

private theorem jointBilinear_schwartz_test_eq (m : Joint → ℝ) (hm : Measurable m)
    {D : ℝ} (hD : ∀ y, ‖m y‖ ≤ D) (f g h : SchwartzMap E ℂ) :
    (∫ x, jointBilinear m f g x * h x) = jointTrilinear m f g h := by
  rw [(jointBilinear_schwartz_pairing m hm hD f g h).2.2, jointTrilinear]
  apply integral_congr_ae
  filter_upwards with y
  simp only [bilinearFourierWeight, jointTestFactor, mul_assoc]

private theorem jointBilinear_of_trilinear_bound {p s r q : ℝ} (hrq : r.HolderConjugate q)
    (m : Joint → ℝ) (hm : ContDiffOn ℝ ∞ m {y | y ≠ 0})
    (hh : ∀ t : ℝ, 0 < t → ∀ y, m (t • y) = m y)
    (f g : SchwartzMap E ℂ) {C : ℝ≥0∞} (hC : C < ⊤)
    (tests : ∀ h : SchwartzMap E ℂ, ‖jointTrilinear m f g h‖ₑ ≤ C * triLpMass f g h p s q) :
    MemLp (jointBilinear m f g) (ENNReal.ofReal r) volume ∧
      eLpNorm (jointBilinear m f g) (ENNReal.ofReal r) volume ≤
        C * (eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume * eLpNorm (g : E → ℂ) (ENNReal.ofReal s) volume) := by
  obtain ⟨hM, D, hD⟩ := homogeneous_joint_symbol_measurable_bounded m hm hh
  have hfin : C * (eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume *
      eLpNorm (g : E → ℂ) (ENNReal.ofReal s) volume) ≠ ⊤ :=
    ENNReal.mul_ne_top hC.ne <| ENNReal.mul_ne_top
      (f.memLp (ENNReal.ofReal p) volume).2.ne (g.memLp (ENNReal.ofReal s) volume).2.ne
  apply CMBilinearDual.memLp_of_schwartz_pairing hrq (jointBilinear_continuous_bounded m hM hD f g).1 hfin
  intro h
  rw [jointBilinear_schwartz_test_eq m hM hD f g h]
  simpa only [triLpMass, mul_assoc] using tests h

/-- The actual whole-space Coifman–Meyer operator on Schwartz inputs at all
finite exponents p, s, r above one with the Hölder balance. -/
theorem joint_bilinear_bound (p s r : ℝ) (hp : 1 < p) (hs : 1 < s) (hr : 1 < r)
    (he : r⁻¹ = p⁻¹ + s⁻¹)
    (m : Joint → ℝ) (hm : ContDiffOn ℝ ∞ m {y | y ≠ 0})
    (hh : ∀ t : ℝ, 0 < t → ∀ y, m (t • y) = m y) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f g : SchwartzMap E ℂ,
      MemLp (jointBilinear m f g) (ENNReal.ofReal r) volume ∧
        eLpNorm (jointBilinear m f g) (ENNReal.ofReal r) volume ≤
          C * (eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume * eLpNorm (g : E → ℂ) (ENNReal.ofReal s) volume) := by
  have hrq := Real.HolderConjugate.conjExponent hr
  obtain ⟨C, hC, tests⟩ := joint_trilinear_bound p s (Real.conjExponent r)
    hp hs hrq.symm.lt (triBalance_of_output_exponent hp hs hr he) m hm hh
  exact ⟨C, hC, fun f g => jointBilinear_of_trilinear_bound hrq m hm hh f g hC (tests f g)⟩

/-- The constant in the actual Schwartz-to-Lʳ estimate is linear in a
bound on the joint unit-sphere ambient derivatives through order fifteen. -/
theorem joint_bilinear_sphere_bound (p s r : ℝ) (hp : 1 < p) (hs : 1 < s) (hr : 1 < r)
    (he : r⁻¹ = p⁻¹ + s⁻¹) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (m : Joint → ℝ), ContDiffOn ℝ ∞ m {y | y ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ y, m (t • y) = m y) → ∀ (D : ℝ), 0 ≤ D →
      (∀ i : ℕ, i ≤ 15 → ∀ ξ ∈ sphere (0 : Freq8) 1,
        ‖iteratedFDeriv ℝ i (fun u => m (splitFreq u)) ξ‖ ≤ D) →
      ∀ f g : SchwartzMap E ℂ,
        MemLp (jointBilinear m f g) (ENNReal.ofReal r) volume ∧
          eLpNorm (jointBilinear m f g) (ENNReal.ofReal r) volume ≤
            K * ENNReal.ofReal D *
              (eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume * eLpNorm (g : E → ℂ) (ENNReal.ofReal s) volume) := by
  have hrq := Real.HolderConjugate.conjExponent hr
  obtain ⟨K, hK, tests⟩ := joint_trilinear_sphere_bound p s (Real.conjExponent r)
    hp hs hrq.symm.lt (triBalance_of_output_exponent hp hs hr he)
  refine ⟨K, hK, fun m hm hh D hD jet f g => ?_⟩
  exact jointBilinear_of_trilinear_bound hrq m hm hh f g (ENNReal.mul_lt_top hK ENNReal.ofReal_lt_top)
    (tests m hm hh D hD jet f g)

end Burnett.A02.FrequencySplit
