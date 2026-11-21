import Burnett.Analysis.CubicEnergy.CompleteEnergy.UniformCubicDifference
import Burnett.Analysis.CubicEnergy.CompleteEnergy.CompleteCubicEuclidean

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Metric Burnett.RicciSymbol
open scoped ContDiff ENNReal

/-- The paper's homogeneous cubic continuity in real Euclidean gradient norms.
The coefficient in front of the common finite symbol-jet bound is chosen
before the symbol and the two fields. -/
theorem complete_cubic_energy_difference_euclidean_sphere_bound {J : Type} [Fintype J]
    (c : EnergyIndex J → J → ℝ) (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l)
    (q : Index → Index → J → J → J → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) → ∀ (D : ℝ), 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ u v : RealEnergyField J,
      |completeCubicEnergy c q b u - completeCubicEnergy c q b v| ≤
        (K * D) * euclideanFieldGradientL3 (↑(u-v) : J → SchwartzMap E ℂ) *
          (euclideanFieldGradientL3 (u : J → SchwartzMap E ℂ) +
            euclideanFieldGradientL3 (v : J → SchwartzMap E ℂ))^2 := by
  obtain ⟨C, hC, bound⟩ := complete_cubic_energy_difference_sphere_bound c hc q
  let m : ℝ≥0∞ := ((Fintype.card J : ℝ≥0∞) * Fintype.card Index)^3
  refine ⟨(C * m).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro b hb hom D hD jet u v
  have fC : C * ENNReal.ofReal D < ⊤ := ENNReal.mul_lt_top hC ENNReal.ofReal_lt_top
  have e := euclidean_cubic_difference_of_component_bound (completeCubicEnergy c q b)
    (C * ENNReal.ofReal D) fC (bound b hb hom D hD jet) u v
  have factor : (C * ENNReal.ofReal D * m).toReal = (C * m).toReal * D := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hD]
    ring
  change _ ≤ (C * ENNReal.ofReal D * m).toReal * _ * _ at e
  rwa [factor] at e

end Burnett.A02.FrequencySplit
