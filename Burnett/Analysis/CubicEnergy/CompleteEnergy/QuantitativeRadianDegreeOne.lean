import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianDegreeOne
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeMikhlinApplications

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open Finset MeasureTheory Metric Burnett.RicciSymbol
open scoped ContDiff ENNReal FourierTransform

/-- The true degree-one action has an Lᵖ gradient bound uniform over symbols
with a common bound on their ambient derivatives through order six on the
unit sphere. The constant is chosen before the symbol and the input. -/
theorem radian_degree_one_gradient_sphere_bound (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ f : SchwartzMap E ℂ,
        MemLp (radianAction b f) (ENNReal.ofReal p) volume ∧
        eLpNorm (radianAction b f) (ENNReal.ofReal p) volume ≤ C * ENNReal.ofReal D *
          eLpNorm (fderiv ℝ (f : E → ℂ)) (ENNReal.ofReal p) volume := by
  classical
  obtain ⟨K, hK, angular⟩ := paper_cj_Schwartz_sphere_bound p hp
  refine ⟨∑ _j : Index, K, ENNReal.sum_lt_top.mpr (fun _ _ => hK), ?_⟩
  intro b hb hom D hD jet f
  let P := ENNReal.ofReal p
  let S := ENNReal.ofReal D
  let Grad := eLpNorm (fderiv ℝ (f : E → ℂ)) P volume
  let g (j : Index) := mikhlinDerivative j f
  let u (j : Index) := radianAction (angularComponent b j) (g j)
  have mem (j : Index) : MemLp (u j) P volume := by
    change MemLp (radianAction (angularComponent b j) (g j)) P volume
    rw [← radianActionSpectrum_inverse (angularComponent b j) (g j)]
    exact (radianActionSpectrum_angular_data b hb hom j (g j)).2.2 p hp
  have grad (j : Index) : eLpNorm (g j : E → ℂ) P volume ≤ Grad := by
    apply eLpNorm_mono
    intro x
    change ‖(-Complex.I) • (fderiv ℝ (f : E → ℂ) x (EuclideanSpace.single j 1))‖ ≤ _
    simpa using (fderiv ℝ (f : E → ℂ) x).le_opNorm (EuclideanSpace.single j 1)
  have p1 : 1 ≤ P := by
    simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  rw [radian_degree_one_derivative_identity b hb hom f]
  refine ⟨memLp_finset_sum' _ (fun j _ => mem j), ?_⟩
  calc
    _ ≤ ∑ j, eLpNorm (u j) P volume := eLpNorm_sum_le (fun j _ => (mem j).1) p1
    _ ≤ ∑ _j : Index, K * S * Grad := sum_le_sum fun j _ =>
      (angular b hb hom D hD jet j (g j)).trans (mul_le_mul_left' (grad j) _)
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

/-- A vanishing sphere jet gives a vanishing norm of the same physical
multiplier, even at arbitrarily low nonzero frequencies. -/
theorem radian_degree_one_gradient_zero_jet (p : ℝ) (hp : 1 < p) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (jet : ∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ 0)
    (f : SchwartzMap E ℂ) :
    MemLp (radianAction b f) (ENNReal.ofReal p) volume ∧
      eLpNorm (radianAction b f) (ENNReal.ofReal p) volume = 0 := by
  obtain ⟨_, _, bound⟩ := radian_degree_one_gradient_sphere_bound p hp
  obtain ⟨mem, bn⟩ := bound b hb hom 0 le_rfl jet f
  exact ⟨mem, le_antisymm (by simpa using bn) (zero_le _)⟩

end Burnett.A02.FrequencySplit
