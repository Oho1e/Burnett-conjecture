import Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedSchwartzWindow
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeRadianDegreeOne

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow
open Finset MeasureTheory Metric Burnett.RicciSymbol
open scoped ContDiff ENNReal FourierTransform RealInnerProductSpace

/-- Convert a fixed profile given in the normalized Fourier variable to a
real symbol in the manuscript's radian variable. -/
def fixedRadianProfile (a : SchwartzMap E ℂ) (ζ : E) : ℝ :=
  (a (tau⁻¹ • ζ)).re

private theorem fixed_tau_pos : 0 < tau := mul_pos (by norm_num) Real.pi_pos

theorem fixedRadianProfile_scaled (a : SchwartzMap E ℂ) (ξ : E) :
    fixedRadianProfile a (tau • ξ) = (a ξ).re := by
  simp only [fixedRadianProfile, smul_smul, inv_mul_cancel₀ fixed_tau_pos.ne', one_smul]

/-- The additive smooth correction agrees with the actual radian multiplier. -/
theorem fixedRadianProfile_action (a : SchwartzMap E ℂ) (areal : ∀ ξ, ((a ξ).re : ℂ) = a ξ)
    (f : SchwartzMap E ℂ) :
    radianAction (fixedRadianProfile a) f = (fixedSchwartzFourierAction a f : E → ℂ) := by
  rw [← radianActionSpectrum_inverse, fixedSchwartzFourierAction_inverse]
  congr 1
  funext ξ
  simp only [radianActionSpectrum, fixedRadianProfile_scaled, areal]

theorem fixedRadianProfile_convolution (a : SchwartzMap E ℂ)
    (areal : ∀ ξ, ((a ξ).re : ℂ) = a ξ) (f : SchwartzMap E ℂ) (x : E) :
    radianAction (fixedRadianProfile a) f x =
      ∫ y, ((SchwartzMap.fourierTransformCLE ℂ).symm a) (x - y) * f y := by
  rw [fixedRadianProfile_action a areal f]
  exact fixedSchwartzFourierAction_convolution a f x

theorem fixedRadianProfile_Lp (a : SchwartzMap E ℂ) (areal : ∀ ξ, ((a ξ).re : ℂ) = a ξ)
    (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : SchwartzMap E ℂ,
      MemLp (radianAction (fixedRadianProfile a) f) (ENNReal.ofReal p) volume ∧
      eLpNorm (radianAction (fixedRadianProfile a) f) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, bound⟩ := fixedSchwartzFourierAction_Lp a p hp
  refine ⟨C, hC, fun f => ?_⟩
  rw [fixedRadianProfile_action a areal f]
  exact ⟨(fixedSchwartzFourierAction a f).memLp _ _, bound f⟩

private def fixedRadianCoordinate (j : Index) : E →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (tau • EuclideanSpace.proj (𝕜 := ℝ) j)

/-- In normalized frequencies the symbol for the fixed, smoothed coordinate
derivative is exactly `(2π ξ_j) a(ξ)`. -/
def fixedCoordinateProfile (a : SchwartzMap E ℂ) (j : Index) : SchwartzMap E ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (fixedRadianCoordinate j).hasTemperateGrowth a

theorem fixedCoordinateProfile_apply (a : SchwartzMap E ℂ) (j : Index) (ξ : E) :
    fixedCoordinateProfile a j ξ = a ξ * ((tau * ξ j : ℝ) : ℂ) := rfl

private theorem fixed_infrared_spectrum_sum (a : SchwartzMap E ℂ)
    (areal : ∀ ξ, ((a ξ).re : ℂ) = a ξ) (b : E → ℝ)
    (hom : ∀ t : ℝ, 0 < t → ∀ z, b (t • z) = t * b z) (f : SchwartzMap E ℂ) :
    radianActionSpectrum (fun ζ => fixedRadianProfile a ζ * b ζ) f =
      ∑ j, radianActionSpectrum (angularComponent b j)
        (fixedSchwartzFourierAction (fixedCoordinateProfile a j) f) := by
  let S (j : Index) := radianActionSpectrum (angularComponent b j)
    (fixedSchwartzFourierAction (fixedCoordinateProfile a j) f)
  funext ξ
  have hsum : (∑ j, angularComponent b j (tau • ξ) * (tau * ξ j)) = b (tau • ξ) := by
    rw [← sum_angularComponent b (homogeneous_value_zero hom) (tau • ξ)]
    apply Finset.sum_congr rfl
    intro j _
    have coordinate : (tau • ξ) j = tau * ξ j := rfl
    rw [coordinate, mul_comm]
  have point (j : Index) : S j ξ =
      ((angularComponent b j (tau • ξ) * (tau * ξ j) : ℝ) : ℂ) *
        (a ξ * 𝓕 (f : E → ℂ) ξ) := by
    dsimp only [S, radianActionSpectrum]
    simp only [fixedSchwartzFourierAction_spectrum, fixedCoordinateProfile_apply, Complex.ofReal_mul]
    ring
  change radianActionSpectrum (fun ζ => fixedRadianProfile a ζ * b ζ) f ξ = (∑ j, S j) ξ
  simp_rw [Finset.sum_apply, point]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, hsum]
  simp only [radianActionSpectrum, fixedRadianProfile_scaled, Complex.ofReal_mul, areal]
  ring

/-- The actual low correction equals the sum of the exterior angular factors
acting on the smoothed real coordinate multipliers. -/
theorem fixed_infrared_decomposition (a : SchwartzMap E ℂ)
    (areal : ∀ ξ, ((a ξ).re : ℂ) = a ξ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ z, b (t • z) = t * b z) (f : SchwartzMap E ℂ) :
    radianAction (fun ζ => fixedRadianProfile a ζ * b ζ) f =
      ∑ j, radianAction (angularComponent b j)
        (fixedSchwartzFourierAction (fixedCoordinateProfile a j) f) := by
  let g (j : Index) := fixedSchwartzFourierAction (fixedCoordinateProfile a j) f
  let S (j : Index) := radianActionSpectrum (angularComponent b j) (g j)
  funext x
  rw [Finset.sum_apply]
  simp_rw [← radianActionSpectrum_inverse]
  change 𝓕⁻ (radianActionSpectrum (fun ζ => fixedRadianProfile a ζ * b ζ) f) x =
    ∑ j, 𝓕⁻ (S j) x
  rw [fixed_infrared_spectrum_sum a areal b hom f]
  let W := fun ξ : E => Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I)
  have wc : Continuous W := by dsimp only [W]; fun_prop
  have wb (ξ : E) : ‖W ξ‖ ≤ 1 := by simp [W, Complex.norm_exp]
  have si (j : Index) : Integrable (fun ξ => W ξ * S j ξ) :=
    (radianActionSpectrum_angular_data b hb hom j (g j)).2.1.bdd_mul
      wc.aestronglyMeasurable ⟨1, wb⟩
  simp_rw [Real.fourierIntegralInv_eq', smul_eq_mul]
  change (∫ ξ, W ξ * (∑ j, S j) ξ) = ∑ j, ∫ ξ, W ξ * S j ξ
  rw [← integral_finset_sum _ (fun j _ => si j)]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [Finset.sum_apply, Finset.mul_sum]

/-- The fixed low correction costs only the undifferentiated physical Lᵖ norm.
For a fixed profile and exponent the constant precedes the symbol and input. -/
theorem fixed_infrared_sphere_bound (a : SchwartzMap E ℂ)
    (areal : ∀ ξ, ((a ξ).re : ℂ) = a ξ) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ f : SchwartzMap E ℂ,
        MemLp (radianAction (fun ζ => fixedRadianProfile a ζ * b ζ) f) (ENNReal.ofReal p) volume ∧
        eLpNorm (radianAction (fun ζ => fixedRadianProfile a ζ * b ζ) f) (ENNReal.ofReal p) volume ≤
          C * ENNReal.ofReal D * eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume := by
  classical
  obtain ⟨K, hK, angular⟩ := paper_cj_Schwartz_sphere_bound p hp
  choose V hV window using fun j : Index => fixedSchwartzFourierAction_Lp (fixedCoordinateProfile a j) p hp
  refine ⟨∑ j, K * V j, ENNReal.sum_lt_top.mpr (fun j _ => ENNReal.mul_lt_top hK (hV j)), ?_⟩
  intro b hb hom D hD jet f
  let P := ENNReal.ofReal p
  let A := ENNReal.ofReal D
  let mass := eLpNorm (f : E → ℂ) P volume
  let g (j : Index) := fixedSchwartzFourierAction (fixedCoordinateProfile a j) f
  let u (j : Index) := radianAction (angularComponent b j) (g j)
  have mem (j : Index) : MemLp (u j) P volume := by
    change MemLp (radianAction (angularComponent b j) (g j)) P volume
    rw [← radianActionSpectrum_inverse]
    exact (radianActionSpectrum_angular_data b hb hom j (g j)).2.2 p hp
  have p1 : 1 ≤ P := by
    simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  rw [fixed_infrared_decomposition a areal b hb hom f]
  refine ⟨memLp_finset_sum' _ (fun j _ => mem j), ?_⟩
  calc
    _ ≤ ∑ j, eLpNorm (u j) P volume := eLpNorm_sum_le (fun j _ => (mem j).1) p1
    _ ≤ ∑ j, (K * V j) * A * mass := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ K * A * eLpNorm (g j : E → ℂ) P volume := angular b hb hom D hD jet j (g j)
        _ ≤ K * A * (V j * mass) := mul_le_mul_left' (window j f) _
        _ = _ := by ac_rfl
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

end Burnett.A02.FrequencySplit
