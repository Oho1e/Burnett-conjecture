import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualSymbolInputs

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Finset MeasureTheory Burnett.RicciSymbol
open scoped ENNReal ContDiff FourierTransform RealInnerProductSpace

/-- Resolve the degree-one multiplier into the paper's angular factors
acting on the four radian coordinate derivatives. -/
theorem radian_degree_one_derivative_identity (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (f : SchwartzMap E ℂ) :
    radianAction b f = ∑ j, radianAction (angularComponent b j) (mikhlinDerivative j f) := by
  let S (j : Index) := radianActionSpectrum (angularComponent b j) (mikhlinDerivative j f)
  have ht : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have spectra : (∑ j, S j) = radianActionSpectrum b f := by
    funext ξ
    have symbol : (∑ j, angularComponent b j ξ * (tau * ξ j)) = b (tau • ξ) := by
      rw [← sum_angularComponent b (homogeneous_value_zero hom) (tau • ξ)]
      apply Finset.sum_congr rfl
      intro j _
      have coordinate : (tau • ξ) j = tau * ξ j := rfl
      rw [coordinate, angularComponent_scale hom j tau ht ξ, mul_comm]
    have point (j : Index) : S j ξ =
        ((angularComponent b j ξ * (tau * ξ j) : ℝ) : ℂ) * 𝓕 (f : E → ℂ) ξ := by
      dsimp only [S]
      rw [radianActionSpectrum_degreeZero_apply _ (angularComponent_scale hom j),
        mikhlinDerivative_fourier, ← mul_assoc, ← Complex.ofReal_mul]
    simp_rw [Finset.sum_apply, point]
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, symbol]
    rfl
  funext x
  rw [Finset.sum_apply]
  simp_rw [← radianActionSpectrum_inverse]
  change 𝓕⁻ (radianActionSpectrum b f) x = ∑ j, 𝓕⁻ (S j) x
  rw [← spectra]
  let W := fun ξ : E => Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I)
  have wc : Continuous W := by dsimp only [W]; fun_prop
  have wb : ∀ ξ, ‖W ξ‖ ≤ 1 := by intro ξ; simp [W, Complex.norm_exp]
  have si (j : Index) : Integrable (fun ξ => W ξ * S j ξ) :=
    (radianActionSpectrum_angular_data b hb hom j (mikhlinDerivative j f)).2.1.bdd_mul
      wc.aestronglyMeasurable ⟨1, wb⟩
  simp_rw [Real.fourierIntegralInv_eq', smul_eq_mul]
  change (∫ ξ, W ξ * (∑ j, S j) ξ) = ∑ j, ∫ ξ, W ξ * S j ξ
  rw [← integral_finset_sum _ (fun j _ => si j)]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [Finset.sum_apply, Finset.mul_sum]

/-- The full Fréchet gradient controls the actual order-one action on Schwartz
inputs for every real finite exponent above one. -/
theorem radian_degree_one_gradient_bound (p : ℝ) (hp : 1 < p) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : SchwartzMap E ℂ,
      MemLp (radianAction b f) (ENNReal.ofReal p) volume ∧
      eLpNorm (radianAction b f) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (fderiv ℝ (f : E → ℂ)) (ENNReal.ofReal p) volume := by
  classical
  let P := ENNReal.ofReal p
  choose C finite estimate using fun j => homogeneous_multiplier_Schwartz_bound _
    (angularComponent_contDiffOn b hb j) (angularComponent_scale hom j) p hp
  refine ⟨∑ j, C j, ENNReal.sum_lt_top.mpr (fun j _ => finite j), fun f => ?_⟩
  let g (j : Index) := mikhlinDerivative j f
  let u (j : Index) := radianAction (angularComponent b j) (g j)
  have mem (j : Index) : MemLp (u j) P volume := by
    change MemLp (radianAction (angularComponent b j) (g j)) P volume
    rw [← radianActionSpectrum_inverse (angularComponent b j) (g j)]
    exact (radianActionSpectrum_angular_data b hb hom j (g j)).2.2 p hp
  have grad (j : Index) : eLpNorm (g j : E → ℂ) P volume ≤
      eLpNorm (fderiv ℝ (f : E → ℂ)) P volume := by
    apply eLpNorm_mono
    intro x
    change ‖(-Complex.I) • (fderiv ℝ (f : E → ℂ) x (EuclideanSpace.single j 1))‖ ≤ _
    simpa using (fderiv ℝ (f : E → ℂ) x).le_opNorm (EuclideanSpace.single j 1)
  have p1 : 1 ≤ P := by
    simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  rw [radian_degree_one_derivative_identity b hb hom f, Finset.sum_mul]
  refine ⟨memLp_finset_sum' _ (fun j _ => mem j), ?_⟩
  apply (eLpNorm_sum_le (fun j _ => (mem j).1) p1).trans
  exact sum_le_sum (fun j _ => (estimate j (g j)).trans (mul_le_mul_left' (grad j) _))

end Burnett.A02.FrequencySplit
