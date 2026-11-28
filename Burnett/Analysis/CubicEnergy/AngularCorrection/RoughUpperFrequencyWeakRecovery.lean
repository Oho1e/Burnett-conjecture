import Burnett.Analysis.CubicEnergy.AngularCorrection.RoughAngularWeakTail

set_option autoImplicit false

noncomputable section

namespace Burnett.A08

open Filter MeasureTheory Burnett.A06 Burnett.A07 Burnett.A02.FrequencySplit Burnett.Fourier
open scoped BigOperators ENNReal Topology

local instance roughUpperFrequencyOneLeTwo : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

private abbrev Test := SchwartzMap E ℂ
private abbrev LP2 := FirstOrderLp 2
private abbrev Index := Fin 4

/-- The physical weak form expands using the tested coordinate derivatives
of the forward correction and its actual high adjoint. -/
theorem testedHighDivergencePair_eq_weakCoordinateForm
    (T S : Test → Test → LP2) (d : Index → Index → BoundedSymbol E) (H u w : Test) :
    testedHighDivergencePair T S d H u w =
      (∑ i : Index, ∑ j : Index,
        inner ℂ (symbolCLM (d i j) ((coordinateDerivative i w).toLp 2 volume))
          (T H (coordinateDerivative j u) + T (coordinateDerivative j H) u)) -
        ∑ i : Index, ∑ j : Index,
          inner ℂ (S H (coordinateDerivative i w) + S (coordinateDerivative i H) w)
            (symbolCLM (d i j) ((coordinateDerivative j u).toLp 2 volume)) := by
  unfold testedHighDivergencePair
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [testedHighCoefficientPair, inner_add_right, inner_add_left]
  abel

namespace OriginalAngularCutoff

variable {η χ : ℝ → ℝ} {F : Joint × RotationSpace → ℂ} {M C₀ C₁ : ℝ}

/-- The symmetric upper cutoff commutes with the tested coordinate derivative
of the actual finite-degree Hermitian correction. -/
theorem partialHermitian_upperCutoff_derivative_test
    (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ) (Λ : ℝ) (a : Index) (H u w : Test) :
    let T (G : Test) := symmetricUpperCutoffOutput (P.partialHermitian L G) Λ;
    -inner ℂ ((coordinateDerivative a w).toLp 2 volume) (T H u) -
        inner ℂ (w.toLp 2 volume) (T H (coordinateDerivative a u)) =
      inner ℂ (w.toLp 2 volume) (T (coordinateDerivative a H) u) := by
  dsimp only
  simp only [inner_symmetricUpperCutoffOutput, ← coordinateDerivative_upperFrequencyCutoff]
  exact P.partialHermitian_derivative L a H (upperFrequencyCutoff Λ u) (upperFrequencyCutoff Λ w)

/-- Strong convergence on fixed Schwartz inputs yields the three tested
divergence limits for bounded multipliers. This includes the real bounded
Lipschitz coefficients by using `boundedRealCoefficient`. -/
theorem partialHermitian_upperCutoff_tendsto_testedHighDivergencePair
    (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ)
    (d : Index → Index → BoundedSymbol E) (H u w : Test) :
    let R := P.partialHermitian L
    let T (Λ : ℝ) (G : Test) := symmetricUpperCutoffOutput (R G) Λ
    (∀ i j : Index,
      Tendsto (fun Λ : ℝ => inner ℂ (symbolCLM (d i j) ((coordinateDerivative i w).toLp 2 volume))
        (T Λ (coordinateDerivative j H) u)) atTop
        (𝓝 (inner ℂ (symbolCLM (d i j) ((coordinateDerivative i w).toLp 2 volume))
          (R (coordinateDerivative j H) u))) ∧
      Tendsto (fun Λ : ℝ => testedHighCoefficientPair (T Λ H) (T Λ H)
        (fun v => symbolCLM (d i j) (v.toLp 2 volume)) (coordinateDerivative j u) (coordinateDerivative i w)) atTop
        (𝓝 (testedHighCoefficientPair (R H) (R H)
          (fun v => symbolCLM (d i j) (v.toLp 2 volume)) (coordinateDerivative j u) (coordinateDerivative i w))) ∧
      Tendsto (fun Λ : ℝ => inner ℂ (T Λ (coordinateDerivative i H) w)
        (symbolCLM (d i j) ((coordinateDerivative j u).toLp 2 volume))) atTop
        (𝓝 (inner ℂ (R (coordinateDerivative i H) w)
          (symbolCLM (d i j) ((coordinateDerivative j u).toLp 2 volume))))) ∧
    Tendsto (fun Λ : ℝ => testedHighDivergencePair (T Λ) (T Λ) d H u w) atTop
      (𝓝 (testedHighDivergencePair R R d H u w)) := by
  intro R T
  have strong (G v : Test) : Tendsto (fun Λ : ℝ => T Λ G v) atTop (𝓝 (R G v)) :=
    (P.partialHermitian_upperRecovery (fun _ _ => 0) (fun _ _ => rfl) L G).strong v
  have first (i j : Index) :=
    (tendsto_const_nhds (x := symbolCLM (d i j) ((coordinateDerivative i w).toLp 2 volume))).inner
      (𝕜 := ℂ) (strong (coordinateDerivative j H) u)
  have middle (i j : Index) :
      Tendsto (fun Λ : ℝ => testedHighCoefficientPair (T Λ H) (T Λ H)
        (fun v => symbolCLM (d i j) (v.toLp 2 volume)) (coordinateDerivative j u) (coordinateDerivative i w)) atTop
        (𝓝 (testedHighCoefficientPair (R H) (R H)
          (fun v => symbolCLM (d i j) (v.toLp 2 volume)) (coordinateDerivative j u) (coordinateDerivative i w))) := by
    unfold testedHighCoefficientPair
    exact (tendsto_const_nhds.inner (strong H (coordinateDerivative j u))).sub
      ((strong H (coordinateDerivative i w)).inner tendsto_const_nhds)
  have third (i j : Index) := (strong (coordinateDerivative i H) w).inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := symbolCLM (d i j) ((coordinateDerivative j u).toLp 2 volume)))
  refine ⟨fun i j => ⟨first i j, middle i j, third i j⟩, ?_⟩
  unfold testedHighDivergencePair
  exact tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ =>
    ((first i j).add (middle i j)).sub (third i j)

end OriginalAngularCutoff

end Burnett.A08
