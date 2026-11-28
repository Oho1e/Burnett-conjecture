import Burnett.Analysis.CubicEnergy.AngularCorrection.LipschitzWeakCoefficientPair

set_option autoImplicit false
set_option maxHeartbeats 12000000

noncomputable section

namespace Burnett.A08

open MeasureTheory Metric Set Burnett.A06 Burnett.A07 Burnett.A02.FrequencySplit Burnett.Fourier
open scoped BigOperators ComplexConjugate ContDiff ENNReal NNReal

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private abbrev Test := SchwartzMap E ℂ
private abbrev LP2 := FirstOrderLp 2
private abbrev Index := Fin 4

open private coordinateDerivative_norm_le_gradient schwartzGradientNorm_nonneg
  from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalWeakDivergenceCommutator

/-- Expanding the two actual weak derivatives gives the three placements
of the original weak commutator. -/
theorem boundedWeakDivergenceCommutatorPair_threeTerms {b : Joint → ℂ} {C : ℝ}
    (P : OriginalAnalyticCorrectionBounds b C)
    (d : Index → Index → BoundedSymbol E) (H u w : Test) :
    boundedWeakDivergenceCommutatorPair P d H u w =
      ∑ a : Index, ∑ j : Index,
        (inner ℂ (symbolCLM (d a j) ((coordinateDerivative a w).toLp 2 volume))
          (P.forward (coordinateDerivative j H) u) +
        boundedCoefficientCorrectionCommutatorPair P (d a j) H (coordinateDerivative j u)
          (coordinateDerivative a w) -
        inner ℂ (P.adjoint (coordinateDerivative a H) w)
          (symbolCLM (d a j) ((coordinateDerivative j u).toLp 2 volume))) := by
  unfold boundedWeakDivergenceCommutatorPair
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [OriginalAnalyticCorrectionBounds.forwardCoordinateOutput,
    OriginalAnalyticCorrectionBounds.adjointCoordinateOutput,
    inner_add_right, inner_add_left, boundedCoefficientCorrectionCommutatorPair]
  abel

/-- The weak three-term identity and each of the estimates in manuscript
lines 1476–1504. The actual two-slot commutator witnesses also give the
Euclidean quartic bound with a fixed dimension factor. -/
theorem PaperAnalyticCorrectionBounds.boundedWeakDivergenceCommutator_bound
    {a : Joint → ℂ} {C : ℝ} (P : PaperAnalyticCorrectionBounds a C) (hC : 0 ≤ C)
    (b : Joint → ℂ) (hb : Measurable b) (B : ℝ) (hB : 0 ≤ B)
    (hsize : ∀ p, ‖b p‖ ≤ B * (1 + ‖p.1‖ + ‖p.2‖)) (hRep : b =ᵐ[volume] a)
    (d : Index → Index → E → ℝ) (D G : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hbounded : ∀ i j x, |d i j x| ≤ D)
    (L : ℝ≥0) (hLip : ∀ i j, LipschitzWith L (d i j))
    (hgrad : ∀ i j, lipschitzGradientLInfty (d i j) ≤ G) (H u : Test) :
    (∀ i j, d i j = d j i) →
    let Q := P.toOriginalAnalyticCorrectionBounds
    let e (i j : Index) := boundedRealCoefficient (d i j) D hD
      (hLip i j).continuous.measurable (hbounded i j)
    ∃ U : Index → Index → LP2,
      (∀ (i j : Index) (w : Test), inner ℂ (w.toLp 2 volume) (U i j) =
        -radianHighCommutatorPair a (d i j) H (coordinateDerivative j u) w) ∧
      (∀ i j, ‖U i j‖ ≤ C * lipschitzGradientLInfty (d i j) * ‖H.toLp 4 volume‖ *
        ‖(coordinateDerivative j u).toLp 4 volume‖) ∧
      (∀ w : Test, boundedWeakDivergenceCommutatorPair Q e H u w =
        ∑ i : Index, ∑ j : Index,
          (inner ℂ (symbolCLM (e i j) ((coordinateDerivative i w).toLp 2 volume))
            (P.forward (coordinateDerivative j H) u) +
          inner ℂ ((coordinateDerivative i w).toLp 2 volume) (U i j) -
          inner ℂ (P.adjoint (coordinateDerivative i H) w)
            (symbolCLM (e i j) ((coordinateDerivative j u).toLp 2 volume)))) ∧
      (∀ i j,
        ‖inner ℂ (symbolCLM (e i j) ((coordinateDerivative i u).toLp 2 volume))
          (P.forward (coordinateDerivative j H) u)‖ ≤
            D * ‖P.forward (coordinateDerivative j H) u‖ * ‖(coordinateDerivative i u).toLp 2 volume‖ ∧
        ‖inner ℂ ((coordinateDerivative i u).toLp 2 volume) (U i j)‖ ≤
          ‖U i j‖ * ‖(coordinateDerivative i u).toLp 2 volume‖ ∧
        ‖inner ℂ (P.adjoint (coordinateDerivative i H) u)
          (symbolCLM (e i j) ((coordinateDerivative j u).toLp 2 volume))‖ ≤
            D * ‖(coordinateDerivative j u).toLp 2 volume‖ * ‖P.adjoint (coordinateDerivative i H) u‖) ∧
      ‖Complex.I * boundedWeakDivergenceCommutatorPair Q e H u u‖ ≤ 32 * C *
        (D * schwartzGradientNorm 2 u * schwartzGradientNorm 4 H * schwartzGradientNorm 4 u +
         G * schwartzGradientNorm 2 u * ‖H.toLp 4 volume‖ * schwartzGradientNorm 4 u) := by
  intro _ Q e
  choose U V hU hV hUtest using fun i j : Index =>
    P.rough_gradient (d i j) (hLip i j) H (coordinateDerivative j u)
  have hPair (i j : Index) (w : Test) :
      boundedCoefficientCorrectionCommutatorPair Q (e i j) H (coordinateDerivative j u)
        (coordinateDerivative i w) = inner ℂ ((coordinateDerivative i w).toLp 2 volume) (U i j) := by
    exact (boundedCoefficientCorrectionCommutatorPair_fourier Q b hb B hB hsize hRep (d i j) L
      (hLip i j) D hD (hbounded i j) H (coordinateDerivative j u) (coordinateDerivative i w)).trans
      (hUtest i j (coordinateDerivative i w)).1.symm
  have hThree (w : Test) : boundedWeakDivergenceCommutatorPair Q e H u w =
      ∑ i : Index, ∑ j : Index,
        (inner ℂ (symbolCLM (e i j) ((coordinateDerivative i w).toLp 2 volume))
          (P.forward (coordinateDerivative j H) u) +
        inner ℂ ((coordinateDerivative i w).toLp 2 volume) (U i j) -
        inner ℂ (P.adjoint (coordinateDerivative i H) w)
          (symbolCLM (e i j) ((coordinateDerivative j u).toLp 2 volume))) := by
    rw [boundedWeakDivergenceCommutatorPair_threeTerms]
    simp_rw [hPair]
    rfl
  have opBound (i j : Index) (v : LP2) : ‖symbolCLM (e i j) v‖ ≤ D * ‖v‖ :=
    symbolL2_norm_le (e i j) v
  have one (i j : Index) :
      ‖inner ℂ (symbolCLM (e i j) ((coordinateDerivative i u).toLp 2 volume))
        (P.forward (coordinateDerivative j H) u)‖ ≤
      D * ‖P.forward (coordinateDerivative j H) u‖ * ‖(coordinateDerivative i u).toLp 2 volume‖ := by
    refine (norm_inner_le_norm _ _).trans ?_
    exact (mul_le_mul_of_nonneg_right (opBound i j _) (norm_nonneg _)).trans_eq (by ring)
  have two (i j : Index) :
      ‖inner ℂ ((coordinateDerivative i u).toLp 2 volume) (U i j)‖ ≤
        ‖U i j‖ * ‖(coordinateDerivative i u).toLp 2 volume‖ := by
    simpa only [mul_comm] using
      (norm_inner_le_norm ((coordinateDerivative i u).toLp 2 volume) (U i j))
  have three (i j : Index) :
      ‖inner ℂ (P.adjoint (coordinateDerivative i H) u)
        (symbolCLM (e i j) ((coordinateDerivative j u).toLp 2 volume))‖ ≤
        D * ‖(coordinateDerivative j u).toLp 2 volume‖ * ‖P.adjoint (coordinateDerivative i H) u‖ := by
    refine (norm_inner_le_norm _ _).trans ?_
    exact (mul_le_mul_of_nonneg_left (opBound i j _) (norm_nonneg _)).trans_eq (by ring)
  refine ⟨U, fun i j z => (hUtest i j z).1, hU, hThree, fun i j => ⟨one i j, two i j, three i j⟩, ?_⟩
  let X₀ := schwartzGradientNorm 2 u
  let X := schwartzGradientNorm 4 u
  let Y := schwartzGradientNorm 4 H
  let Z := ‖H.toLp 4 volume‖
  have hX : 0 ≤ X := schwartzGradientNorm_nonneg 4 u
  have hX₀ : 0 ≤ X₀ := schwartzGradientNorm_nonneg 2 u
  have hY : 0 ≤ Y := schwartzGradientNorm_nonneg 4 H
  have hZ : 0 ≤ Z := norm_nonneg _
  have hDer (j : Index) :
      ‖P.forward (coordinateDerivative j H) u‖ ≤ C*Y*X ∧
      ‖P.adjoint (coordinateDerivative j H) u‖ ≤ C*Y*X := by
    have upper := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (coordinateDerivative_norm_le_gradient 4 H j) hC) hX
    exact ⟨(P.derivative_first_order j H u).1.trans upper, (P.derivative_first_order j H u).2.trans upper⟩
  have hUbound (i j : Index) : ‖U i j‖ ≤ C*G*Z*X := by
    refine (hU i j).trans ?_
    calc
      _ ≤ (C*G*Z)*‖(coordinateDerivative j u).toLp 4 volume‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hgrad i j) hC) hZ) (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (coordinateDerivative_norm_le_gradient 4 u j) (by positivity)
  have hOne (i j : Index) :
      ‖inner ℂ (symbolCLM (e i j) ((coordinateDerivative i u).toLp 2 volume))
        (P.forward (coordinateDerivative j H) u)‖ ≤ D*(C*Y*X)*X₀ :=
    (one i j).trans (mul_le_mul (mul_le_mul_of_nonneg_left (hDer j).1 hD)
      (coordinateDerivative_norm_le_gradient 2 u i) (norm_nonneg _) (by positivity))
  have hTwo (i j : Index) :
      ‖inner ℂ ((coordinateDerivative i u).toLp 2 volume) (U i j)‖ ≤ (C*G*Z*X)*X₀ :=
    (two i j).trans (mul_le_mul (hUbound i j) (coordinateDerivative_norm_le_gradient 2 u i)
      (norm_nonneg _) (by positivity))
  have hThreeBound (i j : Index) :
      ‖inner ℂ (P.adjoint (coordinateDerivative i H) u)
        (symbolCLM (e i j) ((coordinateDerivative j u).toLp 2 volume))‖ ≤ D*X₀*(C*Y*X) :=
    (three i j).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (coordinateDerivative_norm_le_gradient 2 u j) hD)
      (hDer i).2 (norm_nonneg _) (by positivity))
  let term (i j : Index) : ℂ :=
    inner ℂ (symbolCLM (e i j) ((coordinateDerivative i u).toLp 2 volume))
      (P.forward (coordinateDerivative j H) u) +
    inner ℂ ((coordinateDerivative i u).toLp 2 volume) (U i j) -
    inner ℂ (P.adjoint (coordinateDerivative i H) u)
      (symbolCLM (e i j) ((coordinateDerivative j u).toLp 2 volume))
  let cap := D*(C*Y*X)*X₀ + (C*G*Z*X)*X₀ + D*X₀*(C*Y*X)
  have hEntry (i j : Index) : ‖term i j‖ ≤ cap :=
    (norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (hOne i j) (hTwo i j))) (hThreeBound i j))
  calc
    _ = ‖∑ i : Index, ∑ j : Index, term i j‖ := by rw [norm_mul, Complex.norm_I, one_mul, hThree]
    _ ≤ ∑ i : Index, ‖∑ j : Index, term i j‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Index, ∑ _j : Index, cap :=
      Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hEntry i j)
    _ = 32*C*(D*X₀*Y*X) + 16*C*(G*X₀*Z*X) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, cap]
      ring
    _ ≤ 32*C*(D*X₀*Y*X) + 32*C*(G*X₀*Z*X) :=
      add_le_add_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num : (16 : ℝ) ≤ 32) hC)
          (by positivity)) _
    _ = _ := by
      change _ = 32*C*(D*X₀*Y*X + G*X₀*Z*X)
      ring

end Burnett.A08
