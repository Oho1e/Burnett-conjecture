import Burnett.Analysis.CubicEnergy.AngularCorrection.RoughAngularCoefficientTail
import Burnett.Analysis.CubicEnergy.AngularCorrection.LipschitzWeakQuarticBound

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section

namespace Burnett.A08

open MeasureTheory Burnett.A06 Burnett.A07 Burnett.A02.FrequencySplit Burnett.Fourier
open scoped BigOperators ComplexConjugate ENNReal NNReal

local instance roughAngularWeakTailLpTwo : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance roughAngularWeakTailLpFour : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private abbrev Test := SchwartzMap E ℂ
private abbrev LP2 := FirstOrderLp 2
private abbrev Index := Fin 4

open private inner_eq_of_schwartz
  from Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension

private theorem testedHighCoefficientPair_reverse (T S multiply : Test → LP2) (u w : Test) :
    testedHighCoefficientPair S T multiply u w = -conj (testedHighCoefficientPair T S multiply w u) := by
  simp only [testedHighCoefficientPair, map_sub, inner_conj_symm]
  abel

private theorem testedHighCoefficientPair_hermitian (T S multiply : Test → LP2) (u w : Test) :
    testedHighCoefficientPair (hermitianPartOutput T S) (hermitianPartOutput T S) multiply u w =
      (testedHighCoefficientPair T S multiply u w + testedHighCoefficientPair S T multiply u w) / 2 := by
  have halfReal : conj (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, show conj (2 : ℂ) = 2 from map_ofNat (starRingEnd ℂ) 2]
  simp only [testedHighCoefficientPair, hermitianPartOutput, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, halfReal]
  ring

/-- The three weak divergence pairings, with their actual forward and adjoint slots. -/
def testedHighDivergencePair (T S : Test → Test → LP2)
    (d : Index → Index → BoundedSymbol E) (H u w : Test) : ℂ :=
  ∑ i : Index, ∑ j : Index,
    (inner ℂ (symbolCLM (d i j) ((coordinateDerivative i w).toLp 2 volume))
        (T (coordinateDerivative j H) u) +
      testedHighCoefficientPair (T H) (S H) (fun v => symbolCLM (d i j) (v.toLp 2 volume))
        (coordinateDerivative j u) (coordinateDerivative i w) -
      inner ℂ (S (coordinateDerivative i H) w)
        (symbolCLM (d i j) ((coordinateDerivative j u).toLp 2 volume)))

theorem boundedWeakDivergenceCommutatorPair_eq_testedHighDivergencePair {b : Joint → ℂ} {C : ℝ}
    (P : OriginalAnalyticCorrectionBounds b C) (d : Index → Index → BoundedSymbol E) (H u w : Test) :
    boundedWeakDivergenceCommutatorPair P d H u w = testedHighDivergencePair P.forward P.adjoint d H u w := by
  exact boundedWeakDivergenceCommutatorPair_threeTerms P d H u w

namespace OriginalAngularCutoff

variable {η χ : ℝ → ℝ} {F : Joint × RotationSpace → ℂ} {M C₀ C₁ : ℝ}

/-- The Hermitian angular error uses the same forward and high adjoint cutoffs. -/
def hermitianAngularTail (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ) (H u : Test) : LP2 :=
  P.partialHermitian L H u - P.fullHermitian H u

theorem hermitianAngularTail_eq (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ) (H : Test) :
    P.hermitianAngularTail L H = hermitianPartOutput (P.forwardAngularTail L H) (P.adjointAngularTail L H) := by
  funext u
  simp only [hermitianAngularTail, partialHermitian, fullHermitian, forwardAngularTail, adjointAngularTail,
    hermitianPartOutput]
  rw [← smul_sub]
  congr 1
  abel

/-- Subtracting the two weak pairings acts on each term by the same Hermitian
angular error. The low field, coefficient and differentiated tests are fixed. -/
theorem testedHighDivergencePair_angularTail (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ)
    (d : Index → Index → BoundedSymbol E) (H u w : Test) :
    testedHighDivergencePair (P.partialHermitian L) (P.partialHermitian L) d H u w -
      testedHighDivergencePair P.fullHermitian P.fullHermitian d H u w =
      testedHighDivergencePair (P.hermitianAngularTail L) (P.hermitianAngularTail L) d H u w := by
  unfold testedHighDivergencePair hermitianAngularTail
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [testedHighCoefficientPair_sub, inner_sub_left, inner_sub_right]
  abel

/-- For a genuinely Hermitian original correction the full term is the
ordinary weak divergence pairing. Its differentiated low inputs are also
Hermitian by the two actual coordinate commutator identities. -/
theorem originalWeakDivergenceCommutatorPair_angularTail
    (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ) {C : ℝ}
    (Q : OriginalAnalyticCorrectionBounds (originalRegularizedAngularSymbol η χ F) C)
    (d : Index → Index → BoundedSymbol E) (H u w : Test)
    (hHerm : ∀ v z : Test, inner ℂ (z.toLp 2 volume) (Q.forward H v) =
      inner ℂ (Q.forward H z) (v.toLp 2 volume)) :
    testedHighDivergencePair (P.partialHermitian L) (P.partialHermitian L) d H u w -
      boundedWeakDivergenceCommutatorPair Q d H u w =
      testedHighDivergencePair (P.hermitianAngularTail L) (P.hermitianAngularTail L) d H u w := by
  have low : Q.adjoint H = Q.forward H := by
    funext v
    apply inner_eq_of_schwartz
    intro z
    have dual := (Q.adjoint_duality H z v).symm.trans (hHerm z v)
    simpa only [inner_conj_symm] using congrArg (conj : ℂ → ℂ) dual
  have derivative (i : Index) : Q.adjoint (coordinateDerivative i H) = Q.forward (coordinateDerivative i H) := by
    funext v
    apply inner_eq_of_schwartz
    intro z
    rw [← (Q.coordinate_commutator i H v z).2, ← (Q.coordinate_commutator i H v z).1, low]
  have matched (G : Test) (eq : Q.adjoint G = Q.forward G) : P.fullHermitian G = Q.forward G := by
    rw [P.fullHermitian_eq_of_pairs G (Q.forward G) (Q.adjoint G) (Q.forward_pair G) (Q.adjoint_pair G), eq]
    funext v
    rw [hermitianPartOutput, ← two_smul ℂ, smul_smul]
    norm_num
  have full : testedHighDivergencePair P.fullHermitian P.fullHermitian d H u w =
      boundedWeakDivergenceCommutatorPair Q d H u w := by
    rw [boundedWeakDivergenceCommutatorPair_eq_testedHighDivergencePair]
    simp only [testedHighDivergencePair, matched H low, fun i => matched _ (derivative i), low, derivative]
  rw [← full]
  exact P.testedHighDivergencePair_angularTail L d H u w

/-- The three weak rough-commutator pairings have the same degree decay on
the original cutoff, uniformly over bounded Lipschitz coefficients. -/
theorem exists_boundedLipschitzWeakDivergenceAngularTails :
    ∃ K : ℝ≥0, 1 ≤ K ∧
      ∀ {η χ : ℝ → ℝ} {F : Joint × RotationSpace → ℂ} {M C₀ C₁ : ℝ}
        (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ)
        (d : E → ℝ) (D : ℝ) (hD : 0 ≤ D) (hbound : ∀ x, |d x| ≤ D)
        (ℓ : ℝ≥0) (hLip : LipschitzWith ℓ d) (H u w : Test) (i j : Index),
        let e := boundedRealCoefficient d D hD hLip.continuous.measurable hbound
        let S := P.hermitianAngularTail L
        let v := coordinateDerivative j u
        let z := coordinateDerivative i w
        let q := ((L : ℝ) + 1)^2
        ‖inner ℂ (symbolCLM e (z.toLp 2 volume)) (S (coordinateDerivative j H) u)‖ ≤
          D * ‖z.toLp 2 volume‖ * (C₀ * M * ‖(coordinateDerivative j H).toLp 4 volume‖ *
            highDerivativeLp4Sum u / q) ∧
        ‖testedHighCoefficientPair (S H) (S H) (fun y => symbolCLM e (y.toLp 2 volume)) v z‖ ≤
          C₁ * M * (K : ℝ) * lipschitzGradientLInfty d * ‖H.toLp 4 volume‖ *
            ‖v.toLp 4 volume‖ * ‖z.toLp 2 volume‖ / q ∧
        ‖inner ℂ (S (coordinateDerivative i H) w) (symbolCLM e (v.toLp 2 volume))‖ ≤
          (C₀ * M * ‖(coordinateDerivative i H).toLp 4 volume‖ * highDerivativeLp4Sum w / q) *
            (D * ‖v.toLp 2 volume‖) := by
  obtain ⟨K,hK,tail⟩ := exists_boundedLipschitzCoefficientAngularTail
  refine ⟨K,hK,?_⟩
  intro η χ F M C₀ C₁ P L d D hD hbound ℓ hLip H u w i j e S v z q
  have hFirst (G y : Test) : ‖S G y‖ ≤ C₀ * M * ‖G.toLp 4 volume‖ * highDerivativeLp4Sum y / q :=
    P.partialHermitian_tail L G y
  have hMul (y : Test) : ‖symbolCLM e (y.toLp 2 volume)‖ ≤ D * ‖y.toLp 2 volume‖ :=
    symbolL2_norm_le e (y.toLp 2 volume)
  refine ⟨(norm_inner_le_norm _ _).trans (mul_le_mul (hMul z) (hFirst _ u) (norm_nonneg _) (by positivity)), ?_,
    (norm_inner_le_norm _ _).trans (mul_le_mul (hFirst _ w) (hMul v) (norm_nonneg _) ?_)⟩
  · let T := P.forwardAngularTail L H
    let A := P.adjointAngularTail L H
    let multiply (y : Test) := symbolCLM e (y.toLp 2 volume)
    let limit := C₁ * M * (K : ℝ) * lipschitzGradientLInfty d * ‖H.toLp 4 volume‖ *
      ‖v.toLp 4 volume‖ * ‖z.toLp 2 volume‖ / q
    have hF : ‖testedHighCoefficientPair T A multiply v z‖ ≤ limit :=
      (tail P L d D hD hbound ℓ hLip H v z).1
    have hA : ‖testedHighCoefficientPair A T multiply v z‖ ≤ limit := by
      rw [testedHighCoefficientPair_reverse, norm_neg, Complex.norm_conj]
      simpa only [limit, mul_assoc, mul_comm, mul_left_comm] using (tail P L d D hD hbound ℓ hLip H z v).2
    have hS : S H = hermitianPartOutput T A := P.hermitianAngularTail_eq L H
    change ‖testedHighCoefficientPair (S H) (S H) multiply v z‖ ≤ limit
    rw [hS, testedHighCoefficientPair_hermitian, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    exact (div_le_div_of_nonneg_right ((norm_add_le _ _).trans (add_le_add hF hA)) (by norm_num)).trans_eq (by ring)
  · exact (norm_nonneg _).trans (hFirst _ w)

end OriginalAngularCutoff

end Burnett.A08
