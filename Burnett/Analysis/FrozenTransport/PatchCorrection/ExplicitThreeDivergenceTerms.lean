import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalMixedWeakEnergy

set_option autoImplicit false
set_option maxRecDepth 4400
set_option maxHeartbeats 6500000
noncomputable section
namespace Burnett.V11
open Burnett.A07 Burnett.A06 Burnett.A08 Burnett.A02.FrequencySplit
open Set Metric MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff ENNReal NNReal
open private inner_eq_of_schwartz from Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension
open private schwartzGradientNorm_nonneg coordinateDerivative_norm_le_gradient highDerivativeLp4Sum_le_gradient multiplier_norm_le from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalWeakDivergenceCommutator
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
private abbrev Field := SchwartzMap E ℂ
private abbrev LP2 := FirstOrderLp 2
private abbrev Index := Fin 4

/-- All three tested variable-divergence terms on independent high slots, with
their respective low derivatives or coefficient derivative and their signs. -/
theorem exists_originalAngular_threeDivergenceTerms
    (η χ : ℝ → ℝ) {r ρ R₀ : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1/2) (hR : 1 ≤ R₀)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R₀, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
    ∃ (K : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)},
      IsOpen W → Q ×ˢ sphere (0 : RotationSpace) 1 ⊆ W → ContDiffOn ℝ ∞ F W →
      ∀ M : ℝ, 0 ≤ M →
      (∀ n ≤ K, ∀ p ∈ Q, ∀ x : RoundSphere3,
        ‖iteratedFDeriv ℝ n F (p, (x : RotationSpace))‖ ≤ M) →
      ∀ (d : Index → Index → SchwartzMap E ℝ), (∀ a b, d a b = d b a) →
      ∀ (D : ℝ), 0 ≤ D → (∀ a b x, |d a b x| ≤ D) →
      ∀ (L : ℝ≥0), (∀ a b x, ‖fderiv ℝ (d a b : E → ℝ) x‖ ≤ (L : ℝ)) →
      ∀ H : Field, ∃ (T Tstar : Field → LP2) (A B : Index → Field → LP2),
        (∀ u w : Field, inner ℂ (w.toLp 2 volume) (T u) =
          radianHighPair (originalRegularizedAngularSymbol η χ F) H u w ∧
          inner ℂ (w.toLp 2 volume) (T u) = inner ℂ (Tstar w) (u.toLp 2 volume)) ∧
        (∀ (a : Index) (u w : Field), inner ℂ (w.toLp 2 volume) (A a u) =
          radianHighPair (originalRegularizedAngularSymbol η χ F) (coordinateDerivative a H) u w ∧
          inner ℂ (w.toLp 2 volume) (B a u) = radianHighPair (highAdjointSymbol (originalRegularizedAngularSymbol η χ F))
            (fun x => conj (coordinateDerivative a H x)) u w) ∧
        ∀ u w : Field,
        let left (a b : Index) := inner ℂ ((realSchwartzMultiply (d a b) (coordinateDerivative a w)).toLp 2 volume) (A b u)
        let middle (a b : Index) := inner ℂ ((coordinateDerivative a w).toLp 2 volume) (coefficientCommutatorOutput (d a b) T (coordinateDerivative b u))
        let right (a b : Index) := inner ℂ (B a w) ((realSchwartzMultiply (d a b) (coordinateDerivative b u)).toLp 2 volume)
        weakDivergenceCommutatorPair d T u w = ∑ a, ∑ b, (left a b + middle a b - right a b) ∧
        ∀ a b,
          ‖left a b‖ ≤ (D * schwartzGradientNorm 2 w) * (C*M*schwartzGradientNorm 4 H*schwartzGradientNorm 4 u) ∧
          ‖middle a b‖ ≤ schwartzGradientNorm 2 w * (C*M*(L : ℝ)*‖H.toLp 4 volume‖*schwartzGradientNorm 4 u) ∧
          ‖right a b‖ ≤ (C*M*schwartzGradientNorm 4 H*schwartzGradientNorm 4 w) * (D*schwartzGradientNorm 2 u) := by
  obtain ⟨K₀, C₀, _, hWeak⟩ := exists_originalAngular_weakDivergence_commutator_bound
    η χ hr hρ hsmall hR hη hzero hone hχ hcut
  obtain ⟨Corder, hCorder, hFirst⟩ := exists_originalAngular_highAdjoint_firstOrder_and_coordinate_commutator
    η χ hr hρ (hsmall.trans (by norm_num)) hR hη hzero hone hχ hcut
  obtain ⟨Kr, Cr, hCr, hRough⟩ := exists_originalAngular_realSchwartz_roughCommutator
    η χ hr hρ hsmall hR hη hzero hone hχ hcut
  let C := 4 * Corder + Cr
  have hC : 0 ≤ C := add_nonneg (mul_nonneg (by norm_num) hCorder) hCr
  refine ⟨max K₀ (max 27 Kr), C, hC, ?_⟩
  intro F W hW hQ hF M hM hJet d hd D hD hMag L hSlope H
  obtain ⟨P, A, B, hP, hAB, hTerms, _⟩ := hWeak hW hQ hF M hM
    (fun n hn => hJet n (hn.trans (Nat.le_max_left K₀ _))) d hd D hD hMag L hSlope H
  obtain ⟨T, S, hT, hS, hPair, _⟩ := hFirst hW hQ hF M hM
    (fun n hn => hJet n (hn.trans ((Nat.le_max_left 27 Kr).trans (Nat.le_max_right K₀ _))))
  have jetKr n (hn : n ≤ Kr) := hJet n
    (hn.trans ((Nat.le_max_right 27 Kr).trans (Nat.le_max_right K₀ _)))
  have same (v : Field) : T v (H.toLp 4 volume) = P v :=
    inner_eq_of_schwartz (fun w => (hPair H v w).1.trans (hP v w).symm)
  have dual (v w : Field) : inner ℂ (w.toLp 2 volume) (P v) = inner ℂ (S H w) (v.toLp 2 volume) := by
    rw [← inner_conj_symm (S H w), (hPair H w v).2.2, starRingEnd_self_apply, same]
  refine ⟨P, S H, A, B, fun u w => ⟨hP u w, dual u w⟩, hAB, ?_⟩
  intro u w left middle right
  refine ⟨hTerms u w, ?_⟩
  let U (v : Field) := C * M * schwartzGradientNorm 4 H * schwartzGradientNorm 4 v
  let V (v : Field) := C * M * (L : ℝ) * ‖H.toLp 4 volume‖ * schwartzGradientNorm 4 v
  have hG₂ (v : Field) : 0 ≤ schwartzGradientNorm 2 v := schwartzGradientNorm_nonneg _ _
  have hG₄ (v : Field) : 0 ≤ schwartzGradientNorm 4 v := schwartzGradientNorm_nonneg _ _
  have hU (v : Field) : 0 ≤ U v :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hM) (hG₄ H)) (hG₄ v)
  have oneDerivative (a : Index) (v : Field) {x : LP2}
      (hx : ‖x‖ ≤ Corder * M * ‖(coordinateDerivative a H).toLp 4 volume‖ * highDerivativeLp4Sum v) :
      ‖x‖ ≤ U v := by
    calc
      _ ≤ Corder * M * schwartzGradientNorm 4 H * (4 * schwartzGradientNorm 4 v) :=
        hx.trans (mul_le_mul
          (mul_le_mul_of_nonneg_left (coordinateDerivative_norm_le_gradient 4 H a) (mul_nonneg hCorder hM))
          (highDerivativeLp4Sum_le_gradient v) (highDerivativeLp4Sum_nonneg v)
          (mul_nonneg (mul_nonneg hCorder hM) (hG₄ H)))
      _ = (4 * Corder) * M * schwartzGradientNorm 4 H * schwartzGradientNorm 4 v := by ring
      _ ≤ U v := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCr) hM) (hG₄ H)) (hG₄ v)
  have boundA (b : Index) : ‖A b u‖ ≤ U u := by
    have eq : A b u = T u ((coordinateDerivative b H).toLp 4 volume) :=
      inner_eq_of_schwartz (fun v => (hAB b u v).1.trans (hPair (coordinateDerivative b H) u v).1.symm)
    rw [eq]
    exact oneDerivative b u (hT u _)
  have boundB (a : Index) : ‖B a w‖ ≤ U w := by
    have eq : B a w = S (coordinateDerivative a H) w :=
      inner_eq_of_schwartz (fun v => (hAB a w v).2.trans (hPair (coordinateDerivative a H) w v).2.1.symm)
    rw [eq]
    exact oneDerivative a w (hS _ w)
  have roughBound (a b : Index) :
      ‖coefficientCommutatorOutput (d a b) P (coordinateDerivative b u)‖ ≤ V u := by
    let f := coordinateDerivative b u
    have lip : LipschitzWith L (d a b : E → ℝ) :=
      lipschitzWith_of_nnnorm_fderiv_le (d a b).differentiable (fun x => hSlope a b x)
    obtain ⟨P₁, P₂, identities, normR, _⟩ := hRough hW hQ hF M hM jetKr (d a b) L lip f
    have eq₁ : P₁ (H.toLp 4 volume) = P f :=
      inner_eq_of_schwartz (fun v => (identities H v).1.trans (hP f v).symm)
    have eq₂ : P₂ (H.toLp 4 volume) = P (realSchwartzMultiply (d a b) f) :=
      inner_eq_of_schwartz (fun v => (identities H v).2.trans (hP _ v).symm)
    have bound := normR (H.toLp 4 volume)
    rw [eq₁, eq₂] at bound
    have hK : 0 ≤ Cr * M * (L : ℝ) * ‖H.toLp 4 volume‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg hCr hM) L.coe_nonneg) (norm_nonneg _)
    refine bound.trans ((mul_le_mul_of_nonneg_left (coordinateDerivative_norm_le_gradient 4 u b) hK).trans ?_)
    have hCrC : Cr ≤ C := le_add_of_nonneg_left (mul_nonneg (by norm_num) hCorder)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCrC hM) L.coe_nonneg)
      (norm_nonneg _)) (hG₄ u)
  have boundMultiplied (a b j : Index) (v : Field) :
      ‖(realSchwartzMultiply (d a b) (coordinateDerivative j v)).toLp 2 volume‖ ≤
        D * schwartzGradientNorm 2 v :=
    (multiplier_norm_le (d a b) D hD (hMag a b) _).trans
      (mul_le_mul_of_nonneg_left (coordinateDerivative_norm_le_gradient 2 v j) hD)
  intro a b
  exact ⟨(norm_inner_le_norm _ _).trans (mul_le_mul (boundMultiplied a b a w) (boundA b) (norm_nonneg _) (mul_nonneg hD (hG₂ w))),
    (norm_inner_le_norm _ _).trans (mul_le_mul (coordinateDerivative_norm_le_gradient 2 w a) (roughBound a b) (norm_nonneg _) (hG₂ w)),
    (norm_inner_le_norm _ _).trans (mul_le_mul (boundB a) (boundMultiplied a b b u) (norm_nonneg _) (hU w))⟩

end Burnett.V11
