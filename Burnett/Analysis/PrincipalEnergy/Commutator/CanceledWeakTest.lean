import Burnett.Analysis.PrincipalEnergy.Commutator.ActualCanceledForm
import Burnett.Analysis.PrincipalEnergy.Quantization.ActualWeakBall
import Burnett.Analysis.PrincipalEnergy.Commutator.BumpScale

set_option autoImplicit false
set_option maxHeartbeats 2700000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection unitBallVolume unitBallVolume_nonneg schwartz_ball_norm_le)
open scoped NNReal ComplexConjugate InnerProductSpace

/-- The true normalized-ball weak test passes to the canceled form using
the two L² estimates for the physical paraproduct and its exchanged pairing. -/
theorem exists_canceledCoefficientPair_normalizedBall_weakBound
    {a : Space → Space → ℂ} (ha : FrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (hSym : FirstOrderFormalSymmetry a)
    (M : ℝ) (hM : 0≤M) :
    ∃ C : ℝ, 0≤C ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0≤U → (∀ x, conj (r x)=r x) → LipschitzWith L r → (∀ x, ‖r x‖≤U) →
      ∀ (P : SchwartzMap Space ℂ → ComplexL2 Space),
      (∀ f, ‖P f‖≤M*(U+(L:ℝ))*‖f.toLp 2 volume‖) →
      ∀ (c : Space) (ρ : ℝ), 0<ρ → ∀ (f g : SchwartzMap Space ℂ),
      tsupport (f : Space → ℂ) ⊆ Metric.closedBall c ρ →
      tsupport (g : Space → ℂ) ⊆ Metric.closedBall c ρ →
      (∀ x, ‖f x‖≤1) → (∀ x, ‖g x‖≤1) →
      (∀ (j : Fin 4) x, ‖fderiv ℝ (⇑f) x (coordinateDirection j)‖≤ρ⁻¹) →
      (∀ (j : Fin 4) x, ‖fderiv ℝ (⇑g) x (coordinateDirection j)‖≤ρ⁻¹) →
      ‖canceledCoefficientPair a r P f g‖≤C*(U+(L:ℝ))*ρ^4 := by
  obtain ⟨K,hK,hWeak⟩ := exists_actualCoefficientCommutator_normalizedBall_weakBound ha hBase hCont hSym
  refine ⟨K+2*M*unitBallVolume,add_nonneg hK
    (mul_nonneg (mul_nonneg (by norm_num) hM) unitBallVolume_nonneg),?_⟩
  intro r L U hU hReal hLip hR P hP c ρ hρ f g hf hg hF hG hF₁ hG₁
  let B := ρ^2*Real.sqrt unitBallVolume
  have hB : 0≤B := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hBoth : ‖f.toLp 2 volume‖*‖g.toLp 2 volume‖≤ρ^4*unitBallVolume := by
    have hFL : ‖f.toLp 2 volume‖≤B := by
      simpa only [one_mul] using schwartz_ball_norm_le f c ρ 1 hρ.le zero_le_one hf hF
    have hGL : ‖g.toLp 2 volume‖≤B := by
      simpa only [one_mul] using schwartz_ball_norm_le g c ρ 1 hρ.le zero_le_one hg hG
    refine (mul_le_mul hFL hGL (norm_nonneg _) hB).trans_eq ?_
    dsimp only [B]
    rw [show ρ^2*Real.sqrt unitBallVolume*(ρ^2*Real.sqrt unitBallVolume) =
      ρ^4*(Real.sqrt unitBallVolume)^2 by ring,Real.sq_sqrt unitBallVolume_nonneg]
  let J := M*(U+(L:ℝ))
  have hJ : 0≤J := mul_nonneg hM (add_nonneg hU L.coe_nonneg)
  have hP₁ : ‖inner ℂ (g.toLp 2 volume) (P f)‖≤J*(ρ^4*unitBallVolume) := by
    calc
      _ ≤ ‖g.toLp 2 volume‖*‖P f‖ := norm_inner_le_norm _ _
      _ ≤ ‖g.toLp 2 volume‖*(J*‖f.toLp 2 volume‖) := mul_le_mul_of_nonneg_left (hP f) (norm_nonneg _)
      _ = J*(‖f.toLp 2 volume‖*‖g.toLp 2 volume‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hBoth hJ
  have hP₂ : ‖inner ℂ (P g) (f.toLp 2 volume)‖≤J*(ρ^4*unitBallVolume) := by
    calc
      _ ≤ ‖P g‖*‖f.toLp 2 volume‖ := norm_inner_le_norm _ _
      _ ≤ (J*‖g.toLp 2 volume‖)*‖f.toLp 2 volume‖ := mul_le_mul_of_nonneg_right (hP g) (norm_nonneg _)
      _ = J*(‖f.toLp 2 volume‖*‖g.toLp 2 volume‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hBoth hJ
  let T := ∫ x, conj (g x)*actualCoefficientCommutator a r f x
  let X := inner ℂ (g.toLp 2 volume) (P f)
  let Y := inner ℂ (P g) (f.toLp 2 volume)
  change ‖T-X+Y‖≤_
  calc
    _ ≤ ‖T‖+‖X‖+‖Y‖ := (norm_add_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
    _ ≤ K*(U+(L:ℝ))*ρ^4+J*(ρ^4*unitBallVolume)+J*(ρ^4*unitBallVolume) :=
      add_le_add (add_le_add (hWeak r L U hU hReal hLip hR c ρ hρ f g hf hg hF hG hF₁ hG₁) hP₁) hP₂
    _ = _ := by dsimp only [J]; ring

end Burnett.Analysis.CarlesonEmbedding
