import Burnett.Analysis.PrincipalEnergy.Commutator.WeakBoundCoordinates
import Burnett.Analysis.PrincipalEnergy.Commutator.BumpScale

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.Analysis.SymmetricEnergy

open MeasureTheory
open scoped InnerProductSpace SchwartzMap ComplexConjugate

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

/-- Weak boundedness on normalized overlapping ball tests. The operator's
order-one map is explicit, and no disjoint-support hypothesis appears. -/
theorem coordinate_commutator_normalizedBall_weakBound (r : 𝓢(Space, ℂ)) (L : NNReal)
    (hReal : ∀ z : Space, conj (r z) = r z) (hLip : LipschitzWith L r)
    (B : 𝓢(Space, F) →ₗ[ℂ] 𝓢(Space, F)) (hSym : (transportSchwartzOp B).IsSymmetric)
    (K : ℝ) (hK : 0 ≤ K) (hMap : ∀ u : 𝓢(Space, F), ‖(B u).toLp 2 volume‖ ≤ K * coordinateH1 u)
    (c : Space) (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ 1) (f g : 𝓢(Space, F))
    (hf : tsupport (f : Space → F) ⊆ Metric.closedBall c ρ)
    (hg : tsupport (g : Space → F) ⊆ Metric.closedBall c ρ)
    (hf₀ : ∀ x, ‖f x‖ ≤ 1) (hg₀ : ∀ x, ‖g x‖ ≤ 1)
    (hf₁ : ∀ (j : Fin 4) x, ‖fderiv ℝ (⇑f) x (coordinateDirection j)‖ ≤ ρ⁻¹)
    (hg₁ : ∀ (j : Fin 4) x, ‖fderiv ℝ (⇑g) x (coordinateDirection j)‖ ≤ ρ⁻¹) :
    ‖∫ x, ⟪scalarSchwartzMultiplier r (B f) x - B (scalarSchwartzMultiplier r f) x, g x⟫_ℂ‖ ≤
      2 * K * (L : ℝ) * Real.sqrt (5*unitBallVolume) * Real.sqrt unitBallVolume * ρ^4 := by
  obtain ⟨hfL, hfH⟩ := normalizedBallTest_norms f c ρ hρ hr hf hf₀ hf₁
  obtain ⟨hgL, hgH⟩ := normalizedBallTest_norms g c ρ hρ hr hg hg₀ hg₁
  have hy := coordinate_commutator_weakPair_bound r L hReal hLip B hSym K hMap c ρ hρ.le f g hf hg
  have h₁ : coordinateH1 f * ‖g.toLp 2 volume‖ ≤
      (ρ * Real.sqrt (5*unitBallVolume)) * (ρ^2 * Real.sqrt unitBallVolume) :=
    mul_le_mul hfH hgL (norm_nonneg _) (by positivity)
  have h₂ : ‖f.toLp 2 volume‖ * coordinateH1 g ≤
      (ρ^2 * Real.sqrt unitBallVolume) * (ρ * Real.sqrt (5*unitBallVolume)) :=
    mul_le_mul hfL hgH (Real.sqrt_nonneg _) (by positivity)
  exact hy.trans ((mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by positivity)).trans_eq (by ring))

end Burnett.Analysis.SymmetricEnergy
