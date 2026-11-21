import Burnett.Analysis.PrincipalEnergy.Commutator.LocalOscillationRamp
import Burnett.Analysis.PrincipalEnergy.Quantization.CompactHighAction
import Burnett.Analysis.PrincipalEnergy.Commutator.BumpScale

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Metric Burnett.Microlocal.AngularDyadicKernel
open Burnett.Microlocal.HminusReverse Burnett.Analysis.SymmetricEnergy
open scoped BigOperators

/-- The four directional derivatives of the actual localized scalar input
obey the radius-four-ball Schwartz energy bound uniformly in the radius. -/
theorem localOscillationRamp_H1_le (r χ : SchwartzMap E ℂ) (L : NNReal)
    (hLip : LipschitzWith L r) (U D : ℝ) (hU : 0 ≤ U) (hD : 0 ≤ D)
    (hValue : ∀ y : E, ‖r y‖ ≤ U) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχS : tsupport (χ : E → ℂ) ⊆ closedBall 0 2) (hχVal : ∀ y : E, ‖χ y‖ ≤ 1)
    (hχDer : ∀ y : E, ‖fderiv ℝ (χ : E → ℂ) y‖ ≤ D) (c : E) {R : ℝ} (hR : 0 < R) :
    schwartzH1Energy (localOscillationRamp r χ hχ c hR) ≤
      (unitBallVolume * (4*R)^4) * ((2*U)^2 + 4*((1+2*D)*(L : ℝ))^2) := by
  let f := localOscillationRamp r χ hχ c hR
  obtain ⟨hSupp,hAmp,hDer⟩ := localOscillationRamp_bounds r χ L hLip U D hD
    hValue hχ hχS hχVal hχDer c hR
  let A := (1+2*D)*(L : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR4 : 0 ≤ 4*R := by positivity
  let G (i : Fin 4) := SchwartzMap.pderivCLM ℂ (EuclideanSpace.single i 1) f
  have hF : ‖f.toLp 2 volume‖ ≤ (2*U)*(4*R)^2*Real.sqrt unitBallVolume :=
    schwartz_ball_norm_le f c (4*R) (2*U) hR4 (by positivity) hSupp hAmp
  have hG (i : Fin 4) : ‖(G i).toLp 2 volume‖ ≤ A*(4*R)^2*Real.sqrt unitBallVolume := by
    apply schwartz_ball_norm_le (G i) c (4*R) A hR4 hA
    · apply closure_minimal _ isClosed_closedBall
      intro y hy
      exact hSupp (support_fderiv_subset ℝ (fun he => hy (by
        change fderiv ℝ (f : E → ℂ) y (EuclideanSpace.single i 1) = 0
        rw [he,ContinuousLinearMap.zero_apply])))
    · intro y
      change ‖fderiv ℝ (f : E → ℂ) y (EuclideanSpace.single i 1)‖ ≤ A
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [show ‖(EuclideanSpace.single i (1 : ℝ) : E)‖ = 1 by simp, mul_one]
      exact hDer y
  change ‖f.toLp 2 volume‖^2 + ∑ i : Fin 4, ‖(G i).toLp 2 volume‖^2 ≤ _
  calc
    _ ≤ ((2*U)*(4*R)^2*Real.sqrt unitBallVolume)^2 +
        ∑ _i : Fin 4, (A*(4*R)^2*Real.sqrt unitBallVolume)^2 :=
      add_le_add ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hF)
        (Finset.sum_le_sum fun i _ => (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hG i))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,
        mul_pow, Real.sq_sqrt unitBallVolume_nonneg,A]
      ring

end Burnett.Analysis.FirstOrderDyadic
