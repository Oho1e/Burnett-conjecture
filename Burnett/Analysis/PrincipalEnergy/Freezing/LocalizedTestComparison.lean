import Burnett.Analysis.PrincipalEnergy.Freezing.WeylFrequencyShift
import Burnett.Analysis.TransportWard.Weyl.Amplitude.LocalizedPrincipalTest
import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianCommutator
import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedEnergyFields

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Burnett.A03

open MeasureTheory Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal

/-- Exact principal comparison for an actual separated slanted mode and an
actual frozen scalar multiplier, with the same spatial cutoff on both sides. -/
theorem localized_radian_slant_frozen_principal_comparison
    (θ f u : SchwartzMap E ℂ) (b b₀ : E → ℝ) (σ : ℝ) (x : E) :
    sandwichedScalarTest θ (fun v y => separatedRadianQuantization σ b f v y - radianAction b₀ v y) u x -
      (θ x)^2 * (f x * radianAction b u x - radianAction b₀ u x) =
      θ x * separatedRadianSlantRemainder σ b f (energyProduct θ u) x +
      θ x * f x * radianCommutator b θ u x - θ x * radianCommutator b₀ θ u x := by
  unfold sandwichedScalarTest separatedRadianSlantRemainder
  change θ x * (separatedRadianQuantization σ b f (energyProduct θ u) x -
      radianAction b₀ (energyProduct θ u) x) - (θ x)^2 * (f x * radianAction b u x - radianAction b₀ u x) =
      θ x * (separatedRadianQuantization σ b f (energyProduct θ u) x -
        f x * radianAction b (energyProduct θ u) x) +
      θ x * f x * (radianAction b (energyProduct θ u) x - θ x * radianAction b u x) -
      θ x * (radianAction b₀ (energyProduct θ u) x - θ x * radianAction b₀ u x)
  ring

/-- Localizing a genuine order-zero action preserves its W¹,³ estimate.
The cutoff derivative occurs only with the undifferentiated input. -/
theorem sandwiched_order_zero_action_W13
    (θ : SchwartzMap E ℂ) (Q : SchwartzMap E ℂ → E → ℂ) (A B : ℝ≥0∞)
    (hQ : ∀ u : SchwartzMap E ℂ, let p := ENNReal.ofReal 3
      MemLp (Q u) p volume ∧ eLpNorm (Q u) p volume ≤ A * eLpNorm (u : E → ℂ) p volume ∧
      Differentiable ℝ (Q u) ∧
      ∀ j : Index, let d (x : E) := fderiv ℝ (Q u) x (EuclideanSpace.single j 1)
        MemLp d p volume ∧
          eLpNorm d p volume ≤ A * eLpNorm (energyPartial j u : E → ℂ) p volume +
            B * eLpNorm (u : E → ℂ) p volume)
    (u : SchwartzMap E ℂ) :
    let p := ENNReal.ofReal 3
    let P := eLpNorm (θ : E → ℂ) ⊤ volume
    let W := sandwichedScalarTest θ Q u
    MemLp W p volume ∧ eLpNorm W p volume ≤ P ^ 2 * A * eLpNorm (u : E → ℂ) p volume ∧
      Differentiable ℝ W ∧
      ∀ j : Index, let T := eLpNorm (energyPartial j θ : E → ℂ) ⊤ volume
        let d (x : E) := fderiv ℝ W x (EuclideanSpace.single j 1)
        MemLp d p volume ∧ eLpNorm d p volume ≤
          P ^ 2 * A * eLpNorm (energyPartial j u : E → ℂ) p volume +
            (2 * P * T * A + P ^ 2 * B) * eLpNorm (u : E → ℂ) p volume := by
  intro p P W
  let v := energyProduct θ u
  let w := Q v
  let Y := eLpNorm (u : E → ℂ) p volume
  obtain ⟨hV, vBound, hDiff, hGrad⟩ := hQ v
  have H (s : SchwartzMap E ℂ) (g : E → ℂ) (mg : MemLp g p volume) :
      MemLp (fun x => s x * g x) p volume ∧
      eLpNorm (fun x => s x * g x) p volume ≤ eLpNorm (s : E → ℂ) ⊤ volume * eLpNorm g p volume :=
    ⟨mg.mul' (s.memLp ⊤ volume),
      eLpNorm_smul_le_mul_eLpNorm (φ := (s : E → ℂ)) (f := g) (p := ⊤) (q := p) (r := p)
        mg.1 s.continuous.aestronglyMeasurable⟩
  have inp : eLpNorm (v : E → ℂ) p volume ≤ P * Y := energyProduct_eLpNorm_le p θ u
  have out : eLpNorm w p volume ≤ A * (P * Y) := vBound.trans (mul_le_mul_left' inp _)
  have base := H θ w hV
  refine ⟨base.1, base.2.trans ((mul_le_mul_left' out _).trans_eq (by ring)),
    θ.differentiable.mul hDiff, ?_⟩
  intro j T d
  let Xu := eLpNorm (energyPartial j u : E → ℂ) p volume
  let Dv (x : E) := fderiv ℝ w x (EuclideanSpace.single j 1)
  have dvBound : eLpNorm (energyPartial j v : E → ℂ) p volume ≤ T * Y + P * Xu := by
    have eq : (energyPartial j v : E → ℂ) =
        (energyProduct (energyPartial j θ) u : E → ℂ) + (energyProduct θ (energyPartial j u) : E → ℂ) := by
      funext x
      simp only [v, Pi.add_apply, energyPartial_product, energyProduct_apply]
    rw [eq]
    refine (eLpNorm_add_le (energyProduct (energyPartial j θ) u).continuous.aestronglyMeasurable
      (energyProduct θ (energyPartial j u)).continuous.aestronglyMeasurable (by norm_num [p])).trans ?_
    exact add_le_add (energyProduct_eLpNorm_le p _ _) (energyProduct_eLpNorm_le p _ _)
  have gradBound : eLpNorm Dv p volume ≤ A * (T * Y + P * Xu) + B * (P * Y) :=
    (hGrad j).2.trans (add_le_add (mul_le_mul_left' dvBound _) (mul_le_mul_left' inp _))
  have dEq : d = (fun x => energyPartial j θ x * w x) + (fun x => θ x * Dv x) := by
    funext x
    change fderiv ℝ ((θ : E → ℂ) * w) x (EuclideanSpace.single j 1) =
      energyPartial j θ x * w x + θ x * Dv x
    rw [fderiv_mul (θ.differentiable x) (hDiff x)]
    simp only [Dv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      energyPartial, SchwartzMap.pderivCLM_apply]
    ring
  rw [dEq]
  have a := H (energyPartial j θ) w hV
  have b' := H θ Dv (hGrad j).1
  refine ⟨a.1.add b'.1, (eLpNorm_add_le a.1.1 b'.1.1 (by norm_num [p])).trans ?_⟩
  calc
    _ ≤ T * (A * (P * Y)) + P * (A * (T * Y + P * Xu) + B * (P * Y)) :=
      add_le_add (a.2.trans (mul_le_mul_left' out _)) (b'.2.trans (mul_le_mul_left' gradBound _))
    _ = _ := by change _ = P ^ 2 * A * Xu + (2 * P * T * A + P ^ 2 * B) * Y; ring

end Burnett.A03
