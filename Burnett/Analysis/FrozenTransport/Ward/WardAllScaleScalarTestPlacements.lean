import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleScalarTrilinearFourier
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleCyclicCubicExpansion

set_option autoImplicit false
set_option maxRecDepth 6500
set_option maxHeartbeats 4800000

noncomputable section

namespace Burnett.C02

open Set MeasureTheory Burnett.A02.FrequencySplit Burnett.Analysis.CapFourier Burnett.A05
open Burnett.V08 (signedCyclicPhase)
open scoped FourierTransform

private theorem wardRadianWeight_integrable_of_action {b : E → ℝ}
    (f g h : SchwartzMap E ℂ) (hf : Integrable (radianActionSpectrum b f)) :
    Integrable (radianTrilinearWeight (fun x => (b x.1 : ℂ)) f g h) := by
  let F := radianActionSpectrum b f
  let G := SchwartzMap.fourierTransformCLE ℂ g
  let H := SchwartzMap.fourierTransformCLE ℂ h
  have hH : Continuous (fun p : Joint => H (-(p.1+p.2))) :=
    H.continuous.comp (continuous_fst.add continuous_snd).neg
  have hFG : Integrable (fun p : Joint => F p.1 * G p.2) (volume : Measure Joint) := by
    rw [Measure.volume_eq_prod E E]
    exact hf.mul_prod G.integrable
  have hProd : Integrable (fun p : Joint => F p.1 * G p.2 * H (-(p.1+p.2))) := by
    refine (hFG.bdd_mul hH.aestronglyMeasurable
      ⟨SchwartzMap.seminorm ℝ 0 0 H, fun p => H.norm_le_seminorm ℝ (-(p.1+p.2))⟩).congr ?_
    exact Filter.Eventually.of_forall fun _ => mul_comm _ _
  letI := jointVolume_haar
  have hTau : tau ≠ 0 := (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).ne'
  refine (integrable_comp_smul_iff (volume : Measure Joint)
    (radianTrilinearWeight (fun x => (b x.1 : ℂ)) f g h) hTau).mp ?_
  refine hProd.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [radianTrilinearWeight, radianWeight, Complex.ofReal_one, one_mul, Prod.smul_fst,
    Prod.smul_snd, ← smul_add, ← smul_neg, radianFourier_scaled]
  change (b (tau • p.1) : ℂ) * 𝓕 (f : E → ℂ) p.1 * 𝓕 (g : E → ℂ) p.2 *
      𝓕 (h : E → ℂ) (-(p.1+p.2)) =
    (b (tau • p.1) : ℂ) * (𝓕 (f : E → ℂ) p.1 * 𝓕 (g : E → ℂ) p.2 * 𝓕 (h : E → ℂ) (-(p.1+p.2)))
  ring

private theorem wardRadianWeight_cycle (m : Joint → ℂ) (f g h : SchwartzMap E ℂ) :
    radianTrilinearWeight (m ∘ radianCycle) h f g = (radianTrilinearWeight m f g h) ∘ radianCycle := by
  funext p
  have ht : -((radianCycle p).1 + (radianCycle p).2) = p.1 := by
    change -(p.2 + -(p.1+p.2)) = p.1
    abel
  simp only [radianTrilinearWeight, radianWeight, Function.comp_apply, Complex.ofReal_one, one_mul, ht]
  change m (radianCycle p) * (radianFourier h p.1 * radianFourier f p.2 * radianFourier g (-(p.1+p.2))) =
    m (radianCycle p) * (radianFourier f p.2 * radianFourier g (-(p.1+p.2)) * radianFourier h p.1)
  ring

/-- Before the fixed undifferentiated and differentiated slots are
expanded, the three original scalar test placements give the signed sum
of the three test symbols and preserve integrability. -/
theorem wardScalarActionCyclicPlacements (b : E → ℝ)
    (f g h : SchwartzMap E ℂ) (hf : Integrable (radianActionSpectrum b f))
    (hg : Integrable (radianActionSpectrum b g)) (hh : Integrable (radianActionSpectrum b h)) :
    let A (p : Joint) := (signedCyclicPhase b p.1 p.2 : ℂ)
    Integrable (radianTrilinearWeight A f g h) ∧
      ((∫ x, radianAction b f x * g x * h x) +
        (∫ x, radianAction b g x * h x * f x) +
        (∫ x, radianAction b h x * f x * g x)) = radianTrilinearForm A f g h := by
  intro A
  let m (p : Joint) := (b p.1 : ℂ)
  let m₁ := m ∘ radianCycle
  let m₂ := m₁ ∘ radianCycle
  let S : Fin 3 → Joint → ℂ := ![m,m₁,m₂]
  have hS (p : Joint) : (∑ s, S s p) = A p := by
    simp only [S, m, m₁, m₂, A, signedCyclicPhase, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, Function.comp_apply, Complex.ofReal_add]
    change (b p.1 : ℂ) + ((b p.2 : ℂ) + (b (-(p.1+p.2)) : ℂ)) =
      ((b p.1 : ℂ) + (b p.2 : ℂ)) + (b (-(p.1+p.2)) : ℂ)
    ring
  have h₀ : Integrable (radianTrilinearWeight m f g h) := wardRadianWeight_integrable_of_action f g h hf
  have h₁ : Integrable (radianTrilinearWeight m₁ f g h) := by
    unfold m₁
    rw [wardRadianWeight_cycle m g h f]
    exact measurePreserving_radianCycle.integrable_comp_of_integrable
      (wardRadianWeight_integrable_of_action g h f hg)
  have h₂ : Integrable (radianTrilinearWeight m₂ f g h) := by
    unfold m₂
    rw [wardRadianWeight_cycle m₁ g h f]
    unfold m₁
    rw [wardRadianWeight_cycle m h f g]
    exact measurePreserving_radianCycle.integrable_comp_of_integrable
      (measurePreserving_radianCycle.integrable_comp_of_integrable
        (wardRadianWeight_integrable_of_action h f g hh))
  have hW (i : Fin 3) : Integrable (radianTrilinearWeight (S i) f g h) := by
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
  have hWeight :
      (fun p => ∑ i, radianTrilinearWeight (S i) f g h p) = radianTrilinearWeight A f g h := by
    funext p
    simp only [radianTrilinearWeight, ← Finset.sum_mul, hS p]
  refine ⟨hWeight ▸ integrable_finset_sum Finset.univ (fun i _ => hW i), ?_⟩
  rw [wardRadianAction_mul_two_eq_trilinearForm f g h hf,
    wardRadianAction_mul_two_eq_trilinearForm g h f hg, wardRadianAction_mul_two_eq_trilinearForm h f g hh]
  have he := radianTrilinearForm_sum Finset.univ S f g h (fun i _ => hW i)
  have hAt : (fun p => ∑ s ∈ (Finset.univ : Finset (Fin 3)), S s p) = A := funext hS
  rw [hAt] at he
  rw [he]
  simp only [S, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  have h₁eq := radianTrilinearForm_cycle m g h f
  have h₂eq := (radianTrilinearForm_cycle m₁ g h f).trans (radianTrilinearForm_cycle m h f g)
  change radianTrilinearForm m f g h + radianTrilinearForm m g h f + radianTrilinearForm m h f g =
    radianTrilinearForm m f g h + (radianTrilinearForm m₁ f g h + radianTrilinearForm m₂ f g h)
  rw [h₁eq, h₂eq]
  ring

end Burnett.C02
