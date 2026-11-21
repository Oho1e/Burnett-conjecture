import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianOrderOnePairing

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.RicciSymbol
open scoped ComplexConjugate ContDiff ENNReal

/-- Pointwise multiplication kept in the Schwartz test class. -/
def energyProduct (f g : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) g.hasTemperateGrowth f

@[simp] theorem energyProduct_apply (f g : SchwartzMap E ℂ) (x : E) :
    energyProduct f g x = f x * g x := rfl

theorem energyPartial_product (j : Index) (f g : SchwartzMap E ℂ) (x : E) :
    energyPartial j (energyProduct f g) x =
      energyPartial j f x * g x + f x * energyPartial j g x := by
  have hprod : (energyProduct f g : E → ℂ) = (f : E → ℂ) * (g : E → ℂ) :=
    funext (energyProduct_apply f g)
  simp only [energyPartial, SchwartzMap.pderivCLM_apply]
  rw [hprod, fderiv_mul (f.differentiable x) (g.differentiable x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem radian_order_one_test_integrable (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (f g : SchwartzMap E ℂ) :
    Integrable (fun x => f x * conj (radianAction b g x)) := by
  obtain ⟨_, _, bound⟩ := radian_degree_one_gradient_bound 2 (by norm_num) b hb hom
  have hg : MemLp (radianAction b g) 2 volume := by simpa using (bound g).1
  have hgc : MemLp (fun x => conj (radianAction b g x)) 2 volume :=
    hg.mono (Complex.continuous_conj.comp_aestronglyMeasurable hg.1)
      (Filter.Eventually.of_forall fun x => by simp)
  exact (f.memLp 2 volume).integrable_mul hgc

/-- The actual product rule and weak Fourier integration by parts reduce a
second-derivative term to the two terms used in the quasilinear energy. -/
theorem quasilinear_component_ibp (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (a d : Index) (A u v : SchwartzMap E ℂ) :
    (∫ x, A x * energyPartial a (energyPartial d u) x * conj (radianAction b v x)) =
      -(∫ x, A x * energyPartial d u x * conj (radianAction b (energyPartial a v) x)) -
      ∫ x, energyPartial a A x * energyPartial d u x * conj (radianAction b v x) := by
  let U := energyPartial d u
  have main := radian_order_one_partial_pairing b hb hom a (energyProduct A U) v
  have first := radian_order_one_test_integrable b hb hom (energyProduct A (energyPartial a U)) v
  have second := radian_order_one_test_integrable b hb hom (energyProduct (energyPartial a A) U) v
  simp only [energyProduct_apply] at first second
  have terms (x : E) :
      energyPartial a (energyProduct A U) x * conj (radianAction b v x) =
        (A x * energyPartial a U x * conj (radianAction b v x)) +
        (energyPartial a A x * U x * conj (radianAction b v x)) := by
    rw [energyPartial_product]
    ring
  simp_rw [terms] at main
  rw [integral_add first second] at main
  simpa only [energyProduct_apply, U] using eq_sub_of_add_eq main

end Burnett.A02.FrequencySplit
