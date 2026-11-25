import Burnett.Analysis.AllScaleTransfer.RadianTrilinearChange
import Mathlib.MeasureTheory.Group.Prod

set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable section

namespace Burnett.A05

open Filter MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier (radianTrilinearForm radianTrilinearWeight)

def radianCycle : Joint ≃ᵐ Joint where
  toFun p := (p.2, -(p.1 + p.2))
  invFun p := (-(p.1 + p.2), p.1)
  left_inv p := by
    apply Prod.ext
    · change -(p.2 + -(p.1 + p.2)) = p.1
      abel
    · rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · change -(-(p.1 + p.2) + p.1) = p.2
      abel
  measurable_toFun := measurable_snd.prodMk (measurable_fst.add measurable_snd).neg
  measurable_invFun := (measurable_fst.add measurable_snd).neg.prodMk measurable_fst

theorem measurePreserving_radianCycle :
    MeasurePreserving radianCycle (volume : Measure Joint) volume := by
  let μ : Measure E := volume
  rw [Measure.volume_eq_prod E E]
  have hneg : MeasurePreserving (fun p : Joint => (p.1, -p.2)) (μ.prod μ) (μ.prod μ) :=
    (MeasurePreserving.id μ).skew_product measurable_snd.neg
      (Eventually.of_forall (fun _ => (Measure.measurePreserving_neg μ).map_eq))
  have hadd := measurePreserving_prod_add_swap μ μ
  have he : (fun p : Joint => (p.1, -p.2)) ∘ (fun p : Joint => (p.2, p.2+p.1)) = radianCycle := by
    funext p
    change (p.2, -(p.2+p.1)) = (p.2, -(p.1+p.2))
    rw [add_comm p.2 p.1]
  exact he ▸ hneg.comp hadd

/-- The three low-slot choices use the same complex trilinear form
after the measure-preserving cyclic permutation of the frequencies. -/
theorem radianTrilinearForm_cycle (m : Joint → ℂ) (f g h : SchwartzMap E ℂ) :
    radianTrilinearForm (m ∘ radianCycle) h f g = radianTrilinearForm m f g h := by
  unfold radianTrilinearForm
  congr 1
  calc
    _ = ∫ p, radianTrilinearWeight m f g h (radianCycle p) := by
      apply integral_congr_ae
      filter_upwards with p
      have hThird : -((radianCycle p).1 + (radianCycle p).2) = p.1 := by
        change -(p.2 + -(p.1+p.2)) = p.1
        abel
      simp only [radianTrilinearWeight, radianWeight, Function.comp_apply, Complex.ofReal_one, one_mul, hThird]
      change m (radianCycle p) * (radianFourier h p.1 * radianFourier f p.2 * radianFourier g (-(p.1+p.2))) =
        m (radianCycle p) * (radianFourier f p.2 * radianFourier g (-(p.1+p.2)) * radianFourier h p.1)
      ring
    _ = _ := measurePreserving_radianCycle.integral_comp' (radianTrilinearWeight m f g h)

/-- Recombining finitely many integrable symbol pieces recovers the same
trilinear form, including its complex weights and normalization. -/
theorem radianTrilinearForm_sum {ι : Type*} (I : Finset ι) (m : ι → Joint → ℂ)
    (f g h : SchwartzMap E ℂ)
    (hm : ∀ i ∈ I, Integrable (radianTrilinearWeight (m i) f g h)) :
    radianTrilinearForm (fun p => ∑ i ∈ I, m i p) f g h = ∑ i ∈ I, radianTrilinearForm (m i) f g h := by
  unfold radianTrilinearForm
  rw [← Finset.smul_sum, ← integral_finset_sum I hm]
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  simp only [radianTrilinearWeight, Finset.sum_mul]

end Burnett.A05
