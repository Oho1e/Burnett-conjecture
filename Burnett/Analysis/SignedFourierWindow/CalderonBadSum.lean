import Burnett.Analysis.SignedFourierWindow.CalderonCancellation

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Metric Set Function
open scoped ENNReal

theorem measurable_kernelApply (K b : Space → ℂ) (hK : Continuous K) (hb : Measurable b) :
    Measurable (kernelApply K b) := by
  have h : StronglyMeasurable (fun z : Space × Space => K (z.1-z.2)*b z.2) :=
    ((hK.comp (continuous_fst.sub continuous_snd)).measurable.mul (hb.comp measurable_snd)).stronglyMeasurable
  exact h.integral_prod_right'.measurable

/-- The convolution of a countable, absolutely L¹-summable bad part is its
pointwise sum of convolutions. Here boundedness is only needed for each fixed kernel. -/
theorem kernel_split_apply {ι : Type*} [Countable ι] (K : Space → ℂ) (hK : Continuous K)
    (D : ℝ) (hD : ∀ z, ‖K z‖ ≤ D) (f g : Space → ℂ) (hf : Integrable f) (hg : Integrable g)
    (b : ι → Space → ℂ) (hb : ∀ i, Integrable (b i))
    (sumfin : (∑' i, ∫⁻ y, ‖b i y‖ₑ) < ⊤) (eq : ∀ x, g x + ∑' i, b i x = f x) (x : Space) :
    kernelApply K f x = kernelApply K g x + ∑' i, kernelApply K (b i) x := by
  let G := fun i (y : Space) => K (x-y) * b i y
  have hG (i : ι) : Integrable (G i) := kernel_integrand K hK D hD (hb i) x
  have bound (i : ι) : (∫⁻ y, ‖G i y‖ₑ) ≤ ENNReal.ofReal D * ∫⁻ y, ‖b i y‖ₑ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y => ?_
    rw [show ‖G i y‖ₑ = ‖K (x-y)‖ₑ * ‖b i y‖ₑ from enorm_mul ..]
    exact mul_le_mul_right' ((ofReal_norm_eq_enorm _).symm.trans_le (ENNReal.ofReal_le_ofReal (hD _))) _
  have summass : (∑' i, ∫⁻ y, ‖G i y‖ₑ) < ⊤ := by
    refine (ENNReal.tsum_le_tsum bound).trans_lt ?_
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top sumfin
  have he (y : Space) : K (x-y)*f y = K (x-y)*g y + ∑' i, G i y := by
    rw [← eq y,mul_add,tsum_mul_left]
  have hi : Integrable (fun y => ∑' i, G i y) := by
    apply ((kernel_integrand K hK D hD hf x).sub (kernel_integrand K hK D hD hg x)).congr
    filter_upwards with y
    change K (x-y)*f y - K (x-y)*g y = _
    rw [he,add_sub_cancel_left]
  unfold kernelApply
  simp_rw [he]
  rw [integral_add (kernel_integrand K hK D hD hg x) hi,integral_tsum (fun i => (hG i).1) summass.ne]

/-- The sum of all bad convolutions has a uniform off-exceptional L¹ bound. -/
theorem bad_sum_exterior {ι : Type*} [Countable ι] (K : Space → ℂ) (hK : Continuous K) (D : ℝ)
    (hD : ∀ z, ‖K z‖ ≤ D) (A : ℝ≥0∞)
    (hA : ∀ h : Space, (∫⁻ z in {z : Space | 2*‖h‖ ≤ ‖z‖}, ‖K (z-h)-K z‖ₑ) ≤ A)
    (b : ι → Space → ℂ) (hm : ∀ i, Measurable (b i)) (hb : ∀ i, Integrable (b i))
    (hz : ∀ i, (∫ y, b i y) = 0) (p : ι → Space) (r : ι → ℝ)
    (hs : ∀ i y, y ∉ closedBall (p i) (4*r i) → b i y = 0) :
    (∫⁻ x in (⋃ i, closedBall (p i) (8*r i))ᶜ, ‖∑' i, kernelApply K (b i) x‖ₑ) ≤
      A * ∑' i, ∫⁻ y, ‖b i y‖ₑ := by
  refine (lintegral_mono (fun x => enorm_tsum_le_tsum_enorm (f := fun i => kernelApply K (b i) x))).trans ?_
  rw [lintegral_tsum (fun i => (measurable_kernelApply _ _ hK (hm i)).enorm.aemeasurable),← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro i
  refine (lintegral_mono_set (compl_subset_compl.mpr (subset_iUnion _ i))).trans ?_
  exact kernel_bad_block_exterior K hK D hD A hA _ (hm i) (hb i) (hz i) (p i) (r i) (hs i)

end Burnett.Analysis.SignedFourierWindow
