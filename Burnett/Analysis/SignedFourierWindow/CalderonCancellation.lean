import Burnett.Analysis.SignedFourierWindow.CalderonColumn

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Metric Set
open scoped ENNReal

def kernelApply (K b : Space → ℂ) (x : Space) : ℂ := ∫ y, K (x-y)*b y

theorem kernel_integrand (K : Space → ℂ) (hK : Continuous K) (D : ℝ) (hD : ∀ z, ‖K z‖ ≤ D)
    {b : Space → ℂ} (hb : Integrable b) (x : Space) : Integrable (fun y : Space => K (x-y)*b y) :=
  hb.bdd_mul (hK.comp (continuous_const.sub continuous_id)).aestronglyMeasurable ⟨D,fun _ => hD _⟩

/-- Cancel a zero mean at its own center, then use Tonelli and the translated
Hörmander estimate outside the eightfold ball. -/
theorem kernel_bad_block_exterior (K : Space → ℂ) (hK : Continuous K) (D : ℝ) (hD : ∀ z, ‖K z‖ ≤ D)
    (A : ℝ≥0∞) (hA : ∀ h : Space, (∫⁻ z in {z : Space | 2*‖h‖ ≤ ‖z‖}, ‖K (z-h)-K z‖ₑ) ≤ A)
    (b : Space → ℂ) (hm : Measurable b) (hb : Integrable b) (hz : (∫ y, b y) = 0)
    (p : Space) (r : ℝ) (hs : ∀ y ∉ closedBall p (4*r), b y = 0) :
    (∫⁻ x in (closedBall p (8*r))ᶜ, ‖kernelApply K b x‖ₑ) ≤ A * ∫⁻ y, ‖b y‖ₑ := by
  let S := (closedBall p (8*r))ᶜ
  let F := fun x y : Space => ‖K (x-y)-K (x-p)‖ₑ * ‖b y‖ₑ
  have diff (x : Space) : kernelApply K b x = ∫ y, (K (x-y)-K (x-p))*b y := by
    have right := hb.const_mul (K (x-p))
    simp_rw [sub_mul]
    rw [integral_sub (kernel_integrand K hK D hD hb x) right,integral_const_mul,hz,mul_zero,sub_zero]
    rfl
  have point (x : Space) : ‖kernelApply K b x‖ₑ ≤ ∫⁻ y, F x y := by
    rw [diff]
    simpa only [F,enorm_mul] using enorm_integral_le_lintegral_enorm
      (μ := (volume : Measure Space)) (fun y : Space => (K (x-y)-K (x-p))*b y)
  have joint : Measurable (Function.uncurry F) :=
    (((hK.comp (continuous_fst.sub continuous_snd)).sub
      (hK.comp (continuous_fst.sub continuous_const))).measurable.enorm).mul (hm.comp measurable_snd).enorm
  calc
    _ ≤ ∫⁻ x in S, ∫⁻ y, F x y := lintegral_mono point
    _ = ∫⁻ y, ∫⁻ x in S, F x y := lintegral_lintegral_swap joint.aemeasurable
    _ ≤ ∫⁻ y, A * ‖b y‖ₑ := by
      refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ closedBall p (4*r)
      · change (∫⁻ x in S, ‖K (x-y)-K (x-p)‖ₑ*‖b y‖ₑ) ≤ _
        rw [lintegral_mul_const' _ _ enorm_ne_top]
        exact mul_le_mul_right' (exterior_kernel_column K A hA p y r hy) _
      · simp [F,hs y hy]
    _ = _ := lintegral_const_mul _ hm.enorm

end Burnett.Analysis.SignedFourierWindow
