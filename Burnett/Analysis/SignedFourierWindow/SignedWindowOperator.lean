import Burnett.Analysis.SignedFourierWindow.WindowL2
import Burnett.Analysis.SignedFourierWindow.HormanderBands

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
open MeasureTheory Finset Burnett.Fourier
open scoped BigOperators FourierTransform

def finiteWindowKernel (φ : SchwartzMap Space ℂ) (t : ℝ) (q : Space) (I : Finset ℕ) (c : ℕ → ℂ) (z : Space) : ℂ :=
  ∑ k ∈ I, c k * shiftedSpatialKernel φ ((2:ℝ)^k*t) q z

private theorem product_integrable (φ f : SchwartzMap Space ℂ) (s : ℝ) (q x : Space) :
    Integrable (fun y : Space => shiftedSpatialKernel φ s q (x-y) * f y) := by
  let D := |(s^4)⁻¹| * SchwartzMap.seminorm ℝ 0 0 φ
  refine (f.integrable.norm.const_mul D).mono' (by dsimp only [shiftedSpatialKernel]; fun_prop) ?_
  filter_upwards with y
  simp only [shiftedSpatialKernel,D,norm_mul,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ φ _) (abs_nonneg _)) (norm_nonneg _)

private theorem finite_window_integral (a f : SchwartzMap Space ℂ) (t : ℝ) (ht : 0<t) (q x : Space) (I : Finset ℕ)
    (c : ℕ → ℂ) : (∑ k ∈ I, c k * shiftedWindowOperator a f ((2:ℝ)^k*t) q x) =
      ∫ y : Space, finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) t q I c (x-y) * f y := by
  let φ := (SchwartzMap.fourierTransformCLE ℂ).symm a
  let K := fun k : ℕ => shiftedSpatialKernel φ ((2:ℝ)^k*t) q
  have he (k : ℕ) : c k * shiftedWindowOperator a f ((2:ℝ)^k*t) q x =
      ∫ y : Space, c k * (K k (x-y) * f y) := by
    rw [shifted_window_physical _ _ _ (mul_pos (by positivity) ht), ← integral_const_mul]
    rfl
  simp_rw [he]
  rw [← integral_finset_sum I (fun k _ => (product_integrable φ f ((2:ℝ)^k*t) q x).const_mul (c k))]
  simp only [finiteWindowKernel,φ,sum_mul,mul_assoc]

private theorem finite_window_ae (a : SchwartzMap Space ℂ) (ha : HasCompactSupport (a : Space → ℂ)) (f : SchwartzMap Space ℂ)
    (t : ℝ) (ht : 0<t) (q : Space) (I : Finset ℕ) (c : ℕ → ℂ) :
    (fun x => (∑ k ∈ I, c k • fourierMultiplier (rescaleSymbol (modulatedWindowSymbol a q) ((2:ℝ)^k*t)
      (mul_pos (by positivity) ht)) (f.toLp 2 volume)) x) =ᵐ[volume]
      fun x => ∑ k ∈ I, c k * shiftedWindowOperator a f ((2:ℝ)^k*t) q x := by
  classical
  let B := fun k : ℕ => fourierMultiplier (rescaleSymbol (modulatedWindowSymbol a q) ((2:ℝ)^k*t)
    (mul_pos (by positivity) ht)) (f.toLp 2 volume)
  change (fun x => (∑ k ∈ I, c k • B k) x) =ᵐ[volume] _
  induction I using Finset.induction_on with
  | empty => simpa only [sum_empty] using (Lp.coeFn_zero ℂ 2 (volume : Measure Space))
  | @insert k I hk ih =>
    simp only [sum_insert hk]
    filter_upwards [Lp.coeFn_add (c k • B k) (∑ j ∈ I,c j • B j),Lp.coeFn_smul (c k) (B k),
      shiftedWindow_L2_ae a ha f ((2:ℝ)^k*t) (mul_pos (by positivity) ht) q,ih] with x hadd hsm hb hi
    change B k x = _ at hb
    rw [hadd,Pi.add_apply,hsm,Pi.smul_apply,smul_eq_mul,hb,hi]

/-- The L² estimate and the integral Hörmander condition apply to the same
finite sum acting on the original Schwartz input by convolution. -/
theorem signed_window_operator_estimates (a : SchwartzMap Space ℂ) (ha : HasCompactSupport (a : Space → ℂ))
    (cut : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), 0<t → ∀ (q : Space) (I : Finset ℕ) (c : ℕ → ℂ), (∀ k, ‖c k‖ ≤ 1) →
      let K := finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) t q I c
      (∀ h : Space, (∫ z in {z : Space | 2*‖h‖ ≤ ‖z‖}, ‖K (z-h) - K z‖) ≤ C*(1+‖q‖)) ∧
      (∀ f : SchwartzMap Space ℂ, ∃ u : ComplexL2 Space, (u : Space → ℂ) =ᵐ[volume] (fun x => ∫ y : Space, K (x-y)*f y) ∧
        ‖u‖ ≤ (2*SchwartzMap.seminorm ℝ 0 0 a)*‖f.toLp 2 volume‖) := by
  let φ := (SchwartzMap.fourierTransformCLE ℂ).symm a
  obtain ⟨C,hC,hK⟩ := dyadic_kernel_hormander φ
  refine ⟨C,hC,?_⟩
  intro t ht q I c hc
  refine ⟨fun h => hK t ht q h I c hc,?_⟩
  intro f
  let m := modulatedWindowSymbol a q
  have support (ξ : Space) (h : m ξ ≠ 0) : 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2 :=
    cut ξ (fun hz => h (by simp [m,modulatedWindowSymbol,hz]))
  refine ⟨_,(finite_window_ae a ha f t ht q I c).trans (Filter.Eventually.of_forall fun x =>
    finite_window_integral a f t ht q x I c),signed_annular_sum_L2 m support t ht c hc I (f.toLp 2 volume)⟩

end Burnett.Analysis.SignedFourierWindow
