import Burnett.Analysis.Compactness.OrderedPairings
import Burnett.Analysis.PrincipalEnergy.Quantization.ActualDerivative
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option maxHeartbeats 1700000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.SeparablePositive (separableOperator)
open scoped ComplexConjugate FourierTransform InnerProduct

/-- The positive base Fourier phase in the same convention as the inverse kernel. -/
def baseFourierPhase (k x : E) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * inner ℝ k x) : ℂ) * Complex.I)

theorem baseFourierPhase_norm (k x : E) : ‖baseFourierPhase k x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem baseFourierPhase_continuous : Continuous (uncurry baseFourierPhase) := by
  unfold uncurry baseFourierPhase
  fun_prop

theorem baseFourierPhase_continuous_apply {X : Type*} [TopologicalSpace X]
    {a b : X → E} (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun q => baseFourierPhase (a q) (b q)) := by
  change Continuous ((uncurry baseFourierPhase) ∘ fun q => (a q, b q))
  exact baseFourierPhase_continuous.comp (ha.prodMk hb)

/-- Spatial multiplication by the base phase has operator bound one. -/
def baseFourierPhaseSymbol (k : E) : BoundedSymbol E where
  toFun := baseFourierPhase k
  measurable :=
    (baseFourierPhase_continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  bound := 1
  bound_nonneg := zero_le_one
  norm_le x := (baseFourierPhase_norm k x).le

private theorem measurable_inverse_baseModes (m : E → BoundedSymbol E)
    (hm : Measurable (fun q : E × E => m q.1 q.2)) (f : SchwartzMap E ℂ) :
    Measurable (fun q : E × E => (𝓕⁻ (fun ξ => m q.1 ξ * (𝓕 (f : E → ℂ)) ξ)) q.2) := by
  let F := SchwartzMap.fourierTransformCLE ℂ f
  let G (p : (E × E) × E) := baseFourierPhase p.2 p.1.2 * (m p.1.1 p.2 * F p.2)
  have hPhase : Continuous (fun p : (E × E) × E => baseFourierPhase p.2 p.1.2) :=
    baseFourierPhase_continuous_apply
      (a := Prod.snd) (b := fun p : (E × E) × E => p.1.2)
      continuous_snd (continuous_snd.comp continuous_fst)
  have hM : Measurable (fun p : (E × E) × E => m p.1.1 p.2) :=
    hm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hG : Measurable G := hPhase.measurable.mul (hM.mul (F.continuous.measurable.comp measurable_snd))
  have hI := (hG.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure E))).measurable
  convert hI using 1
  funext p
  rw [Real.fourierIntegralInv_eq']
  rfl

private theorem norm_inverse_baseMode_le (m : BoundedSymbol E) (f : SchwartzMap E ℂ) (x : E) :
    ‖(𝓕⁻ (fun ξ => m ξ * (𝓕 (f : E → ℂ)) ξ)) x‖ ≤
      m.bound * ∫ ξ, ‖(𝓕 (f : E → ℂ)) ξ‖ := by
  let F := SchwartzMap.fourierTransformCLE ℂ f
  have hInt : Integrable (fun ξ : E => m.bound * ‖F ξ‖) (volume : Measure E) :=
    F.integrable.norm.const_mul m.bound
  have h := norm_integral_le_of_norm_le hInt
    (Eventually.of_forall fun ξ => show ‖baseFourierPhase ξ x * (m ξ * F ξ)‖ ≤ _ by
      rw [norm_mul, baseFourierPhase_norm, one_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (m.norm_le ξ) (norm_nonneg _))
  rw [Real.fourierIntegralInv_eq']
  simpa only [baseFourierPhase, smul_eq_mul, integral_const_mul, F] using h

/-- With pointwise base Fourier inversion and an integrable uniform symbol
envelope, the exact left Fourier action is the integral of the separated modes. -/
theorem firstOrderAction_eq_integral_baseFourierModes
    (p : E → E → ℂ) (m : E → BoundedSymbol E)
    (hm : Measurable (fun q : E × E => m q.1 q.2))
    (b : E → ℝ) (hb : Integrable b) (hbound : ∀ k, (m k).bound ≤ b k)
    (hInv : ∀ x ξ, (𝓕⁻ (fun k => m k ξ)) x = p x ξ)
    (f : SchwartzMap E ℂ) (x : E) :
    firstOrderAction p f x =
      ∫ k, baseFourierPhase k x * (𝓕⁻ (fun ξ => m k ξ * (𝓕 (f : E → ℂ)) ξ)) x := by
  let F := SchwartzMap.fourierTransformCLE ℂ f
  let G (k ξ : E) := baseFourierPhase k x * (baseFourierPhase ξ x * (m k ξ * F ξ))
  have hK : Continuous (fun q : E × E => baseFourierPhase q.1 x) :=
    baseFourierPhase_continuous_apply
      (a := (Prod.fst : E × E → E)) (b := fun _ => x) continuous_fst continuous_const
  have hXi : Continuous (fun q : E × E => baseFourierPhase q.2 x) :=
    baseFourierPhase_continuous_apply
      (a := (Prod.snd : E × E → E)) (b := fun _ => x) continuous_snd continuous_const
  have hG : Measurable (uncurry G) := hK.measurable.mul
    (hXi.measurable.mul (hm.mul (F.continuous.measurable.comp measurable_snd)))
  have hI : Integrable (uncurry G) ((volume : Measure E).prod volume) := by
    refine (hb.mul_prod F.integrable.norm).mono' hG.aestronglyMeasurable ?_
    filter_upwards with q
    change ‖baseFourierPhase q.1 x * (baseFourierPhase q.2 x * (m q.1 q.2 * F q.2))‖ ≤
      b q.1 * ‖F q.2‖
    simp only [norm_mul, baseFourierPhase_norm, one_mul]
    exact mul_le_mul_of_nonneg_right (((m q.1).norm_le q.2).trans (hbound q.1)) (norm_nonneg _)
  have hReconstruct (ξ : E) : (∫ k, baseFourierPhase k x * m k ξ) = p x ξ := by
    simpa only [Real.fourierIntegralInv_eq', baseFourierPhase, smul_eq_mul] using hInv x ξ
  calc
    _ = ∫ ξ, baseFourierPhase ξ x * (p x ξ * F ξ) := by
      rw [firstOrderAction, Real.fourierIntegralInv_eq']
      rfl
    _ = ∫ ξ, ∫ k, G k ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [← hReconstruct ξ, ← integral_mul_const, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with k
      dsimp only [G]
      ring
    _ = ∫ k, ∫ ξ, G k ξ := (integral_integral_swap hI).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with k
      rw [Real.fourierIntegralInv_eq', ← integral_const_mul]
      rfl

private theorem inner_separable_baseMode (m : BoundedSymbol E) (f v : SchwartzMap E ℂ) (k : E) :
    inner ℂ (v.toLp 2 volume) (separableOperator (baseFourierPhaseSymbol k) m (f.toLp 2 volume)) =
      ∫ x, conj (v x) * (baseFourierPhase k x *
        (𝓕⁻ (fun ξ => m ξ * (𝓕 (f : E → ℂ)) ξ)) x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [v.coeFn_toLp 2 volume,
    symbolL2_ae (baseFourierPhaseSymbol k) (fourierMultiplier m (f.toLp 2 volume)),
    Burnett.Microlocal.AngularDyadicKernel.fourierMultiplier_schwartz_eq_inverse_mul_ae m f]
    with x hx hy hz
  change inner ℂ ((v.toLp 2 volume : E → ℂ) x)
    ((symbolL2 (baseFourierPhaseSymbol k) (fourierMultiplier m (f.toLp 2 volume))) x) = _
  rw [RCLike.inner_apply', hx, hy, hz]
  rfl

/-- The parameter integral uses the actual separated L² operators, with
the test in the conjugate-linear slot of the exact spatial pairing. -/
theorem firstOrderAction_pairing_eq_integral_separable_baseFourier
    (p : E → E → ℂ) (m : E → BoundedSymbol E)
    (hm : Measurable (fun q : E × E => m q.1 q.2))
    (b : E → ℝ) (hb : Integrable b) (hbound : ∀ k, (m k).bound ≤ b k)
    (hInv : ∀ x ξ, (𝓕⁻ (fun k => m k ξ)) x = p x ξ)
    (f v : SchwartzMap E ℂ) :
    let P (k : E) := inner ℂ (v.toLp 2 volume)
      (separableOperator (baseFourierPhaseSymbol k) (m k) (f.toLp 2 volume))
    Integrable P ∧
      (∫ x, conj (v x) * firstOrderAction p f x) = ∫ k, P k := by
  intro P
  let A : ℝ := ∫ ξ, ‖(𝓕 (f : E → ℂ)) ξ‖
  let U (k x : E) := (𝓕⁻ (fun ξ => m k ξ * (𝓕 (f : E → ℂ)) ξ)) x
  let G (k x : E) := conj (v x) * (baseFourierPhase k x * U k x)
  have hA : 0 ≤ A := integral_nonneg (fun _ => norm_nonneg _)
  have hU : Measurable (uncurry U) := measurable_inverse_baseModes m hm f
  have hV : Measurable (fun q : E × E => conj (v q.2)) :=
    Complex.continuous_conj.measurable.comp (v.continuous.measurable.comp measurable_snd)
  have hG : Measurable (uncurry G) := hV.mul (baseFourierPhase_continuous.measurable.mul hU)
  have hI : Integrable (uncurry G) ((volume : Measure E).prod volume) := by
    refine ((hb.mul_const A).mul_prod v.integrable.norm).mono' hG.aestronglyMeasurable ?_
    filter_upwards with q
    change ‖conj (v q.2) * (baseFourierPhase q.1 q.2 * U q.1 q.2)‖ ≤
      (b q.1 * A) * ‖v q.2‖
    simp only [norm_mul, Complex.norm_conj, baseFourierPhase_norm, one_mul, mul_comm ‖v q.2‖]
    exact mul_le_mul_of_nonneg_right ((norm_inverse_baseMode_le (m q.1) f q.2).trans
      (mul_le_mul_of_nonneg_right (hbound q.1) hA)) (norm_nonneg _)
  have hPair (k : E) : P k = ∫ x, G k x := inner_separable_baseMode (m k) f v k
  refine ⟨hI.integral_prod_left.congr (Eventually.of_forall (fun k => (hPair k).symm)), ?_⟩
  calc
    _ = ∫ x, ∫ k, G k x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [firstOrderAction_eq_integral_baseFourierModes p m hm b hb hbound hInv f x,
        ← integral_const_mul]
    _ = ∫ k, ∫ x, G k x := (integral_integral_swap hI).symm
    _ = _ := integral_congr_ae (Eventually.of_forall fun k => (hPair k).symm)

end Burnett.Microlocal.Overlap
