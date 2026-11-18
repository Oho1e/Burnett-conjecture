import Burnett.Analysis.Microlocal.AngularCommutator.AngularSymbol
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Frequency kernel of an angular multiplier commutator

Fourier convolution identifies the high-input kernel. A weighted Schur
estimate gives its squared integral bound.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.AngularCommutator

open Set MeasureTheory
open scoped FourierTransform ContDiff ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The commutator frequency kernel truncated at the high input frequencies. -/
def highCommutatorKernel (m χ : V → ℂ) (R : ℝ) (x y : V) : ℂ :=
  if R ≤ ‖y‖ then (m x - m y) * (𝓕 χ) (x - y) else 0

/-- The first moment of the Fourier transform of a smooth, compactly supported
cutoff is integrable with respect to the actual Euclidean volume. -/
theorem integrable_cutoff_fourier_first_moment (χ : V → ℂ)
    (hsχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    Integrable (fun z => ‖z‖ * ‖(𝓕 χ) z‖) (volume : Measure V) := by
  let f : SchwartzMap V ℂ := hcχ.toSchwartzMap hsχ
  simpa only [pow_one] using (SchwartzMap.fourierTransformCLM ℂ f).integrable_pow_mul volume 1

/-- Both Schur integrals of the actual high-frequency kernel are bounded by
the same finite cutoff first moment times an inverse frequency radius. -/
theorem highCommutatorKernel_row_column_le (m χ : V → ℂ)
    (hsm : ContDiffOn ℝ ∞ m ({0}ᶜ : Set V)) (hh : DegreeZero m)
    (B : ℝ) (hb : ∀ x, ‖m x‖ ≤ B)
    (hsχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℝ≥0∞, A < ⊤ ∧
      A = (∫⁻ z, ENNReal.ofReal (‖z‖ * ‖(𝓕 χ) z‖) ∂(volume : Measure V)) ∧
      ∀ R : ℝ, 0 < R →
      (∀ x, (∫⁻ y, ENNReal.ofReal ‖highCommutatorKernel m χ R x y‖ ∂(volume : Measure V)) ≤
        ENNReal.ofReal (C / R) * A) ∧
      (∀ y, (∫⁻ x, ENNReal.ofReal ‖highCommutatorKernel m χ R x y‖ ∂(volume : Measure V)) ≤
        ENNReal.ofReal (C / R) * A) := by
  let μ := (volume : Measure V)
  let f : SchwartzMap V ℂ := hcχ.toSchwartzMap hsχ
  let g (z : V) := ENNReal.ofReal (‖z‖ * ‖(𝓕 χ) z‖)
  let A := ∫⁻ z, g z ∂μ
  have hf : Continuous (𝓕 χ) := (SchwartzMap.fourierTransformCLM ℂ f).continuous
  have hg : Measurable g := (continuous_norm.mul hf.norm).measurable.ennreal_ofReal
  have hA : A < ⊤ := (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mp
      (integrable_cutoff_fourier_first_moment χ hsχ hcχ).hasFiniteIntegral
  obtain ⟨C, hC, hdiff⟩ := norm_high_input_kernel_le m (𝓕 χ) hsm hh B hb
  refine ⟨C, hC, A, hA, rfl, ?_⟩
  intro R hR
  have hCR : 0 ≤ C / R := div_nonneg hC hR.le
  have hnorm (x y : V) :
      ENNReal.ofReal ‖highCommutatorKernel m χ R x y‖ ≤ ENNReal.ofReal (C / R) * g (x - y) := by
    by_cases hy : R ≤ ‖y‖
    · simp only [highCommutatorKernel, if_pos hy, g, ← ENNReal.ofReal_mul hCR]
      exact ENNReal.ofReal_le_ofReal (hdiff R hR x y hy)
    · simp [highCommutatorKernel, hy]
  constructor
  · intro x
    refine (lintegral_mono (hnorm x)).trans ?_
    have hleft : Measurable (fun y : V => g (x - y)) :=
      hg.comp (measurable_const.sub measurable_id)
    rw [lintegral_const_mul _ hleft]
    rw [(μ.measurePreserving_sub_left x).lintegral_comp hg]
  · intro y
    refine (lintegral_mono (fun x => hnorm x y)).trans ?_
    have hright : Measurable (fun x : V => g (x - y)) :=
      hg.comp (measurable_id.sub measurable_const)
    rw [lintegral_const_mul _ hright]
    have htrans : MeasurePreserving (fun x : V => x - y) μ μ := by
      simpa only [sub_eq_add_neg] using (measurePreserving_add_right μ (-y))
    rw [htrans.lintegral_comp hg]

end Burnett.Microlocal.AngularCommutator

namespace Burnett.Microlocal.AngularCommutator

open MeasureTheory Function
open scoped ENNReal

private theorem sq_half_rpow (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = a := by
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

private theorem sq_lintegral_weight_mul_le {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (w g : Y → ℝ≥0∞) (hw : Measurable w) (hg : Measurable g) :
    (∫⁻ y, w y * g y ∂ν) ^ (2 : ℕ) ≤ (∫⁻ y, w y ∂ν) * ∫⁻ y, w y * (g y)^2 ∂ν := by
  let u (y : Y) := w y ^ (1 / 2 : ℝ)
  let v (y : Y) := u y * g y
  have hum : Measurable u := by
    dsimp only [u]
    fun_prop
  have hvm : Measurable v := hum.mul hg
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
    hum.aemeasurable hvm.aemeasurable
  have huv (y : Y) : u y * v y = w y * g y := by
    dsimp only [v, u]
    rw [← mul_assoc, ← pow_two, sq_half_rpow]
  have hup (y : Y) : u y ^ (2 : ℝ) = w y := by
    dsimp only [u]
    rw [ENNReal.rpow_two, sq_half_rpow]
  have hvp (y : Y) : v y ^ (2 : ℝ) = w y * (g y)^2 := by
    dsimp only [v, u]
    rw [ENNReal.rpow_two, mul_pow, sq_half_rpow]
  simp only [Pi.mul_apply, huv, hup, hvp] at h
  refine (pow_le_pow_left' h 2).trans_eq ?_
  rw [mul_pow, sq_half_rpow, sq_half_rpow]

/-- A squared L² bound for the actual complex kernel integral, estimated by
the product of the two absolute-integral bounds. -/
theorem schur_squared_integral_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (K : X → Y → ℂ) (hK : Measurable (uncurry K)) (f : Y → ℂ) (hf : Measurable f)
    (A B : ℝ≥0∞) (hA : ∀ x, (∫⁻ y, ‖K x y‖ₑ ∂ν) ≤ A)
    (hB : ∀ y, (∫⁻ x, ‖K x y‖ₑ ∂μ) ≤ B) :
    (∫⁻ x, ‖∫ y, K x y * f y ∂ν‖ₑ ^ (2 : ℕ) ∂μ) ≤ A * B * ∫⁻ y, ‖f y‖ₑ ^ (2 : ℕ) ∂ν := by
  let w (x : X) (y : Y) := ‖K x y‖ₑ
  let g (y : Y) := ‖f y‖ₑ
  have hw : Measurable (uncurry w) := hK.enorm
  have hg : Measurable g := hf.enorm
  have hgsq : Measurable (fun y : Y => (g y) ^ (2 : ℕ)) := hg.pow_const (2 : ℕ)
  have hh : Measurable (fun p : X × Y => (g p.2) ^ (2 : ℕ)) :=
    hgsq.comp measurable_snd
  have hz : Measurable (uncurry (fun x y => w x y * (g y) ^ (2 : ℕ))) := hw.mul hh
  have row (x : X) : Measurable (w x) := by
    have hpair : Measurable (fun y : Y => (x, y)) := measurable_const.prodMk measurable_id
    have hcomp : Measurable ((uncurry w) ∘ (fun y : Y => (x, y))) := hw.comp hpair
    simpa only [Function.comp_def, Function.uncurry] using hcomp
  have pointwise (x : X) :
      ‖∫ y, K x y * f y ∂ν‖ₑ ^ (2 : ℕ) ≤ A * ∫⁻ y, w x y * (g y)^2 ∂ν := by
    calc
      _ ≤ (∫⁻ y, w x y * g y ∂ν) ^ (2 : ℕ) := by
        apply pow_le_pow_left' _ 2
        simpa only [w, g, enorm_mul] using
          (enorm_integral_le_lintegral_enorm (μ := ν) (fun y => K x y * f y))
      _ ≤ (∫⁻ y, w x y ∂ν) * ∫⁻ y, w x y * (g y)^2 ∂ν :=
        sq_lintegral_weight_mul_le ν (w x) g (row x) hg
      _ ≤ _ := mul_le_mul_right' (hA x) _
  refine (lintegral_mono pointwise).trans ?_
  rw [lintegral_const_mul _ hz.lintegral_prod_right, lintegral_lintegral_swap hz.aemeasurable]
  rw [mul_assoc]
  apply mul_le_mul_left'
  calc
    (∫⁻ y, ∫⁻ x, w x y * (g y)^2 ∂μ ∂ν) ≤ ∫⁻ y, B * (g y)^2 ∂ν := by
      apply lintegral_mono
      intro y
      have hpair : Measurable (fun x : X => (x, y)) := measurable_id.prodMk measurable_const
      have col : Measurable (fun x => w x y) := by
        have hcomp : Measurable ((uncurry w) ∘ (fun x : X => (x, y))) := hw.comp hpair
        simpa only [Function.comp_def, Function.uncurry] using hcomp
      change (∫⁻ x, w x y * (g y)^2 ∂μ) ≤ B * (g y)^2
      rw [lintegral_mul_const _ col]
      exact mul_le_mul_right' (hB y) _
    _ = _ := lintegral_const_mul _ hgsq

end Burnett.Microlocal.AngularCommutator

namespace Burnett.Microlocal.AngularCommutator

open MeasureTheory Set Function
open scoped ContDiff FourierTransform ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Changing the assigned value at zero preserves Borel measurability. -/
theorem measurable_of_angular_smooth (m : V → ℂ)
    (hs : ContDiffOn ℝ ∞ m ({0}ᶜ : Set V)) : Measurable m := by
  classical
  let U : Set V := {0}ᶜ
  have hpiece : Measurable (U.piecewise m (fun _ => m 0)) :=
    hs.continuousOn.measurable_piecewise continuous_const.continuousOn
      (measurableSet_singleton _).compl
  have heq : U.piecewise m (fun _ => m 0) = m := by
    funext x
    by_cases hx : x = 0 <;> simp [U, hx]
  rwa [heq] at hpiece

theorem measurable_highCommutatorKernel (m χ : V → ℂ)
    (hsm : ContDiffOn ℝ ∞ m ({0}ᶜ : Set V)) (hsχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (R : ℝ) : Measurable (uncurry (highCommutatorKernel m χ R)) := by
  let f : SchwartzMap V ℂ := hcχ.toSchwartzMap hsχ
  have hf : Continuous (𝓕 χ) := (SchwartzMap.fourierTransformCLM ℂ f).continuous
  have hm := measurable_of_angular_smooth m hsm
  change Measurable (fun p : V × V =>
    if R ≤ ‖p.2‖ then (m p.1 - m p.2) * (𝓕 χ) (p.1 - p.2) else 0)
  exact Measurable.ite (measurableSet_le measurable_const measurable_snd.norm)
    (((hm.comp measurable_fst).sub (hm.comp measurable_snd)).mul
      (hf.measurable.comp (measurable_fst.sub measurable_snd))) measurable_const

/-- The high-frequency integral action of the true Fourier cutoff kernel has
the inverse-radius bound in squared L² energy. -/
theorem highCommutatorKernel_squared_integral_le
    (m χ : V → ℂ) (hsm : ContDiffOn ℝ ∞ m ({0}ᶜ : Set V)) (hh : DegreeZero m)
    (B : ℝ) (hb : ∀ x, ‖m x‖ ≤ B)
    (hsχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℝ≥0∞, A < ⊤ ∧
      A = (∫⁻ z, ENNReal.ofReal (‖z‖ * ‖(𝓕 χ) z‖) ∂(volume : Measure V)) ∧
      ∀ R : ℝ, 0 < R → ∀ f : V → ℂ, Measurable f →
      (∫⁻ x, ‖∫ y, highCommutatorKernel m χ R x y * f y‖ₑ ^ (2 : ℕ)) ≤
        (ENNReal.ofReal (C / R) * A)^2 * ∫⁻ y, ‖f y‖ₑ ^ (2 : ℕ) := by
  obtain ⟨C, hC, A, hA, hEq, hs⟩ := highCommutatorKernel_row_column_le m χ hsm hh B hb hsχ hcχ
  refine ⟨C, hC, A, hA, hEq, ?_⟩
  intro R hR f hf
  obtain ⟨hrow, hcol⟩ := hs R hR
  rw [pow_two]
  exact schur_squared_integral_le volume volume _ (measurable_highCommutatorKernel m χ hsm hsχ hcχ R)
    f hf _ _ (by simpa only [ofReal_norm_eq_enorm] using hrow)
    (by simpa only [ofReal_norm_eq_enorm] using hcol)

end Burnett.Microlocal.AngularCommutator

namespace Burnett.Microlocal.AngularCommutator

open MeasureTheory Function
open scoped FourierTransform RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Fourier transform of a physical product with an actual inverse Fourier
integral, using the same normalization as the production Fourier operators. -/
theorem fourier_mul_inverse_eq_integral (χ F : V → ℂ)
    (hχ : Integrable χ (volume : Measure V)) (hF : Integrable F (volume : Measure V))
    (ξ : V) :
    (𝓕 (fun x => χ x * (𝓕⁻ F) x)) ξ =
      ∫ η, (𝓕 χ) (ξ - η) * F η := by
  let μ := (volume : Measure V)
  let P (t : ℝ) : ℂ := Complex.exp ((↑(2 * Real.pi * t) : ℂ) * Complex.I)
  have hP : Continuous P := by
    dsimp only [P]
    fun_prop
  have hPn (t : ℝ) : ‖P t‖ = 1 := by
    simp [P, Complex.norm_exp, Complex.mul_re]
  have hPadd (s t : ℝ) : P s * P t = P (s + t) := by
    unfold P
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hPneg (x z : V) :
      Complex.exp (↑(-2 * Real.pi * ⟪x, z⟫) * Complex.I) = P (-⟪x, z⟫) := by
    have he : (-2 * Real.pi * ⟪x, z⟫ : ℝ) = 2 * Real.pi * (-⟪x, z⟫) := by ring
    exact congrArg (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) he
  let K (x y : V) : ℂ := (P (-⟪x, ξ⟫) * P ⟪y, x⟫) * (χ x * F y)
  have hphase : Continuous (fun p : V × V => P (-⟪p.1, ξ⟫) * P ⟪p.2, p.1⟫) :=
    (hP.comp ((continuous_fst.inner continuous_const).neg)).mul
      (hP.comp (continuous_snd.inner continuous_fst))
  have hprod : Integrable (fun p : V × V => χ p.1 * F p.2) (μ.prod μ) :=
    hχ.op_fst_snd (op := (· * · : ℂ → ℂ → ℂ))
      (continuous_fst.mul continuous_snd)
      ⟨1, fun a b => by rw [norm_mul, one_mul]⟩ hF
  have hK : Integrable (uncurry K) (μ.prod μ) := by
    apply hprod.mono (hphase.aestronglyMeasurable.mul hprod.aestronglyMeasurable)
    filter_upwards with p
    simp [hPn]
  calc
    _ = ∫ x, ∫ y, K x y := by
      rw [Real.fourierIntegral_eq']
      apply integral_congr_ae
      filter_upwards with x
      simp only [Real.fourierIntegralInv_eq', smul_eq_mul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      rw [hPneg x ξ]
      change P (-⟪x, ξ⟫) * (χ x * (P ⟪y, x⟫ * F y)) = _
      unfold K
      ring
    _ = ∫ y, ∫ x, K x y := integral_integral_swap hK
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [Real.fourierIntegral_eq', ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with x
      have harg : -⟪x, ξ⟫ + ⟪y, x⟫ = -⟪x, ξ - y⟫ := by
        rw [inner_sub_right, real_inner_comm y x]
        ring
      simp only [K, smul_eq_mul, hPneg x (ξ - y), hPadd, harg]
      ring

end Burnett.Microlocal.AngularCommutator

namespace Burnett.Microlocal.AngularCommutator

open MeasureTheory Function
open scoped FourierTransform ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Exact Fourier-side commutator identity for spectra with an actual
integrable inverse Fourier representation. -/
theorem fourier_commutator_eq_kernel (m χ F : V → ℂ)
    (hm : Measurable m) (B : ℝ) (hb : ∀ x, ‖m x‖ ≤ B)
    (hsχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hF : Integrable F (volume : Measure V)) (ξ : V) :
    m ξ * (𝓕 (fun x => χ x * (𝓕⁻ F) x)) ξ -
      (𝓕 (fun x => χ x * (𝓕⁻ (fun y => m y * F y)) x)) ξ =
      ∫ η, ((m ξ - m η) * (𝓕 χ) (ξ - η)) * F η := by
  let ψ : SchwartzMap V ℂ := hcχ.toSchwartzMap hsχ
  let k := SchwartzMap.fourierTransformCLM ℂ ψ
  have hχ : Integrable χ (volume : Measure V) := ψ.integrable
  have hmF := hF.bdd_mul hm.aestronglyMeasurable ⟨B, hb⟩
  have hk : Continuous (fun y : V => (𝓕 χ) (ξ - y)) :=
    k.continuous.comp (continuous_const.sub continuous_id)
  have hkB : ∃ A, ∀ y : V, ‖(𝓕 χ) (ξ - y)‖ ≤ A :=
    ⟨SchwartzMap.seminorm ℝ 0 0 k, fun y => SchwartzMap.norm_le_seminorm ℝ k (ξ - y)⟩
  have h1 := hF.bdd_mul hk.aestronglyMeasurable hkB
  have h2 := hmF.bdd_mul hk.aestronglyMeasurable hkB
  rw [fourier_mul_inverse_eq_integral χ F hχ hF,
      fourier_mul_inverse_eq_integral χ (fun y => m y * F y) hχ hmF,
      ← integral_const_mul, ← integral_sub (h1.const_mul (m ξ)) h2]
  apply integral_congr_ae
  filter_upwards with y
  ring

end Burnett.Microlocal.AngularCommutator
