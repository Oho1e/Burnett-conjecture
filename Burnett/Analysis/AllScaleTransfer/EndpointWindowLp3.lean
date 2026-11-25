import Burnett.Analysis.AllScaleTransfer.EndpointAngularMultiplier
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.MikhlinFinite
import Burnett.Analysis.SignedFourierWindow.FiniteLowWindow
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualDensity

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Burnett.A05
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow

open MeasureTheory Filter Burnett.A02.FrequencySplit Burnett.Fourier
open Burnett.A02.FrequencySplit.CMBilinearDual (schwartz_toLp_denseRange)
open scoped FourierTransform ENNReal RealInnerProductSpace Topology

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

/-- The fixed Fourier window at a positive scale uses this actual normalized kernel. -/
def endpointWindowKernel (a : SchwartzMap E ℂ) (s : ℝ) : E → ℂ :=
  shiftedSpatialKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) s 0

private theorem endpointWindowKernel_regular (a : SchwartzMap E ℂ) {s : ℝ} (hs : 0 < s) :
    let K := endpointWindowKernel a s
    Continuous K ∧ Integrable K ∧ MemLp K 2 volume ∧ ∃ D : ℝ, ∀ z, ‖K z‖ ≤ D := by
  have h := finite_kernel_regular ((SchwartzMap.fourierTransformCLE ℂ).symm a) s hs 0
    {0} (fun _ => 1)
  have he : finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) s 0 {0} (fun _ => 1) =
      endpointWindowKernel a s := by
    funext z
    simp [finiteWindowKernel, endpointWindowKernel]
  rw [← he]
  exact h

private theorem endpoint_kernel_eLpNorm_bound (a : SchwartzMap E ℂ) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ (s : ℝ), 0 < s → ∀ (f : E → ℂ),
      MemLp f (ENNReal.ofReal 3) volume →
      eLpNorm (kernelApply (endpointWindowKernel a s) f) (ENNReal.ofReal 3) volume ≤
        B * eLpNorm f (ENNReal.ofReal 3) volume := by
  let φ := (SchwartzMap.fourierTransformCLE ℂ).symm a
  obtain ⟨C,hC,hMax⟩ := shifted_schwartz_kernel_maximal φ
  have hPow : maximalConstant 3 ^ (1/3 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) (maximalConstant_finite 3).ne
  refine ⟨C * maximalConstant 3 ^ (1/3 : ℝ), ENNReal.mul_lt_top hC hPow, ?_⟩
  intro s hs f hf
  let u := hf.1.mk f
  have hu : Measurable u := hf.1.stronglyMeasurable_mk.measurable
  have hfu : f =ᵐ[volume] u := hf.1.ae_eq_mk
  let g := fun y => ‖u y‖ₑ
  have hG : Measurable g := hu.enorm
  let K := endpointWindowKernel a s
  have hEq : kernelApply K f = kernelApply K u := by
    funext x
    exact integral_congr_ae (hfu.mono fun y hy => congrArg (fun v => K (x-y)*v) hy)
  have point (x : E) : ‖kernelApply K u x‖ₑ ≤ C * centeredMax g x := by
    refine (enorm_integral_le_lintegral_enorm (fun y => K (x-y)*u y)).trans ?_
    have h := hMax g hG 0 x s hs
    simp only [norm_zero, add_zero, one_pow, ENNReal.ofReal_one, mul_one] at h
    have hPoint (y : E) : ‖K (x-y)*u y‖ₑ =
        ENNReal.ofReal (‖φ (s⁻¹ • (x-y)+0)‖ / s^4) * g y := by
      change ‖((s ^ 4)⁻¹ • φ (s⁻¹ • (x-y) + 0)) * u y‖ₑ =
        ENNReal.ofReal (‖φ (s⁻¹ • (x-y)+0)‖ / s^4) * ‖u y‖ₑ
      rw [← ofReal_norm_eq_enorm, norm_mul, norm_smul, Real.norm_of_nonneg
        (inv_nonneg.mpr (pow_nonneg hs.le _)), inv_mul_eq_div, ENNReal.ofReal_mul (by positivity),
        ofReal_norm_eq_enorm]
    have hInt : (∫⁻ y, ‖K (x-y)*u y‖ₑ) =
        ∫⁻ y, ENNReal.ofReal (‖φ (s⁻¹ • (x-y))‖ / s^4) * g y :=
      lintegral_congr fun y => by simpa only [add_zero] using hPoint y
    exact hInt.le.trans h
  have hnorm := eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' (μ := (volume : Measure E))
    (f := kernelApply K u) (g := centeredMax g) (c := C) (ENNReal.ofReal 3)
    (centeredMax_measurable g).aestronglyMeasurable (Eventually.of_forall point)
  rw [hEq, eLpNorm_congr_ae hfu]
  exact hnorm.trans ((mul_le_mul_left' (centeredMax_complex_Lp u hu 3 (by norm_num)) C).trans_eq
    (mul_assoc _ _ _).symm)

private theorem endpointWindow_memLp (a : SchwartzMap E ℂ) {s : ℝ} (hs : 0 < s)
    (f : E → ℂ) (hf : MemLp f (ENNReal.ofReal 3) volume) :
    MemLp (kernelApply (endpointWindowKernel a s) f) (ENNReal.ofReal 3) volume := by
  obtain ⟨B,hB,hNorm⟩ := endpoint_kernel_eLpNorm_bound a
  exact ⟨(kernelApply_measurable_ae _ (endpointWindowKernel_regular a hs).1 f hf.1).aestronglyMeasurable,
    (hNorm s hs f hf).trans_lt (ENNReal.mul_lt_top hB hf.2)⟩

private def endpointWindowLinear (a : SchwartzMap E ℂ) {s : ℝ} (hs : 0 < s) :
    EndpointLp3 →ₗ[ℂ] EndpointLp3 where
  toFun f := (endpointWindow_memLp a hs f (Lp.memLp f)).toLp _
  map_add' f g := by
    let K := endpointWindowKernel a s
    obtain ⟨hK,hI,_,D,hD⟩ := endpointWindowKernel_regular a hs
    have h (v : EndpointLp3) (x : E) : Integrable (fun y => K (x-y)*v y) :=
      kernel_integrand_Lp K hK hI D hD 3 (by norm_num) v (Lp.memLp v) x
    change (endpointWindow_memLp a hs ((f+g : EndpointLp3) : E → ℂ) (Lp.memLp (f+g))).toLp _ =
      (endpointWindow_memLp a hs f (Lp.memLp f)).toLp _ + (endpointWindow_memLp a hs g (Lp.memLp g)).toLp _
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards with x
    change kernelApply K (⇑(f+g)) x = kernelApply K f x + kernelApply K g x
    unfold kernelApply
    rw [← integral_add (h f x) (h g x)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy,Pi.add_apply,mul_add]
  map_smul' c f := by
    let K := endpointWindowKernel a s
    change (endpointWindow_memLp a hs ((c • f : EndpointLp3) : E → ℂ) (Lp.memLp (c • f))).toLp _ =
      c • (endpointWindow_memLp a hs f (Lp.memLp f)).toLp _
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    filter_upwards with x
    change kernelApply K (⇑(c • f)) x = c * kernelApply K f x
    unfold kernelApply
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c f] with y hy
    rw [hy,Pi.smul_apply,smul_eq_mul]
    ring

/-- The actual bounded complex window on all of L³. -/
def endpointWindowLp3 (a : SchwartzMap E ℂ) (s : ℝ) (hs : 0 < s) :
    EndpointLp3 →L[ℂ] EndpointLp3 := by
  let B := Classical.choose (endpoint_kernel_eLpNorm_bound a)
  have hB := Classical.choose_spec (endpoint_kernel_eLpNorm_bound a)
  refine (endpointWindowLinear a hs).mkContinuous B.toReal (fun f => ?_)
  have h := ENNReal.toReal_mono (ENNReal.mul_lt_top hB.1 (Lp.memLp f).2).ne
    (hB.2 s hs f (Lp.memLp f))
  change ‖(endpointWindow_memLp a hs f (Lp.memLp f)).toLp _‖ ≤ B.toReal * ‖f‖
  rw [Lp.norm_toLp,Lp.norm_def]
  simpa only [ENNReal.toReal_mul] using h

theorem endpointWindowLp3_ae (a : SchwartzMap E ℂ) (s : ℝ) (hs : 0 < s) (f : EndpointLp3) :
    (endpointWindowLp3 a s hs f : E → ℂ) =ᵐ[volume] kernelApply (endpointWindowKernel a s) f :=
  (endpointWindow_memLp a hs f (Lp.memLp f)).coeFn_toLp

theorem endpointWindowLp3_Schwartz (a f : SchwartzMap E ℂ) (s : ℝ) (hs : 0 < s) :
    (endpointWindowLp3 a s hs (f.toLp (ENNReal.ofReal 3) volume) : E → ℂ) =ᵐ[volume]
      shiftedWindowOperator a f s 0 := by
  refine (endpointWindowLp3_ae a s hs _).trans (Eventually.of_forall fun x => ?_)
  rw [shifted_window_physical a f s hs 0 x]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp (ENNReal.ofReal 3) volume] with y hy
  exact congrArg (fun z => endpointWindowKernel a s (x-y) * z) hy

theorem endpointWindowSymbol_eval (a : SchwartzMap E ℂ) {s : ℝ} (hs : 0 < s) (ξ : E) :
    rescaleSymbol (modulatedWindowSymbol a 0) s hs ξ = a (s • ξ) := by
  change Complex.exp ((↑(2*Real.pi*inner ℝ (s • ξ) (0:E)) : ℂ)*Complex.I) * a (s • ξ) = _
  simp

/-- The actual spectral window on L² agrees with the same convolution,
so its L³ realization acts on angular multiplier outputs in the intersection. -/
theorem endpointWindowLp3_intersection (a : SchwartzMap E ℂ) (hsupp : HasCompactSupport (a : E → ℂ))
    (s : ℝ) (hs : 0 < s) (f : E → ℂ) (h₂ : MemLp f 2 volume)
    (h₃ : MemLp f (ENNReal.ofReal 3) volume) :
    (endpointWindowLp3 a s hs (h₃.toLp f) : E → ℂ) =ᵐ[volume]
      (fourierMultiplier (rescaleSymbol (modulatedWindowSymbol a 0) s hs) (h₂.toLp f) : E → ℂ) := by
  classical
  let K := endpointWindowKernel a s
  let A := fourierMultiplier (rescaleSymbol (modulatedWindowSymbol a 0) s hs)
  obtain ⟨_,_,hK,_,_⟩ := endpointWindowKernel_regular a hs
  have hd := schwartz_toLp_denseRange (V := E) 2 (by norm_num)
  obtain ⟨v,hv,conv⟩ := mem_closure_iff_seq_limit.mp (hd (h₂.toLp f))
  choose g hg using hv
  have eq (n : ℕ) : (g n).toLp 2 volume = v n := hg n
  have cv : Tendsto (fun n => A (v n)) atTop (𝓝 (A (h₂.toLp f))) :=
    A.continuous.continuousAt.tendsto.comp conv
  obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_Lp cv).exists_seq_tendsto_ae
  have tests : ∀ᵐ x ∂volume, ∀ n : ℕ, A (v n) x = kernelApply K (g n) x := by
    apply ae_all_iff.mpr
    intro n
    rw [← eq n]
    exact (shiftedWindow_L2_ae a hsupp (g n) s hs 0).trans
      (Eventually.of_forall fun x => shifted_window_physical a (g n) s hs 0 x)
  have he : (A (h₂.toLp f) : E → ℂ) =ᵐ[volume] kernelApply K f := by
    filter_upwards [hae,tests] with x hlim htest
    obtain ⟨k,hk⟩ := kernelApply_as_inner K hK x
    have h (n : ℕ) : A (v n) x = inner ℂ k (v n) := by
      rw [htest n, ← eq n]
      exact hk _ ((g n).memLp 2 volume)
    have h' : Tendsto (fun n => A (v (ns n)) x) atTop (𝓝 (kernelApply K f x)) := by
      simp_rw [h, hk f h₂]
      exact tendsto_const_nhds.inner (conv.comp hns.tendsto_atTop)
    exact tendsto_nhds_unique hlim h'
  have hConv : kernelApply K (h₃.toLp f) =ᵐ[volume] kernelApply K f :=
    Eventually.of_forall fun x => integral_congr_ae
      (h₃.coeFn_toLp.mono fun y hy => congrArg (fun z => K (x-y)*z) hy)
  exact (endpointWindowLp3_ae a s hs _).trans (hConv.trans he.symm)

end Burnett.A05
