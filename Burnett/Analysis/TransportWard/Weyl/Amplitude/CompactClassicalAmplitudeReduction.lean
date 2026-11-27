import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalAmplitudeCutoffLimit
import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalAmplitudeFourierWeight

set_option autoImplicit false
set_option maxHeartbeats 5600000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal FourierTransform Topology

/-- The needed part of the standard order-one two-point amplitude
conditions on a compactly localized Euclidean chart. Separation into
an operator symbol and a remainder is absent from this input. -/
structure CompactRadianTwoPointOrderOne (a : E → E → E → ℂ) (Rx Ry : ℝ) : Prop where
  jointSmooth : ContDiff ℝ ∞ (fun p : E × E × E => a p.1 p.2.1 p.2.2)
  outputSupport : ∀ x y ζ, x ∉ closedBall (0 : E) Rx → a x y ζ = 0
  inputSupport : ∀ x y ζ, y ∉ closedBall (0 : E) Ry → a x y ζ = 0
  orderOneInputDeriv : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y ζ,
    ‖iteratedFDeriv ℝ j (fun z => a x z ζ) y‖ ≤ C*(1+‖ζ‖)

private theorem radian_amplitude_input_support
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne a Rx Ry) (x ζ : E) :
    tsupport (fun y => a x y ζ) ⊆ closedBall (0 : E) Ry := by
  apply closure_minimal _ isClosed_closedBall
  intro y yne
  by_contra hy
  exact yne (h.inputSupport x y ζ hy)

/-- The true input-base Schwartz slice obtained from smoothness and the
same compact support. -/
def compactRadianTwoPointSlice (a : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianTwoPointOrderOne a Rx Ry) (x ζ : E) : SchwartzMap E ℂ := by
  have compact : HasCompactSupport (fun y => a x y ζ) :=
    (isCompact_closedBall (0 : E) Ry).of_isClosed_subset isClosed_closure
      (radian_amplitude_input_support a Rx Ry h x ζ)
  let args (y : E) : E × E × E := (x,y,ζ)
  have smooth : ContDiff ℝ ∞ (fun y => a x y ζ) := by
    change ContDiff ℝ ∞ ((fun p : E × E × E => a p.1 p.2.1 p.2.2) ∘ args)
    exact h.jointSmooth.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
  exact compact.toSchwartzMap smooth

@[simp] theorem compact_radian_two_point_slice_apply
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne a Rx Ry) (x y ζ : E) :
    compactRadianTwoPointSlice a Rx Ry h x ζ y = a x y ζ := rfl

/-- The actual input-slice estimates pass to the Schwartz seminorms,
using common compact support and preservation of the off-support zero
under differentiation. -/
theorem compact_radian_two_point_slice_order_one
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne a Rx Ry) :
    RadianAmplitudeInputOrderOne (compactRadianTwoPointSlice a Rx Ry h) := by
  intro k j
  obtain ⟨C,C0,bound⟩ := h.orderOneInputDeriv j
  let R := max 0 Ry
  have R0 : 0 ≤ R := le_max_left _ _
  refine ⟨R^k*C,by positivity,fun x ζ => ?_⟩
  apply SchwartzMap.seminorm_le_bound ℝ k j _ (by positivity)
  intro y
  change ‖y‖^k * ‖iteratedFDeriv ℝ j (fun z => a x z ζ) y‖ ≤ _
  by_cases hy : y ∈ closedBall (0 : E) Ry
  · have yB : ‖y‖ ≤ R :=
      (show ‖y‖ ≤ Ry by simpa only [mem_closedBall,dist_zero_right] using hy).trans (le_max_right _ _)
    calc
      _ ≤ R^k * (C*(1+‖ζ‖)) := mul_le_mul
        (pow_le_pow_left₀ (norm_nonneg y) yB k) (bound x y ζ) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have ev : (fun z => a x z ζ) =ᶠ[𝓝 y] (fun _ : E => (0 : ℂ)) := by
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hy] with z hz
      exact h.inputSupport x z ζ hz
    rw [(ev.iteratedFDeriv ℝ j).self_of_nhds,iteratedFDeriv_zero_fun,Pi.zero_apply,norm_zero,mul_zero]
    positivity

/-- Joint measurability of the genuine input Fourier profiles follows
from smoothness of the two-point amplitude. -/
theorem compact_radian_two_point_profile_measurable
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne a Rx Ry) (x : E) :
    Measurable (fun p : E × E =>
      radianSchwartzAmplitudeProfile (compactRadianTwoPointSlice a Rx Ry h) x p.1 p.2) := by
  let G (p : (E × E) × E) := patchFourierPhase (-p.1.1) p.2 * a x p.2 p.1.2
  have gp : Continuous (fun p : (E × E) × E => (-p.1.1,p.2)) :=
    ((continuous_fst.comp continuous_fst).neg).prodMk continuous_snd
  let args (p : (E × E) × E) : E × E × E := (x,p.2,p.1.2)
  have ga : Continuous args := continuous_const.prodMk
    (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
  have gc : Continuous G := by
    change Continuous (((fun q : E × E => patchFourierPhase q.1 q.2) ∘
      (fun p : (E × E) × E => (-p.1.1,p.2))) *
      ((fun q : E × E × E => a q.1 q.2.1 q.2.2) ∘ args))
    exact (patch_fourier_phase_continuous.comp gp).mul (h.jointSmooth.continuous.comp ga)
  have gm : Measurable (fun p : E × E => ∫ y : E, G (p,y)) :=
    (gc.measurable.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have eq : (fun p : E × E =>
      radianSchwartzAmplitudeProfile (compactRadianTwoPointSlice a Rx Ry h) x p.1 p.2) =
        (fun p : E × E => ∫ y : E, G (p,y)) := by
    funext p
    exact radian_fourier_phase_neg_integral (compactRadianTwoPointSlice a Rx Ry h x p.2) p.1
  rw [eq]
  exact gm

/-- Starting with actual smooth compactly localized two-point
amplitudes and their original order-one y derivative estimates, the
genuine physical frequency cutoffs reduce to the same explicit left
symbol in the limit on every Schwartz input and base point. -/
theorem compact_radian_two_point_amplitude_cutoff_tendsto_left
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne a Rx Ry)
    (κ : ℕ → SchwartzMap E ℂ) (κbound : ∀ n ξ, ‖κ n ξ‖ ≤ 1)
    (κlim : ∀ ξ, Tendsto (fun n => κ n ξ) atTop (𝓝 1))
    (u : SchwartzMap E ℂ) (x : E) :
    let b := radianAmplitudeReduced (radianSchwartzAmplitudeProfile (compactRadianTwoPointSlice a Rx Ry h))
    Tendsto (fun n => radianTwoPointCutoffAction a (κ n) u x) atTop
      (𝓝 (radianLeftQuantization b u x)) := by
  let A := compactRadianTwoPointSlice a Rx Ry h
  obtain ⟨w,hw⟩ := exists_radian_amplitude_fourier_bounds A
    (compact_radian_two_point_slice_order_one a Rx Ry h) (compact_radian_two_point_profile_measurable a Rx Ry h)
  exact radian_schwartz_two_point_cutoff_tendsto_left A w hw κ κbound κlim u x

/-- Output support survives the actual amplitude reduction. -/
theorem compact_radian_two_point_amplitude_reduced_support
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne a Rx Ry)
    (x ζ : E) (outside : x ∉ closedBall (0 : E) Rx) :
    radianAmplitudeReduced (radianSchwartzAmplitudeProfile (compactRadianTwoPointSlice a Rx Ry h)) x ζ = 0 := by
  let A := compactRadianTwoPointSlice a Rx Ry h
  have zero (q : E) : A x q = 0 := by
    ext y
    exact h.outputSupport x y q outside
  rw [radianAmplitudeReduced]
  have eq : (fun η : E => patchFourierPhase η x *
      radianSchwartzAmplitudeProfile A x η (ζ+tau • η)) = (fun _ : E => (0 : ℂ)) := by
    funext η
    change patchFourierPhase η x * 𝓕 (A x (ζ+tau • η) : E → ℂ) η = _
    rw [zero]
    change patchFourierPhase η x * 𝓕 (fun _ : E => (0 : ℂ)) η = 0
    rw [Real.fourierIntegral_eq']
    simp
  rw [eq]
  simp

/-- The genuine Fourier diagonal is the original two-point amplitude
evaluated at equal input and output positions. -/
theorem compact_radian_two_point_amplitude_diagonal
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne a Rx Ry)
    (x ζ : E) : radianAmplitudeDiagonal
        (radianSchwartzAmplitudeProfile (compactRadianTwoPointSlice a Rx Ry h)) x ζ = a x x ζ :=
  radian_schwartz_amplitude_profile_inversion (compactRadianTwoPointSlice a Rx Ry h) x x ζ

end Burnett.A03
