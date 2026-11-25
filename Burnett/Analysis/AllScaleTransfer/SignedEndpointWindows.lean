import Burnett.Analysis.AllScaleTransfer.SignedAnnularCharts
import Burnett.Analysis.AllScaleTransfer.EndpointAngularMultiplier
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Burnett.A05

open Set Metric Filter MeasureTheory Burnett.Fourier Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier (frequencyCoordinates)
open Burnett.Microlocal.AngularCommutator
open scoped ContDiff ENNReal FourierTransform Topology

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

/-- The sign of the axial coordinate in the normalized null frame. -/
def capHemisphere (ξ : E) : Bool := decide (0 ≤ endpointDirection ξ 0)

/-- Fixed smooth degree-zero selectors for the two signed cap sheets. -/
def capSignWindow (α : ℝ) (sign : Bool) (ξ : E) : ℝ :=
  let b := Real.smoothTransition ((endpointDirection ξ 0 + α) / (2 * α))
  if sign then b else 1 - b

theorem capSignWindow_partition (α : ℝ) (ξ : E) :
    capSignWindow α true ξ + capSignWindow α false ξ = 1 := by unfold capSignWindow; simp

theorem capSignWindow_eq_selector {α : ℝ} (hα : 0 < α) (sign : Bool) (ξ : E)
    (hξ : α ≤ |endpointDirection ξ 0|) :
    capSignWindow α sign ξ = if sign = capHemisphere ξ then 1 else 0 := by
  have hDen : 0 < 2 * α := mul_pos (by norm_num) hα
  by_cases hx : 0 ≤ endpointDirection ξ 0
  · have hie : 1 ≤ (endpointDirection ξ 0 + α) / (2 * α) :=
      (le_div_iff₀ hDen).mpr (by rw [abs_of_nonneg hx] at hξ; linarith only [hξ])
    cases sign <;> simp [capSignWindow,capHemisphere,hx,Real.smoothTransition.one_of_one_le hie]
  · have hlo : (endpointDirection ξ 0 + α) / (2 * α) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by rw [abs_of_neg (lt_of_not_ge hx)] at hξ; linarith only [hξ]) hDen.le
    cases sign <;> simp [capSignWindow,capHemisphere,hx,Real.smoothTransition.zero_of_nonpos hlo]

theorem capSignWindow_pos_smul (α : ℝ) (sign : Bool) (t : ℝ) (ht : 0 < t) (ξ : E) :
    capSignWindow α sign (t • ξ) = capSignWindow α sign ξ := by
  simp only [capSignWindow,endpointDirection_pos_smul t ht]

private theorem capSignWindow_contDiffOn (α : ℝ) (sign : Bool) :
    ContDiffOn ℝ ∞ (capSignWindow α sign) {ξ : E | ξ ≠ 0} := by
  have hc : ContDiff ℝ ∞ (fun x : E => x 0) := frequencyCoordinates.toContinuousLinearMap.contDiff.fst
  have h : ContDiffOn ℝ ∞ (fun x : E => Real.smoothTransition ((endpointDirection x 0 + α) / (2 * α)))
      {ξ : E | ξ ≠ 0} := Real.smoothTransition.contDiff.comp_contDiffOn
    (((hc.comp_contDiffOn endpointDirection_contDiffOn).add (contDiffOn_const (c := α))).div_const (2 * α))
  cases sign
  · exact contDiffOn_const.sub h
  · exact h

private theorem exists_capSignWindow_sphere_bound (α : ℝ) (sign : Bool) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ j ≤ 6, ∀ ξ ∈ sphere (0 : E) 1,
      ‖iteratedFDeriv ℝ j (capSignWindow α sign) ξ‖ ≤ D := by
  let V : Set E := {ξ | ξ ≠ 0}
  have hv : IsOpen V := isOpen_ne
  have hs : sphere (0 : E) 1 ⊆ V := fun _ hx => ne_of_mem_sphere hx (by norm_num)
  have bounded (j : Fin 7) : ∃ c : ℝ, ∀ ξ ∈ sphere (0 : E) 1,
      ‖iteratedFDeriv ℝ j.val (capSignWindow α sign) ξ‖ ≤ c := by
    have hc := (capSignWindow_contDiffOn α sign).continuousOn_iteratedFDerivWithin
      (m := j.val) (WithTop.coe_le_coe.mpr le_top) hv.uniqueDiffOn
    have hd : ContinuousOn (fun ξ => ‖iteratedFDeriv ℝ j.val (capSignWindow α sign) ξ‖) (sphere (0 : E) 1) := by
      refine ((hc.congr (fun x hx => (iteratedFDerivWithin_of_isOpen j.val hv hx).symm)).mono hs).norm
    obtain ⟨c,hc⟩ := (isCompact_sphere (0 : E) 1).bddAbove_image hd
    exact ⟨c,fun ξ hξ => hc (mem_image_of_mem _ hξ)⟩
  choose c h using bounded
  refine ⟨∑ k : Fin 7, max 0 (c k), Finset.sum_nonneg (fun _ _ => le_max_left _ _), ?_⟩
  intro j hj ξ hx
  let k : Fin 7 := ⟨j, Nat.lt_succ_of_le hj⟩
  exact ((h k ξ hx).trans (le_max_right _ _)).trans
    (Finset.single_le_sum (fun k _ => le_max_left 0 (c k)) (Finset.mem_univ k))

/-- A Schwartz test with its Fourier transform supported in a finite annulus. -/
def EndpointFiniteAnnulus (f : SchwartzMap E ℂ) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ ∀ ξ, 𝓕 (f : E → ℂ) ξ ≠ 0 → a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b

private def signedEndpointSpectrum (α : ℝ) (sign : Bool) (f : SchwartzMap E ℂ) (ξ : E) : ℂ :=
  (capSignWindow α sign ξ : ℂ) * 𝓕 (f : E → ℂ) ξ

private theorem signedEndpointSpectrum_smooth (α : ℝ) (sign : Bool)
    (f : SchwartzMap E ℂ) (hf : EndpointFiniteAnnulus f) :
    ContDiff ℝ ∞ (signedEndpointSpectrum α sign f) := by
  obtain ⟨a,_,ha,hann⟩ := hf
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst ξ
    have z : signedEndpointSpectrum α sign f =ᶠ[𝓝 (0 : E)] fun _ => (0 : ℂ) := by
      filter_upwards [ball_mem_nhds (0 : E) ha] with ξ hx
      have h0 : 𝓕 (f : E → ℂ) ξ = 0 := by
        by_contra hn
        exact (not_lt_of_ge (hann ξ hn).1) (mem_ball_zero_iff.mp hx)
      simp only [signedEndpointSpectrum,h0,mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq z
  · have hm : ContDiffAt ℝ ∞ (capSignWindow α sign) ξ :=
      (capSignWindow_contDiffOn α sign).contDiffAt (isOpen_ne.mem_nhds hξ)
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp ξ hm).mul
      ((SchwartzMap.fourierTransformCLE ℂ f).smooth ⊤).contDiffAt

private theorem signedEndpointSpectrum_compact (α : ℝ) (sign : Bool)
    (f : SchwartzMap E ℂ) (hf : EndpointFiniteAnnulus f) :
    HasCompactSupport (signedEndpointSpectrum α sign f) := by
  obtain ⟨_,b,_,hann⟩ := hf
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) b)
  intro ξ hx
  refine mem_closedBall_zero_iff.mpr (hann ξ ?_).2
  intro hz
  exact hx (by simp only [signedEndpointSpectrum,hz,mul_zero])

/-- A finite spectral band in the original radian convention. -/
theorem endpointFiniteAnnulus_of_radian (f : SchwartzMap E ℂ) (a b : ℝ) (ha : 0 < a)
    (hann : ∀ ξ, radianFourier f ξ ≠ 0 → a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b) :
    EndpointFiniteAnnulus f := by
  have ht : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  refine ⟨a/tau,b/tau,div_pos ha ht,?_⟩
  intro ξ hξ
  have h := hann (tau • ξ) (by simpa only [radianFourier_scaled] using hξ)
  rw [norm_smul,Real.norm_of_nonneg ht.le] at h
  exact ⟨(div_le_iff₀ ht).mpr (by simpa only [mul_comm] using h.1),
    (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using h.2)⟩

/-- The actual sign split on the finite-annulus test. -/
def signedEndpointFactor (α : ℝ) (sign : Bool) (f : SchwartzMap E ℂ)
    (hf : EndpointFiniteAnnulus f) : SchwartzMap E ℂ :=
  (SchwartzMap.fourierTransformCLE ℂ).symm
    ((signedEndpointSpectrum_compact α sign f hf).toSchwartzMap
      (signedEndpointSpectrum_smooth α sign f hf))

theorem signedEndpointFactor_fourier (α : ℝ) (sign : Bool)
    (f : SchwartzMap E ℂ) (hf : EndpointFiniteAnnulus f) (ξ : E) :
    𝓕 (signedEndpointFactor α sign f hf : E → ℂ) ξ =
      (capSignWindow α sign ξ : ℂ) * 𝓕 (f : E → ℂ) ξ :=
  congrArg (fun g : SchwartzMap E ℂ => g ξ) ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply _)

theorem signedEndpointFactor_radian (α : ℝ) (sign : Bool)
    (f : SchwartzMap E ℂ) (hf : EndpointFiniteAnnulus f) (ξ : E) :
    radianFourier (signedEndpointFactor α sign f hf) ξ =
      (capSignWindow α sign ξ : ℂ) * radianFourier f ξ := by
  have ht : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  let ζ := tau⁻¹ • ξ
  have hr : tau • ζ = ξ := by dsimp only [ζ]; rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  rw [← hr, radianFourier_scaled, radianFourier_scaled, signedEndpointFactor_fourier,
    capSignWindow_pos_smul α sign tau ht]

theorem EndpointFiniteAnnulus.radian_ne_zero {f : SchwartzMap E ℂ}
    (hf : EndpointFiniteAnnulus f) {ξ : E} (hξ : radianFourier f ξ ≠ 0) : ξ ≠ 0 := by
  obtain ⟨a,_,ha,hann⟩ := hf
  rintro rfl
  have hz := radianFourier_scaled (f : E → ℂ) 0
  rw [smul_zero] at hz
  have h := (hann 0 (hz ▸ hξ)).1
  exact (not_lt_of_ge (by simpa only [norm_zero] using h)) ha

/-- One L³ constant for both actual selectors, independent of the annulus. -/
theorem exists_signedEndpointFactor_L3_bound (α : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (sign : Bool) (f : SchwartzMap E ℂ) (hf : EndpointFiniteAnnulus f),
      ‖(signedEndpointFactor α sign f hf).toLp (ENNReal.ofReal 3) volume‖ ≤
        D * ‖f.toLp (ENNReal.ofReal 3) volume‖ := by
  classical
  obtain ⟨C,hC,H⟩ := homogeneous_multiplier_all_Lp_sphere_bound 3 (by norm_num)
  choose d hd jets using exists_capSignWindow_sphere_bound α
  refine ⟨C * (d false + d true), mul_nonneg hC (add_nonneg (hd false) (hd true)), ?_⟩
  intro sign f hf
  obtain ⟨M,S,hM,hB,compareL2,_⟩ := H (capSignWindow α sign) (capSignWindow_contDiffOn α sign)
    (capSignWindow_pos_smul α sign) (d sign) (hd sign) (jets sign)
  let g := signedEndpointFactor α sign f hf
  have he : g.toLp 2 volume = fourierMultiplier M (f.toLp 2 volume) := by
    apply fourierL2Equiv.injective
    rw [fourier_fourierMultiplier]
    apply Lp.ext
    filter_upwards [fourierL2Equiv_schwartz_ae g,
      symbolL2_ae M (fourierL2Equiv (f.toLp 2 volume)), fourierL2Equiv_schwartz_ae f] with ξ hg hm hF
    rw [hg,hm,hF,hM,signedEndpointFactor_fourier]
  have eAE : (S (f.toLp (ENNReal.ofReal 3) volume) : E → ℂ) =ᵐ[volume]
      (g.toLp (ENNReal.ofReal 3) volume : E → ℂ) := by
    have eq := compareL2 f (f.memLp 2 volume) (f.memLp (ENNReal.ofReal 3) volume)
    change (S (f.toLp (ENNReal.ofReal 3) volume) : E → ℂ) =ᵐ[volume]
      (fourierMultiplier M (f.toLp 2 volume) : E → ℂ) at eq
    rw [← he] at eq
    exact eq.trans ((g.memLp 2 volume).coeFn_toLp.trans (g.memLp (ENNReal.ofReal 3) volume).coeFn_toLp.symm)
  rw [← Lp.ext eAE]
  apply (hB _).trans
  have hs : d sign ≤ d false + d true := by
    cases sign
    · exact le_add_of_nonneg_right (hd true)
    · exact le_add_of_nonneg_left (hd false)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hC) (norm_nonneg _)

end Burnett.A05
