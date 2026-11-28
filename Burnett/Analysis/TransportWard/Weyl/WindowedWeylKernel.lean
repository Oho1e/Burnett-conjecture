import Burnett.Analysis.TransportWard.Weyl.WindowedWeylLeftAction
import Burnett.Analysis.TransportWard.Weyl.Amplitude.SchwartzWeylPairingLimit

/-! The same limit exhausts the Hermitian, real-odd Weyl kernel with the
physical windows on both sides. -/

set_option autoImplicit false
set_option maxHeartbeats 5600000

noncomputable section

namespace Burnett.V03

open Filter MeasureTheory Metric Set Function Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic
open scoped ComplexConjugate ContDiff FourierTransform RealInnerProductSpace Topology

private theorem windowedWeyl_phase_sub (ξ x y : E) :
    patchFourierPhase ξ x * patchFourierPhase (-ξ) y = patchFourierPhase ξ (x-y) := by
  simp only [Burnett.Microlocal.Overlap.baseFourierPhase, inner_neg_left, inner_sub_right]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- At each actual dyadic cutoff the two integration orders give the
identical doubly localized Weyl test. -/
theorem windowedWeyl_physical_cutoff_eq_dyadic_kernel (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hβ : ∀ x, Continuous (normalizedWeylSymbol β x))
    (n : ℕ) (u : SchwartzMap E ℂ) (x : E) :
    radianTwoPointCutoffAction (windowedWeylAmplitude θ β) (windowedWeylDyadicCutoff n) u x =
      compactKernelAction (a01LocalizedWeylFiniteKernel β (fun s t => θ s * θ t) n) u x := by
  let κ := windowedWeylDyadicCutoff n
  let a := windowedWeylAmplitude θ β
  let F (p : E × E) := (patchFourierPhase p.1 x * κ p.1) *
    (patchFourierPhase (-p.1) p.2 * a x p.2 (tau • p.1) * u p.2)
  have hContA : Continuous (fun p : E × E => a x p.2 (tau • p.1)) :=
    h.jointSmooth.continuous.comp
      (continuous_const.prodMk (continuous_snd.prodMk (continuous_const.smul continuous_fst)))
  have hContF : Continuous F := by
    refine ((patch_fourier_phase_continuous.comp (continuous_fst.prodMk continuous_const)).mul
      (κ.continuous.comp continuous_fst)).mul ?_
    exact ((patch_fourier_phase_continuous.comp (continuous_fst.neg.prodMk continuous_snd)).mul
      hContA).mul (u.continuous.comp continuous_snd)
  obtain ⟨D,D0,hD⟩ := h.orderOneInputDeriv 0
  have tauPos : 0 ≤ tau := (mul_pos (by norm_num) Real.pi_pos).le
  have hIntκ : Integrable (fun ξ : E => D * (1 + tau * ‖ξ‖) * ‖κ ξ‖) volume := by
    apply ((κ.integrable.norm.add ((κ.integrable_pow_mul volume 1).const_mul tau)).const_mul D).congr
    filter_upwards with ξ
    simp only [Pi.add_apply, pow_one]
    ring
  have hIntF : Integrable F ((volume : Measure E).prod volume) := by
    refine (hIntκ.mul_prod u.integrable.norm).mono' hContF.aestronglyMeasurable ?_
    filter_upwards with p
    have he : ‖a x p.2 (tau • p.1)‖ ≤ D * (1 + tau * ‖p.1‖) := by
      simpa only [norm_iteratedFDeriv_zero, norm_smul, Real.norm_of_nonneg tauPos] using hD x p.2 (tau • p.1)
    simp only [F, norm_mul, patch_fourier_phase_norm, one_mul]
    calc
      _ ≤ ‖κ p.1‖ * (D * (1 + tau * ‖p.1‖) * ‖u p.2‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  calc
    _ = ∫ ξ : E, ∫ y : E, F (ξ, y) := by
      unfold radianTwoPointCutoffAction
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [F, κ, a, integral_const_mul]
    _ = ∫ y : E, ∫ ξ : E, F (ξ, y) := integral_integral_swap (f := fun ξ y => F (ξ, y)) hIntF
    _ = _ := by
      unfold compactKernelAction
      apply integral_congr_ae
      filter_upwards with y
      let m := (1 / 2 : ℝ) • (x+y)
      have hK : (𝓕⁻ (dyadicWeylFiniteSymbol β n m)) (x-y) =
          a01CompleteFiniteKernel (normalizedWeylSymbol β) n (m,x-y) :=
        dyadic_weyl_finite_inverse_eq_actual_bands β n m (x-y) (hβ m)
      have he : (fun ξ : E => F (ξ,y)) = fun ξ =>
          ((θ x : ℂ) * (θ y : ℂ)) *
            (patchFourierPhase ξ (x-y) * dyadicWeylFiniteSymbol β n m ξ) * u y := by
        funext ξ
        simp only [F, κ, a, windowedWeylDyadicCutoff_apply, windowedWeylAmplitude,
          dyadic_weyl_finite_symbol_eq_cutoff, m, ← windowedWeyl_phase_sub]
        ring
      rw [he, integral_mul_const, integral_const_mul]
      have hI : ∫ ξ : E, patchFourierPhase ξ (x-y) * dyadicWeylFiniteSymbol β n m ξ =
          a01CompleteFiniteKernel (normalizedWeylSymbol β) n (m,x-y) := by
        rw [← hK, Real.fourierIntegralInv_eq']
        rfl
      rw [hI]
      simp only [a01LocalizedWeylFiniteKernel, Complex.ofReal_mul, m]

/-- The summand here is the original A01 finite Weyl action, with the
same output/input cutoffs. Its limit is the actual reduced left operator. -/
theorem windowedWeyl_dyadic_kernel_tendsto_leftAction (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hβ : ∀ x, Continuous (normalizedWeylSymbol β x)) (u : SchwartzMap E ℂ) (x : E) :
    Tendsto (fun n => compactKernelAction (a01LocalizedWeylFiniteKernel β (fun s t => θ s * θ t) n) u x)
      atTop (𝓝 (firstOrderAction (windowedWeylLeftSymbol θ β R h) u x)) :=
  (windowedWeyl_dyadic_tendsto_leftAction θ β R h u x).congr'
    (Eventually.of_forall fun n => windowedWeyl_physical_cutoff_eq_dyadic_kernel θ β R h hβ n u x)

/-- The physical parity belongs to that exact A01 left action even though
the left symbol itself need not be real. -/
theorem windowedWeyl_leftAction_anticommutes (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hβ : ∀ x, Continuous (normalizedWeylSymbol β x))
    (hReal : ∀ x ξ, conj (β x ξ) = β x ξ) (hOdd : ∀ x ξ, β x (-ξ) = -β x ξ)
    (u v : SchwartzMap E ℂ) (hv : ∀ y, v y = conj (u y)) (x : E) :
    conj (firstOrderAction (windowedWeylLeftSymbol θ β R h) u x) =
      -firstOrderAction (windowedWeylLeftSymbol θ β R h) v x := by
  have hu := windowedWeyl_dyadic_kernel_tendsto_leftAction θ β R h hβ u x
  have hv' := windowedWeyl_dyadic_kernel_tendsto_leftAction θ β R h hβ v x
  have hcu := Complex.continuous_conj.continuousAt.tendsto.comp hu
  have hnv := hv'.neg
  refine tendsto_nhds_unique hcu (hnv.congr' (Eventually.of_forall fun n => ?_))
  exact (a01_weyl_localized_finite_action_anticommutes β hβ hReal hOdd
    (fun s t => θ s * θ t) n u v hv x).symm

private theorem windowedWeyl_physical_cutoff_uniform_bound (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (u : SchwartzMap E ℂ) : ∃ C : ℝ, ∀ n x,
      ‖radianTwoPointCutoffAction (windowedWeylAmplitude θ β) (windowedWeylDyadicCutoff n) u x‖ ≤ C := by
  let a := windowedWeylAmplitude θ β
  let A := compactRadianTwoPointSlice a R R h
  let F := radianSchwartzAmplitudeProfile A
  obtain ⟨w,hw⟩ := exists_radian_amplitude_fourier_bounds A
    (compact_radian_two_point_slice_order_one a R R h) (compact_radian_two_point_profile_measurable a R R h)
  let D (p : E × E) := (w p.1 * (1 + tau * ‖p.1‖)) *
    ((1 + tau * ‖p.2‖) * ‖𝓕 (u : E → ℂ) p.2‖)
  let μ := (volume : Measure E).prod (volume : Measure E)
  have hD : Integrable D μ := hw.momentOne.mul_prod (radian_schwartz_fourier_first_moment u)
  refine ⟨∫ p, D p ∂μ, fun n x => ?_⟩
  let κ := windowedWeylDyadicCutoff n
  let Fcut := radianAmplitudeProfileCutoff F κ
  have hb (ξ : E) : ‖κ ξ‖ ≤ 1 := by
    rw [show κ ξ = (dyadicWeylCutoff n ξ : ℂ) from windowedWeylDyadicCutoff_apply n ξ,
      Complex.norm_real, dyadicWeylCutoff, Real.norm_of_nonneg (Burnett.Microlocal.AngularDyadicKernel.radialCore_nonneg _)]
    exact Burnett.Microlocal.AngularDyadicKernel.radialCore_le_one _
  have hcut := radian_amplitude_profile_cutoff_bounds F w hw κ hb
  have hEq : radianTwoPointCutoffAction a κ u x =
      ∫ p, radianAmplitudeShiftedIntegrand Fcut u x p ∂μ :=
    (radian_schwartz_amplitude_cutoff_action_eq_left A w hw κ hb u x).trans
      (radian_left_amplitude_reduced_eq_product Fcut w hcut u x)
  change ‖radianTwoPointCutoffAction a κ u x‖ ≤ _
  rw [hEq]
  exact norm_integral_le_of_norm_le hD
    (Eventually.of_forall (radian_amplitude_shifted_integrand_bound Fcut w hcut u x))

/-- The genuine A01 left operator is formally symmetric on the full
Schwartz domain. The same finite kernels tend in both pairings. -/
theorem windowedWeyl_leftAction_formallySymmetric (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hβ : ContDiff ℝ 1 (uncurry (normalizedWeylSymbol β)))
    (hOrd : FrequencyOrderOne (normalizedWeylSymbol β))
    (hReal : ∀ x ξ, conj (β x ξ) = β x ξ) :
    FirstOrderFormalSymmetry (windowedWeylLeftSymbol θ β R h) := by
  let w (x y : E) := θ x * θ y
  let K (n : ℕ) := a01LocalizedWeylFiniteKernel β w n
  let B (n : ℕ) (u : SchwartzMap E ℂ) := compactKernelAction (K n) u
  let L (u : SchwartzMap E ℂ) := firstOrderAction (windowedWeylLeftSymbol θ β R h) u
  let a := normalizedWeylSymbol β
  have hw : Continuous (uncurry w) := (hθ.comp continuous_fst).mul (hθ.comp continuous_snd)
  have hPair : Continuous (fun p : E × E => ((1 / 2 : ℝ) • (p.1+p.2),p.1-p.2)) :=
    (continuous_const.smul (continuous_fst.add continuous_snd)).prodMk (continuous_fst.sub continuous_snd)
  have hMeas (n : ℕ) (u : SchwartzMap E ℂ) : AEStronglyMeasurable (B n u) volume := by
    have hK : Continuous (a01CompleteFiniteKernel a n) :=
      (a01_low_frequency_kernel_contDiff a hβ).continuous.add
        (continuous_finset_sum _ fun j _ => (a01_annular_kernel_contDiff_and_base a hβ j).1.continuous)
    have hC : Continuous (uncurry (K n)) := (Complex.continuous_ofReal.comp hw).mul (hK.comp hPair)
    exact ((hC.mul (u.continuous.comp continuous_snd)).measurable.stronglyMeasurable.integral_prod_right'
      (ν := volume)).aestronglyMeasurable
  have hCont : ∀ x, Continuous (a x) := fun x => (hOrd.smooth x).continuous
  have hlim : ∀ u x, Tendsto (fun n => B n u x) atTop (𝓝 (L u x)) :=
    windowedWeyl_dyadic_kernel_tendsto_leftAction θ β R h hCont
  have hUniform (u : SchwartzMap E ℂ) : ∃ C : ℝ, ∀ n x, ‖B n u x‖ ≤ C := by
    obtain ⟨C,hC⟩ := windowedWeyl_physical_cutoff_uniform_bound θ β R h u
    refine ⟨C, fun n x => ?_⟩
    change ‖compactKernelAction (a01LocalizedWeylFiniteKernel β (fun s t => θ s * θ t) n) u x‖ ≤ C
    rw [← windowedWeyl_physical_cutoff_eq_dyadic_kernel θ β R h hCont n u x]
    exact hC n x
  obtain ⟨m,hm⟩ := (hθc.image hθ.norm).bddAbove
  let M := max 0 m
  have hb (x : E) : ‖θ x‖ ≤ M := by
    by_cases hx : x ∈ tsupport θ
    · exact (hm ⟨x,hx,rfl⟩).trans (le_max_right _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
      exact le_max_left _ _
  have hB (x y : E) : ‖w x y‖ ≤ M^2 := by
    rw [show w x y = θ x * θ y from rfl, norm_mul, pow_two]
    exact mul_le_mul (hb x) (hb y) (norm_nonneg _) (le_max_left _ _)
  have hSym (n : ℕ) (u v : SchwartzMap E ℂ) :
      weylLebesguePairing (B n u) v = weylLebesguePairing u (B n v) := by
    have hs := a01_weyl_localized_finite_formal_symmetry β hβ hOrd hReal w hw (M^2) hB
      (fun x y => mul_comm (θ x) (θ y)) n v u
    simpa only [weylLebesguePairing, B, K, mul_comm] using hs
  intro u v
  have hl := (schwartz_weyl_formal_symmetry_of_uniform_pointwise_limit B L hMeas hUniform hlim hSym v u).2.2
  simpa only [weylLebesguePairing, L, mul_comm] using hl

end Burnett.V03
