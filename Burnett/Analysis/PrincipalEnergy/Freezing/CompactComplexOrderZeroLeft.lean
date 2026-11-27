import Burnett.Analysis.PrincipalEnergy.Freezing.CompactOrderZeroLeft
import Burnett.Analysis.PrincipalEnergy.Freezing.FixedTestOrderZeroAlgebra

set_option autoImplicit false
set_option maxHeartbeats 4300000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal FourierTransform

private theorem compact_base_real_order_zero_value (a : E → E → ℝ)
    (ha : CompactBaseFrequencyJets (fun x ξ => (a x ξ : ℂ)) univ)
    (D : ℝ) (hD : CompactBaseOrderZeroBudget a D) (x ξ : E) :
    ‖a x ξ‖ ≤ D := by
  have c : Continuous (a x) :=
    Complex.reCLM.continuous.comp (contDiffOn_univ.mp (ha.frequencySmooth x)).continuous
  let A := {q : E | ‖a x q‖ ≤ D}
  have hA : IsClosed A := isClosed_le c.norm continuous_const
  have incl : (({0} : Set E)ᶜ) ⊆ A := by
    intro q hq
    have nz : q ≠ 0 := hq
    simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero, Complex.norm_real]
      using (hD 0 (by decide) q nz x).1
  have all := closure_minimal incl hA
  rw [closure_compl_singleton] at all
  exact all (mem_univ ξ)

theorem bounded_real_radian_spectrum_integrable (b : E → ℝ) (hM : Measurable b)
    (D : ℝ) (bound : ∀ ξ, ‖b ξ‖ ≤ D) (u : SchwartzMap E ℂ) :
    Integrable (radianActionSpectrum b u) (volume : Measure E) := by
  let U := SchwartzMap.fourierTransformCLM ℂ u
  let F := radianActionSpectrum b u
  have fm : Measurable F := by
    change Measurable (fun ξ : E => (b (tau • ξ) : ℂ) * U ξ)
    exact (Complex.continuous_ofReal.measurable.comp
      (hM.comp (continuous_const.smul continuous_id).measurable)).mul U.continuous.measurable
  have fb (ξ : E) : ‖F ξ‖ ≤ D * ‖U ξ‖ := by
    change ‖(b (tau • ξ) : ℂ) * U ξ‖ ≤ _
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (bound _) (norm_nonneg _)
  exact (U.integrable.norm.const_mul D).mono' fm.aestronglyMeasurable (Eventually.of_forall fb)

private theorem radian_left_real_imaginary_split (a r : E → E → ℝ)
    (aM : ∀ x, Measurable (a x)) (rM : ∀ x, Measurable (r x))
    (D F : ℝ) (da : ∀ x ξ, ‖a x ξ‖ ≤ D) (dr : ∀ x ξ, ‖r x ξ‖ ≤ F) :
    radianLeftQuantization (fun x ξ => (a x ξ : ℂ) + Complex.I * (r x ξ : ℂ)) =
      fun u => radianLeftQuantization (fun x ξ => (a x ξ : ℂ)) u +
        Complex.I • radianLeftQuantization (fun x ξ => (r x ξ : ℂ)) u := by
  funext u x
  let p (ξ : E) := patchFourierPhase ξ x
  let args (ξ : E) : E × E := (ξ,x)
  have argsC : Continuous args := continuous_id.prodMk continuous_const
  have pC : Continuous p := by
    change Continuous ((fun z : E × E => patchFourierPhase z.1 z.2) ∘ args)
    exact patch_fourier_phase_continuous.comp argsC
  have pB : ∃ C : ℝ, ∀ ξ, ‖p ξ‖ ≤ C := ⟨1,fun ξ => (patch_fourier_phase_norm ξ x).le⟩
  let W (b : E → ℝ) (ξ : E) := p ξ * radianActionSpectrum b u ξ
  have ia : Integrable (W (a x)) volume :=
    (bounded_real_radian_spectrum_integrable (a x) (aM x) D (da x) u).bdd_mul pC.aestronglyMeasurable pB
  have ir : Integrable (W (r x)) volume :=
    (bounded_real_radian_spectrum_integrable (r x) (rM x) F (dr x) u).bdd_mul pC.aestronglyMeasurable pB
  have eq (b : E → E → ℝ) :
      radianLeftQuantization (fun y ξ => (b y ξ : ℂ)) u x = ∫ ξ, W (b x) ξ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun ξ => by simp only [W,p,radianActionSpectrum,mul_assoc]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, eq]
  rw [← integral_const_mul, ← integral_add ia (ir.const_mul Complex.I)]
  apply integral_congr_ae
  exact Eventually.of_forall fun ξ => by
    simp only [W, p, radianActionSpectrum]
    ring

/-- The actual compact-base complex left order-zero action, allowing both
real and imaginary parts of a full left symbol. -/
theorem exists_compact_base_complex_order_zero_left_W13 (P R : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) R, ρ x = 1)
    (a r : E → E → ℝ)
    (aSupport : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (rSupport : ∀ x ξ, x ∉ closedBall (0 : E) R → r x ξ = 0)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) univ)
    (hr : CompactBaseFrequencyJets (fun x q => (r x q : ℂ)) univ)
    (D F : ℝ) (D0 : 0 ≤ D) (F0 : 0 ≤ F)
    (hD : CompactBaseOrderZeroBudget a D) (hF : CompactBaseOrderZeroBudget r F) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ SchwartzOrderZeroJetBound
      (radianLeftQuantization (fun x ξ => (a x ξ : ℂ) + Complex.I * (r x ξ : ℂ))) A A := by
  obtain ⟨A,Afin,aB⟩ := exists_compact_base_order_zero_left_action_W13 P R hP hRP ρ hρ hS ρone a aSupport ha D D0 hD
  obtain ⟨B,Bfin,rB⟩ := exists_compact_base_order_zero_left_action_W13 P R hP hRP ρ hρ hS ρone r rSupport hr F F0 hF
  have aM (x : E) : Measurable (a x) :=
    (Complex.reCLM.continuous.comp (contDiffOn_univ.mp (ha.frequencySmooth x)).continuous).measurable
  have rM (x : E) : Measurable (r x) :=
    (Complex.reCLM.continuous.comp (contDiffOn_univ.mp (hr.frequencySmooth x)).continuous).measurable
  rw [radian_left_real_imaginary_split a r aM rM D F
    (compact_base_real_order_zero_value a ha D hD) (compact_base_real_order_zero_value r hr F hF)]
  have im := schwartz_order_zero_jet_bound_const_mul _ _ _ rB Complex.I
  have iUnit : ‖Complex.I‖ₑ = 1 := by rw [← ofReal_norm_eq_enorm, Complex.norm_I, ENNReal.ofReal_one]
  simp only [iUnit, one_mul] at im
  exact ⟨A+B,ENNReal.add_lt_top.mpr ⟨Afin,Bfin⟩,schwartz_order_zero_jet_bound_add _ _ _ _ _ _ aB im⟩

end Burnett.A03
