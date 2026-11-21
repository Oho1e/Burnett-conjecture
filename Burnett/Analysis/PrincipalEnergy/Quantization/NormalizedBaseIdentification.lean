import Burnett.Analysis.PrincipalEnergy.Quantization.CompactBaseFourier

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Set Filter MeasureTheory Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff FourierTransform Topology

private theorem normalizedBaseSymbol_joint_continuous {a : E → E → ℂ}
    (ha : Continuous (Function.uncurry a)) :
    Continuous (Function.uncurry (normalizedBaseSymbol a)) :=
  ((continuous_const.add continuous_snd.norm).inv₀ (fun _ => by positivity)).smul ha

/-- The actual base Fourier coefficient is jointly continuous, including at the
original zero frequency. The common compact base support supplies an integrable
majorant for both Fourier parameters. -/
theorem normalizedBaseFourier_joint_continuous {a : E → E → ℂ}
    (ha : CompactBaseOrderOne a) (hs : Continuous (Function.uncurry a)) :
    Continuous (Function.uncurry (normalizedBaseFourier a)) := by
  obtain ⟨K,hK,hSupport⟩ := ha.support
  obtain ⟨C,hC,hBound⟩ := ha.order 0
  let G (p : E × E) (x : E) :=
    Complex.exp ((↑(-2 * Real.pi * inner ℝ x p.1) : ℂ) * Complex.I) *
      normalizedBaseSymbol a x p.2
  have hx (p : E × E) : Continuous (G p) := by
    exact (Complex.continuous_exp.comp (by fun_prop)).mul
      ((normalizedBaseSymbol_joint_continuous hs).comp (continuous_id.prodMk continuous_const))
  have hp (x : E) : Continuous (fun p => G p x) := by
    exact (Complex.continuous_exp.comp (by fun_prop)).mul
      ((normalizedBaseSymbol_joint_continuous hs).comp (continuous_const.prodMk continuous_snd))
  have hInt : Integrable (K.indicator (fun _ : E => C)) :=
    (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  have hG (p : E × E) (x : E) : ‖G p x‖ ≤ K.indicator (fun _ => C) x := by
    rw [show ‖G p x‖ = ‖normalizedBaseSymbol a x p.2‖ by
      dsimp only [G]; rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]]
    by_cases h : x ∈ K
    · rw [indicator_of_mem h, normalizedBaseSymbol, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
      have hb : ‖a x p.2‖ ≤ C * (1 + ‖p.2‖) := by
        simpa only [norm_iteratedFDeriv_zero] using hBound x p.2
      exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (by positivity))).trans_eq (by
        field_simp)
    · have h0 : a x p.2 = 0 := by
        by_contra hz
        exact h (hSupport p.2 (subset_tsupport _ hz))
      simp [indicator_of_notMem h, normalizedBaseSymbol, h0]
  have hEq (p : E × E) : normalizedBaseFourier a p.1 p.2 = ∫ x, G p x := by
    rw [normalizedBaseFourier, Real.fourierIntegral_eq']
    rfl
  apply continuous_iff_continuousAt.mpr
  intro p
  change Tendsto (fun q : E × E => normalizedBaseFourier a q.1 q.2) (𝓝 p)
    (𝓝 (normalizedBaseFourier a p.1 p.2))
  simp_rw [hEq]
  exact tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall fun q =>
    (hx q).aestronglyMeasurable) (Eventually.of_forall fun q => Eventually.of_forall (hG q))
    hInt (Eventually.of_forall fun x => (hp x).tendsto p)

/-- Exact inverse base Fourier representation of the normalized compact-base
symbol, including every original frequency and spatial point. -/
theorem normalizedBaseFourier_inverse {a : E → E → ℂ} (ha : CompactBaseOrderOne a)
    (x ξ : E) :
    (𝓕⁻ (fun k => normalizedBaseFourier a k ξ)) x = normalizedBaseSymbol a x ξ := by
  obtain ⟨K,hK,hS⟩ := ha.support
  have hCompact : HasCompactSupport (fun y => normalizedBaseSymbol a y ξ) :=
    hK.of_isClosed_subset isClosed_closure
      ((closure_mono (Function.support_const_smul_subset _ _)).trans (hS ξ))
  let s : SchwartzMap E ℂ := hCompact.toSchwartzMap ((ha.smooth ξ).const_smul _)
  let F := SchwartzMap.fourierTransformCLM ℂ s
  exact congrFun (s.continuous.fourier_inversion s.integrable F.integrable) x

end Burnett.Analysis.FirstOrderDyadic
