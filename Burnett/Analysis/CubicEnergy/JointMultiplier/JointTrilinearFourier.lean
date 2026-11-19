import Burnett.Analysis.CubicEnergy.JointMultiplier.PhysicalBandLimit

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory
open scoped ContDiff FourierTransform RealInnerProductSpace

private def F (f : SchwartzMap E ℂ) : SchwartzMap E ℂ := SchwartzMap.fourierTransformCLM ℂ f
private def osc (x : E) (p : Joint) : ℂ :=
  Complex.exp ((↑(2*Real.pi*(inner ℝ p.1 x + inner ℝ p.2 x)) : ℂ)*Complex.I)
private theorem osc_norm (x : E) (p : Joint) : ‖osc x p‖ = 1 := by simp [osc,Complex.norm_exp]
private theorem osc_test (h : SchwartzMap E ℂ) (p : Joint) :
    (∫ x, osc x p * h x) = 𝓕 (h : E → ℂ) (-(p.1+p.2)) := by
  rw [Real.fourierIntegral_eq']
  apply integral_congr_ae
  filter_upwards with x
  simp only [osc,inner_neg_right,inner_add_right,real_inner_comm x p.1,real_inner_comm x p.2,
    smul_eq_mul,neg_mul,mul_neg,neg_neg]

/-- Pairing the physical bilinear block with the third Schwartz function
recovers its Fourier transform at minus the sum of the input frequencies. -/
theorem block_trilinear_fourier (a : Joint → ℂ) (ha : HasCompactSupport a) (hs : ContDiff ℝ ∞ a)
    (s : ℝ) (f g h : SchwartzMap E ℂ) :
    (∫ x, (∫ y : Joint, blockKernel a y*(f (x-s • y.1)*g (x-s • y.2)))*h x) =
      ∫ p : Joint, a (s • p)*(𝓕 (f : E → ℂ) p.1 * 𝓕 (g : E → ℂ) p.2)*𝓕 (h : E → ℂ) (-(p.1+p.2)) := by
  let T := fun p : Joint => a (s • p)*(F f p.1*F g p.2)
  obtain ⟨u,hu⟩ := hs.continuous.norm.exists_forall_ge_of_hasCompactSupport ha.norm
  have hT : Integrable T := ((F f).integrable.mul_prod (F g).integrable).bdd_mul
    ((hs.continuous.comp (continuous_const.smul continuous_id)).aestronglyMeasurable) ⟨_,fun p => hu (s • p)⟩
  have tc : Continuous T := (hs.continuous.comp (continuous_const.smul continuous_id)).mul
    (((F f).continuous.comp continuous_fst).mul ((F g).continuous.comp continuous_snd))
  let U := fun (x : E) (p : Joint) => T p*(osc x p*h x)
  have iu : Integrable (Function.uncurry U) ((volume : Measure E).prod volume) := by
    have oc : Continuous (fun q : E × Joint => osc q.1 q.2) := by unfold osc; fun_prop
    apply (h.integrable.norm.mul_prod hT.norm).mono' ((tc.comp continuous_snd).mul (oc.mul
      (h.continuous.comp continuous_fst))).aestronglyMeasurable
    filter_upwards with q
    change ‖T q.2*(osc q.1 q.2*h q.1)‖ ≤ ‖h q.1‖*‖T q.2‖
    simp only [norm_mul,osc_norm,one_mul,mul_comm,le_refl]
  have left (x : E) : (∫ y : Joint, blockKernel a y*(f (x-s • y.1)*g (x-s • y.2)))*h x =
      ∫ p, U x p := by
    rw [block_operator_fourier a ha hs,← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with p
    change (a (s • p)*(osc x p*(F f p.1*F g p.2)))*h x = (a (s • p)*(F f p.1*F g p.2))*(osc x p*h x)
    ring
  simp_rw [left]
  rw [integral_integral_swap iu]
  apply integral_congr_ae
  filter_upwards with p
  change (∫ x, T p*(osc x p*h x)) = _
  rw [integral_const_mul,osc_test]
  rfl

end Burnett.A02.FrequencySplit
