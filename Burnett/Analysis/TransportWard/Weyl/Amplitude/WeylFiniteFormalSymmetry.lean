import Burnett.Analysis.TransportWard.Weyl.Amplitude.WeylParity
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option maxHeartbeats 4700000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set
open Burnett.A02.FrequencySplit (E tau)
open Burnett.Analysis.FirstOrderDyadic
open Burnett.Microlocal.AngularDyadicKernel
  (radialCore radialCore_eq_zero radialCore_nonneg radialCore_le_one dyadicScale)
open scoped ContDiff FourierTransform ComplexConjugate Topology

/-- The Hermitian two-point kernel satisfies formal symmetry on the
Schwartz pairing when its joint bound makes the Fubini step absolute. -/
theorem compact_kernel_formal_symmetry_of_hermitian (K : E → E → ℂ)
    (c : Continuous (Function.uncurry K))
    (C : ℝ) (bound : ∀ x y, ‖K x y‖ ≤ C)
    (sym : ∀ x y, conj (K x y) = K y x) (u v : SchwartzMap E ℂ) :
    (∫ x : E, conj (u x) * compactKernelAction K v x) =
      ∫ y : E, conj (compactKernelAction K u y) * v y := by
  let F (x y : E) := conj (u x) * (K x y * v y)
  have Fc : Continuous (Function.uncurry F) :=
    (Complex.continuous_conj.comp (u.continuous.comp continuous_fst)).mul
      (c.mul (v.continuous.comp continuous_snd))
  have ui : Integrable (u : E → ℂ) (volume : Measure E) := u.integrable
  have vi : Integrable (v : E → ℂ) (volume : Measure E) := v.integrable
  have m := (ui.norm.const_mul C).mul_prod vi.norm
  have fI : Integrable (Function.uncurry F) ((volume : Measure E).prod volume) := by
    apply m.mono' Fc.aestronglyMeasurable
    refine Eventually.of_forall fun p => ?_
    simp only [Function.uncurry,F,norm_mul,Complex.norm_conj]
    calc
      _ ≤ ‖u p.1‖ * (C * ‖v p.2‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (bound p.1 p.2) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  calc
    _ = ∫ x : E, ∫ y : E, F x y := by
      simp only [F,compactKernelAction,integral_const_mul]
    _ = ∫ y : E, ∫ x : E, F x y := integral_integral_swap fI
    _ = _ := by
      apply integral_congr_ae
      refine Eventually.of_forall fun y => ?_
      change (∫ x : E, F x y) = conj (∫ x : E, K y x * u x) * v y
      rw [← integral_conj, ← integral_mul_const]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [F,map_mul,sym y x,mul_assoc]
        ring

private theorem exists_plain_actual_weyl_finite_kernel_bound (β : E → E → ℂ)
    (ord : FrequencyOrderOne (normalizedWeylSymbol β)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z,
      ‖a01CompleteFiniteKernel (normalizedWeylSymbol β) N (x,z)‖ ≤ C := by
  obtain ⟨M,M0,Mo⟩ := ord.order 0
  have growth (x ξ : E) : ‖β x (tau • ξ)‖ ≤ M*(1+‖ξ‖) := by
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one,normalizedWeylSymbol] using Mo x ξ
  let s := dyadicScale N
  have sp : 0 < s := by dsimp [s,dyadicScale]; positivity
  let S := closedBall (0 : E) (2*s)
  let g : E → ℝ := S.indicator (fun ξ => M*(1+‖ξ‖))
  have gi : Integrable g volume := by
    have Sc : IsCompact S := isCompact_closedBall _ _
    rw [integrable_indicator_iff Sc.measurableSet]
    exact ((continuous_const.mul (continuous_const.add continuous_norm)).continuousOn).integrableOn_compact Sc
  refine ⟨∫ ξ : E, g ξ, integral_nonneg (indicator_nonneg (fun ξ _ => by positivity)),?_⟩
  intro x z
  change ‖firstOrderLowKernel _ x z + ∑ j ∈ Finset.range N, firstOrderAnnularKernel _ x j z‖ ≤ _
  rw [← dyadic_weyl_finite_inverse_eq_actual_bands β N x z ((ord.smooth x).continuous)]
  simp only [Real.fourierIntegralInv_eq',dyadic_weyl_finite_symbol_eq_cutoff,smul_eq_mul]
  apply norm_integral_le_of_norm_le gi
  refine Eventually.of_forall fun ξ => ?_
  by_cases ξin : ξ ∈ S
  · rw [show g ξ = M*(1+‖ξ‖) from indicator_of_mem ξin _]
    change ‖patchFourierPhase ξ z * ((dyadicWeylCutoff N ξ : ℂ) * β x (tau • ξ))‖ ≤ _
    rw [norm_mul,norm_mul,patch_fourier_phase_norm, one_mul, Complex.norm_real,
      dyadicWeylCutoff, Real.norm_of_nonneg (radialCore_nonneg _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (radialCore_le_one _)).trans (growth x ξ)
  · have far : 2*s < ‖ξ‖ := by simpa only [S,mem_closedBall,dist_zero_right,not_le] using ξin
    have f : 2 ≤ ‖s⁻¹ • ξ‖ := by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr sp.le),← div_eq_inv_mul]
      exact (le_div_iff₀ sp).mpr far.le
    have cutZero : dyadicWeylCutoff N ξ = 0 := radialCore_eq_zero _ f
    simp [g,ξin,cutZero]

/-- An actual finite Weyl action for a real complete symbol with a bounded
real symmetric localization is formally self-adjoint on Schwartz tests. -/
theorem a01_weyl_localized_finite_formal_symmetry
    (β : E → E → ℂ)
    (bs : ContDiff ℝ 1 (Function.uncurry (normalizedWeylSymbol β)))
    (ord : FrequencyOrderOne (normalizedWeylSymbol β))
    (real : ∀ x ξ, conj (β x ξ) = β x ξ)
    (w : E → E → ℝ) (wc : Continuous (Function.uncurry w))
    (W : ℝ) (wb : ∀ x y, ‖w x y‖ ≤ W)
    (sym : ∀ x y, w x y = w y x) (N : ℕ) (u v : SchwartzMap E ℂ) :
    let K := a01LocalizedWeylFiniteKernel β w N
    (∫ x : E, conj (u x) * compactKernelAction K v x) =
      ∫ y : E, conj (compactKernelAction K u y) * v y := by
  intro K
  let A := normalizedWeylSymbol β
  have cont : ∀ x, Continuous (A x) := fun x => (ord.smooth x).continuous
  have C : Continuous (a01CompleteFiniteKernel A N) :=
    (a01_low_frequency_kernel_contDiff A bs).continuous.add
      (continuous_finset_sum _ fun j _ => (a01_annular_kernel_contDiff_and_base A bs j).1.continuous)
  have P : Continuous (fun p : E × E => (((1/2 : ℝ) • (p.1+p.2)), p.1-p.2)) :=
    (continuous_const.smul (continuous_fst.add continuous_snd)).prodMk (continuous_fst.sub continuous_snd)
  have kc : Continuous (Function.uncurry K) :=
    (Complex.continuous_ofReal.comp wc).mul (C.comp P)
  obtain ⟨D,_,b⟩ := exists_plain_actual_weyl_finite_kernel_bound β ord N
  apply compact_kernel_formal_symmetry_of_hermitian K kc (W*D) _ _
  · intro x y
    rw [show K x y = (w x y : ℂ) *
      a01CompleteFiniteKernel A N ((1/2 : ℝ) • (x+y),x-y) from rfl, norm_mul,Complex.norm_real]
    exact mul_le_mul (wb x y) (b _ _) (norm_nonneg _) ((norm_nonneg _).trans (wb x y))
  · exact a01_weyl_localized_finite_kernel_hermitian β cont real w sym N

end Burnett.A03
