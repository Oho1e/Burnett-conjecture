import Burnett.Analysis.PrincipalEnergy.Commutator.WaveletOperator
import Burnett.Analysis.PrincipalEnergy.Quantization.ActualConstantMean

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Set Filter Metric
open Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators NNReal

/-- All finite wavelet energies on a ball at scales at most its radius
are controlled by a single local mean-square oscillation on the doubled ball. -/
theorem exists_compactWaveletAction_local_square_bound (ψ : SchwartzMap Space ℂ)
    (hψ : ∀ z, 1<‖z‖ → ψ z = 0) (hMean : (∫ z, ψ z) = 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : Space → ℂ), MemLp b 2 volume →
      ∀ (m : ℂ) (c : Space) (R t : ℝ), 0<t → ∀ (J : Finset ℕ),
        (∀ j ∈ J, compactWaveletScale t j ≤ R) →
        (∑ j ∈ J, ∫ x in ball c R, ‖compactWaveletAction ψ (compactWaveletScale t j) b x‖^2) ≤
          D * ∫ x in ball c (2*R), ‖b x-m‖^2 := by
  obtain ⟨D,hD,hSquare⟩ := exists_compactWaveletAction_square_bound ψ hMean
  refine ⟨D,hD,fun b hb m c R t ht J hJ => ?_⟩
  let S := ball c (2*R)
  let μ := (volume : Measure Space).restrict S
  let g := S.indicator (fun x => b x-m)
  letI : IsFiniteMeasure μ := ⟨by
    change (volume : Measure Space).restrict S univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  have hBm : MemLp (fun x => b x-m) 2 μ := (hb.restrict S).sub (memLp_const m)
  have hG₂ : MemLp g 2 volume := (memLp_indicator_iff_restrict measurableSet_ball).mpr hBm
  have hG₁ : Integrable g volume :=
    (integrable_indicator_iff measurableSet_ball).mpr (hBm.integrable (by norm_num))
  obtain ⟨hOutput,hTotal⟩ := hSquare t ht J g hG₁ hG₂
  have hInput : (∫ x, ‖g x‖^2) = ∫ x in S, ‖b x-m‖^2 := by
    rw [← integral_indicator measurableSet_ball]
    apply congrArg (fun F : Space → ℝ => ∫ x, F x)
    funext x
    change ‖g x‖^2 = S.indicator (fun y => ‖b y-m‖^2) x
    by_cases hx : x∈S
    · simp only [g,indicator_of_mem hx]
    · simp only [g,indicator_of_notMem hx,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)]
  rw [← hInput]
  refine (Finset.sum_le_sum (fun j hj => ?_)).trans hTotal
  let s := compactWaveletScale t j
  have hs : 0 < s := div_pos ht (pow_pos (by norm_num) _)
  have hLoc (x : Space) (hx : x∈ball c R) :
      compactWaveletAction ψ s b x = compactWaveletAction ψ s g x :=
    compactWaveletAction_localize ψ hψ hMean b hb m c x R s hs (hJ j hj) hx
  calc
    _ = ∫ x in ball c R, ‖compactWaveletAction ψ s g x‖^2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      change ‖compactWaveletAction ψ s b x‖^2 = ‖compactWaveletAction ψ s g x‖^2
      rw [hLoc x hx]
    _ ≤ ∫ x, ‖compactWaveletAction ψ s g x‖^2 :=
      setIntegral_le_integral ((hOutput j).integrable_norm_pow (p := 2) (by decide))
        (Eventually.of_forall fun _ => sq_nonneg _)

/-- On the actual compact-base coefficient commutator, the identified T(1)
has uniformly bounded dyadic energy on every ball at all smaller scales. -/
theorem exists_compactBase_commutatorConstant_wavelet_carleson {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (ψ : SchwartzMap Space ℂ)
    (hψ : ∀ z, 1<‖z‖ → ψ z = 0) (hMean : (∫ z, ψ z) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0 ≤ U → LipschitzWith L r → (∀ x, ‖r x‖ ≤ U) →
      ∀ (c : Space) (R t : ℝ), 0<R → 0<t → ∀ (J : Finset ℕ),
        (∀ j ∈ J, compactWaveletScale t j ≤ R) →
        (∑ j ∈ J, ∫ x in ball c R, ‖compactWaveletAction ψ (compactWaveletScale t j)
          (coefficientCommutatorConstant a r) x‖^2) ≤ C*(U+(L:ℝ))^2*R^4 := by
  obtain ⟨D,hD,hLocal⟩ := exists_compactWaveletAction_local_square_bound ψ hψ hMean
  obtain ⟨A,hA,hOsc⟩ := exists_compactBase_coefficientCommutatorConstant_meanOscillation ha hBase hCont
  refine ⟨16*D*A,by positivity,?_⟩
  intro r L U hU hLip hR c R t hRpos ht J hJ
  let b := coefficientCommutatorConstant a r
  have hb : MemLp b 2 volume := coefficientCommutatorConstant_memLp ha.frequency hBase hCont r
  have hRadius : 0 < 2*R := mul_pos (by norm_num) hRpos
  obtain ⟨m,hm⟩ := hOsc r L U hU hLip hR c (2*R) hRadius
  calc
    _ ≤ D * ∫ x in ball c (2*R), ‖b x-m‖^2 := hLocal b hb m c R t ht J hJ
    _ ≤ D*(A*(U+(L:ℝ))^2*(2*R)^4) := mul_le_mul_of_nonneg_left hm hD
    _ = _ := by ring

end Burnett.Analysis.CarlesonEmbedding
