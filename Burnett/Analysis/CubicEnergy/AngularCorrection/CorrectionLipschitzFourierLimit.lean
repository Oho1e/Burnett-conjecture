import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotFixedTest
import Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighCoefficientGapRadian
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section

namespace Burnett.A08

open Filter MeasureTheory Burnett.A02.FrequencySplit Burnett.A06 Burnett.A07
open scoped ComplexConjugate NNReal RealInnerProductSpace Topology

open private weightedSpaceMass weightedSpectrum_integrable unit_jointWeights_le
  norm_radianFourier_lipschitz_schwartz measurable_radianHighPairWeight
  from Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotFixedTest

private def radianPhase (ξ x : E) : ℂ :=
  Complex.exp ((- (inner ℝ x ξ : ℝ) : ℂ) * Complex.I)

private theorem norm_radianPhase (ξ x : E) : ‖radianPhase ξ x‖ = 1 := by
  rw [radianPhase, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]

private theorem normalizedPhaseProduct_bound {d : E → ℝ} {L : ℝ≥0}
    (hd : LipschitzWith L d) (hzero : d 0 = 0) (v : SchwartzMap E ℂ) (ξ x : E) :
    ‖radianPhase ξ x * ((d x : ℂ) * v x)‖ ≤ (L : ℝ) * (‖x‖ * ‖v x‖) := by
  have h : ‖d x‖ ≤ (L : ℝ) * ‖x‖ := by simpa [dist_eq_norm, hzero] using hd.dist_le_mul x 0
  rw [norm_mul, norm_radianPhase, one_mul, norm_mul, Complex.norm_real, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

private theorem normalizedPhaseProduct_continuous {d : E → ℝ} {L : ℝ≥0}
    (hd : LipschitzWith L d) (v : SchwartzMap E ℂ) (ξ : E) :
    Continuous (fun x => radianPhase ξ x * ((d x : ℂ) * v x)) := by
  have h : Continuous d := hd.continuous
  unfold radianPhase
  fun_prop

private theorem normalizedPhaseProduct_majorant_integrable (L : ℝ≥0) (v : SchwartzMap E ℂ) :
    Integrable (fun x : E => (L : ℝ) * (‖x‖ * ‖v x‖)) :=
  ((by simpa only [pow_one] using v.integrable_pow_mul volume 1 :
    Integrable (fun x : E => ‖x‖ * ‖v x‖))).const_mul _

private theorem radianFourier_normalizedCoefficient_tendsto
    (d : ℕ → E → ℝ) (d₀ : E → ℝ) (L : ℝ≥0) (hd : ∀ n, LipschitzWith L (d n))
    (hzero : ∀ n, d n 0 = 0) (hlim : ∀ x, Tendsto (fun n => d n x) atTop (𝓝 (d₀ x)))
    (v : SchwartzMap E ℂ) (ξ : E) :
    Tendsto (fun n => radianFourier (fun x => (d n x : ℂ) * v x) ξ) atTop
      (𝓝 (radianFourier (fun x => (d₀ x : ℂ) * v x) ξ)) := by
  change Tendsto (fun n => ∫ x, radianPhase ξ x * ((d n x : ℂ) * v x)) atTop
    (𝓝 (∫ x, radianPhase ξ x * ((d₀ x : ℂ) * v x)))
  refine tendsto_integral_of_dominated_convergence (fun x : E => (L : ℝ) * (‖x‖ * ‖v x‖))
    (fun n => (normalizedPhaseProduct_continuous (hd n) v ξ).aestronglyMeasurable)
    (normalizedPhaseProduct_majorant_integrable L v)
    (fun n => Eventually.of_forall (normalizedPhaseProduct_bound (hd n) (hzero n) v ξ)) ?_
  refine Eventually.of_forall fun x => ?_
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp (hlim x)
  exact (h.mul_const (v x)).const_mul (radianPhase ξ x)

private theorem radianHighPair_normalizedCoefficient_test_tendsto
    (b : Joint → ℂ) (hb : Measurable b) (B : ℝ) (hB : 0 ≤ B)
    (hsize : ∀ p, ‖b p‖ ≤ B * (1 + ‖p.1‖ + ‖p.2‖))
    (d : ℕ → E → ℝ) (d₀ : E → ℝ) (L : ℝ≥0) (hd : ∀ n, LipschitzWith L (d n))
    (hzero : ∀ n, d n 0 = 0) (hlim : ∀ x, Tendsto (fun n => d n x) atTop (𝓝 (d₀ x)))
    (H u w : SchwartzMap E ℂ) :
    Tendsto (fun n => radianHighPair b H u (fun x => (d n x : ℂ) * w x)) atTop
      (𝓝 (radianHighPair b H u (fun x => (d₀ x : ℂ) * w x))) := by
  let D := B * (L : ℝ) * weightedSpaceMass w
  let majorant (p : Joint) :=
    D * (((1 + ‖p.1‖) * ‖radianFourier H p.1‖) * ((1 + ‖p.2‖) * ‖radianFourier u p.2‖))
  have hI : Integrable majorant := by
    rw [Measure.volume_eq_prod E E]
    exact ((weightedSpectrum_integrable H).mul_prod (weightedSpectrum_integrable u)).const_mul D
  let g (n : ℕ) (x : E) := (d n x : ℂ) * w x
  let g₀ (x : E) := (d₀ x : ℂ) * w x
  have hMeas (n : ℕ) : Measurable (radianHighPairWeight b H u (g n)) :=
    measurable_radianHighPairWeight b hb H u (g n) H.continuous.measurable u.continuous.measurable
      ((Complex.continuous_ofReal.comp (hd n).continuous).mul w.continuous).measurable
  have hbound (n : ℕ) (p : Joint) : ‖radianHighPairWeight b H u (g n) p‖ ≤ majorant p := by
    simp only [radianHighPairWeight, norm_mul, Complex.norm_conj]
    calc
      _ ≤ (B * ((1 + ‖p.1‖) * (1 + ‖p.2‖))) * ‖radianFourier H p.1‖ * ‖radianFourier u p.2‖ *
          ((L : ℝ) * weightedSpaceMass w) := by
        gcongr
        · exact (hsize p).trans (mul_le_mul_of_nonneg_left (unit_jointWeights_le _ _) hB)
        · exact norm_radianFourier_lipschitz_schwartz (hd n) (hzero n) w _
      _ = majorant p := by dsimp only [majorant, D]; ring
  have hpoint (p : Joint) :
      Tendsto (fun n => radianHighPairWeight b H u (g n) p) atTop
        (𝓝 (radianHighPairWeight b H u g₀ p)) := by
    have hf := radianFourier_normalizedCoefficient_tendsto d d₀ L hd hzero hlim w (p.2 + p.1)
    exact (Complex.continuous_conj.continuousAt.tendsto.comp hf).const_mul _
  have h := tendsto_integral_of_dominated_convergence majorant
    (fun n => (hMeas n).aestronglyMeasurable) hI
    (fun n => Eventually.of_forall (hbound n)) (Eventually.of_forall hpoint)
  exact h.const_smul ((tau ^ 8)⁻¹)

/-- Pointwise convergence with a uniform Lipschitz bound at zero passes
through both actual high-slot Fourier integrals for fixed Schwartz tests. -/
theorem tendsto_radianHighCommutatorPair_normalizedCoefficient
    (b : Joint → ℂ) (hb : Measurable b) (B : ℝ) (hB : 0 ≤ B)
    (hsize : ∀ p, ‖b p‖ ≤ B * (1 + ‖p.1‖ + ‖p.2‖))
    (d : ℕ → E → ℝ) (d₀ : E → ℝ) (L : ℝ≥0) (hd : ∀ n, LipschitzWith L (d n))
    (hzero : ∀ n, d n 0 = 0) (hlim : ∀ x, Tendsto (fun n => d n x) atTop (𝓝 (d₀ x)))
    (H u w : SchwartzMap E ℂ) :
    Tendsto (fun n => radianHighCommutatorPair b (d n) H u w) atTop
      (𝓝 (radianHighCommutatorPair b d₀ H u w)) := by
  have hadj : Measurable (highAdjointSymbol b) :=
    Complex.continuous_conj.measurable.comp (hb.comp highAdjointFrequencies.measurable)
  have sizeAdj (p : Joint) :
      ‖highAdjointSymbol b p‖ ≤ (2 * B) * (1 + ‖p.1‖ + ‖p.2‖) := by
    rw [highAdjointSymbol, Complex.norm_conj]
    refine (hsize (highAdjointFrequencies p)).trans ?_
    change B * (1 + ‖-p.1‖ + ‖p.2 + p.1‖) ≤ _
    have ht := norm_add_le p.2 p.1
    rw [norm_neg]
    nlinarith [norm_nonneg p.2, mul_nonneg hB (norm_nonneg p.2),
      mul_nonneg hB (sub_nonneg.mpr ht)]
  have adj := radianHighPair_normalizedCoefficient_test_tendsto (highAdjointSymbol b) hadj
    (2 * B) (by positivity) sizeAdj d d₀ L hd hzero hlim (gapConjugate H) w u
  have adjEq (a : E → ℝ) :
      radianHighPair (highAdjointSymbol b) (gapConjugate H) w (fun x => (a x : ℂ) * u x) =
        conj (radianHighPair b H (fun x => (a x : ℂ) * u x) w) := by
    rw [show (gapConjugate H : E → ℂ) = (fun x => conj (H x)) from rfl]
    exact radianHighPair_highAdjoint b H _ w
  have hforward : Tendsto (fun n => radianHighPair b H (fun x => (d n x : ℂ) * u x) w) atTop
      (𝓝 (radianHighPair b H (fun x => (d₀ x : ℂ) * u x) w)) := by
    have h := Complex.continuous_conj.continuousAt.tendsto.comp adj
    change Tendsto (fun n => conj (radianHighPair (highAdjointSymbol b) (gapConjugate H)
      w (fun x => (d n x : ℂ) * u x))) atTop
      (𝓝 (conj (radianHighPair (highAdjointSymbol b) (gapConjugate H) w (fun x => (d₀ x : ℂ) * u x)))) at h
    simpa only [adjEq, starRingEnd_self_apply] using h
  exact hforward.sub (radianHighPair_normalizedCoefficient_test_tendsto
    b hb B hB hsize d d₀ L hd hzero hlim H u w)

/-- Adding a constant to the real coefficient cancels between the two
actual high-slot Fourier terms, also for coefficients of linear growth. -/
theorem radianHighCommutatorPair_sub_value_at_zero
    (b : Joint → ℂ) (hb : Measurable b) (B : ℝ) (hB : 0 ≤ B)
    (hsize : ∀ p, ‖b p‖ ≤ B * (1 + ‖p.1‖ + ‖p.2‖))
    (d : E → ℝ) (L : ℝ≥0) (hd : LipschitzWith L d) (H u w : SchwartzMap E ℂ) :
    radianHighCommutatorPair b (fun x => d x - d 0) H u w =
      radianHighCommutatorPair b d H u w := by
  let d₀ x := d x - d 0
  have hLip : LipschitzWith L d₀ := lipschitzWith_iff_norm_sub_le.2
    (fun x y => by simpa only [d₀, sub_sub_sub_cancel_right] using hd.norm_sub_le x y)
  have hZero : d₀ 0 = 0 := sub_self _
  obtain ⟨C, hC, tested⟩ := exists_radianHighCommutatorPair_test_bound H u w
  obtain ⟨h₁, h₂, _⟩ := tested b hb B hB hsize d₀ L hLip hZero
  have h₀ := integrable_radianHighPairWeight_of_orderOne b hb B hB hsize H u w
  have expansion (v : SchwartzMap E ℂ) (ξ : E) :
      radianFourier (fun x => (d x : ℂ) * v x) ξ =
        radianFourier (fun x => (d₀ x : ℂ) * v x) ξ + (d 0 : ℂ) * radianFourier v ξ := by
    let f x := radianPhase ξ x * ((d₀ x : ℂ) * v x)
    let g x := radianPhase ξ x * v x
    have hf : Integrable f := (normalizedPhaseProduct_majorant_integrable L v).mono'
      (normalizedPhaseProduct_continuous hLip v ξ).aestronglyMeasurable
      (Eventually.of_forall (normalizedPhaseProduct_bound hLip hZero v ξ))
    have hg : Integrable g := v.integrable.norm.mono'
      (by unfold g radianPhase; fun_prop)
      (Eventually.of_forall fun x => by
        simpa only [g, norm_mul, norm_radianPhase, one_mul] using (le_rfl : ‖v x‖ ≤ ‖v x‖))
    change (∫ x, radianPhase ξ x * ((d x : ℂ) * v x)) =
      (∫ x, f x) + (d 0 : ℂ) * ∫ x, g x
    rw [← integral_const_mul, ← integral_add hf (hg.const_mul _)]
    apply integral_congr_ae
    filter_upwards with x
    simp only [f, g, d₀, Complex.ofReal_sub]
    ring
  have first :
      radianHighPairWeight b H (fun x => (d x : ℂ) * u x) w =
        fun p => radianHighPairWeight b H (fun x => (d₀ x : ℂ) * u x) w p +
          (d 0 : ℂ) * radianHighPairWeight b H u w p := by
    funext p
    simp only [radianHighPairWeight, expansion]
    ring
  have second :
      radianHighPairWeight b H u (fun x => (d x : ℂ) * w x) =
        fun p => radianHighPairWeight b H u (fun x => (d₀ x : ℂ) * w x) p +
          (d 0 : ℂ) * radianHighPairWeight b H u w p := by
    funext p
    simp only [radianHighPairWeight, expansion, map_add, map_mul, Complex.conj_ofReal]
    ring
  simp only [radianHighCommutatorPair, radianHighPair, first, second, integral_add h₁ (h₀.const_mul _),
    integral_add h₂ (h₀.const_mul _), smul_add, add_sub_add_right_eq_sub]
  rfl

end Burnett.A08
