import Burnett.Analysis.Microlocal.AngularCommutator.Infrared

set_option autoImplicit false
set_option maxHeartbeats 4400000

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open Burnett.X02.SobolevTestJet (Space D)
open Burnett.Microlocal.AngularCommutator
open scoped ContDiff ComplexConjugate Topology

/-- The product frequency symbol that appears when the real angular
projection is applied to both entries of a defect test. -/
def projectedPairingSymbol (m a p : BoundedSymbol Space) : BoundedSymbol Space where
  toFun ξ := m ξ * (a ξ * p ξ)
  measurable := m.measurable.mul (a.measurable.mul p.measurable)
  bound := m.bound * (a.bound * p.bound)
  bound_nonneg := mul_nonneg m.bound_nonneg (mul_nonneg a.bound_nonneg p.bound_nonneg)
  norm_le ξ := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (m.norm_le ξ) (mul_le_mul (a.norm_le ξ) (p.norm_le ξ)
      (norm_nonneg _) a.bound_nonneg) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) m.bound_nonneg

private theorem projectedPairingSymbol_action (m a p : BoundedSymbol Space) (v : ComplexL2 Space) :
    fourierMultiplier (projectedPairingSymbol m a p) v =
      fourierMultiplier m (fourierMultiplier a (fourierMultiplier p v)) := by
  apply (fourierL2Equiv (V := Space)).injective
  simp only [fourier_fourierMultiplier]
  apply Lp.ext
  let w := fourierL2Equiv v
  filter_upwards [symbolL2_ae (projectedPairingSymbol m a p) w,
    symbolL2_ae p w, symbolL2_ae a (symbolL2 p w), symbolL2_ae m (symbolL2 a (symbolL2 p w))]
    with x h hp ha hm
  change symbolL2 (projectedPairingSymbol m a p) w x = symbolL2 m (symbolL2 a (symbolL2 p w)) x
  rw [h, hm, ha, hp]
  change m x * (a x * p x) * w x = m x * (a x * (p x * w x))
  rw [mul_assoc (m x), mul_assoc (a x)]

private theorem inner_real_symbol (m : BoundedSymbol Space) (hm : ∀ x, conj (m x) = m x)
    (u v : ComplexL2 Space) : inner ℂ (symbolCLM m u) v = inner ℂ u (symbolCLM m v) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [symbolL2_ae m u, symbolL2_ae m v] with x hu hv
  change inner ℂ (symbolL2 m u x) (v x) = inner ℂ (u x) (symbolL2 m v x)
  rw [hu, hv]
  simp only [RCLike.inner_apply, map_mul, hm]
  ac_rfl

private theorem inner_real_fourier_multiplier (m : BoundedSymbol Space)
    (hm : ∀ x, conj (m x) = m x) (u v : ComplexL2 Space) :
    inner ℂ (fourierMultiplier m u) v = inner ℂ u (fourierMultiplier m v) := by
  rw [← fourierL2Equiv.inner_map_map (fourierMultiplier m u) v,
    ← fourierL2Equiv.inner_map_map u (fourierMultiplier m v),
    fourier_fourierMultiplier, fourier_fourierMultiplier]
  exact inner_real_symbol m hm _ _

private theorem sourceSchwartz_norm_eq_real
    (f : Space → ℝ) (hf : ContDiff ℝ ∞ f) (χ : D)
    (hχ : ∀ x, f x ≠ 0 → (χ : Space → ℝ) x = 1) (hLp : MemLp f 2 volume) :
    ‖(sourceSchwartz hf χ hχ).toLp 2 volume‖ = ‖hLp.toLp f‖ := by
  rw [SchwartzMap.toLp, Lp.norm_toLp, Lp.norm_toLp]
  congr 1
  change eLpNorm (fun x => (f x : ℂ)) 2 volume = eLpNorm f 2 volume
  exact le_antisymm (eLpNorm_mono (fun x => (Complex.norm_real _).le))
    (eLpNorm_mono (fun x => (Complex.norm_real _).ge))

/-- For a compact-base real test the projected pairing is asymptotically
the original pairing with the product homogeneous frequency symbol. Both
infrared cutoffs are the actual bounded changes of the corresponding
symbols on one finite frequency ball. -/
theorem projectedDefectScalarPairing_sub_tendsto_zero
    (m mReg p pReg a χ : BoundedSymbol Space) (R : ℝ)
    (hmR : ∀ x, x ∉ Metric.closedBall (0 : Space) R → mReg x = m x)
    (hpR : ∀ x, x ∉ Metric.closedBall (0 : Space) R → pReg x = p x)
    (hm : ContDiffOn ℝ ∞ (m : Space → ℂ) ({0}ᶜ : Set Space))
    (hdeg : DegreeZero (m : Space → ℂ))
    (hmReal : ∀ x, conj (mReg x) = mReg x) (hχReal : ∀ x, conj (χ x) = χ x)
    (hχ : ContDiff ℝ ∞ (χ : Space → ℂ)) (hχc : HasCompactSupport (χ : Space → ℂ))
    (f g : ℕ → Space → ℝ) (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hg : ∀ n, ContDiff ℝ ∞ (g n))
    (fLp : ∀ n, MemLp (f n) 2 (volume : Measure Space))
    (gLp : ∀ n, MemLp (g n) 2 (volume : Measure Space))
    (χ₀ : D) (hχf : ∀ n x, f n x ≠ 0 → (χ₀ : Space → ℝ) x = 1)
    (hχg : ∀ n x, g n x ≠ 0 → (χ₀ : Space → ℝ) x = 1)
    (Bf Bg : ℝ) (hBf : ∀ n, ‖(fLp n).toLp (f n)‖ ≤ Bf) (hBg : ∀ n, ‖(gLp n).toLp (g n)‖ ≤ Bg)
    (htf : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0))
    (htg : ∀ φ : D, Tendsto (fun n => ∫ x, g n x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    let u := fun n => (sourceSchwartz (hf n) χ₀ (hχf n)).toLp 2 volume
    let v := fun n => (sourceSchwartz (hg n) χ₀ (hχg n)).toLp 2 volume
    Tendsto (fun n =>
      inner ℂ (fourierMultiplier mReg (u n))
        (symbolCLM χ (fourierMultiplier a (fourierMultiplier pReg (v n)))) -
      inner ℂ (u n) (symbolCLM χ (fourierMultiplier (projectedPairingSymbol m a p) (v n))))
      atTop (𝓝 0) := by
  intro u v
  let W n := fourierMultiplier a (fourierMultiplier pReg (v n))
  let V n := symbolCLM χ (u n)
  let S := projectedPairingSymbol mReg a pReg
  let S₀ := projectedPairingSymbol m a p
  let q := symbolDifference S S₀
  have hU (n : ℕ) : ‖u n‖ ≤ Bf := by
    rw [show ‖u n‖ = ‖(fLp n).toLp (f n)‖ from sourceSchwartz_norm_eq_real _ _ _ _ _]
    exact hBf n
  have hV (n : ℕ) : ‖v n‖ ≤ Bg := by
    rw [show ‖v n‖ = ‖(gLp n).toLp (g n)‖ from sourceSchwartz_norm_eq_real _ _ _ _ _]
    exact hBg n
  have hComm : Tendsto (fun n => cutoffCommutator mReg χ (u n)) atTop (𝓝 0) :=
    cutoffCommutator_tendsto_zero_of_infrared_regularization m mReg χ R hmR hm hdeg hχ hχc
      f hf fLp χ₀ hχf Bf hBf htf
  have hq (x : Space) (hx : x ∉ Metric.closedBall (0 : Space) R) : q x = 0 := by
    change mReg x * (a x * pReg x) - m x * (a x * p x) = 0
    rw [hmR _ hx, hpR _ hx, sub_self]
  have hLow : Tendsto (fun n => fourierMultiplier q (v n)) atTop (𝓝 0) :=
    compactFrequency_tendsto_zero_of_localized_weak_zero q R hq g hg gLp χ₀ hχg Bg hBg htg
  have hWN (n : ℕ) : ‖W n‖ ≤ ‖fourierMultiplier a‖ * (‖fourierMultiplier pReg‖ * Bg) :=
    ((fourierMultiplier a).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (((fourierMultiplier pReg).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hV n) (norm_nonneg _))) (norm_nonneg _))
  have hVN (n : ℕ) : ‖V n‖ ≤ ‖symbolCLM χ‖ * Bf :=
    ((symbolCLM χ).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hU n) (norm_nonneg _))
  have hE₁ : Tendsto (fun n => inner ℂ (cutoffCommutator mReg χ (u n)) (W n)) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).2
    refine squeeze_zero (g := fun n => ‖cutoffCommutator mReg χ (u n)‖ *
      (‖fourierMultiplier a‖ * (‖fourierMultiplier pReg‖ * Bg))) (fun n => norm_nonneg _) (fun n => ?_) ?_
    · exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans (mul_le_mul_of_nonneg_left (hWN n) (norm_nonneg _))
    · simpa only [norm_zero, zero_mul] using hComm.norm.mul
        (tendsto_const_nhds (x := ‖fourierMultiplier a‖ * (‖fourierMultiplier pReg‖ * Bg)))
  have hE₂ : Tendsto (fun n => inner ℂ (V n) (fourierMultiplier q (v n))) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).2
    refine squeeze_zero (g := fun n => (‖symbolCLM χ‖ * Bf) * ‖fourierMultiplier q (v n)‖)
      (fun n => norm_nonneg _) (fun n => ?_) ?_
    · exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans (mul_le_mul_of_nonneg_right (hVN n) (norm_nonneg _))
    · simpa only [norm_zero, mul_zero] using
        (tendsto_const_nhds (x := ‖symbolCLM χ‖ * Bf)).mul hLow.norm
  have heq (n : ℕ) :
      inner ℂ (fourierMultiplier mReg (u n)) (symbolCLM χ (W n)) -
        inner ℂ (u n) (symbolCLM χ (fourierMultiplier S₀ (v n))) =
          -inner ℂ (cutoffCommutator mReg χ (u n)) (W n) +
            inner ℂ (V n) (fourierMultiplier q (v n)) := by
    have hS : fourierMultiplier S (v n) = fourierMultiplier mReg (W n) :=
      projectedPairingSymbol_action mReg a pReg (v n)
    rw [← inner_real_symbol χ hχReal _ (W n), ← inner_real_symbol χ hχReal (u n),
      fourierMultiplier_symbolDifference, inner_sub_right, hS,
      ← inner_real_fourier_multiplier mReg hmReal _ (W n)]
    change _ = -inner ℂ (fourierMultiplier mReg (V n) -
      symbolCLM χ (fourierMultiplier mReg (u n))) (W n) + _
    rw [inner_sub_left]
    abel
  have hT := hE₁.neg.add hE₂
  rw [neg_zero, zero_add] at hT
  exact hT.congr (fun n => (heq n).symm)

end Burnett.P01
