import Burnett.Analysis.Microlocal.AngularCommutator.Convergence

/-!
# Infrared regularization of the angular commutator

Bounded changes of the multiplier in a fixed frequency ball preserve
strong convergence of the commutator. Fixed bounded multipliers that
decay uniformly at infinity also act strongly to zero.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.AngularCommutator

open MeasureTheory Set Filter Burnett.Fourier Burnett.Analysis.LocalHminusFourier
open Burnett.X02.SobolevTestJet
open scoped ContDiff ENNReal FourierTransform Topology

/-- The difference of actual bounded frequency symbols, with its uniform bound. -/
def symbolDifference (a b : BoundedSymbol Space) : BoundedSymbol Space where
  toFun x := a x - b x
  measurable := a.measurable.sub b.measurable
  bound := a.bound + b.bound
  bound_nonneg := add_nonneg a.bound_nonneg b.bound_nonneg
  norm_le x := (norm_sub_le _ _).trans (add_le_add (a.norm_le x) (b.norm_le x))

theorem fourierMultiplier_symbolDifference (a b : BoundedSymbol Space) (u : ComplexL2 Space) :
    fourierMultiplier (symbolDifference a b) u = fourierMultiplier a u - fourierMultiplier b u := by
  have heq : symbolL2 (symbolDifference a b) (fourierL2Equiv u) =
      symbolL2 a (fourierL2Equiv u) - symbolL2 b (fourierL2Equiv u) := by
    apply Lp.ext
    filter_upwards [symbolL2_ae (symbolDifference a b) (fourierL2Equiv u),
      symbolL2_ae a (fourierL2Equiv u), symbolL2_ae b (fourierL2Equiv u),
      Lp.coeFn_sub (symbolL2 a (fourierL2Equiv u)) (symbolL2 b (fourierL2Equiv u))]
        with x hd ha hb hs
    rw [hd, hs, Pi.sub_apply, ha, hb]
    exact sub_mul _ _ _
  simp only [fourierMultiplier_apply, heq, map_sub]

theorem cutoffCommutator_symbolDifference (a b χ : BoundedSymbol Space) (u : ComplexL2 Space) :
    cutoffCommutator (symbolDifference a b) χ u =
      cutoffCommutator a χ u - cutoffCommutator b χ u := by
  change fourierMultiplier (symbolDifference a b) (symbolCLM χ u) -
      symbolCLM χ (fourierMultiplier (symbolDifference a b) u) =
        (fourierMultiplier a (symbolCLM χ u) - symbolCLM χ (fourierMultiplier a u)) -
        (fourierMultiplier b (symbolCLM χ u) - symbolCLM χ (fourierMultiplier b u))
  rw [fourierMultiplier_symbolDifference, fourierMultiplier_symbolDifference, map_sub]
  abel

/-- A bounded symbol supported in a fixed finite-frequency ball has strongly
zero action on the same compactly localized, distributionally null sequence. -/
theorem compactFrequency_tendsto_zero_of_localized_weak_zero
    (q : BoundedSymbol Space) (R : ℝ)
    (hq : ∀ x, x ∉ Metric.closedBall (0 : Space) R → q x = 0)
    (f : ℕ → Space → ℝ) (hs : ∀ n, ContDiff ℝ ∞ (f n))
    (hf : ∀ n, MemLp (f n) 2 (volume : Measure Space))
    (χ0 : D) (hχ0 : ∀ n x, f n x ≠ 0 → (χ0 : Space → ℝ) x = 1)
    (B : ℝ) (hB : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (ht : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    Tendsto (fun n => fourierMultiplier q ((sourceSchwartz (hs n) χ0 (hχ0 n)).toLp 2 volume))
      atTop (𝓝 0) := by
  exact fourierMultiplier_schwartz_tendsto_zero q Metric.isClosed_closedBall.measurableSet hq
    (fun n => sourceSchwartz (hs n) χ0 (hχ0 n))
    (low_frequency_energy_tendsto_zero hs hf χ0 hχ0 hB ht R)

private theorem fixedRealWeight_preserves_test_limits
    (w : Space → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (f : ℕ → Space → ℝ)
    (ht : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    ∀ φ : D, Tendsto (fun n => ∫ x, (w x * f n x) * (φ : Space → ℝ) x) atTop (𝓝 0) := by
  intro φ
  let ψ : D := ⟨fun x => w x * (φ : Space → ℝ) x, hw.mul (test_smooth φ), hc.mul_right⟩
  convert ht ψ using 1
  funext n
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by change (w x * f n x) * φ.val x = f n x * (w x * φ.val x); ring)

/-- The compact-frequency action remains strongly zero after any fixed smooth
compactly supported complex spatial multiplier on the same localized sequence. -/
theorem compactFrequency_after_cutoff_tendsto_zero
    (q χ : BoundedSymbol Space) (R : ℝ)
    (hq : ∀ x, x ∉ Metric.closedBall (0 : Space) R → q x = 0)
    (hχ : ContDiff ℝ ∞ (χ : Space → ℂ)) (hcχ : HasCompactSupport (χ : Space → ℂ))
    (f : ℕ → Space → ℝ) (hs : ∀ n, ContDiff ℝ ∞ (f n))
    (hf : ∀ n, MemLp (f n) 2 (volume : Measure Space))
    (χ0 : D) (hχ0 : ∀ n x, f n x ≠ 0 → (χ0 : Space → ℝ) x = 1)
    (B : ℝ) (hB : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (ht : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    Tendsto (fun n => fourierMultiplier q
      (symbolCLM χ ((sourceSchwartz (hs n) χ0 (hχ0 n)).toLp 2 volume))) atTop (𝓝 0) := by
  let u (n : ℕ) := (sourceSchwartz (hs n) χ0 (hχ0 n)).toLp 2 volume
  have hseq (w : Space → ℝ) (hw : ContDiff ℝ ∞ w) (hcw : HasCompactSupport w)
      (hbw : ∀ x, ‖w x‖ ≤ χ.bound) :
      ∃ v : ℕ → ComplexL2 Space,
        (∀ n, v n =ᵐ[volume] fun x => (w x * f n x : ℝ)) ∧
        Tendsto (fun n => fourierMultiplier q (v n)) atTop (𝓝 0) := by
    let fw (n : ℕ) (x : Space) := w x * f n x
    have hsw (n : ℕ) : ContDiff ℝ ∞ (fw n) := hw.mul (hs n)
    have hpoint (n : ℕ) (x : Space) : ‖fw n x‖ ≤ χ.bound * ‖f n x‖ := by
      rw [show fw n x = w x * f n x from rfl, norm_mul]
      exact mul_le_mul_of_nonneg_right (hbw x) (norm_nonneg _)
    have hfw (n : ℕ) : MemLp (fw n) 2 (volume : Measure Space) :=
      (hf n).of_le_mul (hsw n).continuous.aestronglyMeasurable (Eventually.of_forall (hpoint n))
    have hbw' (n : ℕ) : ‖(hfw n).toLp (fw n)‖ ≤ χ.bound * B := by
      have hscaled := (hf n).const_smul χ.bound
      have hle : ‖(hfw n).toLp (fw n)‖ ≤ ‖hscaled.toLp (χ.bound • f n)‖ := by
        apply Lp.norm_le_norm_of_ae_le
        filter_upwards [(hfw n).coeFn_toLp, hscaled.coeFn_toLp] with x hx hy
        rw [hx, hy]
        simpa only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg χ.bound_nonneg] using hpoint n x
      change ‖(hfw n).toLp (fw n)‖ ≤ ‖χ.bound • (hf n).toLp (f n)‖ at hle
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg χ.bound_nonneg] at hle
      exact hle.trans (mul_le_mul_of_nonneg_left (hB n) χ.bound_nonneg)
    have hcut (n : ℕ) (x : Space) (hx : fw n x ≠ 0) : (χ0 : Space → ℝ) x = 1 :=
      hχ0 n x (mul_ne_zero_iff.mp hx).2
    let vw (n : ℕ) := sourceSchwartz (hsw n) χ0 (hcut n)
    refine ⟨fun n => (vw n).toLp 2 volume, ?_, ?_⟩
    · intro n
      exact SchwartzMap.coeFn_toLp (vw n) 2 volume
    · exact compactFrequency_tendsto_zero_of_localized_weak_zero q R hq fw hsw hfw χ0 hcut
        (χ.bound * B) hbw' (fixedRealWeight_preserves_test_limits w hw hcw f ht)
  obtain ⟨uRe, hRe, htRe⟩ := hseq (fun x => (χ x).re)
    (Complex.reCLM.contDiff.comp hχ) (hcχ.comp_left Complex.zero_re)
    (fun x => (Complex.abs_re_le_norm _).trans (χ.norm_le x))
  obtain ⟨uIm, hIm, htIm⟩ := hseq (fun x => (χ x).im)
    (Complex.imCLM.contDiff.comp hχ) (hcχ.comp_left Complex.zero_im)
    (fun x => (Complex.abs_im_le_norm _).trans (χ.norm_le x))
  have heq (n : ℕ) : symbolCLM χ (u n) = uRe n + Complex.I • uIm n := by
    apply Lp.ext
    filter_upwards [symbolL2_ae χ (u n), SchwartzMap.coeFn_toLp
      (sourceSchwartz (hs n) χ0 (hχ0 n)) 2 volume, hRe n, hIm n,
      Lp.coeFn_add (uRe n) (Complex.I • uIm n), Lp.coeFn_smul Complex.I (uIm n)]
      with x hχx hu hr hi hsum hsmul
    change symbolL2 χ (u n) x = _
    rw [hχx, hsum, Pi.add_apply, hsmul, Pi.smul_apply, hr, hi]
    change χ x * (u n) x = _
    rw [show (u n) x = (f n x : ℂ) from hu]
    calc
      χ x * (f n x : ℂ) =
          (((χ x).re : ℂ) + (χ x).im * Complex.I) * (f n x : ℂ) :=
        congrArg (fun z : ℂ => z * (f n x : ℂ)) (Complex.re_add_im (χ x)).symm
      _ = _ := by push_cast; simp only [smul_eq_mul]; ring
  change Tendsto (fun n => fourierMultiplier q (symbolCLM χ (u n))) atTop (𝓝 0)
  simp_rw [heq, map_add, map_smul]
  simpa only [smul_zero, add_zero] using htRe.add (htIm.const_smul Complex.I)

/-- Symbols agreeing outside one fixed ball have the same limiting cutoff
commutator on these localized sequences. This includes fixed infrared changes. -/
theorem cutoffCommutator_tendsto_zero_of_infrared_regularization
    (m mReg χ : BoundedSymbol Space) (R : ℝ)
    (hReg : ∀ x, x ∉ Metric.closedBall (0 : Space) R → mReg x = m x)
    (hsm : ContDiffOn ℝ ∞ (m : Space → ℂ) ({0}ᶜ : Set Space))
    (hh : DegreeZero (m : Space → ℂ))
    (hsχ : ContDiff ℝ ∞ (χ : Space → ℂ)) (hcχ : HasCompactSupport (χ : Space → ℂ))
    (f : ℕ → Space → ℝ) (hs : ∀ n, ContDiff ℝ ∞ (f n))
    (hf : ∀ n, MemLp (f n) 2 (volume : Measure Space))
    (χ0 : D) (hχ0 : ∀ n x, f n x ≠ 0 → (χ0 : Space → ℝ) x = 1)
    (B : ℝ) (hB : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (ht : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    Tendsto (fun n => cutoffCommutator mReg χ ((sourceSchwartz (hs n) χ0 (hχ0 n)).toLp 2 volume))
      atTop (𝓝 0) := by
  let q := symbolDifference mReg m
  let u (n : ℕ) := (sourceSchwartz (hs n) χ0 (hχ0 n)).toLp 2 volume
  have hq (x : Space) (hx : x ∉ Metric.closedBall (0 : Space) R) : q x = 0 :=
    sub_eq_zero.mpr (hReg x hx)
  have hA := compactFrequency_after_cutoff_tendsto_zero q χ R hq hsχ hcχ f hs hf χ0 hχ0 B hB ht
  have hB' := compactFrequency_tendsto_zero_of_localized_weak_zero q R hq f hs hf χ0 hχ0 B hB ht
  have hBχ := ((symbolCLM χ).continuous.tendsto 0).comp hB'
  have hq' : Tendsto (fun n => cutoffCommutator q χ (u n)) atTop (𝓝 0) := by
    change Tendsto (fun n => fourierMultiplier q (symbolCLM χ (u n)) -
      symbolCLM χ (fourierMultiplier q (u n))) atTop (𝓝 0)
    simpa only [sub_zero, map_zero] using hA.sub hBχ
  have hm := cutoffCommutator_tendsto_zero_of_localized_weak_zero m χ hsm hh hsχ hcχ f hs hf χ0 hχ0 B hB ht
  have hsum := hq'.add hm
  rw [zero_add] at hsum
  apply hsum.congr
  intro n
  change cutoffCommutator q χ (u n) + cutoffCommutator m χ (u n) = cutoffCommutator mReg χ (u n)
  rw [show q = symbolDifference mReg m from rfl, cutoffCommutator_symbolDifference, sub_add_cancel]

end Burnett.Microlocal.AngularCommutator

namespace Burnett.Microlocal.AngularCommutator

open MeasureTheory Set Filter Burnett.Fourier Burnett.Analysis.LocalHminusFourier
open Burnett.X02.SobolevTestJet
open scoped ContDiff ENNReal FourierTransform Topology

/-- Fixed bounded Fourier remainders with symbol tending to zero at large
frequency have strongly zero action on the localized weakly null sequence. -/
theorem vanishingFrequency_tendsto_zero_of_localized_weak_zero
    (q : BoundedSymbol Space)
    (hq : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x, x ∉ Metric.closedBall (0 : Space) R → ‖q x‖ ≤ ε)
    (f : ℕ → Space → ℝ) (hs : ∀ n, ContDiff ℝ ∞ (f n))
    (hf : ∀ n, MemLp (f n) 2 (volume : Measure Space))
    (χ0 : D) (hχ0 : ∀ n x, f n x ≠ 0 → (χ0 : Space → ℝ) x = 1)
    (B : ℝ) (hB : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (ht : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    Tendsto (fun n => fourierMultiplier q ((sourceSchwartz (hs n) χ0 (hχ0 n)).toLp 2 volume))
      atTop (𝓝 0) := by
  let u (n : ℕ) := (sourceSchwartz (hs n) χ0 (hχ0 n)).toLp 2 volume
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hBu (n : ℕ) : ‖u n‖ ≤ B := by
    have heq : ‖u n‖ = ‖(hf n).toLp (f n)‖ := by
      simp only [u, SchwartzMap.toLp, Lp.norm_toLp]
      congr 1
      exact eLpNorm_congr_norm_ae (Eventually.of_forall (fun x => Complex.norm_real (f n x)))
    exact heq.le.trans (hB n)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (2 * (B + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδB : δ * B < ε / 2 := by
    have hden : 0 < 2 * (B + 1) := by positivity
    change ε / (2 * (B + 1)) * B < ε / 2
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  obtain ⟨R, hR⟩ := hq δ hδ
  let S := Metric.closedBall (0 : Space) R
  have hS : MeasurableSet S := Metric.isClosed_closedBall.measurableSet
  let qlo : BoundedSymbol Space := {
    toFun := S.indicator (q : Space → ℂ)
    measurable := q.measurable.indicator hS
    bound := q.bound
    bound_nonneg := q.bound_nonneg
    norm_le := fun x => by
      by_cases hx : x ∈ S <;> simp [hx, q.norm_le x, q.bound_nonneg] }
  let qhi : BoundedSymbol Space := {
    toFun := Sᶜ.indicator (q : Space → ℂ)
    measurable := q.measurable.indicator hS.compl
    bound := δ
    bound_nonneg := hδ.le
    norm_le := fun x => by
      by_cases hx : x ∈ S
      · simp [hx, hδ.le]
      · simpa [hx] using hR x hx }
  have hslo (x : Space) (hx : x ∉ S) : qlo x = 0 := indicator_of_notMem hx _
  have hsplit (v : ComplexL2 Space) :
      fourierMultiplier q v = fourierMultiplier qlo v + fourierMultiplier qhi v := by
    have heq : symbolL2 q (fourierL2Equiv v) =
        symbolL2 qlo (fourierL2Equiv v) + symbolL2 qhi (fourierL2Equiv v) := by
      apply Lp.ext
      filter_upwards [symbolL2_ae q (fourierL2Equiv v), symbolL2_ae qlo (fourierL2Equiv v),
        symbolL2_ae qhi (fourierL2Equiv v), Lp.coeFn_add (symbolL2 qlo (fourierL2Equiv v))
          (symbolL2 qhi (fourierL2Equiv v))] with x hq0 hqL hqH ha
      rw [hq0, ha, Pi.add_apply, hqL, hqH]
      change q x * _ = S.indicator (q : Space → ℂ) x * _ + Sᶜ.indicator (q : Space → ℂ) x * _
      by_cases hx : x ∈ S <;> simp [hx]
    simp only [fourierMultiplier_apply, heq, map_add]
  have hlo := compactFrequency_tendsto_zero_of_localized_weak_zero qlo R hslo f hs hf χ0 hχ0 B hB ht
  filter_upwards [(Metric.tendsto_nhds.mp hlo) (ε / 2) (by positivity)] with n hn
  change dist (fourierMultiplier q (u n)) 0 < ε
  have hlow : ‖fourierMultiplier qlo (u n)‖ < ε / 2 := by
    simpa only [dist_zero_right] using hn
  have hhigh : ‖fourierMultiplier qhi (u n)‖ < ε / 2 :=
    ((fourierMultiplier_norm_le qhi (u n)).trans
      (mul_le_mul_of_nonneg_left (hBu n) hδ.le)).trans_lt hδB
  rw [dist_zero_right, hsplit]
  exact (norm_add_le _ _).trans_lt (by linarith)

end Burnett.Microlocal.AngularCommutator
