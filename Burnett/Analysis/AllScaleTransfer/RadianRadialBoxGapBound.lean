import Burnett.Analysis.AllScaleTransfer.RadianBoxRadialSum
import Burnett.Analysis.AllScaleTransfer.EightDimensionalModeSummation

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section

namespace Burnett.A05

open MeasureTheory Metric
open Burnett.A02.FrequencySplit
open Burnett.A03 (spatialLatticeVector spatialLatticeWeight)
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier (radianTrilinearForm)
open scoped ContDiff ENNReal

private theorem joinedInputs_mem_normalized_box (ζ υ : E) (hζ : ‖ζ‖ < 2) (hυ : ‖υ‖ < 2) :
    joinedInputs ζ υ ∈ closedBall (0 : BoxSpace) 4 := by
  have hs : ‖joinedInputs ζ υ‖ ^ 2 = ‖ζ‖ ^ 2 + ‖υ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq ζ, EuclideanSpace.norm_sq_eq υ,
      Fintype.sum_sum_type]
    rfl
  rw [mem_closedBall_zero_iff]
  nlinarith only [hs, sq_nonneg (‖ζ‖ - 2), sq_nonneg (‖υ‖ - 2),
    mul_nonneg (norm_nonneg ζ) (sub_nonneg.mpr hζ.le),
    mul_nonneg (norm_nonneg υ) (sub_nonneg.mpr hυ.le), hζ, hυ,
    sq_nonneg (‖joinedInputs ζ υ‖ - 4)]

private theorem scaled_mode_loss (L : ℝ) (k : FourierMode) :
    1 + ‖L • spatialLatticeVector k‖ ≤ max 1 ‖L‖ * spatialLatticeWeight k ^ 6 := by
  have hw : 1 ≤ spatialLatticeWeight k :=
    le_add_of_nonneg_right (norm_nonneg (spatialLatticeVector k))
  have hPow : spatialLatticeWeight k ≤ spatialLatticeWeight k ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hw (by decide : (1 : ℕ) ≤ 6)
  calc
    _ ≤ max 1 ‖L‖ * spatialLatticeWeight k := by
      unfold spatialLatticeWeight
      rw [norm_smul, mul_add, mul_one]
      exact add_le_add (le_max_left _ _) (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    _ ≤ _ := mul_le_mul_of_nonneg_left hPow (le_trans zero_le_one (le_max_left _ _))

private theorem triLpMass_finite (f g h : SchwartzMap E ℂ) : triLpMass f g h 3 3 3 < ⊤ := by
  have mass (i : SchwartzMap E ℂ) : eLpNorm (i : E → ℂ) (ENNReal.ofReal 3) (volume : Measure E) < ⊤ :=
    (i.memLp (ENNReal.ofReal 3) (volume : Measure E)).2
  unfold triLpMass
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (mass f) (mass g)) (mass h)

/-- On the actual box-profile radial sums the bound per gap has the precise
(2^{-s}) decay. The Fourier integrals retain the third output window.
Summing those same integrals over the admitted gaps is absolutely convergent. -/
theorem exists_radianRadialBoxGap_bound (P : ℝ) (hP : 4 < P)
    (a b d : SchwartzMap E ℂ) (ha : HasCompactSupport (a : E → ℂ))
    (hb : HasCompactSupport (b : E → ℂ)) (ca : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (cb : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℕ → BoxSpace → ℂ) (A : ℝ), 0 ≤ A →
      (∀ s, ContDiffOn ℝ 99 (G s) (ball (0 : BoxSpace) P)) →
      (∀ s n, n ≤ 40 → ∀ z ∈ ball (0 : BoxSpace) P,
        ‖iteratedFDeriv ℝ n (G s) z‖ ≤ A * radialGapDecay s) →
      ∀ (t u : ℕ → ℝ), (∀ s, 0 < t s) → (∀ s, 0 < u s) →
      ∀ (v : ℕ → ℤ → ℝ), (∀ s j, 0 < v s j) → ∀ (f g h : SchwartzMap E ℂ),
      let T (s : ℕ) := radianTrilinearForm
        (fun p => ∑' j : ℤ, radianBoxBlock a b d ((2 : ℝ)^(-j) * t s)
            ((2 : ℝ)^(-j) * u s) (v s j) (G s) p) f g h
      let M := (triLpMass f g h 3 3 3).toReal
      (∀ s, ‖T s‖ ≤ C * A * radialGapDecay s * M) ∧
      ∀ cutoff : ℕ,
        Summable (fun s : {s : ℕ // cutoff ≤ s} => ‖T s.val‖) ∧
        ‖∑' s : {s : ℕ // cutoff ≤ s}, T s.val‖ ≤ C * A * (radialGapDecay cutoff * 2) * M := by
  let α := 1 / (2 * P)
  let L := max 1 ‖α‖
  have hL : 0 ≤ L := le_trans zero_le_one (le_max_left _ _)
  obtain ⟨χ, Cbox, _, _, _, hCbox, hBox⟩ :=
    exists_normalized_gap_box_series 4 P (by norm_num) hP
  obtain ⟨Crad, hCrad, hRad⟩ := integer_radial_mode_full_trilinear_bound a b d ha hb ca cb
  have hK : 0 ≤ modePairSummationConstant := by
    unfold modePairSummationConstant
    exact tsum_nonneg (fun k => by unfold modePairMajorant; positivity)
  let C := Crad.toReal * (L * L) * (Cbox * modePairSummationConstant)
  refine ⟨C, by unfold C; positivity, ?_⟩
  intro G A hA hSmooth hJets t u ht hu v hv f g h T M
  have hMass := triLpMass_finite f g h
  have hT (s : ℕ) : ‖T s‖ ≤ C * A * radialGapDecay s * M := by
    let c (k : FourierModePair) := boxCubeFourierCoefficient P (modeIndex k) (fun z => χ z • G s z)
    obtain ⟨hC, hSeries⟩ := hBox G A hA hSmooth hJets s
    have hC' : ∀ k, ‖c k‖ ≤ (Cbox * A) * radialGapDecay s * modePairDecay k := hC
    obtain ⟨hW,hWsum,_⟩ := weighted_fourier_modes_at_gap c (Cbox*A) (mul_nonneg hCbox hA) s hC'
    have hCoeff : Summable (fun k => ‖c k‖) := by
      apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) _ hW
      intro k
      change ‖c k‖ ≤ ‖c k‖ * modePairLoss k
      exact le_mul_of_one_le_right (norm_nonneg _) (one_le_modePairLoss k)
    let R (k : FourierModePair) (j : ℤ) := radianSeparatedWindowSymbol a b d
      ((2 : ℝ)^(-j) * t s) ((2 : ℝ)^(-j) * u s) (v s j)
      (α • spatialLatticeVector k.1) (α • spatialLatticeVector k.2)
    let Z (k : FourierModePair) := c k * radianTrilinearForm (fun p => ∑' j, R k j p) f g h
    have hSum : HasSum Z (T s) :=
      hasSum_radianTrilinearForm_radial_box_modes P (lt_trans (by norm_num) hP) a b d f g h
        (t s) (u s) (ht s) (v s) ca (G s) c hCoeff
        (fun ζ υ hζ hυ => (hSeries _ (joinedInputs_mem_normalized_box ζ υ (ca _ hζ).2 (cb _ hυ).2)).2)
    let D := Crad.toReal * (L * L) * M
    have hD : 0 ≤ D := by unfold D; positivity
    have hZ (k : FourierModePair) : ‖Z k‖ ≤ D * weightedModeCoefficient c k := by
      let q := α • spatialLatticeVector k.1
      let r := α • spatialLatticeVector k.2
      have hFin : Crad * ENNReal.ofReal (1 + ‖q‖) * ENNReal.ofReal (1 + ‖r‖) * triLpMass f g h 3 3 3 < ⊤ :=
        ENNReal.mul_lt_top
          (ENNReal.mul_lt_top (ENNReal.mul_lt_top hCrad ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top) hMass
      have hR : ‖radianTrilinearForm (fun p => ∑' j, R k j p) f g h‖ ≤
          Crad.toReal * (1 + ‖q‖) * (1 + ‖r‖) * M := by
        have H := ENNReal.toReal_mono hFin.ne (hRad (t s) (u s) (ht s) (hu s) q r (v s) (hv s) f g h)
        simpa only [R, M, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 + ‖q‖),
          ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 + ‖r‖), toReal_enorm] using H
      have hQR : (1 + ‖q‖) * (1 + ‖r‖) ≤ (L * L) * modePairLoss k := by
        refine (mul_le_mul (scaled_mode_loss α k.1) (scaled_mode_loss α k.2)
          (by positivity) (by unfold spatialLatticeWeight; positivity)).trans_eq ?_
        unfold L modePairLoss
        ring
      have hR' : ‖radianTrilinearForm (fun p => ∑' j, R k j p) f g h‖ ≤ D * modePairLoss k := by
        calc
          _ ≤ _ := hR
          _ = Crad.toReal * ((1 + ‖q‖) * (1 + ‖r‖)) * M := by ring
          _ ≤ Crad.toReal * ((L * L) * modePairLoss k) * M :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQR ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
          _ = _ := by unfold D; ring
      change ‖c k * _‖ ≤ _
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left hR' (norm_nonneg _)).trans_eq (by unfold weightedModeCoefficient; ring)
    have hWD : Summable (fun k => D * weightedModeCoefficient c k) := hW.mul_left D
    have hAbs : Summable fun k => ‖Z k‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hZ hWD
    calc
      _ = ‖∑' k, Z k‖ := congrArg norm hSum.tsum_eq.symm
      _ ≤ ∑' k, ‖Z k‖ := norm_tsum_le_tsum_norm hAbs
      _ ≤ ∑' k, D * weightedModeCoefficient c k := hAbs.tsum_le_tsum hZ hWD
      _ = D * ∑' k, weightedModeCoefficient c k := hW.tsum_mul_left D
      _ ≤ D * (Cbox * A * radialGapDecay s * modePairSummationConstant) :=
        mul_le_mul_of_nonneg_left hWsum hD
      _ = _ := by unfold D C; ring
  refine ⟨hT, ?_⟩
  intro cutoff
  let S := {s : ℕ // cutoff ≤ s}
  let B := C * A * M
  have hDecay := hasSum_radialGapDecay cutoff
  have hB := hDecay.mul_left B
  have hLe (s : S) : ‖T s.val‖ ≤ B * radialGapDecay s.val :=
    (hT s.val).trans_eq (by unfold B; ring)
  have hAbs : Summable (fun s : S => ‖T s.val‖) :=
    Summable.of_nonneg_of_le (fun s => norm_nonneg _) hLe hB.summable
  refine ⟨hAbs, ?_⟩
  calc
    _ ≤ ∑' s : S, ‖T s.val‖ := norm_tsum_le_tsum_norm hAbs
    _ ≤ ∑' s : S, B * radialGapDecay s.val := hAbs.tsum_le_tsum hLe hB.summable
    _ = B * (radialGapDecay cutoff * 2) := hB.tsum_eq
    _ = _ := by unfold B; ring

end Burnett.A05
