import Burnett.Analysis.SpatialFreezing.SpatialLatticeSummability
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
noncomputable section

namespace Burnett.A05

open Burnett.A03

abbrev FourierMode := Fin 4 → ℤ
abbrev FourierModePair := FourierMode × FourierMode

/-- The two integer modes, embedded together in the Euclidean eight-dimensional lattice. -/
def modePairLatticeVector (ab : FourierModePair) : EuclideanSpace ℝ (Fin 4 ⊕ Fin 4) :=
  WithLp.toLp 2 (Sum.elim (fun i => (ab.1 i : ℝ)) (fun i => (ab.2 i : ℝ)))

theorem modePairLatticeVector_norm_sq (ab : FourierModePair) :
    ‖modePairLatticeVector ab‖ ^ 2 =
      ‖spatialLatticeVector ab.1‖ ^ 2 + ‖spatialLatticeVector ab.2‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq (spatialLatticeVector ab.1),
    EuclideanSpace.norm_sq_eq (spatialLatticeVector ab.2), Fintype.sum_sum_type]
  rfl

/-- The coefficient envelope from the normalized eight-dimensional box. -/
def modePairDecay (ab : FourierModePair) : ℝ :=
  1 / (1 + ‖spatialLatticeVector ab.1‖ + ‖spatialLatticeVector ab.2‖) ^ 40

/-- The separate losses of the two translated annular multiplier families. -/
def modePairLoss (ab : FourierModePair) : ℝ :=
  spatialLatticeWeight ab.1 ^ 6 * spatialLatticeWeight ab.2 ^ 6

/-- The Euclidean lattice majorant after charging both multiplier losses. -/
def modePairMajorant (ab : FourierModePair) : ℝ :=
  1 / (1 + ‖modePairLatticeVector ab‖) ^ 28

private theorem modePairMajorant_nonneg (ab : FourierModePair) : 0 ≤ modePairMajorant ab := by
  unfold modePairMajorant
  positivity

private theorem modePairLoss_nonneg (ab : FourierModePair) : 0 ≤ modePairLoss ab := by
  unfold modePairLoss spatialLatticeWeight
  positivity

theorem modePairDecay_mul_loss_le (ab : FourierModePair) :
    modePairDecay ab * modePairLoss ab ≤ modePairMajorant ab := by
  let x := ‖spatialLatticeVector ab.1‖
  let y := ‖spatialLatticeVector ab.2‖
  let t := 1 + x + y
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have ht : 0 < t := by dsimp [t]; positivity
  have left : 1 + x ≤ t := le_add_of_nonneg_right hy
  have right : 1 + y ≤ t := by dsimp [t]; linarith only [hx]
  have hloss : (1 + x) ^ 6 * (1 + y) ^ 6 ≤ t ^ 12 := by
    rw [show (12 : ℕ) = 6 + 6 by decide, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) left _)
      (pow_le_pow_left₀ (by positivity) right _) (by positivity) (by positivity)
  have hxy : ‖modePairLatticeVector ab‖ ≤ x + y := by
    apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg hx hy)).mp
    rw [modePairLatticeVector_norm_sq]
    change x ^ 2 + y ^ 2 ≤ (x + y) ^ 2
    nlinarith only [mul_nonneg hx hy]
  have hpair : 1 + ‖modePairLatticeVector ab‖ ≤ t := by
    dsimp only [t]
    linarith only [hxy]
  change 1 / t ^ 40 * ((1 + x) ^ 6 * (1 + y) ^ 6) ≤ modePairMajorant ab
  calc
    _ ≤ t ^ 12 / t ^ 40 := by
      rw [div_eq_mul_inv, one_mul, div_eq_mul_inv, mul_comm (t ^ 40)⁻¹]
      exact mul_le_mul_of_nonneg_right hloss (by positivity)
    _ = 1 / t ^ 28 := by
      rw [show (40 : ℕ) = 12 + 28 by decide, pow_add, div_mul_eq_div_div,
        div_self (pow_ne_zero _ ht.ne')]
    _ ≤ modePairMajorant ab := by
      unfold modePairMajorant
      exact one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_left₀ (by positivity) hpair _)

theorem summable_modePairMajorant : Summable modePairMajorant := by
  let decay (a : FourierMode) : ℝ := 1 / spatialLatticeWeight a ^ 14
  have hdecay : Summable decay := by
    simpa only [decay, pow_zero] using
      summable_spatial_lattice_weighted_decay 14 0 (by decide) (by decide)
  have hn (a : FourierMode) : 0 ≤ decay a := by
    unfold decay spatialLatticeWeight
    positivity
  refine Summable.of_nonneg_of_le modePairMajorant_nonneg ?_ (hdecay.mul_of_nonneg hdecay hn hn)
  intro ab
  have left : ‖spatialLatticeVector ab.1‖ ≤ ‖modePairLatticeVector ab‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [modePairLatticeVector_norm_sq]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have right : ‖spatialLatticeVector ab.2‖ ≤ ‖modePairLatticeVector ab‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [modePairLatticeVector_norm_sq]
    exact le_add_of_nonneg_left (sq_nonneg _)
  let t := 1 + ‖modePairLatticeVector ab‖
  change 1 / t ^ 28 ≤ (1 / spatialLatticeWeight ab.1 ^ 14) * (1 / spatialLatticeWeight ab.2 ^ 14)
  rw [← mul_div_mul_comm, one_mul, show (28 : ℕ) = 14 + 14 by decide, pow_add]
  apply one_div_le_one_div_of_le (by unfold spatialLatticeWeight; positivity)
  have hl : spatialLatticeWeight ab.1 ≤ t := add_le_add_left left 1
  have hr : spatialLatticeWeight ab.2 ≤ t := add_le_add_left right 1
  exact mul_le_mul (pow_le_pow_left₀ (by unfold spatialLatticeWeight; positivity) hl _)
    (pow_le_pow_left₀ (by unfold spatialLatticeWeight; positivity) hr _)
    (by unfold spatialLatticeWeight; positivity) (by dsimp [t]; positivity)

/-- A fixed constant of the integer lattice, shared by all coefficient families and cutoffs. -/
def modePairSummationConstant : ℝ := ∑' ab, modePairMajorant ab

/-- The exact gap factor \(2^{-s}\). -/
def radialGapDecay (s : ℕ) : ℝ := (1 / 2 : ℝ) ^ s

/-- The absolute contribution of a coefficient once both multiplier bounds are applied. -/
def weightedModeCoefficient (c : FourierModePair → ℂ) (ab : FourierModePair) : ℝ :=
  ‖c ab‖ * modePairLoss ab

private theorem weightedModeCoefficient_nonneg (c : FourierModePair → ℂ) (ab : FourierModePair) :
    0 ≤ weightedModeCoefficient c ab :=
  mul_nonneg (norm_nonneg _) (modePairLoss_nonneg _)

private theorem weightedModeCoefficient_le {c : FourierModePair → ℂ} {A : ℝ} (hA : 0 ≤ A)
    {s : ℕ} {ab : FourierModePair} (h : ‖c ab‖ ≤ A * radialGapDecay s * modePairDecay ab) :
    weightedModeCoefficient c ab ≤ A * radialGapDecay s * modePairMajorant ab := by
  calc
    _ ≤ (A * radialGapDecay s * modePairDecay ab) * modePairLoss ab :=
      mul_le_mul_of_nonneg_right h (modePairLoss_nonneg _)
    _ = (A * radialGapDecay s) * (modePairDecay ab * modePairLoss ab) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (modePairDecay_mul_loss_le _) (by unfold radialGapDecay; positivity)

/-- At each gap, absolute and all finitely truncated mode sums use the same lattice constant.
The nonnegative coefficient scale can be instantiated with \(C\mathfrak A_{100}\). -/
theorem weighted_fourier_modes_at_gap (c : FourierModePair → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (s : ℕ) (hc : ∀ ab, ‖c ab‖ ≤ A * radialGapDecay s * modePairDecay ab) :
    Summable (weightedModeCoefficient c) ∧
      (∑' ab, weightedModeCoefficient c ab) ≤ A * radialGapDecay s * modePairSummationConstant ∧
      ∀ modes : Finset FourierModePair,
        ∑ ab ∈ modes, weightedModeCoefficient c ab ≤ A * radialGapDecay s * modePairSummationConstant := by
  have hm := summable_modePairMajorant.mul_left (A * radialGapDecay s)
  have hle ab := weightedModeCoefficient_le hA (hc ab)
  have hs := Summable.of_nonneg_of_le (weightedModeCoefficient_nonneg c) hle hm
  have hsum := hs.tsum_le_tsum hle hm
  rw [summable_modePairMajorant.tsum_mul_left] at hsum
  exact ⟨hs, hsum, fun modes => (hs.sum_le_tsum modes (fun ab _ => weightedModeCoefficient_nonneg c ab)).trans hsum⟩

private def radialGapEquiv (cutoff : ℕ) : ℕ ≃ {s : ℕ // cutoff ≤ s} where
  toFun n := ⟨cutoff + n, Nat.le_add_right cutoff n⟩
  invFun s := s.1 - cutoff
  left_inv n := by simp
  right_inv s := Subtype.ext (Nat.add_sub_of_le s.2)

/-- The sum is over the actual integer tail, including the first admitted gap. -/
theorem hasSum_radialGapDecay (cutoff : ℕ) :
    HasSum (fun s : {s : ℕ // cutoff ≤ s} => radialGapDecay s.1) (radialGapDecay cutoff * 2) := by
  apply (radialGapEquiv cutoff).hasSum_iff.mp
  change HasSum (fun n : ℕ => radialGapDecay (cutoff + n)) (radialGapDecay cutoff * 2)
  simpa only [radialGapDecay, pow_add] using hasSum_geometric_two.mul_left (radialGapDecay cutoff)

/-- A nonnegative bound for the gap contributions, with the same constant for finite and
absolute sums. Apply this to the norms of the already constructed gap trilinear forms. -/
theorem radial_gap_sum_bound (cutoff : ℕ) (v : {s : ℕ // cutoff ≤ s} → ℝ)
    (hv : ∀ s, 0 ≤ v s) (B : ℝ) (hle : ∀ s, v s ≤ B * radialGapDecay s.1) :
    Summable v ∧
      (∑' s, v s) ≤ B * (radialGapDecay cutoff * 2) ∧
      ∀ gaps : Finset {s : ℕ // cutoff ≤ s},
        ∑ s ∈ gaps, v s ≤ B * (radialGapDecay cutoff * 2) := by
  have hm := (hasSum_radialGapDecay cutoff).mul_left B
  have hs := Summable.of_nonneg_of_le hv hle hm.summable
  have hsum := (hs.tsum_le_tsum hle hm.summable).trans_eq hm.tsum_eq
  exact ⟨hs, hsum, fun gaps => (hs.sum_le_tsum gaps (fun s _ => hv s)).trans hsum⟩

/-- The whole mode-and-gap family is absolutely summable with one constant, also for finite
subsets that are not products. The cutoff-dependent factor is bounded above by two. -/
theorem weighted_fourier_modes_over_radial_gaps (cutoff : ℕ) (c : ℕ → FourierModePair → ℂ)
    (A : ℝ) (hA : 0 ≤ A)
    (hc : ∀ s, cutoff ≤ s → ∀ ab, ‖c s ab‖ ≤ A * radialGapDecay s * modePairDecay ab) :
    let term := fun p : {s : ℕ // cutoff ≤ s} × FourierModePair => weightedModeCoefficient (c p.1.1) p.2
    Summable term ∧
      (∑' p, term p) ≤ A * (radialGapDecay cutoff * 2) * modePairSummationConstant ∧
      ∀ truncation : Finset ({s : ℕ // cutoff ≤ s} × FourierModePair),
        ∑ p ∈ truncation, term p ≤ A * (radialGapDecay cutoff * 2) * modePairSummationConstant := by
  let term := fun p : {s : ℕ // cutoff ≤ s} × FourierModePair => weightedModeCoefficient (c p.1.1) p.2
  have hg := (hasSum_radialGapDecay cutoff).mul_left A
  have hm : Summable (fun p : {s : ℕ // cutoff ≤ s} × FourierModePair =>
      (A * radialGapDecay p.1.1) * modePairMajorant p.2) :=
    hg.summable.mul_of_nonneg summable_modePairMajorant
      (by intro s; unfold radialGapDecay; positivity) modePairMajorant_nonneg
  have hle (p : {s : ℕ // cutoff ≤ s} × FourierModePair) :
      term p ≤ (A * radialGapDecay p.1.1) * modePairMajorant p.2 :=
    weightedModeCoefficient_le hA (hc p.1.1 p.1.2 p.2)
  have hnonneg (p : {s : ℕ // cutoff ≤ s} × FourierModePair) : 0 ≤ term p :=
    weightedModeCoefficient_nonneg _ _
  have hs := Summable.of_nonneg_of_le hnonneg hle hm
  have hsum := hs.tsum_le_tsum hle hm
  rw [hm.tsum_prod' (fun s => summable_modePairMajorant.mul_left (A * radialGapDecay s.1))] at hsum
  simp_rw [summable_modePairMajorant.tsum_mul_left] at hsum
  change (∑' p, term p) ≤ ∑' s : {s : ℕ // cutoff ≤ s}, A * radialGapDecay s.1 * modePairSummationConstant at hsum
  rw [(hg.mul_right modePairSummationConstant).tsum_eq] at hsum
  exact ⟨hs, hsum, fun truncation => (hs.sum_le_tsum truncation (fun p _ => hnonneg p)).trans hsum⟩

theorem radialGapDecay_tail_le_two (cutoff : ℕ) : radialGapDecay cutoff * 2 ≤ 2 := by
  unfold radialGapDecay
  have hh : (1 / 2 : ℝ) ^ cutoff ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  linarith only [hh]

end Burnett.A05
