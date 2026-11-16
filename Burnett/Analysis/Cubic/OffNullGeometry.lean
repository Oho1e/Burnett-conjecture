import Burnett.Analysis.Cubic.FrequencyBounds

/-! Frequency geometry for the fixed off-null localization obligation.
The vectors below are the actual angular-frequency vectors of the same
`fSequence` and `wSequence`; the Fourier convention with `2π` rescales them
by `(2π)⁻¹` when used as Fourier translations. -/

noncomputable section

namespace Burnett.CubicOffNull

open CubicExplicit CubicFrequencies Filter
open scoped Topology RealInnerProductSpace

def minkowskiQ (ξ : Space) : ℝ := -(ξ 0)^2 + (ξ 1)^2 + (ξ 2)^2 + (ξ 3)^2

def offNullRegion (δ : ℝ) : Set Space :=
  {ξ | ξ ≠ 0 ∧ δ * ‖ξ‖^2 ≤ |minkowskiQ ξ|}

def nullU : Space := basis 0 - basis 1
def nullV : Space := basis 0 + basis 1

@[simp] theorem inner_nullU (x : Space) : ⟪nullU, x⟫ = u x := by
  simp [nullU, basis, inner_sub_left, EuclideanSpace.inner_single_left, u]

@[simp] theorem inner_nullV (x : Space) : ⟪nullV, x⟫ = v x := by
  simp [nullV, basis, inner_add_left, EuclideanSpace.inner_single_left, v]

def fAngularFrequency (n : ℕ) (s : ℝ) : Space :=
  (N n)^2 • nullU + (s * N n) • nullV

def wAngularFrequency (n : ℕ) : Space := (2 * N n) • nullV

@[simp] theorem inner_fAngularFrequency (n : ℕ) (s : ℝ) (x : Space) :
    ⟪fAngularFrequency n s, x⟫ = (N n)^2 * u x + s * N n * v x := by
  simp [fAngularFrequency, inner_add_left, real_inner_smul_left]

@[simp] theorem inner_wAngularFrequency (n : ℕ) (x : Space) :
    ⟪wAngularFrequency n, x⟫ = 2 * N n * v x := by
  simp [wAngularFrequency, real_inner_smul_left]

theorem minkowskiQ_fAngularFrequency (n : ℕ) (s : ℝ) :
    minkowskiQ (fAngularFrequency n s) = -4 * s * (N n)^3 := by
  simp [minkowskiQ, fAngularFrequency, nullU, nullV, basis,
    EuclideanSpace.single_apply]
  ring

theorem norm_sq_fAngularFrequency (n : ℕ) (s : ℝ) :
    ‖fAngularFrequency n s‖^2 = 2 * (N n)^4 + 2 * s^2 * (N n)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [fAngularFrequency, nullU, nullV, basis, EuclideanSpace.single_apply,
    Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
  ring

@[simp] theorem minkowskiQ_wAngularFrequency (n : ℕ) :
    minkowskiQ (wAngularFrequency n) = 0 := by
  simp [minkowskiQ, wAngularFrequency, nullV, basis, EuclideanSpace.single_apply]

theorem norm_sq_wAngularFrequency (n : ℕ) :
    ‖wAngularFrequency n‖^2 = 8 * (N n)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [wAngularFrequency, nullV, basis, EuclideanSpace.single_apply,
    Fin.sum_univ_succ, Real.norm_eq_abs, abs_of_pos (N_pos n)]
  ring

theorem minkowskiQ_neg (ξ : Space) : minkowskiQ (-ξ) = minkowskiQ ξ := by
  simp [minkowskiQ]

theorem minkowskiQ_smul (c : ℝ) (ξ : Space) :
    minkowskiQ (c • ξ) = c^2 * minkowskiQ ξ := by
  simp only [minkowskiQ, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The two real cosine phases of every coordinate of the actual f gradient. -/
theorem D_fSequence_two_cosines (n : ℕ) (i : Index) (x : Space) :
    D i (fSequence n) x =
      ((u (basis i) + (N n)⁻¹ * v (basis i)) / 2) *
        Real.cos ⟪fAngularFrequency n 1, x⟫ +
      ((u (basis i) - (N n)⁻¹ * v (basis i)) / 2) *
        Real.cos ⟪fAngularFrequency n (-1), x⟫ := by
  rw [fSequence, D_waveF _ _ (pow_ne_zero _ (N_ne_zero n)), N_ratio]
  simp only [inner_fAngularFrequency, one_mul, Real.cos_add,
    sub_eq_add_neg, neg_mul, Real.cos_neg, Real.sin_neg]
  ring

theorem D_wSequence_cosine (n : ℕ) (i : Index) (x : Space) :
    D i (wSequence n) x = v (basis i) * Real.cos ⟪wAngularFrequency n, x⟫ := by
  rw [wSequence, D_waveW _ (N_ne_zero n), inner_wAngularFrequency]
  ring

theorem abs_coordinate_sq_sub_le (ξ κ : Space) (i : Index) :
    |(ξ i)^2 - (κ i)^2| ≤ ‖ξ - κ‖ * (‖ξ‖ + ‖κ‖) := by
  have hd : |ξ i - κ i| ≤ ‖ξ - κ‖ := by
    simpa only [Real.norm_eq_abs, PiLp.sub_apply] using PiLp.norm_apply_le (ξ - κ) i
  have hs : |ξ i + κ i| ≤ ‖ξ‖ + ‖κ‖ :=
    (abs_add_le _ _).trans (add_le_add (PiLp.norm_apply_le ξ i) (PiLp.norm_apply_le κ i))
  calc
    _ = |ξ i - κ i| * |ξ i + κ i| := by rw [← abs_mul]; congr 1; ring
    _ ≤ _ := mul_le_mul hd hs (abs_nonneg _) (norm_nonneg _)

theorem abs_minkowskiQ_sub_le (ξ κ : Space) :
    |minkowskiQ ξ - minkowskiQ κ| ≤ 4 * ‖ξ - κ‖ * (‖ξ‖ + ‖κ‖) := by
  have he : minkowskiQ ξ - minkowskiQ κ =
      -((ξ 0)^2 - (κ 0)^2) + ((ξ 1)^2 - (κ 1)^2) +
        ((ξ 2)^2 - (κ 2)^2) + ((ξ 3)^2 - (κ 3)^2) := by
    unfold minkowskiQ; ring
  rw [he]
  calc
    _ ≤ |(ξ 0)^2 - (κ 0)^2| + |(ξ 1)^2 - (κ 1)^2| +
        |(ξ 2)^2 - (κ 2)^2| + |(ξ 3)^2 - (κ 3)^2| := by
      have h01 := abs_add_le (-((ξ 0)^2 - (κ 0)^2)) ((ξ 1)^2 - (κ 1)^2)
      have h012 := abs_add_le (-((ξ 0)^2 - (κ 0)^2) + ((ξ 1)^2 - (κ 1)^2))
        ((ξ 2)^2 - (κ 2)^2)
      have h0123 := abs_add_le (-((ξ 0)^2 - (κ 0)^2) + ((ξ 1)^2 - (κ 1)^2) +
        ((ξ 2)^2 - (κ 2)^2)) ((ξ 3)^2 - (κ 3)^2)
      simp only [abs_neg] at h01
      linarith
    _ ≤ _ := by
      linarith [abs_coordinate_sq_sub_le ξ κ 0, abs_coordinate_sq_sub_le ξ κ 1,
        abs_coordinate_sq_sub_le ξ κ 2, abs_coordinate_sq_sub_le ξ κ 3]

def separationConstant (δ : ℝ) : ℝ := min (1/2) (δ/160)

theorem separationConstant_pos {δ : ℝ} (hδ : 0 < δ) : 0 < separationConstant δ :=
  lt_min (by norm_num) (div_pos hδ (by norm_num))

/-- A fixed conic region is uniformly separated from any sufficiently null
frequency. The estimate is global in ξ, including all large Fourier tails. -/
theorem offNull_separation {δ : ℝ} (hδ : 0 < δ) {κ ξ : Space}
    (hκ : κ ≠ 0) (hq : |minkowskiQ κ| ≤ (δ/8) * ‖κ‖^2)
    (hξ : ξ ∈ offNullRegion δ) :
    separationConstant δ * ‖κ‖ ≤ ‖ξ - κ‖ := by
  by_contra! hd
  have hb : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  have hc1 : separationConstant δ ≤ 1/2 := min_le_left _ _
  have hc2 : separationConstant δ ≤ δ/160 := min_le_right _ _
  have hd1 : ‖ξ - κ‖ < ‖κ‖/2 := by nlinarith [mul_le_mul_of_nonneg_right hc1 hb.le]
  have hd2 : ‖ξ - κ‖ < (δ/160) * ‖κ‖ :=
    hd.trans_le (mul_le_mul_of_nonneg_right hc2 hb.le)
  have ha1 : ‖κ‖/2 < ‖ξ‖ := by
    have := norm_sub_norm_le κ ξ
    rw [norm_sub_rev] at this
    linarith
  have ha2 : ‖ξ‖ < 3*‖κ‖/2 := by
    have := norm_sub_norm_le ξ κ
    linarith
  have hlower : δ * ‖κ‖^2/4 < δ * ‖ξ‖^2 := by
    nlinarith [mul_pos hδ (show 0 < ‖ξ‖^2 - (‖κ‖/2)^2 by nlinarith)]
  have hvar := abs_minkowskiQ_sub_le ξ κ
  have hqξ : |minkowskiQ ξ| ≤ |minkowskiQ κ| +
      4 * ‖ξ - κ‖ * (‖ξ‖ + ‖κ‖) := by
    have := abs_add_le (minkowskiQ ξ - minkowskiQ κ) (minkowskiQ κ)
    simp only [sub_add_cancel] at this
    linarith
  have hvar2 : 4 * ‖ξ - κ‖ * (‖ξ‖ + ‖κ‖) ≤ 10 * ‖ξ - κ‖ * ‖κ‖ := by
    nlinarith [mul_nonneg (norm_nonneg (ξ - κ)) (show 0 ≤ 3*‖κ‖/2 - ‖ξ‖ by linarith)]
  have hsmall : 10 * ‖ξ - κ‖ * ‖κ‖ < δ * ‖κ‖^2/16 := by
    nlinarith [mul_pos hb (show 0 < (δ/160) * ‖κ‖ - ‖ξ - κ‖ by linarith)]
  have hpos : 0 < δ * ‖κ‖^2 := mul_pos hδ (sq_pos_of_pos hb)
  have hcone := hξ.2
  linarith

theorem fAngularFrequency_norm_lower (n : ℕ) {s : ℝ} (hs : s^2 = 1) :
    N n ≤ ‖fAngularFrequency n s‖ := by
  have hnorm := norm_sq_fAngularFrequency n s
  rw [hs] at hnorm
  nlinarith [norm_nonneg (fAngularFrequency n s), N_pos n, sq_nonneg ((N n)^2)]

theorem fAngularFrequency_ne_zero (n : ℕ) {s : ℝ} (hs : s^2 = 1) :
    fAngularFrequency n s ≠ 0 := by
  intro hz
  have hb := fAngularFrequency_norm_lower n hs
  rw [hz, norm_zero] at hb
  linarith [N_pos n]

theorem tendsto_norm_fAngularFrequency {s : ℝ} (hs : s^2 = 1) :
    Tendsto (fun n => ‖fAngularFrequency n s‖) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [tendsto_N_atTop.eventually (Ici_mem_atTop b)] with n hn
  exact hn.trans (fAngularFrequency_norm_lower n hs)

theorem fAngularFrequency_eventually_near_null {δ : ℝ} (hδ : 0 < δ)
    {s : ℝ} (hs : s^2 = 1) :
    ∀ᶠ n in atTop, |minkowskiQ (fAngularFrequency n s)| ≤
      (δ/8) * ‖fAngularFrequency n s‖^2 := by
  have habs : |s| = 1 := by nlinarith [sq_abs s, abs_nonneg s]
  filter_upwards [tendsto_N_atTop.eventually (Ici_mem_atTop (16/δ))] with n hn
  rw [minkowskiQ_fAngularFrequency, norm_sq_fAngularFrequency, hs]
  simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), habs,
    mul_one, abs_of_nonneg (pow_nonneg (N_pos n).le 3)]
  have hdN : 16 ≤ δ * N n := by
    have := (div_le_iff₀ hδ).mp hn
    nlinarith
  have hprod := mul_nonneg (pow_nonneg (N_pos n).le 3)
    (show 0 ≤ δ * N n - 16 by linarith)
  nlinarith [mul_nonneg hδ.le (sq_nonneg (N n))]

theorem wAngularFrequency_ne_zero (n : ℕ) : wAngularFrequency n ≠ 0 := by
  intro hz
  have hnorm := norm_sq_wAngularFrequency n
  rw [hz, norm_zero] at hnorm
  nlinarith [N_pos n]

theorem tendsto_norm_wAngularFrequency :
    Tendsto (fun n => ‖wAngularFrequency n‖) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [tendsto_N_atTop.eventually (Ici_mem_atTop b)] with n hn
  have hnorm := norm_sq_wAngularFrequency n
  have hl : N n ≤ ‖wAngularFrequency n‖ := by
    nlinarith [norm_nonneg (wAngularFrequency n), N_pos n]
  exact hn.trans hl

/-- The same relative null estimate survives the normalization `1/(2π)`
and both signs of every real trigonometric mode. -/
theorem near_null_smul {δ c : ℝ} {κ : Space}
    (hq : |minkowskiQ κ| ≤ (δ/8) * ‖κ‖^2) :
    |minkowskiQ (c • κ)| ≤ (δ/8) * ‖c • κ‖^2 := by
  rw [minkowskiQ_smul, abs_mul, abs_of_nonneg (sq_nonneg c), norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  nlinarith [mul_nonneg (sq_nonneg c) (show 0 ≤ (δ/8) * ‖κ‖^2 - |minkowskiQ κ| by linarith)]

end Burnett.CubicOffNull
