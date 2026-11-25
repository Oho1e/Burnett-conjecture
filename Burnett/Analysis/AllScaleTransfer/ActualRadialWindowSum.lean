import Burnett.Analysis.CubicEnergy.JointMultiplier.JointDyadicWindows

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.A05
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow

open Finset MeasureTheory
open Burnett.A02.FrequencySplit
open scoped ENNReal

/-- An arbitrary finite selection of integer dyadic frequencies can be
realized in the natural-index annular theorem by changing the starting
dilation. The two windows keep their own fixed dilation ratios. -/
private theorem integer_radial_dilations {n : ℕ} (j : Fin n ↪ ℤ) :
    ∃ (base : ℝ) (k : Fin n ↪ ℕ), 0 < base ∧
      ∀ i, (2 : ℝ) ^ (k i) * base = (2 : ℝ) ^ (-j i) := by
  let N : ℕ := ∑ i : Fin n, (j i).natAbs
  have hN (i : Fin n) : j i ≤ (N : ℤ) := by
    have hi : (j i).natAbs ≤ N :=
      Finset.single_le_sum (f := fun l : Fin n => (j l).natAbs) (fun l _ => Nat.zero_le _) (mem_univ i)
    exact Int.le_natAbs.trans (by exact_mod_cast hi)
  let index (i : Fin n) : ℕ := ((N : ℤ) - j i).toNat
  have hIndex (i : Fin n) : (index i : ℤ) = (N : ℤ) - j i :=
    Int.toNat_of_nonneg (sub_nonneg.mpr (hN i))
  have hInj : Function.Injective index := by
    intro i l h
    have eq := congrArg (fun m : ℕ => (m : ℤ)) h
    change (index i : ℤ) = (index l : ℤ) at eq
    rw [hIndex i, hIndex l] at eq
    exact j.injective (by omega)
  let base : ℝ := (2 : ℝ) ^ (-(N : ℤ))
  refine ⟨base, ⟨index, hInj⟩, by dsimp [base]; positivity, ?_⟩
  intro i
  change (2 : ℝ) ^ (index i) * (2 : ℝ) ^ (-(N : ℤ)) = _
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), hIndex]
  congr 2
  omega

private theorem triLpMass_three_finite (f g h : SchwartzMap E ℂ) : triLpMass f g h 3 3 3 < ⊤ := by
  have l3 (k : SchwartzMap E ℂ) :
      eLpNorm (k : E → ℂ) (ENNReal.ofReal 3) (volume : Measure E) < ⊤ := by
    have hm : MemLp (k : E → ℂ) (ENNReal.ofReal 3) (volume : Measure E) :=
      k.memLp (ENNReal.ofReal 3) (volume : Measure E)
    exact hm.2
  unfold triLpMass
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (l3 f) (l3 g)) (l3 h)

/-- The actual separated radial windows obey a uniform cubic sum over an
arbitrary finite selection of integer frequencies, with any two fixed
positive dilation ratios. The third factor is the same scaled Fourier
window throughout, with arbitrary positive scales. In the remainder
application that window is the unmodulated thick output annulus. -/
theorem integer_radial_window_trilinear_bound
    (a b d : SchwartzMap E ℂ) (ha : HasCompactSupport (a : E → ℂ))
    (hb : HasCompactSupport (b : E → ℂ)) (ca : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (cb : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (t u : ℝ), 0 < t → 0 < u → ∀ (q v : E) (n : ℕ) (j : Fin n ↪ ℤ)
      (sc : Fin n → ℝ), (∀ i, 0 < sc i) → ∀ (f g h : SchwartzMap E ℂ),
      let T (i : Fin n) (x : E) :=
        shiftedWindowOperator a f ((2 : ℝ) ^ (-j i) * t) q x *
          shiftedWindowOperator b g ((2 : ℝ) ^ (-j i) * u) v x *
          shiftedWindowOperator d h (sc i) 0 x
      (∀ i, Integrable (T i)) ∧
        ‖∑ i, ∫ x, T i x‖ₑ ≤
          C * ENNReal.ofReal (1 + ‖q‖) * ENNReal.ofReal (1 + ‖v‖) * triLpMass f g h 3 3 3 := by
  let P := ENNReal.ofReal (3 : ℝ)
  let Q := (P⁻¹ + P⁻¹)⁻¹
  letI : ENNReal.HolderTriple P P Q := ENNReal.HolderTriple.of P P
  letI : ENNReal.HolderTriple Q P 1 := ⟨by
    change Q⁻¹ + P⁻¹ = (1 : ℝ≥0∞)⁻¹
    simp only [Q, inv_inv, inv_one, P, ENNReal.ofReal_ofNat]
    have hn : (3 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by norm_num)
    have hs : (3 : ℝ≥0∞)⁻¹ + (3 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hn, hn⟩
    apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr ⟨hs, hn⟩) ENNReal.one_ne_top).mp
    rw [ENNReal.toReal_add hs hn, ENNReal.toReal_add hn hn]
    norm_num⟩
  obtain ⟨C, hC, hBase⟩ := two_annular_one_low a b d ha hb ca cb 3 3 3
    (by norm_num) (by norm_num) (by norm_num) Q
  refine ⟨C, hC, ?_⟩
  intro t u ht hu q v n j sc hsc f g h T
  obtain ⟨base, k, hp, hk⟩ := integer_radial_dilations j
  have hScale (c : ℝ) (i : Fin n) : (2 : ℝ) ^ (k i) * (base * c) = (2 : ℝ) ^ (-j i) * c := by
    rw [← mul_assoc, hk i]
  have hA (i : Fin n) (x : E) : kernelApply (annularKernel a (base * t) q (k i)) f x =
      shiftedWindowOperator a f ((2 : ℝ) ^ (-j i) * t) q x := by
    rw [← hScale t i, shifted_window_physical _ _ _ (mul_pos (by positivity) (mul_pos hp ht))]
    rfl
  have hB (i : Fin n) (x : E) : kernelApply (annularKernel b (base * u) v (k i)) g x =
      shiftedWindowOperator b g ((2 : ℝ) ^ (-j i) * u) v x := by
    rw [← hScale u i, shifted_window_physical _ _ _ (mul_pos (by positivity) (mul_pos hp hu))]
    rfl
  let bound := C * ENNReal.ofReal (1 + ‖q‖) * ENNReal.ofReal (1 + ‖v‖) * triLpMass f g h 3 3 3
  have hSum : (∫⁻ x, ∑ i, ‖T i x‖ₑ) ≤ bound := by
    have H := hBase (base * t) (base * u) (mul_pos hp ht) (mul_pos hp hu) q v 0 n k k sc hsc
      f g h (f.memLp _) (g.memLp _)
    let W (x : E) : ℝ≥0∞ := ENNReal.ofReal (∑ i : Fin n,
      ‖kernelApply (annularKernel a (base * t) q (k i)) f x‖ *
        ‖kernelApply (annularKernel b (base * u) v (k i)) g x‖ *
        ‖shiftedWindowOperator d h (sc i) 0 x‖)
    have hW (x : E) : W x = ∑ i : Fin n, ‖T i x‖ₑ := by
      dsimp only [W]
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      apply Finset.sum_congr rfl
      intro i _
      rw [hA i, hB i]
      simp only [T, enorm_mul, ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
        ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
    have hBound : (∫⁻ x : E, W x) ≤ bound := by
      simpa only [W, bound, triLpMass, norm_zero, add_zero, one_pow, ENNReal.ofReal_one, mul_one,
        mul_assoc] using H
    exact (le_of_eq (lintegral_congr fun x => (hW x).symm)).trans hBound
  have hCont (i : Fin n) : Continuous (T i) :=
    ((shiftedWindow_continuous a f _ (mul_pos (by positivity) ht) q).mul
      (shiftedWindow_continuous b g _ (mul_pos (by positivity) hu) v)).mul
        (shiftedWindow_continuous d h _ (hsc i) 0)
  have hFinite : bound < ⊤ := by
    unfold bound
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top)
      (triLpMass_three_finite f g h)
  have hInt (i : Fin n) : Integrable (T i) := by
    refine ⟨(hCont i).aestronglyMeasurable, ?_⟩
    change (∫⁻ x, ‖T i x‖ₑ) < ⊤
    have hTerm (x : E) : ‖T i x‖ₑ ≤ ∑ l : Fin n, ‖T l x‖ₑ :=
      Finset.single_le_sum (f := fun l : Fin n => ‖T l x‖ₑ) (fun l _ => zero_le _) (mem_univ i)
    have hOne : (∫⁻ x : E, ‖T i x‖ₑ) ≤ (∫⁻ x : E, ∑ l : Fin n, ‖T l x‖ₑ) := lintegral_mono hTerm
    exact (hOne.trans hSum).trans_lt hFinite
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∑ i, ‖∫ x, T i x‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ i, ∫⁻ x, ‖T i x‖ₑ := Finset.sum_le_sum fun i _ => enorm_integral_le_lintegral_enorm (T i)
    _ = ∫⁻ x, ∑ i, ‖T i x‖ₑ :=
      (lintegral_finset_sum _ fun i _ => (hCont i).measurable.enorm).symm
    _ ≤ _ := hSum

end Burnett.A05
