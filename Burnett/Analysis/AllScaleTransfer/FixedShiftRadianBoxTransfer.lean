import Burnett.Analysis.AllScaleTransfer.RadianRadialBoxGapBound

set_option autoImplicit false
set_option maxHeartbeats 3600000

noncomputable section

namespace Burnett.A05

open Finset Metric
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier (radianTrilinearForm)
open scoped ContDiff

/-- The literal two-frequency block at low or signed index j+k and reference
index j, with one unchanged third-window profile evaluated at the signed sum. -/
def radianFixedShiftBoxBlock (d : SchwartzMap E ℂ) (G : BoxSpace → ℂ)
    (k j : ℤ) (p : Joint) : ℂ :=
  G (joinedInputs ((2 : ℝ)^(-(j+k)) • p.1) ((2 : ℝ)^(-j) • p.2)) *
    ((integerRadialWindow (j+k) p.1 : ℂ) * (integerRadialWindow j p.2 : ℂ) *
      d ((2 : ℝ)^(-j) • (-(p.1+p.2))))

/-- A fixed signed shift in the actual radian trilinear form. -/
def radianFixedShiftBoxForm (d : SchwartzMap E ℂ) (G : BoxSpace → ℂ) (k : ℤ)
    (f g w : SchwartzMap E ℂ) : ℂ :=
  radianTrilinearForm (fun p => ∑' j : ℤ, radianFixedShiftBoxBlock d G k j p) f g w

theorem radianFixedShiftBoxBlock_eq_boxBlock (d : SchwartzMap E ℂ) (G : BoxSpace → ℂ)
    (k j : ℤ) (p : Joint) :
    radianBoxBlock endpointHighProfile endpointHighProfile d
      ((2 : ℝ)^(-j) * (tau*(2 : ℝ)^(-k))) ((2 : ℝ)^(-j)*tau) ((2 : ℝ)^(-j)*tau) G p =
      radianFixedShiftBoxBlock d G k j p := by
  have hTau : tau ≠ 0 := (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).ne'
  have cancel (r : ℝ) : r * tau * tau⁻¹ = r := by
    rw [mul_assoc, mul_inv_cancel₀ hTau, mul_one]
  have firstScale : ((2 : ℝ)^(-j) * (tau*(2 : ℝ)^(-k))) * tau⁻¹ =
      (2 : ℝ)^(-(j+k)) := by
    rw [neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    calc
      _ = (((2 : ℝ)^(-j)*(2 : ℝ)^(-k))*tau)*tau⁻¹ := by ring
      _ = _ := cancel _
  have firstCoord : ((2 : ℝ)^(-j) * (tau*(2 : ℝ)^(-k))) • (tau⁻¹ • p.1) =
      (2 : ℝ)^(-(j+k)) • p.1 := by rw [smul_smul, firstScale]
  have secondCoord : ((2 : ℝ)^(-j)*tau) • (tau⁻¹ • p.2) = (2 : ℝ)^(-j) • p.2 := by
    rw [smul_smul, cancel]
  have thirdCoord : ((2 : ℝ)^(-j)*tau) • (-((tau⁻¹ • p.1)+(tau⁻¹ • p.2))) =
      (2 : ℝ)^(-j) • (-(p.1+p.2)) := by
    rw [← smul_add, ← smul_neg, smul_smul, cancel]
  unfold radianBoxBlock radianFixedShiftBoxBlock
  dsimp only
  rw [firstCoord, secondCoord, thirdCoord, endpointHighProfile_eq_integerRadialWindow,
    endpointHighProfile_eq_integerRadialWindow]

/-- One bound for every signed shift in a finite set, applied to the
actual radian integrals with the original third window. The per-shift
profile is the original normalized annular-box extension. -/
theorem exists_radianFixedShift_box_forms_bound (P : ℝ) (hP : 4 < P) (d : SchwartzMap E ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Finset ℤ) (G : ℤ → BoxSpace → ℂ) (A : ℝ), 0 ≤ A →
      (∀ k ∈ I, ContDiffOn ℝ 100 (G k) (ball (0 : BoxSpace) P)) →
      (∀ k ∈ I, ∀ n ≤ 40, ∀ z ∈ ball (0 : BoxSpace) P, ‖iteratedFDeriv ℝ n (G k) z‖ ≤ A) →
      ∀ f g w : SchwartzMap E ℂ,
        let M := (triLpMass f g w 3 3 3).toReal
        (∀ k ∈ I, ‖radianFixedShiftBoxForm d (G k) k f g w‖ ≤ C*A*M) ∧
        ‖∑ k ∈ I, radianFixedShiftBoxForm d (G k) k f g w‖ ≤ (I.card : ℝ)*C*A*M := by
  obtain ⟨C, hC, H⟩ := exists_radianRadialBoxGap_bound P hP endpointHighProfile endpointHighProfile d
    endpointHighProfile_properties.2.1 endpointHighProfile_properties.2.1
    endpointHighProfile_properties.2.2 endpointHighProfile_properties.2.2
  refine ⟨C, hC, ?_⟩
  intro I G A hA hSmooth hJet f g w M
  have hTau : 0 < tau := mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos
  have term_bound (k : ℤ) (hk : k ∈ I) : ‖radianFixedShiftBoxForm d (G k) k f g w‖ ≤ C*A*M := by
    let profiles (s : ℕ) : BoxSpace → ℂ := if s = 0 then G k else 0
    have smooth (s : ℕ) : ContDiffOn ℝ 99 (profiles s) (ball (0 : BoxSpace) P) := by
      by_cases hs : s = 0
      · simpa only [profiles, if_pos hs] using (hSmooth k hk).of_le
          (show (99 : WithTop ℕ∞) ≤ 100 by norm_num)
      · simp only [profiles, if_neg hs]
        exact contDiffOn_const
    have jets (s n : ℕ) (hn : n ≤ 40) (z : BoxSpace) (hz : z ∈ ball (0 : BoxSpace) P) :
        ‖iteratedFDeriv ℝ n (profiles s) z‖ ≤ A * radialGapDecay s := by
      by_cases hs : s = 0
      · simpa only [profiles, if_pos hs, hs, radialGapDecay, pow_zero, mul_one] using hJet k hk n hn z hz
      · simp only [profiles, if_neg hs]
        change ‖iteratedFDeriv ℝ n (fun _ : BoxSpace => (0 : ℂ)) z‖ ≤ _
        rw [iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
        exact mul_nonneg hA (by unfold radialGapDecay; positivity)
    have bound := (H profiles A hA smooth jets (fun _ => tau*(2 : ℝ)^(-k)) (fun _ => tau)
      (fun _ => mul_pos hTau (by positivity)) (fun _ => hTau)
      (fun _ j => (2 : ℝ)^(-j)*tau) (fun _ j => mul_pos (by positivity) hTau) f g w).1 0
    simpa only [profiles, if_pos rfl, radialGapDecay, pow_zero, mul_one, M, radianFixedShiftBoxForm,
      radianFixedShiftBoxBlock_eq_boxBlock] using bound
  refine ⟨term_bound, ?_⟩
  calc
    _ ≤ ∑ k ∈ I, C*A*M := norm_sum_le_of_le _ term_bound
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end Burnett.A05
