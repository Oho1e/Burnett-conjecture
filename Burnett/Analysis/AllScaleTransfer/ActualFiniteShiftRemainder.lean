import Burnett.Analysis.AllScaleTransfer.FiniteShiftRemainderBox
import Burnett.Analysis.AllScaleTransfer.SignedGapFixedShiftTransfer
import Burnett.Analysis.AllScaleTransfer.LowPassCorrectionNormalized

set_option autoImplicit false
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.A05.BoxFourier

open Set Metric Burnett.Analysis Burnett.Analysis.CapFourier
open Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal

/-- The cutoff numerator uses the same divided difference as the
large-gap tail. -/
theorem cutoffRemainderNumerator_eq_ratio_remainder (M : LowRatio.Point → ℂ)
    (χ η : ℝ → ℝ) (hχ : χ 0 = 1) (z : LowRatio.Point) :
    cutoffRemainderNumerator M χ η z = η z.2 • (z.2 • LowRatio.remainder M χ z) := by
  have h : M z - χ z.2 • M (z.1,0) = z.2 • LowRatio.remainder M χ z := by
    change M z - χ z.2 • LowRatio.endpoint M z.1 = _
    rw [LowRatio.exact_split M χ hχ z, add_sub_cancel_left]
  exact congrArg (fun w : ℂ => η z.2 • w) h

/-- The signed box uses the original physical ratio for the same A. -/
theorem fixedShiftPhysicalRatio_at_frequencies (A : E ≃L[ℝ] E) (k j : ℤ) (p q : E) :
    fixedShiftPhysicalRatio A k (((2 : ℝ)^(-(j+k))) • p, ((2 : ℝ)^(-j)) • q) =
      ‖A p‖ / ‖A q‖ := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have restore (i : ℤ) (v : E) : (2 : ℝ)^i • ((2 : ℝ)^(-i) • v) = v := by
    rw [smul_smul, ← zpow_add₀ h2, add_neg_cancel, zpow_zero, one_smul]
  have scale (ζ υ : E) : ‖A (((2 : ℝ)^(j+k)) • ζ)‖ / ‖A (((2 : ℝ)^j) • υ)‖ =
      fixedShiftPhysicalRatio A k (ζ,υ) := by
    have hj : 0 < (2 : ℝ)^j := by positivity
    have hjk : 0 < (2 : ℝ)^(j+k) := by positivity
    change _ = (2 : ℝ)^k * (‖A ζ‖ / ‖A υ‖)
    rw [map_smul, map_smul, norm_smul, norm_smul, Real.norm_of_nonneg hj.le,
      Real.norm_of_nonneg hjk.le, zpow_add₀ h2, mul_assoc, mul_div_mul_left _ _ hj.ne', mul_div_assoc]
  rw [← scale, restore, restore]

/-- A single normalized third thick annulus supplies every signed shift.
It is one wherever the original Fourier integrand and symbol are active. -/
theorem exists_finite_shift_remainder_bound_of_profiles (I : Finset ℤ)
    (L U u : ℝ) (hL : 0 < L) (hU : 0 < U) (hu : 0 < u) (hu1 : u < 1) :
    ∃ (d : SchwartzMap E ℂ) (C : ℝ), 0 ≤ C ∧
      ∀ (A : E ≃L[ℝ] E), (∀ p, ‖A p‖ ≤ U * ‖p‖) →
        ∀ (m : Joint → ℂ) (G : ℤ → BoxSpace → ℂ) (Q : ℝ), 0 ≤ Q →
          (∀ k ∈ I, ContDiffOn ℝ 100 (G k) (ball (0 : BoxSpace) 5)) →
          (∀ k ∈ I, ∀ n ≤ 40, ∀ z ∈ ball (0 : BoxSpace) 5,
            ‖iteratedFDeriv ℝ n (G k) z‖ ≤ Q) →
          ∀ (f g h : SchwartzMap E ℂ),
          (∀ p, radianWeight (fun _ => 1) f g h p ≠ 0 → m p ≠ 0 →
            L * ‖p.1‖ ≤ ‖A p.1‖ ∧ L * ‖p.2‖ ≤ ‖A p.2‖ ∧ ‖A p.1‖ / ‖A p.2‖ ≤ u) →
          (∀ k ∈ I, ∀ (j : ℤ) (p : Joint), radianWeight (fun _ => 1) f g h p ≠ 0 →
            integerRadialWindow (j+k) p.1 ≠ 0 → integerRadialWindow j p.2 ≠ 0 →
            G k (joinedInputs ((2 : ℝ)^(-(j+k)) • p.1) ((2 : ℝ)^(-j) • p.2)) = m p) →
          let F (k : ℤ) := radianTrilinearForm (radianSignedGapSymbol m k) f g h
          let mass := (triLpMass f g h 3 3 3).toReal
          (∀ k ∈ I, F k = radianFixedShiftBoxForm d (G k) k f g h ∧ ‖F k‖ ≤ C * Q * mass) ∧
          ‖∑ k ∈ I, F k‖ ≤ (I.card : ℝ) * C * Q * mass := by
  let v : ℝ := (u+1)/2
  have huv : u < v := by dsimp [v]; linarith
  have hv : 0 ≤ v := ((hu.trans huv).le)
  have hv1 : v < 1 := by dsimp [v]; linarith
  let d := lowPassCorrectionThirdProfile L U v hL hU hv1
  obtain ⟨C,hC,box⟩ := exists_radianFixedShift_box_forms_bound 5 (by norm_num) d
  refine ⟨d,C,hC,?_⟩
  intro A hUpper m G Q hQ sG jG f g h hActive matchG F mass
  have eq (k : ℤ) (hk : k ∈ I) : F k = radianFixedShiftBoxForm d (G k) k f g h := by
    apply radianTrilinearForm_signedGap_eq_fixedShiftBoxForm
    intro j p hW hLo hHi
    rw [matchG k hk j p hW hLo hHi]
    by_cases hm : m p = 0
    · simp only [hm, zero_mul]
    · obtain ⟨hp,hq,hRatio⟩ := hActive p hW hm
      have hr : 0 < (2 : ℝ)^j := by positivity
      have hAnn := radialAnnularCutoff_nonzero hr hHi
      have hD : d ((2 : ℝ)^(-j) • (-(p.1+p.2))) = 1 :=
        lowPassCorrectionThirdProfile_at_dyadic A hL hU hv hv1 hUpper hp hq j
          ⟨hAnn.1.le,hAnn.2.le⟩ (hRatio.trans_lt huv)
      rw [hD, mul_one]
  have hBound := box I G Q hQ sG jG f g h
  refine ⟨fun k hk => ⟨eq k hk,?_⟩,?_⟩
  · rw [eq k hk]
    exact hBound.1 k hk
  · rw [Finset.sum_congr rfl eq]
    exact hBound.2

/-- Actual finite transitions on a fixed annular chart. The one-sided
raw numerator is required on all active blocks in its positive window.
Its ratio support has a strict margin inside this window. -/
theorem exists_actual_finite_shift_remainder_bound
    (I : Finset ℤ) (B L U u b : ℝ) (hB : 0 ≤ B) (hL : 0 < L) (hU : 0 < U)
    (hu : 0 < u) (hu1 : u < 1) (hub : u < b)
    {K V : Set FrequencyPair} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (hNonzero : ∀ p ∈ V, p.1 ≠ 0 ∧ p.2 ≠ 0)
    {O : Set LowRatio.Angles} (hO : IsOpen O) (angular : FrequencyPair → LowRatio.Angles)
    (hAngular : ContDiffOn ℝ ∞ angular V) (hMap : MapsTo angular V O)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : E ≃L[ℝ] E), (∀ p, ‖A p‖ ≤ U * ‖p‖) →
        (∀ n ≤ 40, ∀ p ∈ V,
          ‖iteratedFDeriv ℝ n (physicalRadialRatio A.toContinuousLinearMap) p‖ ≤ B) →
        ∀ (M : LowRatio.Point → ℂ) (A₁₀₀ : ℝ), 0 ≤ A₁₀₀ →
          ContDiffOn ℝ 100 M (O ×ˢ Ico 0 b) →
          (∀ n ≤ 100, ∀ z ∈ O ×ˢ Ico 0 b,
            ‖iteratedFDerivWithin ℝ n M (O ×ˢ Ico 0 b) z‖ ≤ A₁₀₀) →
          ∀ (m : Joint → ℂ) (f g h : SchwartzMap E ℂ),
          (∀ p, radianWeight (fun _ => 1) f g h p ≠ 0 → m p ≠ 0 →
            L * ‖p.1‖ ≤ ‖A p.1‖ ∧ L * ‖p.2‖ ≤ ‖A p.2‖ ∧ ‖A p.1‖ / ‖A p.2‖ ≤ u) →
          (∀ k ∈ I, ∀ (j : ℤ) (p : Joint), radianWeight (fun _ => 1) f g h p ≠ 0 →
            integerRadialWindow (j+k) p.1 ≠ 0 → integerRadialWindow j p.2 ≠ 0 →
            let pq : FrequencyPair := (((2 : ℝ)^(-(j+k))) • p.1, ((2 : ℝ)^(-j)) • p.2)
            pq ∈ K ∧ ∀ ρ ∈ Ioo 0 b, ρ = ‖A p.1‖ / ‖A p.2‖ →
              m p = M (angular pq,ρ) - χ ρ • M (angular pq,0)) →
          let F (k : ℤ) := radianTrilinearForm (radianSignedGapSymbol m k) f g h
          let mass := (triLpMass f g h 3 3 3).toReal
          (∀ k ∈ I, ‖F k‖ ≤ C * A₁₀₀ * mass) ∧
          ‖∑ k ∈ I, F k‖ ≤ (I.card : ℝ) * C * A₁₀₀ * mass := by
  obtain ⟨η,Cext,hCext,oneη,zeroη,ext⟩ :=
    exists_finite_shift_remainder_boxes I B hB hK hV hKV hNonzero hO angular hAngular hMap hu hub χ hχ
  obtain ⟨d,Cbox,hCbox,box⟩ := exists_finite_shift_remainder_bound_of_profiles I L U u hL hU hu hu1
  refine ⟨Cbox*Cext,mul_nonneg hCbox hCext,?_⟩
  intro A hUpper bR M A₁₀₀ hA₁₀₀ sM bM m f g h hActive hLiteral F mass
  obtain ⟨G,sG,_,bG,eG⟩ := ext A bR M A₁₀₀ hA₁₀₀ sM bM
  have gMatch (k : ℤ) (hk : k ∈ I) (j : ℤ) (p : Joint) (hW : radianWeight (fun _ => 1) f g h p ≠ 0)
      (hl : integerRadialWindow (j+k) p.1 ≠ 0) (hq : integerRadialWindow j p.2 ≠ 0) :
      G k (joinedInputs ((2 : ℝ)^(-(j+k)) • p.1) ((2 : ℝ)^(-j) • p.2)) = m p := by
    let ζ := (2 : ℝ)^(-(j+k)) • p.1
    let υ := (2 : ℝ)^(-j) • p.2
    let ρ := ‖A p.1‖ / ‖A p.2‖
    have hρ : 0 < ρ := by
      have hn (l : ℤ) (x : E) (hx : integerRadialWindow l x ≠ 0) : 0 < ‖A x‖ := by
        have h0 : x ≠ 0 := fun hz => hx (by rw [hz, integerRadialWindow_zero])
        exact norm_pos_iff.mpr (fun hz => h0 (A.injective (hz.trans A.map_zero.symm)))
      exact div_pos (hn _ _ hl) (hn _ _ hq)
    obtain ⟨hKp,hVal⟩ := hLiteral k hk j p hW hl hq
    change G k (joinedInputs ζ υ) = m p
    rw [eG k ζ υ hKp, fixedShiftPhysicalRatio_at_frequencies A k j p.1 p.2]
    change η ρ • (M (angular (ζ,υ),ρ) - χ ρ • M (angular (ζ,υ),0)) = m p
    by_cases hρb : ρ < b
    · rw [← hVal ρ ⟨hρ,hρb⟩ rfl]
      by_cases hm : m p = 0
      · rw [hm, smul_zero]
      · rw [oneη ρ ⟨hρ.le,(hActive p hW hm).2.2⟩, one_smul]
    · have hm : m p = 0 := by
        by_contra hn
        exact hρb ((hActive p hW hn).2.2.trans_lt hub)
      rw [zeroη ρ (le_of_not_gt hρb), zero_smul, hm]
  have out := box A hUpper m G (Cext * A₁₀₀) (mul_nonneg hCext hA₁₀₀)
    (fun k _ => (sG k).contDiffOn) (fun k hk n hn z _ => bG k hk n hn z) f g h hActive gMatch
  exact ⟨fun k hk => by simpa only [mul_assoc] using (out.1 k hk).2,
    by simpa only [mul_assoc] using out.2⟩

end Burnett.A05.BoxFourier
