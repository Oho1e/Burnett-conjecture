import Burnett.Analysis.AllScaleTransfer.CapCorrectionTrace
import Burnett.Analysis.AllScaleTransfer.CapCorrectionRatio
import Burnett.Analysis.AllScaleTransfer.LowPassCorrectionBound

set_option autoImplicit false
set_option maxHeartbeats 6800000
noncomputable section

namespace Burnett.A05

open Filter MeasureTheory Set Metric
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis CapFourier ProjectiveNullCaps
open scoped ContDiff Topology

private theorem capCorrectionBlock_mask (χ : ℝ → ℝ) (A : E ≃L[ℝ] E) (gap : ℕ) (M₀ : Joint → ℂ)
    (α : ℝ) (j : ℤ) (p : Joint) :
    radianLowPassCorrectionBlock χ A gap (axialLocalizeEndpoint α M₀) j p =
      (axialCapPairWindow α p : ℂ) * radianLowPassCorrectionBlock χ A gap M₀ j p := by
  have e : radianEndpointAngular (axialLocalizeEndpoint α M₀) p.1 p.2 =
      (axialCapPairWindow α p : ℂ) * radianEndpointAngular M₀ p.1 p.2 :=
    axialLocalizeEndpoint_eval α M₀ p
  simp only [radianLowPassCorrectionBlock,e,mul_assoc]

/-- The localized angular trace puts the one common two-slot mask outside
the full actual correction sum. -/
theorem capCorrection_multiply_window (χ : ℝ → ℝ) (A : E ≃L[ℝ] E) (gap : ℕ) (M₀ : Joint → ℂ)
    (α : ℝ) (p : Joint) :
    (∑' j, radianLowPassCorrectionBlock χ A gap (axialLocalizeEndpoint α M₀) j p) =
      (axialCapPairWindow α p : ℂ) * ∑' j, radianLowPassCorrectionBlock χ A gap M₀ j p := by
  obtain ⟨I,_,hz⟩ := exists_integerRadialWindow_support_card_le_three p.2
  have zero (N : Joint → ℂ) (j : ℤ) (hj : j ∉ I) : radianLowPassCorrectionBlock χ A gap N j p = 0 := by
    simp only [radianLowPassCorrectionBlock,hz j hj,Complex.ofReal_zero,zero_mul,mul_zero]
  rw [tsum_eq_sum (s := I) (zero (axialLocalizeEndpoint α M₀)),tsum_eq_sum (s := I) (zero M₀),
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => capCorrectionBlock_mask χ A gap M₀ α j p)

private theorem capCorrection_off_axes_ae :
    ∀ᵐ p : Joint ∂(volume : Measure Joint), p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  let μ : Measure E := volume
  have h : ∀ᵐ x : E ∂μ, x ≠ 0 := (Set.countable_singleton (0 : E)).ae_notMem μ
  rw [Measure.volume_eq_prod E E]
  exact Filter.Eventually.and ((Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae h)
    ((Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae h)

/-- On the actual input spectra the correction with the masked endpoint is
the original correction. Both input spectra use the same axial margin. -/
theorem radianCapCorrection_localization_eq (χ : ℝ → ℝ) (A : E ≃L[ℝ] E) (gap : ℕ) (M₀ : Joint → ℂ)
    {α : ℝ} (hα : 0 < α) (f g w : SchwartzMap E ℂ)
    (hf : ∀ p, radianFourier f p ≠ 0 → α*‖p‖ ≤ |p 0|)
    (hg : ∀ q, radianFourier g q ≠ 0 → α*‖q‖ ≤ |q 0|) :
    radianTrilinearForm (fun p => ∑' j, radianLowPassCorrectionBlock χ A gap (axialLocalizeEndpoint α M₀) j p)
      f g w = radianTrilinearForm (fun p => ∑' j, radianLowPassCorrectionBlock χ A gap M₀ j p) f g w := by
  unfold radianTrilinearForm
  congr 1
  apply integral_congr_ae
  filter_upwards [capCorrection_off_axes_ae] with p hp
  by_cases h₁ : radianFourier f p.1 = 0
  · simp only [radianTrilinearWeight,radianWeight,h₁,mul_zero,zero_mul]
  by_cases h₂ : radianFourier g p.2 = 0
  · simp only [radianTrilinearWeight,radianWeight,h₂,mul_zero,zero_mul]
  simp only [radianTrilinearWeight,capCorrection_multiply_window χ A gap M₀ α p,axialCapPairWindow,
    axialCapWindow_eq_one hα hp.1 (hf p.1 h₁),axialCapWindow_eq_one hα hp.2 (hg p.2 h₂),
    mul_one,Complex.ofReal_one,one_mul]

/-- The same actual cap scale, fixed axial window and four signed one-sided
charts bound the original finite-offset low-pass correction. -/
theorem exists_actual_cap_radianLowPassCorrection_bound {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (B tube outer enlarged α r R b l u : ℝ)
    (hB : 0 < B) (hTube : 0 < tube) (hOut : 0 ≤ outer) (hOE : outer < enlarged)
    (hα : 0 < α) (hrR : r < R) (hb : 0 < b)
    (tail : ∀ x ∈ sphere (0 : E) 1, α/2 ≤ |x 0| → ‖endpointTail x‖ ≤ r)
    (hl : 0 < l) (hu : 0 ≤ u) (hu1 : u < 1)
    (hOne : ∀ t, 0 ≤ t → t ≤ l → χ t = 1) (hZero : ∀ t, u ≤ t → χ t = 0) :
    ∃ (gap : ℕ) (C : ℝ), 3 ≤ gap ∧ 0 ≤ C ∧
      ∀ (m : Form) (v : Vec) (F : NullCapChart m v),
        ‖v‖ = 1 → ‖F.toFrequency.toContinuousLinearMap‖ ≤ B →
        ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
        ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → 4*B*(5*δ) ≤ 1 →
        ∀ (M : E → E → ℝ → ℂ) (A₁₀₀ : ℝ), 0 ≤ A₁₀₀ →
          (∀ s : CapSigns, ContDiffOn ℝ 100 (signedEndpointProfile M s)
            (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b)) →
          (∀ (s : CapSigns) n, n ≤ 100 → ∀ z ∈ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b,
            ‖iteratedFDerivWithin ℝ n (signedEndpointProfile M s)
              (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) z‖ ≤ A₁₀₀) →
          ∀ f g h : SchwartzMap E ℂ,
            let A := capFrequencyEquiv F hδ.ne'
            let localized (p : Joint) := ∑' j, radianLowPassCorrectionBlock χ A gap (capCorrectionTrace α M) j p
            let original (p : Joint) := ∑' j, radianLowPassCorrectionBlock χ A gap (fun uv => M uv.1 uv.2 0) j p
            let P := tsupport (enlargedCapMultiplier m δ (tube*δ^2) outer enlarged v)
            ‖radianTrilinearForm localized f g h‖ ≤ C * A₁₀₀ * (triLpMass f g h 3 3 3).toReal ∧
            ((∀ p : E, A p ∈ P → α*‖p‖ ≤ |p 0|) →
              (∀ p, radianFourier f p ≠ 0 → A p ∈ P) →
              (∀ q, radianFourier g q ≠ 0 → A q ∈ P) →
              radianTrilinearForm localized f g h = radianTrilinearForm original f g h ∧
                ‖radianTrilinearForm original f g h‖ ≤ C * A₁₀₀ * (triLpMass f g h 3 3 3).toReal) := by
  let L := (α/2)/B
  let U := B * (‖frequencyCoordinates.toContinuousLinearMap‖+1)
  have hL : 0 < L := div_pos (half_pos hα) hB
  have hU : 0 < U := mul_pos hB (by positivity)
  obtain ⟨gap,H,C₀,hgap,_,hC₀,box⟩ := exists_radianLowPassCorrection_bound
    5 L U l u (by norm_num) hL hU hl hu hu1 hOne hZero
  let I := lowPassCorrectionShifts gap H
  let V := capCorrectionDomain α R
  have hV := capCorrectionDomain_open α R
  obtain ⟨β,hβ,compactβ,βV,oneβ⟩ := exists_capCorrection_domain_cutoff α r R hα hrR tail
  obtain ⟨D,hD,bβ⟩ := exists_compact_contDiffOn_jet_bound compactβ isOpen_univ (subset_univ _) hβ.contDiffOn 40
  obtain ⟨X,hX,trace⟩ := exists_capCorrection_trace_budget α R b hα hb compactβ βV
  obtain ⟨J,hJ,ratio⟩ := exists_capCorrection_ratio_budget B tube outer enlarged α R hB hTube hOut hOE hα
    χ hχ gap I compactβ βV
  let C₁ := (2 : ℝ)^40*X*J
  let C₂ := (2 : ℝ)^40*D*C₁
  have hC₁ : 0 ≤ C₁ := by unfold C₁; positivity
  have hC₂ : 0 ≤ C₂ := by unfold C₂; positivity
  refine ⟨gap,C₀*C₂,hgap,mul_nonneg hC₀ hC₂,?_⟩
  intro m v F hv hF hInv δ hδ hδone hSmall M Ajet hAjet hM jets f g h A localForm origForm P
  let M₀ := capCorrectionTrace α M
  obtain ⟨sE,bE⟩ := trace M Ajet hAjet hM jets
  have fromRatio := ratio m v F hv hF hInv δ hδ hδone hSmall
  have upper (p : E) : ‖A p‖ ≤ U*‖p‖ :=
    (A.toContinuousLinearMap.le_opNorm p).trans
      (mul_le_mul_of_nonneg_right ((capFrequencyEquiv_opNorm_le F hδ hδone hB.le hF).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hB.le)) (norm_nonneg p))
  have maskedAt (p : Joint) : radianEndpointAngular M₀ p.1 p.2 =
      (axialCapPairWindow α p : ℂ) * radianEndpointAngular (fun uv => M uv.1 uv.2 0) p.1 p.2 :=
    axialLocalizeEndpoint_eval α (fun uv => M uv.1 uv.2 0) p
  have inputLower (j : ℤ) (p : Joint) (hn : radianLowPassCorrectionBlock χ A gap M₀ j p ≠ 0) :
      L*‖p.1‖ ≤ ‖A p.1‖ ∧ L*‖p.2‖ ≤ ‖A p.2‖ := by
    have nz : axialCapPairWindow α p ≠ 0 := by
      intro hz
      exact hn (by simp only [radianLowPassCorrectionBlock,maskedAt p,hz,Complex.ofReal_zero,zero_mul])
    have lower (q : E) (hq : axialCapWindow α q ≠ 0) : L*‖q‖ ≤ ‖A q‖ := by
      apply capFrequencyEquiv_lower_on_axial_cone F hδ.ne' hB hInv
      rw [frequencyCoordinates_axis]
      exact (axialCapWindow_nonzero_cone hα hq).2.le
    exact ⟨lower p.1 (left_ne_zero_of_mul nz),lower p.2 (right_ne_zero_of_mul nz)⟩
  let raw (k : ℤ) := normalizedLowPassCorrection χ A gap M₀ k
  have smoothRaw (k : ℤ) (hk : k ∈ I) : ContDiffOn ℝ 100 (raw k) V :=
    sE.mul ((fromRatio k hk).1.of_le (WithTop.coe_le_coe.mpr le_top))
  have rawJets (k : ℤ) (hk : k ∈ I) (n : ℕ) (hn : n ≤ 40) (z : BoxSpace) (hz : z ∈ tsupport β) :
      ‖iteratedFDeriv ℝ n (raw k) z‖ ≤ C₁*Ajet := by
    have zv := βV hz
    have hn' : (n : WithTop ℕ∞) ≤ 100 := by exact_mod_cast (show n ≤ 100 by omega)
    rw [← iteratedFDerivWithin_of_isOpen n hV zv]
    refine (norm_iteratedFDerivWithin_mul_le sE
      ((fromRatio k hk).1.of_le (WithTop.coe_le_coe.mpr le_top)) hV.uniqueDiffOn zv hn').trans ?_
    calc
      _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*(X*Ajet)*J := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := (Finset.mem_range.mp hj)
        rw [iteratedFDerivWithin_of_isOpen j hV zv,iteratedFDerivWithin_of_isOpen (n-j) hV zv]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (bE j (by omega) z hz) (by positivity))
          ((fromRatio k hk).2 (n-j) ((Nat.sub_le _ _).trans hn) z hz) (norm_nonneg _) (by positivity)
      _ = (2 : ℝ)^n*(X*Ajet)*J := by
        rw [← Finset.sum_mul,← Finset.sum_mul]
        norm_cast
        rw [Nat.sum_range_choose]
      _ ≤ (2 : ℝ)^40*(X*Ajet)*J := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) (mul_nonneg hX hAjet)) hJ
      _ = C₁*Ajet := by unfold C₁; ring
  let G (k : ℤ) (z : BoxSpace) := β z • raw k z
  have pData (k : ℤ) (hk : k ∈ I) :=
    normalizedLowPassCorrection_cutoff_profile χ A gap M₀ k β hβ hV βV
      (smoothRaw k hk) D (C₁*Ajet) hD (mul_nonneg hC₁ hAjet) bβ
      (rawJets k hk) (fun p q hp hq hraw => by
        apply oneβ p q hp hq
        intro hz
        apply hraw
        have e : radianEndpointAngular M₀ p q =
            (axialCapPairWindow α (p,q) : ℂ) * radianEndpointAngular (fun uv => M uv.1 uv.2 0) p q :=
          maskedAt (p,q)
        have hzero : radianEndpointAngular M₀ p q = 0 := by
          rw [e,hz,Complex.ofReal_zero,zero_mul]
        simp only [normalizedLowPassCorrection,firstInput_joined,secondInput_joined,hzero,zero_mul])
  have result := box A upper M₀ inputLower G (C₂*Ajet) (mul_nonneg hC₂ hAjet)
    (fun k hk => (pData k hk).1.contDiffOn)
    (fun k hk n hn z _ => by simpa only [C₂,G,raw,mul_assoc] using (pData k hk).2.1 n hn z)
    (fun k hk => (pData k hk).2.2) f g h
  have bound : ‖radianTrilinearForm localForm f g h‖ ≤ (C₀*C₂)*Ajet*(triLpMass f g h 3 3 3).toReal := by
    simpa only [mul_assoc] using result.2
  refine ⟨bound,?_⟩
  intro actualAxis hf hg
  have eq : radianTrilinearForm localForm f g h = radianTrilinearForm origForm f g h :=
    radianCapCorrection_localization_eq χ A gap (fun uv => M uv.1 uv.2 0) hα f g h
      (fun p hp => actualAxis p (hf p hp)) (fun q hq => actualAxis q (hg q hq))
  exact ⟨eq,by simpa only [eq] using bound⟩

end Burnett.A05
