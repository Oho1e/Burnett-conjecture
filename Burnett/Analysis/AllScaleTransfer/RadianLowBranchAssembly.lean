import Burnett.Analysis.AllScaleTransfer.RadianZeroRatioSplit
import Burnett.Analysis.AllScaleTransfer.RadianFourBranchAssembly
import Burnett.Analysis.AllScaleTransfer.LowRatioSplit

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.A05

open MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier
open Burnett.Analysis.LowRatio
open scoped ENNReal

/-- The radial remainder is the difference of the actual symbol and its
zero-ratio endpoint with the original ratio cutoff. -/
def radianRatioRemainderSymbol (χ₀ : ℝ → ℝ) (A : E ≃L[ℝ] E) (M₀ m : Joint → ℂ)
    (p : Joint) : ℂ :=
  m p - radianEndpointAngular M₀ p.1 p.2 * (χ₀ (‖A p.1‖ / ‖A p.2‖) : ℂ)

theorem radianRatioRemainderSymbol_eq_original
    (χ₀ : ℝ → ℝ) (hχ : χ₀ 0 = 1) (A : E ≃L[ℝ] E) (M₀ m : Joint → ℂ)
    (M : Point → ℂ) (p : Joint) (ang : Angles)
    (hm : m p = M (ang,‖A p.1‖ / ‖A p.2‖))
    (hM₀ : radianEndpointAngular M₀ p.1 p.2 = endpoint M ang) :
    radianRatioRemainderSymbol χ₀ A M₀ m p =
      (‖A p.1‖ / ‖A p.2‖) • remainder M χ₀ (ang,‖A p.1‖ / ‖A p.2‖) := by
  let ρ := ‖A p.1‖ / ‖A p.2‖
  change m p - radianEndpointAngular M₀ p.1 p.2 * (χ₀ ρ : ℂ) = ρ • remainder M χ₀ (ang,ρ)
  rw [hm,hM₀]
  have e : M (ang,ρ) = (χ₀ ρ : ℂ) * endpoint M ang + ρ • remainder M χ₀ (ang,ρ) := by
    simpa only [Complex.real_smul] using exact_split M χ₀ hχ (ang,ρ)
  rw [e]
  ring

/-- The original first-low Fourier form is exactly the sum of the full
low-pass endpoint, the genuine cutoff correction, and the genuine
ratio remainder. The three identities use the same original factors. -/
theorem radianTrilinearForm_first_low_split
    (χ₀ : ℝ → ℝ) (hχ₀ : Measurable χ₀) (hχ : ∀ t ≥ 0, ‖χ₀ t‖ ≤ 1)
    (A : E ≃L[ℝ] E) (gap : ℕ) (hgap : 3 ≤ gap) (m M₀ : Joint → ℂ)
    (hm : Measurable m) (hM₀ : Measurable M₀) (B B₀ : ℝ)
    (hB : ∀ p, ‖m p‖ ≤ B) (hB₀ : ∀ p, ‖M₀ p‖ ≤ B₀) (hB₀pos : 0 ≤ B₀)
    (f g h : SchwartzMap E ℂ) :
    let L (p : Joint) := radianEndpointAngular M₀ p.1 p.2 * ∑' j, lowEndpointRadianWindows gap j p
    let D (p : Joint) := ∑' j, radianLowPassCorrectionBlock χ₀ A gap M₀ j p
    radianTrilinearForm m f g h =
      radianTrilinearForm L f g h + radianTrilinearForm D f g h +
        radianTrilinearForm (radianRatioRemainderSymbol χ₀ A M₀ m) f g h := by
  intro L D
  let E₀ (p : Joint) := radianEndpointAngular M₀ p.1 p.2 * (χ₀ (‖A p.1‖ / ‖A p.2‖) : ℂ)
  let rem := radianRatioRemainderSymbol χ₀ A M₀ m
  have hEnd : Measurable E₀ := by
    have hm' : Measurable (fun p : Joint => radianEndpointAngular M₀ p.1 p.2) :=
      hM₀.comp ((measurable_fst.norm.inv.smul measurable_fst).prodMk (measurable_snd.norm.inv.smul measurable_snd))
    have hc : Measurable (fun p : Joint => χ₀ (‖A p.1‖ / ‖A p.2‖)) :=
      hχ₀.comp (((A.continuous.comp continuous_fst).norm.measurable).div
        ((A.continuous.comp continuous_snd).norm.measurable))
    exact hm'.mul (Complex.continuous_ofReal.measurable.comp hc)
  have hNorm₀ (p : Joint) : ‖E₀ p‖ ≤ B₀ := by
    simp only [E₀,radianEndpointAngular,norm_mul,Complex.norm_real]
    have hCut := hχ (‖A p.1‖ / ‖A p.2‖) (div_nonneg (norm_nonneg _) (norm_nonneg _))
    exact (mul_le_mul (hB₀ _) hCut (norm_nonneg _) hB₀pos).trans_eq (mul_one _)
  have im := integrable_radianTrilinearWeight_of_bounded m hm.aestronglyMeasurable B hB f g h
  have iE := integrable_radianTrilinearWeight_of_bounded E₀ hEnd.aestronglyMeasurable B₀ hNorm₀ f g h
  have iRem : Integrable (radianTrilinearWeight rem f g h) := by
    have e : radianTrilinearWeight rem f g h =
        fun p => radianTrilinearWeight m f g h p - radianTrilinearWeight E₀ f g h p := by
      funext p
      simp only [rem,radianRatioRemainderSymbol,radianTrilinearWeight,E₀,sub_mul]
    rw [e]
    exact im.sub iE
  have end_split : radianTrilinearForm E₀ f g h =
      radianTrilinearForm L f g h + radianTrilinearForm D f g h :=
    radianTrilinearForm_zero_ratio_split χ₀ hχ₀ hχ A gap hgap M₀ hM₀ B₀ hB₀pos hB₀ f g h
  have symbol_eq : m = fun p => E₀ p + rem p := by
    funext p
    change m p = E₀ p + (m p - E₀ p)
    ring
  have whole := (congrArg (fun x => radianTrilinearForm x f g h) symbol_eq).trans
    (radianTrilinearForm_add f g h iE iRem)
  rwa [end_split] at whole

/-- Adding the actual first-low estimates in the three cyclic coordinates
and the actual comparable estimate gives the full original form bound. -/
theorem radianTrilinearForm_bound_of_four_branch_estimates
    (ϑ : ℝ → ℝ) (hϑ : Measurable ϑ) (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1) (κ : ℝ)
    (m : Joint → ℂ) (hm : Measurable m) (B : ℝ) (hB : ∀ p, ‖m p‖ ≤ B)
    (f g h : SchwartzMap E ℂ) (C₀ C₁ C₂ C₃ : ℝ)
    (h0 : ‖radianTrilinearForm (radianFourBranchSymbol ϑ κ m 0) f g h‖ ≤
      C₀ * (triLpMass f g h 3 3 3).toReal)
    (h1 : ‖radianTrilinearForm (radianFourBranchSymbol ϑ κ (m ∘ radianCycle.symm) 0) g h f‖ ≤
      C₁ * (triLpMass g h f 3 3 3).toReal)
    (h2 : ‖radianTrilinearForm (radianFourBranchSymbol ϑ κ (m ∘ radianCycle) 0) h f g‖ ≤
      C₂ * (triLpMass h f g 3 3 3).toReal)
    (h3 : ‖radianTrilinearForm (radianFourBranchSymbol ϑ κ m 3) f g h‖ ≤
      C₃ * (triLpMass f g h 3 3 3).toReal) :
    ‖radianTrilinearForm m f g h‖ ≤ (C₀+C₁+C₂+C₃) * (triLpMass f g h 3 3 3).toReal := by
  obtain ⟨e1,e2⟩ := radianTrilinearForm_rotate_low_branches ϑ κ m f g h
  let T (i : Fin 4) := radianTrilinearForm (radianFourBranchSymbol ϑ κ m i) f g h
  let mass := (triLpMass f g h 3 3 3).toReal
  have ea : triLpMass g h f 3 3 3 = triLpMass f g h 3 3 3 := by
    simp only [triLpMass,mul_assoc,mul_comm]
  have eb : triLpMass h f g 3 3 3 = triLpMass f g h 3 3 3 := by
    simp only [triLpMass,mul_assoc,mul_comm,mul_left_comm]
  have h₀ : ‖T 0‖ ≤ C₀ * mass := h0
  have h₁ : ‖T 1‖ ≤ C₁ * mass := by
    unfold T
    rw [e1]
    simpa only [mass,ea] using h1
  have h₂ : ‖T 2‖ ≤ C₂ * mass := by
    unfold T
    rw [e2]
    simpa only [mass,eb] using h2
  have h₃ : ‖T 3‖ ≤ C₃ * mass := h3
  rw [radianTrilinearForm_actual_four_branches ϑ hϑ hRange κ m hm B hB f g h]
  change ‖∑ i : Fin 4, T i‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  change ‖T 0‖ + (‖T 1‖ + (‖T 2‖ + ‖T 3‖)) ≤ (C₀+C₁+C₂+C₃)*mass
  nlinarith only [h₀,h₁,h₂,h₃]

end Burnett.A05
