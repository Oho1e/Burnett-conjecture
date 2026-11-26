import Burnett.Analysis.CubicEnergy.AngularCorrection.CoordinateQuotientCMCore

set_option autoImplicit false
set_option maxHeartbeats 4800000

noncomputable section

namespace Burnett.A07

open Filter MeasureTheory Metric
open Burnett.A02.FrequencySplit (E Joint Freq8 splitFreq radianFourier radianWeight
  radianWeight_integral bilinearFourierWeight jointTrilinear jointTestFactor triBalance
  triLpMass joint_trilinear_sphere_bound homogeneous_joint_symbol_measurable_bounded)
open Burnett.A06 (radianHighPair radianHighPairWeight radianFourier_conj_neg)
open scoped ComplexConjugate ContDiff ENNReal FourierTransform

private def conjugateSchwartzTest (w : SchwartzMap E ℂ) : SchwartzMap E ℂ where
  toFun := Complex.conjLIE ∘ (w : E → ℂ)
  smooth' := Complex.conjCLE.contDiff.comp w.smooth'
  decay' k n := by
    obtain ⟨D, _, hD⟩ := w.decay k n
    refine ⟨D, fun x => ?_⟩
    rw [Complex.conjLIE.norm_iteratedFDeriv_comp_left]
    exact hD x

private theorem conjugateSchwartzTest_eLpNorm (w : SchwartzMap E ℂ) (q : ℝ≥0∞) :
    eLpNorm (conjugateSchwartzTest w : E → ℂ) q volume =
      eLpNorm (w : E → ℂ) q volume := by
  apply eLpNorm_congr_enorm_ae
  filter_upwards with x
  change ‖conj (w x)‖ₑ = ‖w x‖ₑ
  simp only [← ofReal_norm_eq_enorm, Complex.norm_conj]

/-- The real-symbol Hermitian radian pairing is the actual A02 trilinear
Fourier form evaluated against the conjugate Schwartz test. -/
theorem radianHighPair_real_eq_jointTrilinear
    (m : Joint → ℝ) (hh : ∀ t : ℝ, 0 < t → ∀ x, m (t • x) = m x)
    (f u w : SchwartzMap E ℂ) :
    radianHighPair (fun p => (m p : ℂ)) f u w =
      jointTrilinear m f u (conjugateSchwartzTest w) := by
  have eq : radianHighPairWeight (fun p => (m p : ℂ)) f u w =
      radianWeight m f u (conjugateSchwartzTest w) := by
    funext p
    unfold radianHighPairWeight radianWeight
    change (m p : ℂ) * radianFourier f p.1 * radianFourier u p.2 *
      conj (radianFourier w (p.2+p.1)) =
        (m p : ℂ) * radianFourier f p.1 * radianFourier u p.2 *
          radianFourier (fun x => conj (w x)) (-(p.1+p.2))
    rw [radianFourier_conj_neg, add_comm p.1 p.2]
  have hτ : 0 < Burnett.A02.FrequencySplit.tau := mul_pos (by norm_num) Real.pi_pos
  unfold radianHighPair
  rw [eq, radianWeight_integral, show
    (fun q => m (Burnett.A02.FrequencySplit.tau • q)) = m from funext (hh _ hτ)]
  apply integral_congr_ae
  filter_upwards with p
  simp only [bilinearFourierWeight, jointTestFactor, mul_assoc]

private theorem radianHighPair_eq_real_imag
    (m : Joint → ℂ) (hr : ContDiffOn ℝ ∞ (fun p => (m p).re) {p | p ≠ 0})
    (hi : ContDiffOn ℝ ∞ (fun p => (m p).im) {p | p ≠ 0})
    (hh : ∀ t : ℝ, 0 < t → ∀ x, m (t • x) = m x)
    (f u w : SchwartzMap E ℂ) :
    radianHighPair m f u w =
      radianHighPair (fun p => ((m p).re : ℂ)) f u w +
        Complex.I * radianHighPair (fun p => ((m p).im : ℂ)) f u w := by
  have intPart (p : ℂ →L[ℝ] ℝ) (hp : ContDiffOn ℝ ∞ (fun x => p (m x)) {x | x ≠ 0}) :
      Integrable (radianHighPairWeight (fun x => (p (m x) : ℂ)) f u w) := by
    obtain ⟨hm, B, hB⟩ := homogeneous_joint_symbol_measurable_bounded _ hp
      (fun t ht x => congrArg p (hh t ht x))
    have B0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    apply integrable_radianHighPairWeight_of_orderOne _ (Complex.continuous_ofReal.measurable.comp hm)
      B B0 _ f u w
    intro x
    change ‖(p (m x) : ℂ)‖ ≤ _
    rw [Complex.norm_real]
    have hpos : 1 ≤ 1 + ‖x.1‖ + ‖x.2‖ := by
      linarith [norm_nonneg x.1, norm_nonneg x.2]
    exact (hB x).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpos B0)
  have hR := intPart Complex.reCLM hr
  have hI := intPart Complex.imCLM hi
  have hW : radianHighPairWeight m f u w =
      fun p => radianHighPairWeight (fun q => ((m q).re : ℂ)) f u w p +
        Complex.I * radianHighPairWeight (fun q => ((m q).im : ℂ)) f u w p := by
    funext p
    simp only [radianHighPairWeight]
    have hmi : m p = ((m p).re : ℂ) + ((m p).im : ℂ) * Complex.I :=
      (Complex.re_add_im (m p)).symm
    conv_lhs => rw [hmi]
    ring
  let V := radianHighPairWeight (fun q => ((m q).re : ℂ)) f u w
  let W := radianHighPairWeight (fun q => ((m q).im : ℂ)) f u w
  have hVI : Integrable V := hR
  have hWI : Integrable W := hI
  have hsplit : (∫ p, V p + Complex.I * W p) =
      (∫ p, V p) + Complex.I * ∫ p, W p := by
    calc
      _ = (∫ p, V p) + ∫ p, Complex.I * W p :=
        integral_add (μ := volume) (f := V) (g := fun p => Complex.I * W p)
          hVI (hWI.const_mul Complex.I)
      _ = _ := by rw [integral_const_mul]
  unfold radianHighPair
  rw [hW]
  change _ • (∫ p, V p + Complex.I * W p) = _
  rw [hsplit, smul_add]
  simp only [Complex.real_smul]
  ring

private theorem triBalance_four_four_two : triBalance 4 4 2 := by
  rw [triBalance, ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4),
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  norm_num

/-- The quantitative A02 Coifman–Meyer estimate now applies to the same
Hermitian radian pairing as the coordinate-quotient decomposition.
A single real jet budget for the real and imaginary parts suffices. -/
theorem exists_radianHighPair_CM_four_four_two_bound :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (m : Joint → ℂ), ContDiffOn ℝ ∞ m {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, m (t • x) = m x) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ i : ℕ, i ≤ 15 → ∀ ξ ∈ sphere (0 : Freq8) 1,
        ‖iteratedFDeriv ℝ i (fun y => (m (splitFreq y)).re) ξ‖ ≤ D) →
      (∀ i : ℕ, i ≤ 15 → ∀ ξ ∈ sphere (0 : Freq8) 1,
        ‖iteratedFDeriv ℝ i (fun y => (m (splitFreq y)).im) ξ‖ ≤ D) →
      ∀ f u w : SchwartzMap E ℂ,
        ‖radianHighPair m f u w‖ₑ ≤ K * ENNReal.ofReal D * triLpMass f u w 4 4 2 := by
  obtain ⟨K, hK, est⟩ := joint_trilinear_sphere_bound 4 4 2
    (by norm_num) (by norm_num) (by norm_num) triBalance_four_four_two
  refine ⟨K+K, ENNReal.add_lt_top.mpr ⟨hK, hK⟩, ?_⟩
  intro m hm hh D D0 hjR hjI f u w
  have hR : ContDiffOn ℝ ∞ (fun p => (m p).re) {p | p ≠ 0} :=
    Complex.reCLM.contDiff.comp_contDiffOn hm
  have hI : ContDiffOn ℝ ∞ (fun p => (m p).im) {p | p ≠ 0} :=
    Complex.imCLM.contDiff.comp_contDiffOn hm
  have hscaleR (t : ℝ) (ht : 0 < t) (p : Joint) := congrArg Complex.re (hh t ht p)
  have hscaleI (t : ℝ) (ht : 0 < t) (p : Joint) := congrArg Complex.im (hh t ht p)
  have eR := est _ hR hscaleR D D0 hjR f u (conjugateSchwartzTest w)
  have eI := est _ hI hscaleI D D0 hjI f u (conjugateSchwartzTest w)
  have hmass : triLpMass f u (conjugateSchwartzTest w) 4 4 2 = triLpMass f u w 4 4 2 := by
    unfold triLpMass
    rw [conjugateSchwartzTest_eLpNorm]
  rw [hmass] at eR eI
  rw [radianHighPair_eq_real_imag m hR hI hh, radianHighPair_real_eq_jointTrilinear _ hscaleR,
    radianHighPair_real_eq_jointTrilinear _ hscaleI]
  have hnormI (z : ℂ) : ‖Complex.I * z‖ₑ = ‖z‖ₑ := by
    simp only [← ofReal_norm_eq_enorm, norm_mul, Complex.norm_I, one_mul]
  calc
    _ ≤ _ := enorm_add_le _ _
    _ ≤ K * ENNReal.ofReal D * triLpMass f u w 4 4 2 +
        K * ENNReal.ofReal D * triLpMass f u w 4 4 2 := by rw [hnormI]; exact add_le_add eR eI
    _ = _ := by rw [add_mul, add_mul]

end Burnett.A07
