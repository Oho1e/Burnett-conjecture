import Burnett.Analysis.FrozenTransport.NormalizedPhysicalCubicProfile

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4000

noncomputable section

namespace Burnett.V10

open Set Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry.InverseField
open scoped ContDiff Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι]

def farPhysicalCubicCorrection (S : ι → Mat) (G : Mat) (a : Vec → ℝ)
    (ϑ : ℝ → ℝ) (κ δ b : ℝ) (H J L : FarProfilePoint → ι → ℂ) (x : FarProfilePoint) : ℂ :=
  cutoffGuardedFarProfile ϑ κ δ (inverseMatrix G) (b * δ ^ 2)
    (normalizedPhysicalCubicNumerator S G a H J L) x

private theorem cyclicExtensionDomain_subset_far :
    cyclicExtensionDomain ⊆ farProfileOpenDomain := by
  intro x hx hZero
  have hNeg : x.2.2 = -x.2.1 := eq_neg_of_add_eq_zero_left hZero
  have hn := hx.2
  rw [hNeg, norm_neg] at hn
  exact (lt_irrefl _) hn

theorem farPhysicalCubicCorrection_contDiffOn (S : ι → Mat) (G : Mat)
    {a : Vec → ℝ} (ha : ContDiffOn ℝ ∞ a ({0}ᶜ : Set Vec))
    {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) {κ : ℝ} (hκ : 0 < κ) (δ b : ℝ)
    (H J L : FarProfilePoint → ι → ℂ)
    (hH : ∀ i, ContDiffOn ℝ ∞ (fun x => H x i) cyclicExtensionDomain)
    (hJ : ∀ i, ContDiffOn ℝ ∞ (fun x => J x i) cyclicExtensionDomain)
    (hL : ∀ i, ContDiffOn ℝ ∞ (fun x => L x i) cyclicExtensionDomain) :
    ContDiffOn ℝ ∞ (farPhysicalCubicCorrection S G a ϑ κ δ b H J L) cyclicExtensionDomain := by
  have cutoff := (farCutoffExtension_contDiffOn hϑ hκ δ).mono cyclicExtensionDomain_subset_far
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn cutoff).mul
    (guardedFarCorrectionProfile_contDiffOn (inverseMatrix G) (b * δ ^ 2)
      (normalizedPhysicalCubicNumerator_contDiffOn S G ha H J L hH hJ hL))

/-- On a compact normalization window, the ambient derivative of each
prescribed order of the actual density quotient is bounded. -/
theorem farPhysicalCubicCorrection_iteratedFDeriv_bound (S : ι → Mat) (G : Mat)
    {a : Vec → ℝ} (ha : ContDiffOn ℝ ∞ a ({0}ᶜ : Set Vec))
    {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) {κ : ℝ} (hκ : 0 < κ) (hκ' : κ < 1 / 16) (δ b : ℝ)
    (H J L : FarProfilePoint → ι → ℂ)
    (hH : ∀ i, ContDiffOn ℝ ∞ (fun x => H x i) cyclicExtensionDomain)
    (hJ : ∀ i, ContDiffOn ℝ ∞ (fun x => J x i) cyclicExtensionDomain)
    (hL : ∀ i, ContDiffOn ℝ ∞ (fun x => L x i) cyclicExtensionDomain) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ cyclicLowCompact κ,
      ‖iteratedFDeriv ℝ n (farPhysicalCubicCorrection S G a ϑ κ δ b H J L) x‖ ≤ B := by
  have hOpen := isOpen_cyclicExtensionDomain
  have hDiff := farPhysicalCubicCorrection_contDiffOn S G ha hϑ hκ δ b H J L hH hJ hL
  have hWithin := (contDiffOn_infty.mp hDiff n).continuousOn_iteratedFDerivWithin
    (le_rfl : (n : WithTop ℕ∞) ≤ n) hOpen.uniqueDiffOn
  have hGlobal := hWithin.congr
    (fun x hx => (iteratedFDerivWithin_of_isOpen n hOpen hx).symm)
  obtain ⟨B, hB⟩ := (isCompact_cyclicLowCompact κ).bddAbove_image
    (hGlobal.norm.mono (cyclicLowCompact_subset_domain κ hκ'))
  exact ⟨max B 0, le_max_right _ _, fun x hx =>
    (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)⟩

/-- The exact signed phase recovers the weighted cyclic ΓΓ numerator on the
physical support, with the inverse matrix of the same frozen metric. -/
theorem exists_farPhysicalCubicCorrection_exact_on_support
    {K : Set Form} (hK : IsCompact K)
    (hFrame : ∀ m ∈ K, Nonempty (Burnett.RicciSymbol.TensorFrame.LorentzFrame m))
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ c₀ b : ℝ, 0 < c₀ ∧ 0 < b ∧
      ∀ (S : ι → Mat) (G : Mat), inverseMatrix G ∈ K →
      ∀ κ : ℝ, 0 < κ → κ < 1 / 16 →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∀ ϑ : ℝ → ℝ, (∀ t : ℝ, 1 ≤ t → ϑ t = 0) →
        (∀ t : ℝ, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1) →
      ∀ (a : Vec → ℝ), (∀ x : Vec, x ≠ 0 → a (-x) = -a x) →
        (∀ d : ℝ, 0 < d → ∀ x : Vec, x ≠ 0 → a (d • x) = d * a x) →
        ContDiffOn ℝ 1 a ({0}ᶜ : Set Vec) →
      ∀ p q r : Vec, p ≠ 0 → q ≠ 0 → r ≠ 0 → p + q + r = 0 →
        InRelativeCone (inverseMatrix G) (C * (c * κ * δ ^ 2)) p →
        InRelativeCone (inverseMatrix G) (C * (c * κ * δ ^ 2)) q →
        InRelativeCone (inverseMatrix G) (C * (c * κ * δ ^ 2)) r →
        InLowFarTriadSupport ϑ κ δ p q r →
      ∀ (H J L : FarProfilePoint → ι → ℂ),
        let x := physicalFarProfilePoint p q
        Complex.I * (signedQuadraticPhase (inverseMatrix G) p q : ℂ) *
            ((‖q‖ : ℂ) * farPhysicalCubicCorrection S G a ϑ κ δ b H J L x) =
          ((lowSlotWeight ϑ κ p q r * (1 - angularNearWeight ϑ δ p q r) : ℝ) : ℂ) *
            physicalCubicNumerator S G a p (H x) q (J x) r (L x) := by
  obtain ⟨c₀, b, hc₀, hb, gap⟩ := exists_guardedFarCorrectionProfile_on_actual_support hK hFrame C hC
  refine ⟨c₀, b, hc₀, hb, ?_⟩
  intro S G hG κ hκ hκ' δ hδ hδ' c hc hc' ϑ hCut hFlat a hOdd hScale ha p q r hp hq hr hSum
    hP hQ hR hSupport H J L x
  have hGap := (gap (inverseMatrix G) hG κ hκ hκ' δ hδ hδ' c hc hc' ϑ hCut hFlat
    p q r hp hq hr hP hQ hR hSupport).1
  have hSym : Symmetric (inverseMatrix G) := (hFrame (inverseMatrix G) hG).elim lorentzFrame_symm
  have h := cutoffGuardedFarProfile_eq_signed_weightedNumerator hSym hκ
    (mul_pos hb (pow_pos hδ 2)) ϑ δ hp hq hr hSum hGap
    (normalizedPhysicalCubicNumerator S G a H J L)
  have hLow := (lowFarTriadSupport_separated hCut hFlat hκ hκ' hδ hp hq hr hSupport).1
  have hNum := physicalCubicNumerator_eq_normalized_on_lowSlot S G a hOdd hScale ha hκ' hSum hp hq hLow H J L
  rw [hNum]
  simpa only [farPhysicalCubicCorrection, mul_assoc] using h

end Burnett.V10
