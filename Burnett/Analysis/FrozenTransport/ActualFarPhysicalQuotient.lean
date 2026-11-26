import Burnett.Analysis.FrozenTransport.ActualFarAngularProfile

set_option autoImplicit false
set_option maxHeartbeats 5400000
set_option maxRecDepth 4000

noncomputable section

namespace Burnett.V10.OriginalGaugeCompatibility

open Set Burnett.C02 Burnett.V03 Burnett.V04
open Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.TransportWardSymbol
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.RicciSymbol.TensorFrame (LorentzFrame)
open scoped ContDiff Matrix.Norms.Elementwise BigOperators

def actualThinFarWeightedNumerator (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ)
    (κ δ i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix g))
    {η : ℝ} (hη : 0 < η) (inn out : ℝ) (k j l : OrderedPair) (p q r : Vec) : ℂ :=
  let M := thinScreenAngular (inverseMatrix g) i o hm hη inn out
  ((lowSlotWeight ϑ κ p q r * (1 - angularNearWeight ϑ δ p q r) : ℝ) : ℂ) *
    physicalCubicNumerator orderedMetricDirection g a
      p (fun t => M.complex p t k) q (fun t => M.complex q t j) r (fun t => M.complex r t l)

/-- On every nonzero physical triad the guarded coefficient is the exact
quotient with its actual three screen columns. The cone assumptions needed
for the phase gap follow from the nonzero weighted coefficient itself. -/
theorem exists_actualThinFar_exact_physicalQuotient {K : Set Form} (hK : IsCompact K)
    (hFrame : ∀ m ∈ K, Nonempty (LorentzFrame m)) (D : ℝ) (hD : 0 ≤ D) :
    ∃ c₀ b : ℝ, 0 < c₀ ∧ 0 < b ∧
      ∀ (g : Mat), inverseMatrix g ∈ K →
      ∀ (a : Vec → ℝ), (∀ x : Vec, x ≠ 0 → a (-x) = -a x) →
        (∀ d : ℝ, 0 < d → ∀ x : Vec, x ≠ 0 → a (d • x) = d * a x) →
        ContDiffOn ℝ 1 a ({0}ᶜ : Set Vec) →
      ∀ (ϑ : ℝ → ℝ), (∀ t : ℝ, 1 ≤ t → ϑ t = 0) →
        (∀ t : ℝ, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1) →
      ∀ κ : ℝ, 0 < κ → κ < 1 / 16 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∀ (i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix g)),
      ∀ (inn out : ℝ), 0 ≤ inn → inn < out → out ≤ D →
      ∀ (k j l : OrderedPair) (p q r : Vec), p ≠ 0 → q ≠ 0 → r ≠ 0 → p + q + r = 0 →
        ∀ hη : 0 < c * κ * δ ^ 2,
        let B := (‖q‖ : ℂ) * actualThinFarCubicCorrection g a ϑ κ δ b i o hm hη inn out k j l
            (physicalFarProfilePoint p q)
        let N := actualThinFarWeightedNumerator g a ϑ κ δ i o hm hη inn out k j l p q r
        let phase := Complex.I * (signedQuadraticPhase (inverseMatrix g) p q : ℂ)
        B = N / phase ∧ phase * B = N := by
  obtain ⟨c₀, b, hc₀, hb, gap⟩ := exists_guardedFarCorrectionProfile_on_actual_support hK hFrame D hD
  refine ⟨c₀, b, hc₀, hb, ?_⟩
  intro g hg a hodd hhom ha ϑ cut flat κ hκ hκ' δ hδ hδ' c hc hc' i o hm inn out hin hio hout k j l p q r hp hq hr hsum hη
  let m := inverseMatrix g
  let x := physicalFarProfilePoint p q
  let M := thinScreenAngular m i o hm hη inn out
  let H (y : FarProfilePoint) (t : OrderedPair) := M.complex y.1 t k
  let J (y : FarProfilePoint) (t : OrderedPair) := M.complex y.2.2 t j
  let L (y : FarProfilePoint) (t : OrderedPair) := M.complex (-farHighOutput y) t l
  let N := normalizedPhysicalCubicNumerator orderedMetricDirection g a H J L
  let P := physicalCubicNumerator orderedMetricDirection g a p (fun t => M.complex p t k)
    q (fun t => M.complex q t j) r (fun t => M.complex r t l)
  let w := lowSlotWeight ϑ κ p q r * (1 - angularNearWeight ϑ δ p q r)
  let B := (‖q‖ : ℂ) * cutoffGuardedFarProfile ϑ κ δ m (b * δ ^ 2) N x
  let phase := Complex.I * (signedQuadraticPhase m p q : ℂ)
  change B = ((w : ℂ) * P) / phase ∧ phase * B = (w : ℂ) * P
  have hw : farCutoffExtension ϑ κ δ x = w := farCutoffExtension_eq_physical hκ ϑ δ hp hq hr hsum
  by_cases hw₀ : w = 0
  · simp [B, cutoffGuardedFarProfile, hw, hw₀]
  have support := inLowFarTriadSupport_of_nonzero hsum hp hq hr hw₀
  have hlow := (lowFarTriadSupport_separated cut flat hκ hκ' hδ hp hq hr support).1
  obtain ⟨hH, hJ, hL⟩ := farAngularColumns_eq_physical M hsum hp hq
  have hnorm : P = ((‖p‖ * ‖q‖ ^ 2 : ℝ) : ℂ) * N x := by
    calc
      P = physicalCubicNumerator orderedMetricDirection g a p (H x) q (J x) r (L x) := by
        simp only [P, H, J, L, x, hH, hJ, hL]
      _ = _ := physicalCubicNumerator_eq_normalized_on_lowSlot orderedMetricDirection g a
        hodd hhom ha hκ' hsum hp hq (by simpa only [mul_assoc] using hlow) H J L
  by_cases hP₀ : P = 0
  · have hfactor : ((‖p‖ * ‖q‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (norm_ne_zero_iff.mpr hp) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hq)))
    have hN₀ : N x = 0 := (mul_eq_zero.mp (hnorm.symm.trans hP₀)).resolve_left hfactor
    simp [B, cutoffGuardedFarProfile, guardedFarCorrectionProfile, hN₀, hP₀]
  have zeroColumn (v : Vec) (s : OrderedPair)
      (hz : thinConeProfile m (c * κ * δ ^ 2) inn out v = 0) (t : OrderedPair) :
      M.complex v t s = 0 := by
    simp [M, RealOrderedAngularMatrix.complex, thinScreenAngular, hz]
  have pNZ : thinConeProfile m (c * κ * δ ^ 2) inn out p ≠ 0 := by
    intro he
    apply hP₀
    simp [P, zeroColumn p k he, physicalCubicNumerator, frozenDensityCubicVertex,
      frozenDensityCubicTerm, densityCoefficientDirection]
  have qNZ : thinConeProfile m (c * κ * δ ^ 2) inn out q ≠ 0 := by
    intro he
    apply hP₀
    simp [P, zeroColumn q j he, physicalCubicNumerator, frozenDensityCubicVertex,
      frozenDensityCubicTerm, densityCoefficientDirection]
  have rNZ : thinConeProfile m (c * κ * δ ^ 2) inn out r ≠ 0 := by
    intro he
    apply hP₀
    simp [P, zeroColumn r l he, physicalCubicNumerator, frozenDensityCubicVertex,
      frozenDensityCubicTerm, densityCoefficientDirection]
  have cone (v : Vec) (hv : v ≠ 0) (hNZ : thinConeProfile m (c * κ * δ ^ 2) inn out v ≠ 0) :
      InRelativeCone m (D * (c * κ * δ ^ 2)) v :=
    (thinConeProfile_nonzero_cone hη hin hio hv hNZ).le.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hout hη.le) (sq_nonneg _))
  have hSym : Symmetric m := (hFrame m hg).elim lorentzFrame_symm
  obtain ⟨hgap, exactness⟩ := gap m hg κ hκ hκ' δ hδ hδ' c hc hc' ϑ cut flat p q r hp hq hr
    (cone p hp pNZ) (cone q hq qNZ) (cone r hr rNZ) support
  have hΔ : signedQuadraticPhase m p q ≠ 0 := by
    intro hz
    rw [normalizedFarPhase_eq_signedQuadraticPhase hSym hp hq, hz, zero_div, abs_zero] at hgap
    exact (not_le_of_gt (mul_pos hb (pow_pos hδ 2))) hgap
  have weighted := congrArg (fun z : ℂ => (w : ℂ) * z) (exactness N)
  have hphase : phase * B = (w : ℂ) * P := by
    simpa only [B, phase, cutoffGuardedFarProfile, hw, hnorm, mul_left_comm, mul_comm, mul_assoc] using weighted
  exact ⟨(eq_div_iff (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hΔ))).mpr
    ((mul_comm B phase).trans hphase), hphase⟩

end Burnett.V10.OriginalGaugeCompatibility
