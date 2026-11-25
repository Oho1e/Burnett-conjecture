import Burnett.Analysis.FrozenTransport.IndependentFarCutoffs

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 3500

noncomputable section

namespace Burnett.V10

open Set Burnett.Analysis.ProjectiveNullCaps
open scoped ContDiff ComplexConjugate BigOperators

open private guardedFarCorrectionProfile_exact from Burnett.Analysis.FrozenTransport.NormalizedFarReciprocal

def cutoffGuardedFarProfile (ϑ : ℝ → ℝ) (κ δ : ℝ) (m : Form) (s : ℝ)
    (N : FarProfilePoint → ℂ) (x : FarProfilePoint) : ℂ :=
  (farCutoffExtension ϑ κ δ x : ℂ) * guardedFarCorrectionProfile m s N x

theorem cutoffGuardedFarProfile_contDiffOn {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ ∞ ϑ)
    {κ : ℝ} (hκ : 0 < κ) (δ : ℝ) (m : Form) (s : ℝ)
    {N : FarProfilePoint → ℂ} (hN : ContDiffOn ℝ ∞ N farProfileOpenDomain) :
    ContDiffOn ℝ ∞ (cutoffGuardedFarProfile ϑ κ δ m s N) farProfileOpenDomain :=
  (Complex.ofRealCLM.contDiff.comp_contDiffOn (farCutoffExtension_contDiffOn hϑ hκ δ)).mul
    (guardedFarCorrectionProfile_contDiffOn m s hN)

/-- The extended correction has finite ambient derivative bounds at every
prescribed finite order on a compact window containing the physical support. -/
theorem exists_cutoffGuardedFarProfile_derivatives_le {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ ∞ ϑ)
    {κ : ℝ} (hκ : 0 < κ) (δ : ℝ) (m : Form) (s : ℝ)
    {N : FarProfilePoint → ℂ} (hN : ContDiffOn ℝ ∞ N farProfileOpenDomain) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ k ≤ n, ∀ x ∈ farProfileCompactDomain,
        ‖iteratedFDeriv ℝ k (cutoffGuardedFarProfile ϑ κ δ m s N) x‖ ≤ B := by
  let f := cutoffGuardedFarProfile ϑ κ δ m s N
  have hs := farProfileOpenDomain_isOpen
  have hd : ContDiffOn ℝ ∞ f farProfileOpenDomain := cutoffGuardedFarProfile_contDiffOn hϑ hκ δ m s hN
  have bound (k : ℕ) : ∃ b : ℝ, 0 ≤ b ∧
      ∀ x ∈ farProfileCompactDomain, ‖iteratedFDeriv ℝ k f x‖ ≤ b := by
    have hc := (contDiffOn_infty.mp hd k).continuousOn_iteratedFDerivWithin
      (le_rfl : (k : WithTop ℕ∞) ≤ k) hs.uniqueDiffOn
    have hOn := hc.congr (fun x hx => (iteratedFDerivWithin_of_isOpen k hs hx).symm)
    obtain ⟨b, hb⟩ := farProfileCompactDomain_isCompact.bddAbove_image
      (hOn.norm.mono farProfileCompactDomain_subset)
    exact ⟨max b 0, le_max_right _ _, fun x hx =>
      (hb (mem_image_of_mem _ hx)).trans (le_max_left _ _)⟩
  choose b hb nonneg_bound using bound
  refine ⟨∑ k ∈ Finset.range (n + 1), b k, Finset.sum_nonneg (fun k _ => hb k), ?_⟩
  intro k hk x hx
  exact (nonneg_bound k x hx).trans (Finset.single_le_sum (fun j _ => hb j)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))

theorem cutoffGuardedFarProfile_eq_signed_weightedNumerator
    {m : Form} (hm : Symmetric m) {κ s : ℝ} (hκ : 0 < κ) (hs : 0 < s)
    (ϑ : ℝ → ℝ) (δ : ℝ) {p q r : Vec} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hTriad : p + q + r = 0) (hgap : s ≤ |normalizedFarPhase m (physicalFarProfilePoint p q)|)
    (N : FarProfilePoint → ℂ) :
    let x := physicalFarProfilePoint p q
    Complex.I * (signedQuadraticPhase m p q : ℂ) *
        ((‖q‖ : ℂ) * cutoffGuardedFarProfile ϑ κ δ m s N x) =
      ((lowSlotWeight ϑ κ p q r * (1 - angularNearWeight ϑ δ p q r) : ℝ) : ℂ) *
        ((‖p‖ * ‖q‖ ^ 2 : ℝ) : ℂ) * N x := by
  intro x
  change Complex.I * (signedQuadraticPhase m p q : ℂ) *
        ((‖q‖ : ℂ) * cutoffGuardedFarProfile ϑ κ δ m s N (physicalFarProfilePoint p q)) =
      ((lowSlotWeight ϑ κ p q r * (1 - angularNearWeight ϑ δ p q r) : ℝ) : ℂ) *
        ((‖p‖ * ‖q‖ ^ 2 : ℝ) : ℂ) * N (physicalFarProfilePoint p q)
  rw [cutoffGuardedFarProfile, farCutoffExtension_eq_physical hκ ϑ δ hp hq hr hTriad]
  let w : ℂ := (lowSlotWeight ϑ κ p q r * (1 - angularNearWeight ϑ δ p q r) : ℝ)
  have h := congrArg (fun z : ℂ => w * z) (guardedFarCorrectionProfile_exact hm hs hp hq hgap N)
  simpa only [w, mul_left_comm, mul_comm, mul_assoc] using h

theorem signedQuadraticPhase_highAdjoint (m : Form) (p q : Vec) :
    signedQuadraticPhase m (-p) (p + q) = -signedQuadraticPhase m p q := by
  have h : p + q + -p = q := by abel
  rw [signedQuadraticPhase, signedQuadraticPhase, h, add_comm q p, neg_sub]

/-- Swapping the two high slots preserves the Hermitian quotient of a Hermitian
numerator because the signed phase and the imaginary unit each reverse sign. -/
theorem signedHermitianQuotient_highAdjoint {I : Type*} (m : Form)
    (S : Vec → Vec → I → I → ℂ)
    (hS : ∀ p q i j, conj (S (-p) (p + q) j i) = S p q i j)
    (p q : Vec) (i j : I) :
    conj (S (-p) (p + q) j i / (Complex.I * (signedQuadraticPhase m (-p) (p + q) : ℂ))) =
      S p q i j / (Complex.I * (signedQuadraticPhase m p q : ℂ)) := by
  rw [map_div₀, hS p q i j, map_mul, Complex.conj_I, Complex.conj_ofReal,
    signedQuadraticPhase_highAdjoint, Complex.ofReal_neg, neg_mul_neg]

end Burnett.V10
