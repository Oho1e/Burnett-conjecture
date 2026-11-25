import Burnett.Analysis.FrozenTransport.FarPhysicalCubicCorrection
import Burnett.Analysis.TransportPatches.ActualThinScreenCombination

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option maxRecDepth 4000

noncomputable section

namespace Burnett.V10

open Set Burnett.C02 Burnett.V03 Burnett.Analysis.ProjectiveNullCaps
open Burnett.Analysis.TransportWardSymbol Burnett.Geometry.InverseField
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff Matrix.Norms.Elementwise

def orderedMetricDirection (i : OrderedPair) : Mat := Matrix.single i.1 i.2 1

theorem assemble_orderedMetricDirection (H : OrderedPair → ℝ) (a b : Fin 4) :
    assembleMetricComponents orderedMetricDirection H a b = H (a, b) := by
  classical
  rw [assembleMetricComponents_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (a, b)]
  · rw [orderedMetricDirection, Matrix.single_apply_same, mul_one]
  · intro i _ hi
    have h : ¬(i.1 = a ∧ i.2 = b) := fun he => hi (Prod.ext he.1 he.2)
    rw [orderedMetricDirection, Matrix.single_apply_of_ne i.1 i.2 (1 : ℝ) a b h, mul_zero]
  · simp

private theorem farAngularColumn_contDiffOn (M : RealOrderedAngularMatrix)
    (f : FarProfilePoint → Vec) (hf : ContDiff ℝ ∞ f)
    (hf₀ : ∀ x ∈ cyclicExtensionDomain, f x ≠ 0) (i j : OrderedPair) :
    ContDiffOn ℝ ∞ (fun x => M.complex (f x) i j) cyclicExtensionDomain := by
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn
    ((M.smooth i j).comp hf.contDiffOn (fun x hx => hf₀ x hx))

theorem farAngularColumns_contDiffOn (M : RealOrderedAngularMatrix) (k i j l : OrderedPair) :
    ContDiffOn ℝ ∞ (fun x : FarProfilePoint => M.complex x.1 k i) cyclicExtensionDomain ∧
    ContDiffOn ℝ ∞ (fun x : FarProfilePoint => M.complex x.2.2 k j) cyclicExtensionDomain ∧
    ContDiffOn ℝ ∞ (fun x : FarProfilePoint => M.complex (-farHighOutput x) k l) cyclicExtensionDomain := by
  have hz : ContDiff ℝ ∞ (fun x : FarProfilePoint => x.2.1) := contDiff_fst.comp contDiff_snd
  have hθ : ContDiff ℝ ∞ (fun x : FarProfilePoint => x.2.2) := contDiff_snd.comp contDiff_snd
  have hρ : ContDiff ℝ ∞ (fun x : FarProfilePoint => -farHighOutput x) := (hθ.add hz).neg
  refine ⟨farAngularColumn_contDiffOn M _ contDiff_fst (fun _ hx => hx.1) _ _,
    farAngularColumn_contDiffOn M _ hθ ?_ _ _, farAngularColumn_contDiffOn M _ hρ ?_ _ _⟩
  · intro x hx he
    have hd := hx.2
    rw [he, norm_zero] at hd
    exact (not_lt_of_ge (norm_nonneg _)) hd
  · intro x hx he
    have hd := hx.2
    have he' := neg_eq_zero.mp he
    have eq : x.2.2 = -x.2.1 := eq_neg_of_add_eq_zero_left he'
    rw [eq, norm_neg] at hd
    exact (lt_irrefl _) hd

theorem farAngularColumns_eq_physical (M : RealOrderedAngularMatrix) {p q r : Vec}
    (hSum : p + q + r = 0) (hp : p ≠ 0) (hq : q ≠ 0) :
    let x := physicalFarProfilePoint p q
    M.complex x.1 = M.complex p ∧ M.complex x.2.2 = M.complex q ∧
      M.complex (-farHighOutput x) = M.complex r := by
  intro x
  have hScale (a : ℝ) (ha : 0 < a) (v : Vec) : M.complex (a • v) = M.complex v := by
    unfold RealOrderedAngularMatrix.complex
    rw [M.degree a ha v]
  have hq' : 0 < ‖q‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hq)
  have hOut : -farHighOutput x = ‖q‖⁻¹ • r := by
    change -(‖q‖⁻¹ • q + ‖q‖⁻¹ • p) = _
    rw [← smul_add, add_comm q p, triad_third_eq_neg_add hSum, smul_neg]
  refine ⟨hScale _ (inv_pos.mpr (norm_pos_iff.mpr hp)) p, hScale _ hq' q, ?_⟩
  rw [hOut]
  exact hScale _ hq' r

def actualThinFarCubicCorrection (G : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ) (κ δ b : ℝ)
    (i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix G))
    {η : ℝ} (hη : 0 < η) (inner outer : ℝ) (k j l : OrderedPair) (x : FarProfilePoint) : ℂ :=
  let M := thinScreenAngular (inverseMatrix G) i o hm hη inner outer
  farPhysicalCubicCorrection orderedMetricDirection G a ϑ κ δ b
    (fun y t => M.complex y.1 t k) (fun y t => M.complex y.2.2 t j)
    (fun y t => M.complex (-farHighOutput y) t l) x

theorem actualThinFarCubicCorrection_contDiffOn (G : Mat)
    {a : Vec → ℝ} (ha : ContDiffOn ℝ ∞ a ({0}ᶜ : Set Vec))
    {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) {κ : ℝ} (hκ : 0 < κ) (δ b : ℝ)
    (i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix G))
    {η : ℝ} (hη : 0 < η) (inner outer : ℝ) (k j l : OrderedPair) :
    ContDiffOn ℝ ∞ (actualThinFarCubicCorrection G a ϑ κ δ b i o hm hη inner outer k j l)
      cyclicExtensionDomain := by
  let M := thinScreenAngular (inverseMatrix G) i o hm hη inner outer
  exact farPhysicalCubicCorrection_contDiffOn orderedMetricDirection G ha hϑ hκ δ b _ _ _
    (fun t => (farAngularColumns_contDiffOn M t k j l).1)
    (fun t => (farAngularColumns_contDiffOn M t k j l).2.1)
    (fun t => (farAngularColumns_contDiffOn M t k j l).2.2)

theorem actualThinFarCubicCorrection_exact_coefficient
    (G : Mat) (hSym : Symmetric (inverseMatrix G))
    (a : Vec → ℝ) (hodd : ∀ x : Vec, x ≠ 0 → a (-x) = -a x)
    (hscale : ∀ d : ℝ, 0 < d → ∀ x : Vec, x ≠ 0 → a (d • x) = d * a x)
    (ha : ContDiffOn ℝ 1 a ({0}ᶜ : Set Vec))
    {κ δ b : ℝ} (hκ : 0 < κ) (hκ' : κ < 1 / 16) (hδ : 0 < δ) (hb : 0 < b)
    (ϑ : ℝ → ℝ) (i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix G))
    {η : ℝ} (hη : 0 < η) (inner outer : ℝ) (k j l : OrderedPair)
    {p q r : Vec} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hSum : p + q + r = 0)
    (hLow : ‖p‖ ≤ 2 * κ * ‖q‖)
    (hGap : b * δ ^ 2 ≤ |normalizedFarPhase (inverseMatrix G) (physicalFarProfilePoint p q)|) :
    let x := physicalFarProfilePoint p q
    let M := thinScreenAngular (inverseMatrix G) i o hm hη inner outer
    Complex.I * (signedQuadraticPhase (inverseMatrix G) p q : ℂ) *
        ((‖q‖ : ℂ) * actualThinFarCubicCorrection G a ϑ κ δ b i o hm hη inner outer k j l x) =
      ((lowSlotWeight ϑ κ p q r * (1 - angularNearWeight ϑ δ p q r) : ℝ) : ℂ) *
        physicalCubicNumerator orderedMetricDirection G a
          p (fun t => M.complex p t k) q (fun t => M.complex q t j) r (fun t => M.complex r t l) := by
  intro x M
  let H := fun y : FarProfilePoint => fun t => M.complex y.1 t k
  let J := fun y : FarProfilePoint => fun t => M.complex y.2.2 t j
  let L := fun y : FarProfilePoint => fun t => M.complex (-farHighOutput y) t l
  have exactness := cutoffGuardedFarProfile_eq_signed_weightedNumerator hSym hκ
    (mul_pos hb (pow_pos hδ 2)) ϑ δ hp hq hr hSum hGap
    (normalizedPhysicalCubicNumerator orderedMetricDirection G a H J L)
  have numerator := physicalCubicNumerator_eq_normalized_on_lowSlot orderedMetricDirection G a
    hodd hscale ha hκ' hSum hp hq hLow H J L
  have ⟨left, middle, right⟩ := farAngularColumns_eq_physical M hSum hp hq
  have hNum : physicalCubicNumerator orderedMetricDirection G a p (H x) q (J x) r (L x) =
      physicalCubicNumerator orderedMetricDirection G a
          p (fun t => M.complex p t k) q (fun t => M.complex q t j) r (fun t => M.complex r t l) := by
    dsimp only [H, J, L, x]
    rw [left, middle, right]
  rw [← hNum, numerator]
  simpa only [actualThinFarCubicCorrection, farPhysicalCubicCorrection, mul_assoc] using exactness

end Burnett.V10
