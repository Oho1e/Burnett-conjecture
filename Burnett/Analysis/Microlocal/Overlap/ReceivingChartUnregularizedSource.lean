import Burnett.Analysis.Microlocal.Overlap.AngularBilateralPrincipal

/-! The bilaterally cut source principal action, before infrared regularization. -/

set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Filter MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol radialCore radialCore_contDiff)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient coeffMul coeffMul_toLp)
open Burnett.Microlocal.SeparablePositive
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped ComplexConjugate ContDiff FourierTransform InnerProduct Topology

open private norm_baseMode_pairing_le inner_coeffMul_left_eq_weightedSlotBase pairing_coeffMul_left
  from Burnett.Analysis.Microlocal.Overlap.AngularBilateralPrincipal

theorem tendsto_angularPrincipal_twoCutoff_difference
    (p : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (hSupport : ∀ ξ, tsupport (fun x => p x ξ) ⊆ S)
    (hJoint : ContDiffOn ℝ ∞ (uncurry p) (univ ×ˢ ({0}ᶜ : Set E)))
    (hZero : ContDiff ℝ ∞ (fun x => p x 0)) (hDegree : ∀ x, DegreeZero (p x))
    (c d : D) (u v : ℕ → SchwartzMap E ℂ) (K : Set E) (hK : IsCompact K)
    (hVS : ∀ n, tsupport (v n : E → ℂ) ⊆ K)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁)
    (hU : ∀ n, ‖(u n).toLp 2 volume‖ ≤ B₁) (hV : ∀ n, ‖(v n).toLp 2 volume‖ ≤ B₂)
    (hw : ∀ w : ComplexL2 E, Tendsto (fun n => inner ℂ w ((v n).toLp 2 volume)) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ x, conj (coeffMul c (u n) x) *
      firstOrderAction p (coeffMul d (v n)) x) -
      (∫ x, conj (u n x) * firstOrderAction
        (fun y ξ => (physicalCoefficient c y * physicalCoefficient d y) * p y ξ) (v n) x))
      atTop (𝓝 0) := by
  let a := physicalCoefficient c
  let b := physicalCoefficient d
  have hSmooth := contDiff_baseAngularSection p hJoint hZero
  have hAngular (x : E) : ContinuousOn (p x) ({0}ᶜ : Set E) :=
    hJoint.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hξ => ⟨mem_univ x, hξ⟩)
  have hOrder := exists_uniform_baseDerivative_of_homogeneousAngular p S hS hSupport hJoint hZero hDegree
  obtain ⟨m, g, hg, hnorm, hcoeff, hP⟩ :=
    exists_compactBaseAngular_leftFourier_pairing ⟨S, hS, hSupport⟩ hSmooth hOrder hAngular
  have hm (k : E) : (m k : E → ℂ) = baseFourierCoefficient p k := funext (hcoeff k)
  have hMBound (k : E) : (m k).bound ≤ 2 * g k := by
    rw [← hnorm k]
    linarith [(m k).bound_nonneg]
  let P (n : ℕ) (k : E) := inner ℂ ((coeffMul c (u n)).toLp 2 volume)
    (separableOperator (baseFourierPhaseSymbol k) (m k) ((coeffMul d (v n)).toLp 2 volume))
  let Q (n : ℕ) (k : E) := inner ℂ ((coeffMul d (coeffMul c (u n))).toLp 2 volume)
    (separableOperator (baseFourierPhaseSymbol k) (m k) ((v n).toLp 2 volume))
  have hPI (n : ℕ) := hP (coeffMul d (v n)) (coeffMul c (u n))
  have hQI (n : ℕ) := hP (v n) (coeffMul d (coeffMul c (u n)))
  have hPoint (k : E) : Tendsto (fun n => P n k - Q n k) atTop (𝓝 0) := by
    have hQ (n : ℕ) : Q n k = inner ℂ ((u n).toLp 2 volume)
        (separableOperator (weightedSlotBaseSymbol (baseFourierPhaseSymbol k) a b) (m k)
          ((v n).toLp 2 volume)) :=
      inner_coeffMul_left_eq_weightedSlotBase c d (baseFourierPhaseSymbol k) (m k) (u n) (v n)
    have hSmoothM : ContDiffOn ℝ ∞ (m k : E → ℂ) ({0}ᶜ : Set E) := by
      rw [hm]
      exact contDiffOn_baseFourierCoefficient p S hS hSupport hJoint k
    have hDegreeM : DegreeZero (m k : E → ℂ) := by
      rw [hm]
      exact degreeZero_baseFourierCoefficient hDegree k
    have H := weightedSlot_sum_pairing_difference_tendsto_zero (I := Unit) (J := Unit)
      (baseFourierPhaseSymbol k) (m k) (m k) hSmoothM hDegreeM 2
      (fun _ _ => rfl) (fun _ => a) (fun _ => b)
      (fun _ => Complex.ofRealCLM.contDiff.comp (test_smooth d))
      (fun _ => (test_compactSupport d).comp_left Complex.ofReal_zero) K hK
      (fun n _ => (u n).toLp 2 volume) (fun n _ => v n) (fun n _ => hVS n)
      B₁ B₂ hB₁ (fun n _ => hU n) (fun n _ => hV n) (fun _ => hw)
    simpa only [P, hQ, coeffMul_toLp, Fintype.sum_unique, a, b] using H
  have hUC (n : ℕ) : ‖(coeffMul c (u n)).toLp 2 volume‖ ≤ a.bound * B₁ := by
    rw [coeffMul_toLp]
    exact (symbolL2_norm_le a _).trans (mul_le_mul_of_nonneg_left (hU n) a.bound_nonneg)
  have hVD (n : ℕ) : ‖(coeffMul d (v n)).toLp 2 volume‖ ≤ b.bound * B₂ := by
    rw [coeffMul_toLp]
    exact (symbolL2_norm_le b _).trans (mul_le_mul_of_nonneg_left (hV n) b.bound_nonneg)
  have hUCD (n : ℕ) : ‖(coeffMul d (coeffMul c (u n))).toLp 2 volume‖ ≤ b.bound * (a.bound * B₁) := by
    rw [coeffMul_toLp]
    exact (symbolL2_norm_le b _).trans (mul_le_mul_of_nonneg_left (hUC n) b.bound_nonneg)
  let C := (a.bound * B₁) * (b.bound * B₂)
  have hDCT : Tendsto (fun n => ∫ k, P n k - Q n k) atTop (𝓝 (∫ _ : E, (0 : ℂ))) := by
    apply tendsto_integral_of_dominated_convergence (bound := fun k => (3 * C) * g k)
      (fun n => (hPI n).1.aestronglyMeasurable.sub (hQI n).1.aestronglyMeasurable) (hg.const_mul _)
    · intro n
      filter_upwards with k
      have hNonneg : 0 ≤ g k := hnorm k ▸ (m k).bound_nonneg
      have hPn : ‖P n k‖ ≤ 2 * C * g k := by
        calc
          _ ≤ (a.bound * B₁) * ((2 * g k) * (b.bound * B₂)) :=
            (norm_baseMode_pairing_le _ _ _ _).trans (mul_le_mul (hUC n)
              (mul_le_mul (hMBound k) (hVD n) (norm_nonneg _) (mul_nonneg (by norm_num) hNonneg))
              (mul_nonneg (m k).bound_nonneg (norm_nonneg _)) (mul_nonneg a.bound_nonneg hB₁))
          _ = _ := by ring
      have hQn : ‖Q n k‖ ≤ C * g k := by
        calc
          _ ≤ (b.bound * (a.bound * B₁)) * (g k * B₂) :=
            (norm_baseMode_pairing_le _ _ _ _).trans (mul_le_mul (hUCD n)
              (mul_le_mul (le_of_eq (hnorm k)) (hV n) (norm_nonneg _) hNonneg)
              (mul_nonneg (m k).bound_nonneg (norm_nonneg _))
              (mul_nonneg b.bound_nonneg (mul_nonneg a.bound_nonneg hB₁)))
          _ = _ := by ring
      calc
        _ ≤ ‖P n k‖ + ‖Q n k‖ := norm_sub_le _ _
        _ ≤ 2 * C * g k + C * g k := add_le_add hPn hQn
        _ = _ := by ring
    · exact Eventually.of_forall hPoint
  have hEq (n : ℕ) : (∫ k, P n k - Q n k) =
      (∫ x, conj (coeffMul c (u n) x) * firstOrderAction p (coeffMul d (v n)) x) -
        (∫ x, conj (u n x) * firstOrderAction
          (fun y ξ => (a y * b y) * p y ξ) (v n) x) := by
    rw [integral_sub (hPI n).1 (hQI n).1, ← (hPI n).2, ← (hQI n).2, pairing_coeffMul_left]
  simpa only [integral_zero, hEq, a, b] using hDCT

end Burnett.Microlocal.Overlap
