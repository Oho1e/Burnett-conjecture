import Burnett.Analysis.TransportPatches.ActualWideScreenLipschitz
import Burnett.Analysis.TransportPatches.ScreenFixedSupport
import Burnett.Analysis.TransportPatches.IntrinsicProjectedSupport

/-! Two actual C02 principal errors on the original Ricci range. -/

set_option autoImplicit false
set_option maxRecDepth 4800
set_option maxHeartbeats 6200000

noncomputable section

namespace Burnett.C02

open Set Matrix Burnett.Geometry Burnett.RicciSymbol Burnett.V06 TensorFrame
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere hamiltonian projection)
open Burnett.Microlocal.Overlap
open Burnett.P01 (principalGaugeProjection)
open Burnett.Analysis.ProjectiveNullCaps (quadratic)
open scoped BigOperators ContDiff Matrix Manifold

open private symbolNorm_unit_eq from Burnett.Analysis.TransportPatches.ScreenGlobalCutoffSupport
open private chartInverseMetric_isUnit chartInverseMetric_has_frame from Burnett.Analysis.TransportPatches.ActualWideScreenLipschitz

local notation "E" => CoordinateSpace

/-- The wide screen in the actual complex Fourier components. -/
def complexWideScreen (inner outer : ℝ) (B : ScreenMatrix) (H : ComplexTensor2)
    (q : Covector) : ComplexTensor2 :=
  fun i j => ⟨globalAngularScreenSymbol inner outer B (tensorRe H) q i j,
    globalAngularScreenSymbol inner outer B (tensorIm H) q i j⟩

theorem normalizedFrozenPhase_eq_unitPhase (B : Tensor2) (ξ : E) :
    normalizedFrozenPhase B ξ = symbolNorm B (screenUnitCovector (fun i : Index => ξ i)) := by
  rw [normalizedFrozenPhase, quadratic_eq_symbolNorm, symbolNorm_unit_eq, PiLp.norm_sq_eq_of_L2]
  simp only [dotProduct, Real.norm_eq_abs, sq_abs, ← pow_two]

private theorem norm_tensorRe_le (H : ComplexTensor2) : ‖tensorRe H‖ ≤ ‖H‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg H)).2
  intro i
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg H)).2
  intro j
  exact (Complex.abs_re_le_norm (H i j)).trans
    ((norm_le_pi_norm (H i) j).trans (norm_le_pi_norm H i))

private theorem norm_tensorIm_le (H : ComplexTensor2) : ‖tensorIm H‖ ≤ ‖H‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg H)).2
  intro i
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg H)).2
  intro j
  exact (Complex.abs_im_le_norm (H i j)).trans
    ((norm_le_pi_norm (H i) j).trans (norm_le_pi_norm H i))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- This estimate is uniform in direction and in the input on the true
projected null Ricci range of the variable background. -/
theorem exists_actualFrozenScreen_phase_errors {r : Metric (M := M)}
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target) :
    ∃ inner outer L C : ℝ, 0 < inner ∧ inner < outer ∧ 0 ≤ L ∧ 0 ≤ C ∧
      ∀ x₀ ∈ K, ∀ p : Cosphere r, projection p ∈ c.chart.source →
        c.chart (projection p) ∈ K → hamiltonian B hSig.isNondegenerate p = 0 →
        ∀ ℓ : ℝ, ‖c.chart (projection p) - x₀‖ ≤ ℓ → ℓ ≤ 1 →
        ∀ k : ComplexTensor2, IsSymmetricComplexTensor k →
        (∀ a b, complexRicciSymbol (chartInverseMetric B c (c.chart (projection p)))
          (atlasChartUnitCovector c p) k a b = 0) →
        let m := chartInverseMetric B c x₀
        let q := atlasChartUnitCovector c p
        let ξ : E := WithLp.toLp 2 q
        let J : ComplexTensor2 := principalGaugeProjection ξ k
        let S := complexWideScreen inner outer m J q
        ‖J - S‖ ≤ C * ℓ * ‖J‖ ∧
        ‖(normalizedFrozenPhase m ξ : ℂ) • S‖ ≤ C * ℓ * ‖J‖ ∧
        (L * ℓ ≤ inner → angularScreenCutoff inner outer (normalizedFrozenPhase m ξ) = 1) := by
  obtain ⟨inner, outer, C₀, hInner, hIO, hC, hScreen⟩ :=
    exists_actualWideScreen_chart_lipschitz B hB hSig c K hK hConv hKU
  obtain ⟨L, hL, hPhase⟩ :=
    exists_actualNull_frozenPhaseAndThinCone (r := r) B hB hSig.isSymmetric hSig.isNondegenerate c K hK hConv hKU
  let C := max (2 * C₀) (L * (1 + 2 * C₀))
  have hC2 : 0 ≤ 2 * C₀ := mul_nonneg (by norm_num) hC
  refine ⟨inner, outer, L, C, hInner, hIO, hL, hC2.trans (le_max_left _ _), ?_⟩
  intro x₀ hx₀ p hp hx hNull ℓ hℓ hℓ₁ k hSym hRic m q ξ J S
  let x := c.chart (projection p)
  let G := chartInverseMetric B c x
  have hℓ₀ : 0 ≤ ℓ := (norm_nonneg _).trans hℓ
  have hq : q ≠ 0 := atlasChartUnitCovector_ne_zero c p hp
  have hPhaseBound : |normalizedFrozenPhase m ξ| ≤ L * ℓ :=
    (hPhase x₀ hx₀ p hp hx hNull ℓ hℓ).1
  have hGNull : symbolNorm G q = 0 := by
    have h := actualNull_chart_quadratic B hSig.isSymmetric hSig.isNondegenerate c p hp hNull
    rwa [quadratic_eq_symbolNorm] at h
  have hUnitNull : |symbolNorm G (screenUnitCovector q)| ≤ inner := by
    rw [symbolNorm_unit_eq, hGNull, zero_div, abs_zero]
    exact hInner.le
  obtain ⟨frame⟩ := chartInverseMetric_has_frame B hSig c (hKU hx)
  have hAtX : complexWideScreen inner outer G J q = J := by
    have hFix := complexFrozenScreen_fixes_projected_nullRicciKernel G frame
      (chartInverseMetric_isUnit B hSig.isNondegenerate c (hKU hx)) ξ k hSym hq hGNull hRic
    change complexFrozenScreen G J q = J at hFix
    unfold complexWideScreen
    rw [globalAngularScreenSymbol_eq_on_inner inner outer hInner.le hIO G (tensorRe J) q hUnitNull,
      globalAngularScreenSymbol_eq_on_inner inner outer hInner.le hIO G (tensorIm J) q hUnitNull]
    exact hFix
  let R (z : E) : Tensor2 := globalAngularScreenSymbol inner outer (chartInverseMetric B c z) (tensorRe J) q
  let I (z : E) : Tensor2 := globalAngularScreenSymbol inner outer (chartInverseMetric B c z) (tensorIm J) q
  have hR : ‖R x - R x₀‖ ≤ C₀ * ‖x - x₀‖ * ‖tensorRe J‖ :=
    hScreen x hx x₀ hx₀ (tensorRe J) q hq
  have hI : ‖I x - I x₀‖ ≤ C₀ * ‖x - x₀‖ * ‖tensorIm J‖ :=
    hScreen x hx x₀ hx₀ (tensorIm J) q hq
  have hE₁ : ‖J - S‖ ≤ (2 * C₀) * ℓ * ‖J‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hC2 hℓ₀) (norm_nonneg J))).2
    intro i
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hC2 hℓ₀) (norm_nonneg J))).2
    intro j
    have hRj : |((J - S) i j).re| ≤ C₀ * ℓ * ‖J‖ := by
      have hJ : (J i j).re = R x i j := congrArg (fun H : ComplexTensor2 => (H i j).re) hAtX.symm
      change |(J i j).re - (S i j).re| ≤ _
      rw [hJ]
      change ‖(R x - R x₀) i j‖ ≤ _
      exact ((norm_le_pi_norm ((R x - R x₀) i) j).trans (norm_le_pi_norm (R x - R x₀) i)).trans
        (hR.trans (mul_le_mul (mul_le_mul_of_nonneg_left hℓ hC) (norm_tensorRe_le J)
          (norm_nonneg _) (mul_nonneg hC hℓ₀)))
    have hIj : |((J - S) i j).im| ≤ C₀ * ℓ * ‖J‖ := by
      have hJ : (J i j).im = I x i j := congrArg (fun H : ComplexTensor2 => (H i j).im) hAtX.symm
      change |(J i j).im - (S i j).im| ≤ _
      rw [hJ]
      change ‖(I x - I x₀) i j‖ ≤ _
      exact ((norm_le_pi_norm ((I x - I x₀) i) j).trans (norm_le_pi_norm (I x - I x₀) i)).trans
        (hI.trans (mul_le_mul (mul_le_mul_of_nonneg_left hℓ hC) (norm_tensorIm_le J)
          (norm_nonneg _) (mul_nonneg hC hℓ₀)))
    exact (Complex.norm_le_abs_re_add_abs_im _).trans ((add_le_add hRj hIj).trans_eq (by ring))
  have hS : ‖S‖ ≤ (1 + 2 * C₀) * ‖J‖ := calc
    ‖S‖ = ‖J - (J - S)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖J‖ + ‖J - S‖ := norm_sub_le _ _
    _ ≤ ‖J‖ + (2 * C₀) * ℓ * ‖J‖ := add_le_add_left hE₁ _
    _ ≤ (1 + 2 * C₀) * ‖J‖ := by
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓ₁ hC2) (norm_nonneg J)
      rw [mul_one] at h
      linarith
  refine ⟨hE₁.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hℓ₀) (norm_nonneg J)), ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |normalizedFrozenPhase m ξ| * ‖S‖ ≤ (L * ℓ) * ((1 + 2 * C₀) * ‖J‖) :=
        mul_le_mul hPhaseBound hS (norm_nonneg _) (mul_nonneg hL hℓ₀)
      _ = (L * (1 + 2 * C₀)) * ℓ * ‖J‖ := by ring
      _ ≤ C * ℓ * ‖J‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hℓ₀) (norm_nonneg J)
  · intro hSmall
    exact angularScreenCutoff_one inner outer _ hInner.le hIO (hPhaseBound.trans hSmall)

end Burnett.C02
