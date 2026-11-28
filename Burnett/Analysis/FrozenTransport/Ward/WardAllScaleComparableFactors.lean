import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer
import Burnett.Analysis.FrozenTransport.Ward.WardAllScalePhaseTransfer

set_option autoImplicit false
set_option maxRecDepth 6500
set_option maxHeartbeats 12500000
noncomputable section

namespace Burnett.C02

open Set Burnett.A05 Burnett.A02.FrequencySplit
open Burnett.RicciSymbol (Tensor2)
open Burnett.V08 (signedCyclicPhase)
open Burnett.Analysis.ProjectiveNullCaps (quadratic)
open scoped ContDiff

open private wardSignedThird_smooth from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer

theorem wardPhaseCovector_contDiff (j : Fin 3) : ContDiff ℝ ∞ (fun x : Joint => wardPhaseCovector x j) := by
  fin_cases j
  · exact contDiff_fst
  · exact contDiff_snd
  · exact wardSignedThird_smooth

theorem wardPhaseCovector_ne_zero (j : Fin 3) {x : Joint} (hx : x ∈ wardTriadDomain) : wardPhaseCovector x j ≠ 0 := by
  fin_cases j
  · exact hx.1
  · exact hx.2.1
  · exact hx.2.2

theorem wardPhaseCovector_smul (t : ℝ) (x : Joint) (j : Fin 3) :
    wardPhaseCovector (t • x) j = t • wardPhaseCovector x j := by
  fin_cases j
  · rfl
  · rfl
  · change -(t • x.1 + t • x.2) = t • (-(x.1+x.2))
    rw [smul_neg, smul_add]

private def wardComparableDenominator (x : Joint) : ℂ :=
  ((‖x.1‖ * ‖x.2‖ * ‖wardSignedThird x‖ : ℝ) : ℂ)

private theorem wardComparableDenominator_ne_zero {x : Joint} (hx : x ∈ wardTriadDomain) :
    wardComparableDenominator x ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (mul_ne_zero (mul_ne_zero (norm_ne_zero_iff.mpr hx.1) (norm_ne_zero_iff.mpr hx.2.1))
    (norm_ne_zero_iff.mpr hx.2.2))

/-- Comparable normalization of `α_a w_m q_m` before putting the last
factor on its own physical slot. -/
def wardComparablePhaseFactor (w : ℝ) (a : E → ℝ) (j : Fin 3) (x : Joint) : ℂ :=
  (signedCyclicPhase a x.1 x.2 : ℂ) * (w : ℂ) * (‖wardPhaseCovector x j‖ : ℂ)^2 / wardComparableDenominator x

theorem wardComparablePhaseFactor_smooth (w : ℝ) (a : E → ℝ) (j : Fin 3)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) :
    ContDiffOn ℝ ∞ (wardComparablePhaseFactor w a j) wardTriadDomain := by
  have hP : ContDiffOn ℝ ∞ (fun x : Joint => a x.1) wardTriadDomain :=
    ha.comp contDiff_fst.contDiffOn (fun _ hx => hx.1)
  have hQ : ContDiffOn ℝ ∞ (fun x : Joint => a x.2) wardTriadDomain :=
    ha.comp contDiff_snd.contDiffOn (fun _ hx => hx.2.1)
  have hR : ContDiffOn ℝ ∞ (fun x : Joint => a (wardSignedThird x)) wardTriadDomain :=
    ha.comp wardSignedThird_smooth.contDiffOn (fun _ hx => hx.2.2)
  have hα : ContDiffOn ℝ ∞ (fun x : Joint => (signedCyclicPhase a x.1 x.2 : ℂ)) wardTriadDomain :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn ((hP.add hQ).add hR)
  have hN (i : Fin 3) : ContDiffOn ℝ ∞ (fun x : Joint => (‖wardPhaseCovector x i‖ : ℂ)) wardTriadDomain :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn ((wardPhaseCovector_contDiff i).contDiffOn.norm ℝ
      (fun _ hx => wardPhaseCovector_ne_zero i hx))
  have hDen : ContDiffOn ℝ ∞ wardComparableDenominator wardTriadDomain := by
    unfold wardComparableDenominator
    push_cast
    exact ((hN 0).mul (hN 1)).mul (hN 2)
  have hInv := hDen.inv (fun _ hx => wardComparableDenominator_ne_zero hx)
  simpa only [wardComparablePhaseFactor, div_eq_mul_inv] using
    (((hα.mul (contDiffOn_const (c := (w : ℂ)))).mul ((hN j).pow 2)).mul hInv)

theorem wardComparablePhaseFactor_homogeneous (w : ℝ) (a : E → ℝ) (j : Fin 3)
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (t : ℝ) (ht : 0 < t) (x : Joint) (hx : x ∈ wardTriadDomain) :
    wardComparablePhaseFactor w a j (t • x) = wardComparablePhaseFactor w a j x := by
  have hα : signedCyclicPhase a (t • x.1) (t • x.2) = t * signedCyclicPhase a x.1 x.2 := by
    simp only [signedCyclicPhase, ← smul_add, ← smul_neg, hHom t ht, mul_add]
  have hN (y : E) : ‖t • y‖ = t * ‖y‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
  have hR : wardSignedThird (t • x) = t • wardSignedThird x := wardPhaseCovector_smul t x 2
  have hD : wardComparableDenominator (t • x) = (t : ℂ)^3 * wardComparableDenominator x := by
    simp only [wardComparableDenominator, Prod.smul_fst, Prod.smul_snd, hR, hN, Complex.ofReal_mul]
    ring
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hDen := wardComparableDenominator_ne_zero hx
  simp only [wardComparablePhaseFactor, Prod.smul_fst, Prod.smul_snd, hα, hD, wardPhaseCovector_smul, hN, Complex.ofReal_mul]
  field_simp

/-- Phase extraction in the literal signed comparable scalar coefficient. -/
theorem wardComparablePhaseFactor_mul_phase (m : Tensor2) (w : ℝ) (a : E → ℝ) (j : Fin 3)
    (x : Joint) (hx : x ∈ wardTriadDomain) :
    wardComparableDenominator x * (wardComparablePhaseFactor w a j x *
        (normalizedFrozenPhase m (wardPhaseCovector x j) : ℂ)) =
      (signedCyclicPhase a x.1 x.2 : ℂ) * (w : ℂ) * (quadratic m (wardPhaseCovector x j) : ℂ) := by
  let ξ := wardPhaseCovector x j
  have hξ : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr (wardPhaseCovector_ne_zero j hx)
  have hQ : (quadratic m ξ : ℂ) = (normalizedFrozenPhase m ξ : ℂ) * (‖ξ‖ : ℂ)^2 := by
    exact_mod_cast (div_eq_iff (pow_ne_zero 2 hξ)).mp (show quadratic m ξ / ‖ξ‖^2 = normalizedFrozenPhase m ξ from rfl)
  change _ = (signedCyclicPhase a x.1 x.2 : ℂ) * (w : ℂ) * (quadratic m ξ : ℂ)
  rw [hQ]
  have hD := wardComparableDenominator_ne_zero hx
  simp only [wardComparablePhaseFactor, ξ]
  field_simp

end Burnett.C02
