import Burnett.Analysis.TransportWard.Weyl.CompactBaseZeroDerivative
import Burnett.Analysis.TransportWard.Weyl.RegularizedGradientSymbol
import Burnett.Analysis.TransportWard.Weyl.WeylGradientPairing
import Burnett.Analysis.TransportWard.Weyl.HomogeneousGradientTest
import Burnett.Analysis.Microlocal.Overlap.CompactAngularBaseBounds
import Burnett.Analysis.TransportWard.Weyl.RadianParameterWeights

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 2300

noncomputable section

namespace Burnett.V03

open Burnett.A03 (RadianParameter radianFrequencyWeight radian_frequency_weight_pos)


open Function Set Metric Burnett.A02.FrequencySplit
open Burnett.Analysis.CarlesonEmbedding (contDiff_firstPartialJet)
open Burnett.Microlocal.Overlap (contDiff_baseAngularSection exists_uniform_baseDerivative_of_homogeneousAngular)
open scoped ContDiff

private theorem quadraticSymbol_eq_norm_sq_mul_homogeneousGradientTest
    (p : E → E → ℂ) (x ξ : E) (hξ : ξ ≠ 0) :
    p x ξ = ((‖ξ‖^2 : ℝ) : ℂ) * homogeneousGradientTest p x ξ := by
  have ht : ((‖ξ‖^2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ))
  rw [homogeneousGradientTest,← mul_assoc,mul_inv_cancel₀ ht,one_mul]

/-- A globally smooth compact-base symbol agreeing with its homogeneous
quadratic part above a fixed radius has every pure base derivative of
order two. The proof uses the same zero-order angular principal family. -/
theorem BaseDerivativeBounds.of_quadratic_classical_tail {p pHom : E → E → ℂ} {K : Set E}
    (hK : IsCompact K) (hS : ∀ x ∉ K, ∀ ξ, p x ξ = 0)
    (hHomS : ∀ x ∉ K, ∀ ξ, pHom x ξ = 0)
    (hs : ContDiff ℝ ∞ (uncurry p))
    (hHomDiff : ContDiffOn ℝ ∞ (uncurry pHom) (univ ×ˢ ({0}ᶜ : Set E)))
    (hHomDegree : ∀ x (s : ℝ), 0 < s → ∀ ξ ≠ 0, pHom x (s • ξ) = (s : ℂ)^2 * pHom x ξ)
    (R : ℝ) (hTail : ∀ x ξ, R ≤ ‖ξ‖ → p x ξ = (tau : ℂ)^2 * pHom x ξ) :
    BaseDerivativeBounds p (fun ξ => (1 + ‖ξ‖)^2) := by
  let a := homogeneousGradientTest pHom
  have haDiff := homogeneousGradientTest_smooth hHomDiff
  have haZero : ContDiff ℝ ∞ (fun x => a x 0) := by
    rw [show (fun x => a x 0) = fun _ => 0 from funext (homogeneousGradientTest_zero pHom)]
    exact contDiff_const
  let L := max 1 R
  refine ⟨fun ξ => hs.comp (contDiff_id.prodMk contDiff_const),fun n => ?_⟩
  obtain ⟨A,hA,hAngular⟩ := exists_uniform_baseDerivative_of_homogeneousAngular a K hK
    (homogeneousGradientTest_support hK hHomS) haDiff haZero (homogeneousGradientTest_degreeZero hHomDegree) n
  let J (z : E × E) := ‖iteratedFDeriv ℝ n (fun y => p y z.2) z.1‖
  have hJ : Continuous J := (contDiff_firstPartialJet hs n).continuous.norm
  have hCompact : IsCompact (K ×ˢ closedBall (0 : E) L) := hK.prod (isCompact_closedBall 0 L)
  obtain ⟨B,hBound⟩ := (hCompact.image hJ).isBounded.exists_norm_le
  let D := max (tau^2 * A) B
  have hD : 0 ≤ D := (mul_nonneg (sq_nonneg _) hA).trans (le_max_left _ _)
  refine ⟨D,hD,fun x ξ => ?_⟩
  by_cases hHigh : L ≤ ‖ξ‖
  · have hξ : ξ ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le ((le_max_left _ _).trans hHigh))
    have he : (fun y => p y ξ) =
        fun y => (((tau^2 * ‖ξ‖^2 : ℝ) : ℂ)) • a y ξ := by
      funext y
      rw [hTail y ξ ((le_max_right _ _).trans hHigh),
        quadraticSymbol_eq_norm_sq_mul_homogeneousGradientTest pHom y ξ hξ]
      simp only [a,Complex.ofReal_mul,Complex.ofReal_pow,smul_eq_mul,mul_assoc]
    have hAξ : ContDiffAt ℝ n (fun y => a y ξ) x :=
      (contDiff_baseAngularSection a haDiff haZero ξ).contDiffAt.of_le
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
    rw [he,iteratedFDeriv_const_smul_apply' hAξ,norm_smul,Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    calc
      _ ≤ (tau^2 * ‖ξ‖^2) * A := mul_le_mul_of_nonneg_left (hAngular x ξ) (by positivity)
      _ = (tau^2 * A) * ‖ξ‖^2 := by ring
      _ ≤ D * (1+‖ξ‖)^2 := mul_le_mul (le_max_left _ _)
        (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) 2) (sq_nonneg _) hD
  · by_cases hx : x ∈ K
    · have hξ : ξ ∈ closedBall (0 : E) L := by
        simpa only [mem_closedBall,dist_zero_right] using (le_of_not_ge hHigh)
      have hNorm := hBound (J (x,ξ)) (mem_image_of_mem J (show (x,ξ) ∈ K ×ˢ closedBall 0 L from ⟨hx,hξ⟩))
      change J (x,ξ) ≤ D * (1+‖ξ‖)^2
      have hBD : B ≤ D := le_max_right (tau^2 * A) B
      have hOne : 1 ≤ (1+‖ξ‖)^2 := by nlinarith only [norm_nonneg ξ,sq_nonneg ‖ξ‖]
      exact ((le_abs_self (J (x,ξ))).trans hNorm).trans (hBD.trans (le_mul_of_one_le_right hD hOne))
    · have hSupport : tsupport (fun y => p y ξ) ⊆ K :=
        closure_minimal (fun y hy => by by_contra h; exact hy (hS y h ξ)) hK.isClosed
      have hZero : iteratedFDeriv ℝ n (fun y => p y ξ) x = 0 := by
        by_contra h
        exact hx (hSupport (support_iteratedFDeriv_subset n h))
      rw [hZero,norm_zero]
      exact mul_nonneg hD (sq_nonneg _)

end Burnett.V03
