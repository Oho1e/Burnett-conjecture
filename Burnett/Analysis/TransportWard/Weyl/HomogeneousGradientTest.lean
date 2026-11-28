import Burnett.Analysis.TransportWard.Weyl.RegularizedGradientSymbol
import Burnett.Analysis.Microlocal.Overlap.CompactAngularBaseBounds
import Burnett.Analysis.TransportWard.Weyl.RadianParameterWeights
import Burnett.Analysis.Microlocal.Overlap.BaseFourierAngularRegularity

set_option autoImplicit false
set_option maxHeartbeats 2100000
set_option maxRecDepth 2000

noncomputable section

namespace Burnett.V03

open Burnett.A03 (RadianParameter radianFrequencyWeight radian_frequency_weight_pos)


open Function Set Burnett.A02.FrequencySplit
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.Overlap (contDiff_baseAngularSection exists_uniform_baseDerivative_of_homogeneousAngular)
open scoped ContDiff

/-- Divide the homogeneous Poisson symbol by precisely the squared norm
reconstructed by the four actual derivative test slots. -/
def homogeneousGradientTest (p : E → E → ℂ) (x ξ : E) : ℂ :=
  ((‖ξ‖^2 : ℝ) : ℂ)⁻¹ * p x ξ

theorem homogeneousGradientTest_zero (p : E → E → ℂ) (x : E) :
    homogeneousGradientTest p x 0 = 0 := by
  simp [homogeneousGradientTest]

theorem homogeneousGradientTest_degreeZero {p : E → E → ℂ}
    (h : ∀ x (s : ℝ), 0 < s → ∀ ξ ≠ 0, p x (s • ξ) = (s : ℂ)^2 * p x ξ)
    (x : E) : DegreeZero (homogeneousGradientTest p x) := by
  intro s hs ξ
  by_cases hξ : ξ = 0
  · rw [hξ, smul_zero]
  have hsc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  rw [homogeneousGradientTest, homogeneousGradientTest, h x s hs ξ hξ, norm_smul,
    Real.norm_of_nonneg hs.le,mul_pow,Complex.ofReal_mul,Complex.ofReal_pow,mul_inv_rev]
  calc
    _ = ((‖ξ‖^2 : ℝ) : ℂ)⁻¹ * (((s : ℂ)^2)⁻¹ * (s : ℂ)^2) * p x ξ := by ring
    _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero 2 hsc),mul_one]

theorem homogeneousGradientTest_smooth {p : E → E → ℂ}
    (hs : ContDiffOn ℝ ∞ (uncurry p) (univ ×ˢ ({0}ᶜ : Set E))) :
    ContDiffOn ℝ ∞ (uncurry (homogeneousGradientTest p)) (univ ×ˢ ({0}ᶜ : Set E)) := by
  have hN : ContDiff ℝ ∞ (fun z : E × E => ((‖z.2‖^2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_norm_sq ℝ).comp contDiff_snd)
  have hn : ∀ z ∈ (univ : Set E) ×ˢ ({0}ᶜ : Set E), ((‖z.2‖^2 : ℝ) : ℂ) ≠ 0 :=
    fun _ hz => Complex.ofReal_ne_zero.mpr
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz.2))
  exact (hN.contDiffOn.inv hn).mul hs

theorem homogeneousGradientTest_support {p : E → E → ℂ} {K : Set E}
    (hK : IsCompact K) (h : ∀ x ∉ K, ∀ ξ, p x ξ = 0) (ξ : E) :
    tsupport (fun x => homogeneousGradientTest p x ξ) ⊆ K := by
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hOut
  exact hx (by simp only [homogeneousGradientTest,h x hOut ξ,mul_zero])

private theorem regularizedGradientSymbol_sub_homogeneous_value {p pHom : E → E → ℂ}
    (ξ : E) (hξ : ξ ≠ 0) (h : ∀ y, p y ξ = (tau : ℂ)^2 * pHom y ξ) :
    (fun x => regularizedGradientSymbol p x ξ - homogeneousGradientTest pHom x ξ) =
      fun x => -((1 + squaredRadianLength ξ : ℝ) : ℂ)⁻¹ * homogeneousGradientTest pHom x ξ := by
  let t : ℂ := tau
  let N : ℂ := (‖ξ‖^2 : ℝ)
  have hR : ((squaredRadianLength ξ : ℝ) : ℂ) = t^2 * N := by
    rw [squaredRadianLength_eq, mul_pow,Complex.ofReal_mul,Complex.ofReal_pow]
  have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ))
  have hden : 1 + t^2 * N ≠ 0 := by
    rw [← hR, ← Complex.ofReal_one, ← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (by rw [squaredRadianLength_eq]; positivity)
  funext x
  rw [regularizedGradientSymbol,homogeneousGradientTest,h x,Complex.ofReal_add,Complex.ofReal_one,hR]
  change (1 + t^2 * N)⁻¹ * (t^2 * pHom x ξ) - N⁻¹ * pHom x ξ =
    -(1 + t^2 * N)⁻¹ * (N⁻¹ * pHom x ξ)
  field_simp [hN,hden]
  ring

/-- At high frequency the regularized gradient action and the homogeneous
angular principal differ by a symbol with at least one full power of decay. -/
theorem regularizedGradientSymbol_classical_tail {p pHom : E → E → ℂ} {K : Set E}
    (hK : IsCompact K) (hSupport : ∀ x ∉ K, ∀ ξ, pHom x ξ = 0)
    (hs : ContDiffOn ℝ ∞ (uncurry pHom) (univ ×ˢ ({0}ᶜ : Set E)))
    (hh : ∀ x (s : ℝ), 0 < s → ∀ ξ ≠ 0, pHom x (s • ξ) = (s : ℂ)^2 * pHom x ξ)
    (R : ℝ) (hTail : ∀ x ξ, R ≤ ‖ξ‖ → p x ξ = (tau : ℂ)^2 * pHom x ξ) :
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ, max 1 R ≤ ‖ξ‖ →
      (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n
        (fun y => regularizedGradientSymbol p y ξ - homogeneousGradientTest pHom y ξ) x‖ ≤ C := by
  intro n
  let a := homogeneousGradientTest pHom
  have ha := homogeneousGradientTest_smooth hs
  have hZero : ContDiff ℝ ∞ (fun x => a x 0) := by
    rw [show (fun x => a x 0) = fun _ => 0 from funext (homogeneousGradientTest_zero pHom)]
    exact contDiff_const
  obtain ⟨C,hC,hB⟩ := exists_uniform_baseDerivative_of_homogeneousAngular a K hK
    (homogeneousGradientTest_support hK hSupport) ha hZero (homogeneousGradientTest_degreeZero hh) n
  refine ⟨C,hC,fun x ξ hHigh => ?_⟩
  have hl : 1 ≤ ‖ξ‖ := (le_max_left _ _).trans hHigh
  have hξ : ξ ≠ 0 := by
    intro h
    rw [h,norm_zero] at hl
    exact (by norm_num : ¬ (1 : ℝ) ≤ 0) hl
  have he := regularizedGradientSymbol_sub_homogeneous_value ξ hξ
    (fun y => hTail y ξ ((le_max_right _ _).trans hHigh))
  let c : ℂ := -((1 + squaredRadianLength ξ : ℝ) : ℂ)⁻¹
  have hd : ContDiff ℝ ∞ (fun y => a y ξ) := contDiff_baseAngularSection a ha hZero ξ
  rw [he]
  change (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => c • a y ξ) x‖ ≤ C
  rw [iteratedFDeriv_const_smul_apply' (hd.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))),
    norm_smul, ← mul_assoc]
  have hτ : 1 ≤ tau := by
    change 1 ≤ 2 * Real.pi
    linarith only [Real.two_le_pi]
  have hr := le_mul_of_one_le_left (norm_nonneg ξ) hτ
  have hN : ‖ξ‖ ≤ squaredRadianLength ξ := by
    rw [squaredRadianLength_eq]
    exact (le_self_pow₀ hl (by norm_num : 2 ≠ 0)).trans (pow_le_pow_left₀ (norm_nonneg ξ) hr 2)
  have hc : (1 + ‖ξ‖) * ‖c‖ ≤ 1 := by
    have hD : 0 < 1 + squaredRadianLength ξ := by rw [squaredRadianLength_eq]; positivity
    simp only [c,norm_neg,norm_inv,Complex.norm_real,Real.norm_of_nonneg hD.le,← div_eq_mul_inv]
    exact (div_le_one hD).mpr (add_le_add_left hN 1)
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (hB x ξ)

end Burnett.V03
