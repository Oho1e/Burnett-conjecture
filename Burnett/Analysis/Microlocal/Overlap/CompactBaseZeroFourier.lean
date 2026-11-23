import Burnett.Analysis.Microlocal.Overlap.BaseFourierAction
import Burnett.Analysis.PrincipalEnergy.Quantization.NormalizedBaseIdentification

set_option autoImplicit false
set_option maxHeartbeats 1400000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Function MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.SeparablePositive (separableOperator)
open scoped ComplexConjugate ContDiff FourierTransform InnerProduct

/-- Fourier transform in the base variable, with the original frequency
held fixed. -/
def baseFourierCoefficient (p : E → E → ℂ) (k ξ : E) : ℂ :=
  (𝓕 (fun y => p y ξ)) k

/-- Base continuity and angular continuity away from the origin imply
joint measurability, with arbitrary values on the zero-frequency section. -/
theorem measurable_baseAngularSymbol {p : E → E → ℂ}
    (hBase : ∀ ξ, Continuous (fun x => p x ξ))
    (hAngular : ∀ x, ContinuousOn (p x) ({0}ᶜ : Set E)) :
    Measurable (uncurry p) :=
  measurable_uncurry_of_continuous_of_measurable hBase
    (fun x => measurable_of_continuousOn_compl_singleton 0 (hAngular x))

theorem measurable_baseFourierCoefficient {p : E → E → ℂ}
    (hp : Measurable (uncurry p)) : Measurable (uncurry (baseFourierCoefficient p)) := by
  let G (q : (E × E) × E) := baseFourierPhase (-q.1.1) q.2 * p q.2 q.1.2
  have hPhase : Continuous (fun q : (E × E) × E => baseFourierPhase (-q.1.1) q.2) :=
    baseFourierPhase_continuous_apply
      (a := fun q : (E × E) × E => -q.1.1) (b := Prod.snd)
      ((continuous_fst.comp continuous_fst).neg) continuous_snd
  have hP : Measurable (fun q : (E × E) × E => p q.2 q.1.2) :=
    hp.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hG : Measurable G := hPhase.measurable.mul hP
  have hInt := (hG.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure E))).measurable
  convert hInt using 1
  funext q
  change (𝓕 (fun y => p y q.2)) q.1 = ∫ x, G (q, x)
  rw [Real.fourierIntegral_eq']
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [G, baseFourierPhase]
  rw [smul_eq_mul, inner_neg_left, real_inner_comm x q.1]
  congr 2
  ring

/-- Uniform pure base derivative bounds at order zero enter the existing
compact-base API after multiplication by its fixed frequency weight. -/
theorem compactBaseOrderOne_frequencyWeight {p : E → E → ℂ}
    (hSupport : ∃ K : Set E, IsCompact K ∧ ∀ ξ, tsupport (fun x => p x ξ) ⊆ K)
    (hSmooth : ∀ ξ, ContDiff ℝ ∞ (fun x => p x ξ))
    (hOrder : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => p y ξ) x‖ ≤ C) :
    CompactBaseOrderOne (fun x ξ => (1 + ‖ξ‖) • p x ξ) where
  support := by
    obtain ⟨K, hK, h⟩ := hSupport
    refine ⟨K, hK, fun ξ => ?_⟩
    exact (closure_mono (Function.support_const_smul_subset _ _)).trans (h ξ)
  smooth ξ := (hSmooth ξ).const_smul _
  order n := by
    obtain ⟨C, hC, h⟩ := hOrder n
    refine ⟨C, hC, fun x ξ => ?_⟩
    have hs : ContDiffAt ℝ n (fun y => p y ξ) x :=
      (hSmooth ξ).contDiffAt.of_le (by exact_mod_cast le_top)
    change ‖iteratedFDeriv ℝ n ((1 + ‖ξ‖) • (fun y => p y ξ)) x‖ ≤ C * (1 + ‖ξ‖)
    rw [iteratedFDeriv_const_smul_apply hs, norm_smul,
      Real.norm_of_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖)]
    exact (mul_le_mul_of_nonneg_left (h x ξ) (by positivity)).trans_eq (mul_comm _ _)

private theorem normalizedBaseSymbol_frequencyWeight_eq (p : E → E → ℂ) :
    normalizedBaseSymbol (fun x ξ => (1 + ‖ξ‖) • p x ξ) = p := by
  funext x ξ
  rw [normalizedBaseSymbol, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

private theorem normalizedBaseFourier_frequencyWeight_eq (p : E → E → ℂ) :
    normalizedBaseFourier (fun x ξ => (1 + ‖ξ‖) • p x ξ) =
      baseFourierCoefficient p := by
  funext k ξ
  unfold normalizedBaseFourier baseFourierCoefficient
  rw [normalizedBaseSymbol_frequencyWeight_eq]

theorem baseFourierCoefficient_inverse {p : E → E → ℂ}
    (hBase : CompactBaseOrderOne (fun x ξ => (1 + ‖ξ‖) • p x ξ)) (x ξ : E) :
    (𝓕⁻ (fun k => baseFourierCoefficient p k ξ)) x = p x ξ := by
  simpa only [normalizedBaseFourier_frequencyWeight_eq, normalizedBaseSymbol_frequencyWeight_eq]
    using normalizedBaseFourier_inverse hBase x ξ

/-- A common integrable envelope for all frequency sections, in the
actual unweighted base Fourier coefficients. -/
theorem baseFourierCoefficient_dominated {p : E → E → ℂ}
    (hBase : CompactBaseOrderOne (fun x ξ => (1 + ‖ξ‖) • p x ξ)) :
    ∃ C : ℝ, 0 < C ∧ Integrable (fun k : E => C * ((1 + ‖k‖ ^ 2) ^ 3)⁻¹) ∧
      ∀ k ξ, ‖baseFourierCoefficient p k ξ‖ ≤ C * ((1 + ‖k‖ ^ 2) ^ 3)⁻¹ := by
  simpa only [normalizedBaseFourier_frequencyWeight_eq] using normalizedBaseFourier_dominated hBase

/-- The actual base Fourier section as a bounded multiplier, with its
same uniform envelope serving as the bound. -/
def baseFourierCoefficientSymbol (p : E → E → ℂ) (hp : Measurable (uncurry p))
    (b : E → ℝ) (hb : ∀ k ξ, ‖baseFourierCoefficient p k ξ‖ ≤ b k) (k : E) :
    BoundedSymbol E where
  toFun := baseFourierCoefficient p k
  measurable :=
    ((measurable_baseFourierCoefficient hp).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  bound := b k
  bound_nonneg := (norm_nonneg _).trans (hb k 0)
  norm_le := hb k

/-- The actual Fourier coefficients of a compact-base zero-order symbol
realize its left Fourier pairings. Joint measurability suffices at the
original zero frequency. -/
theorem exists_compactBaseZero_leftFourier_pairing {p : E → E → ℂ}
    (hBase : CompactBaseOrderOne (fun x ξ => (1 + ‖ξ‖) • p x ξ))
    (hp : Measurable (uncurry p)) :
    ∃ b : E → ℝ, ∃ hb : ∀ k ξ, ‖baseFourierCoefficient p k ξ‖ ≤ b k,
      Integrable b ∧ ∀ f v : SchwartzMap E ℂ,
        let m := baseFourierCoefficientSymbol p hp b hb
        let P (k : E) := inner ℂ (v.toLp 2 volume)
          (separableOperator (baseFourierPhaseSymbol k) (m k) (f.toLp 2 volume))
        Integrable P ∧
          (∫ x, conj (v x) * firstOrderAction p f x) = ∫ k, P k := by
  obtain ⟨C, _, hI, hB⟩ := baseFourierCoefficient_dominated hBase
  let b (k : E) := C * ((1 + ‖k‖ ^ 2) ^ 3)⁻¹
  let m := baseFourierCoefficientSymbol p hp b hB
  refine ⟨b, hB, hI, fun f v => ?_⟩
  exact firstOrderAction_pairing_eq_integral_separable_baseFourier
    p m (measurable_baseFourierCoefficient hp) b hI (fun _ => le_rfl)
    (baseFourierCoefficient_inverse hBase) f v

/-- The separated representation for a compactly based angular symbol
from its uniform pure base bounds and continuity in the nonzero direction. -/
theorem exists_compactBaseAngular_leftFourier_pairing {p : E → E → ℂ}
    (hSupport : ∃ K : Set E, IsCompact K ∧ ∀ ξ, tsupport (fun x => p x ξ) ⊆ K)
    (hSmooth : ∀ ξ, ContDiff ℝ ∞ (fun x => p x ξ))
    (hOrder : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => p y ξ) x‖ ≤ C)
    (hAngular : ∀ x, ContinuousOn (p x) ({0}ᶜ : Set E)) :
    ∃ (m : E → BoundedSymbol E) (b : E → ℝ), Integrable b ∧
      (∀ k, (m k).bound = b k) ∧ (∀ k ξ, m k ξ = baseFourierCoefficient p k ξ) ∧
      ∀ f v : SchwartzMap E ℂ,
        let P (k : E) := inner ℂ (v.toLp 2 volume)
          (separableOperator (baseFourierPhaseSymbol k) (m k) (f.toLp 2 volume))
        Integrable P ∧ (∫ x, conj (v x) * firstOrderAction p f x) = ∫ k, P k := by
  have hBase := compactBaseOrderOne_frequencyWeight hSupport hSmooth hOrder
  let hp := measurable_baseAngularSymbol (fun ξ => (hSmooth ξ).continuous) hAngular
  obtain ⟨b, hB, hI, hP⟩ := exists_compactBaseZero_leftFourier_pairing hBase hp
  exact ⟨baseFourierCoefficientSymbol p hp b hB, b, hI, fun _ => rfl, fun _ _ => rfl, hP⟩

end Burnett.Microlocal.Overlap
