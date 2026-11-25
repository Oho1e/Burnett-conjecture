import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalWeakDivergenceCommutator
import Burnett.Analysis.CubicEnergy.AngularCorrection.RadianWavePhase

set_option autoImplicit false
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.A08

open Burnett.A07 Burnett.A06 Burnett.A02.FrequencySplit MeasureTheory Metric Set
open scoped ComplexConjugate ContDiff ENNReal NNReal

open private inner_eq_of_schwartz from Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private abbrev Test := SchwartzMap E ℂ

/-- The Hermitian part of the original correction and its actual high adjoint. -/
def hermitianPartOutput (T S : Test → FirstOrderLp 2) (u : Test) : FirstOrderLp 2 :=
  (1 / 2 : ℂ) • (T u + S u)

private theorem inner_hermitianPartOutput (T S : Test → FirstOrderLp 2) (u w : Test) :
    inner ℂ (w.toLp 2 volume) (hermitianPartOutput T S u) =
      (inner ℂ (w.toLp 2 volume) (T u) + inner ℂ (w.toLp 2 volume) (S u)) / 2 := by
  rw [hermitianPartOutput, inner_smul_right, inner_add_right]
  ring

private theorem inner_hermitianPartOutput_symmetric (T S : Test → FirstOrderLp 2)
    (dual : ∀ u w : Test, inner ℂ (w.toLp 2 volume) (S u) = conj (inner ℂ (u.toLp 2 volume) (T w)))
    (u w : Test) :
    inner ℂ (w.toLp 2 volume) (hermitianPartOutput T S u) =
      inner ℂ (hermitianPartOutput T S w) (u.toLp 2 volume) := by
  rw [← inner_conj_symm (hermitianPartOutput T S w), inner_hermitianPartOutput,
    inner_hermitianPartOutput, dual u w, dual w u]
  have conjTwo : conj (2 : ℂ) = 2 := map_ofNat (starRingEnd ℂ) 2
  simp [map_add, add_comm, conjTwo]

private theorem weakDivergenceCommutatorPair_hermitianPart
    (d : Fin 4 → Fin 4 → SchwartzMap E ℝ) (T S : Test → FirstOrderLp 2)
    (dual : ∀ u w : Test, inner ℂ (w.toLp 2 volume) (S u) = conj (inner ℂ (u.toLp 2 volume) (T w)))
    (u w : Test) :
    weakDivergenceCommutatorPair d (hermitianPartOutput T S) u w =
      (weakDivergenceCommutatorPair d T u w - conj (weakDivergenceCommutatorPair d T w u)) / 2 := by
  unfold weakDivergenceCommutatorPair
  rw [inner_hermitianPartOutput, inner_hermitianPartOutput, dual u (schwartzDivergence d w),
    dual (schwartzDivergence d u) w, map_sub]
  ring

private theorem mul_I_half_sub_conj (z : ℂ) :
    Complex.I * ((z - conj z) / 2) = ((Complex.I * z).re : ℂ) := by
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re]
    ring
  · simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_im]
    ring

/-- Weak testing of the frozen wave commutator with the same L² correction. -/
def weakConstantWaveCommutatorPair (m : Fin 4 → Fin 4 → ℝ)
    (R : Test → FirstOrderLp 2) (u w : Test) : ℂ :=
  inner ℂ ((constantWave m w).toLp 2 volume) (R u) -
    inner ℂ (w.toLp 2 volume) (R (constantWave m u))

private theorem weakConstantWave_energy_eq
    (d : Fin 4 → Fin 4 → SchwartzMap E ℝ) (m : Fin 4 → Fin 4 → ℝ)
    (R : Test → FirstOrderLp 2)
    (symmetric : ∀ u w : Test, inner ℂ (w.toLp 2 volume) (R u) = inner ℂ (R w) (u.toLp 2 volume))
    (u : Test) :
    Complex.I * weakConstantWaveCommutatorPair m R u u =
      ((2 * (inner ℂ (R u) ((constantWave m u + schwartzDivergence d u).toLp 2 volume)).im : ℝ) : ℂ) -
        Complex.I * weakDivergenceCommutatorPair d R u u := by
  have split : (constantWave m u + schwartzDivergence d u).toLp 2 volume =
      (constantWave m u).toLp 2 volume + (schwartzDivergence d u).toLp 2 volume :=
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_add _ _
  rw [weakConstantWaveCommutatorPair, weakDivergenceCommutatorPair, symmetric (constantWave m u) u,
    symmetric (schwartzDivergence d u) u, split, inner_add_right,
    ← inner_conj_symm (R u) ((constantWave m u).toLp 2 volume),
    ← inner_conj_symm (R u) ((schwartzDivergence d u).toLp 2 volume)]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]
    ring
  · simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]
    ring

private theorem sourcePairing_imaginary_bound (v w : FirstOrderLp 2) :
    ‖((2 * (inner ℂ w v).im : ℝ) : ℂ)‖ ≤ 2 * ‖v‖ * ‖w‖ := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
  calc
    _ ≤ 2 * ‖inner ℂ w v‖ := mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (by norm_num)
    _ ≤ 2 * (‖w‖ * ‖v‖) := mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
    _ = _ := by ring

/-- The actual Hermitian scalar correction at fixed Schwartz fields. The
rough energy estimate keeps the same constant, and the weak frozen wave
energy has the original source term and imaginary commutator sign. -/
theorem exists_originalAngular_hermitian_weak_energy
    (η χ : ℝ → ℝ) {r ρ R₀ : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1/2) (hR : 1 ≤ R₀)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R₀, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
    ∃ (K : ℕ) (Corder Cweak : ℝ), 0 ≤ Corder ∧ 0 ≤ Cweak ∧
      ∀ {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)},
      IsOpen W → Q ×ˢ sphere (0 : RotationSpace) 1 ⊆ W → ContDiffOn ℝ ∞ F W →
      ∀ M : ℝ, 0 ≤ M →
      (∀ n ≤ K, ∀ p ∈ Q, ∀ x : RoundSphere3, ‖iteratedFDeriv ℝ n F (p, (x : RotationSpace))‖ ≤ M) →
      ∀ (d : Fin 4 → Fin 4 → SchwartzMap E ℝ), (∀ a b, d a b = d b a) →
      ∀ (D : ℝ), 0 ≤ D → (∀ a b x, |d a b x| ≤ D) →
      ∀ (L : ℝ≥0), (∀ a b x, ‖fderiv ℝ (d a b : E → ℝ) x‖ ≤ (L : ℝ)) →
      ∀ H : Test, ∃ T S : Test → FirstOrderLp 2,
        (∀ u w : Test,
          inner ℂ (w.toLp 2 volume) (T u) = radianHighPair (originalRegularizedAngularSymbol η χ F) H u w ∧
          inner ℂ (w.toLp 2 volume) (S u) = radianHighPair
            (highAdjointSymbol (originalRegularizedAngularSymbol η χ F)) (fun x => conj (H x)) u w ∧
          inner ℂ (w.toLp 2 volume) (S u) = conj (inner ℂ (u.toLp 2 volume) (T w))) ∧
        let R := hermitianPartOutput T S
        let budget (u : Test) := Cweak * M *
          (D * schwartzGradientNorm 2 u * schwartzGradientNorm 4 H * schwartzGradientNorm 4 u +
           (L : ℝ) * schwartzGradientNorm 2 u * ‖H.toLp 4 volume‖ * schwartzGradientNorm 4 u)
        (∀ u : Test, ‖R u‖ ≤ Corder * M * ‖H.toLp 4 volume‖ * highDerivativeLp4Sum u) ∧
        (∀ u w : Test, inner ℂ (w.toLp 2 volume) (R u) = inner ℂ (R w) (u.toLp 2 volume)) ∧
        (∀ u w : Test, weakDivergenceCommutatorPair d R u w =
          (weakDivergenceCommutatorPair d T u w - conj (weakDivergenceCommutatorPair d T w u)) / 2) ∧
        (∀ u : Test, ‖Complex.I * weakDivergenceCommutatorPair d T u u‖ ≤ budget u ∧
          Complex.I * weakDivergenceCommutatorPair d R u u =
            ((Complex.I * weakDivergenceCommutatorPair d T u u).re : ℂ) ∧
          ‖Complex.I * weakDivergenceCommutatorPair d R u u‖ ≤ budget u) ∧
        ∀ (m : Fin 4 → Fin 4 → ℝ) (u : Test),
          let pn := constantWave m u + schwartzDivergence d u
          Complex.I * weakConstantWaveCommutatorPair m R u u =
            ((2 * (inner ℂ (R u) (pn.toLp 2 volume)).im : ℝ) : ℂ) -
              Complex.I * weakDivergenceCommutatorPair d R u u ∧
          ‖Complex.I * weakConstantWaveCommutatorPair m R u u‖ ≤ 2 * ‖pn.toLp 2 volume‖ * ‖R u‖ + budget u := by
  obtain ⟨K, Cweak, hCweak, weak⟩ := exists_originalAngular_weakDivergence_commutator_bound
    η χ hr hρ hsmall hR hη hzero hone hχ hcut
  obtain ⟨Corder, hCorder, firstOrder⟩ := exists_originalAngular_highAdjoint_firstOrder_and_coordinate_commutator
    η χ hr hρ (hsmall.trans (by norm_num)) hR hη hzero hone hχ hcut
  refine ⟨max K 27, Corder, Cweak, hCorder, hCweak, ?_⟩
  intro F W hW hQ hF M hM hjet d hdSym D hD hd L hd₁ H
  have jetK n (hn : n ≤ K) := hjet n (hn.trans (Nat.le_max_left K 27))
  have jet27 n (hn : n ≤ 27) := hjet n (hn.trans (Nat.le_max_right K 27))
  obtain ⟨T, _, _, pairT, _, _, boundWeak⟩ := weak hW hQ hF M hM jetK d hdSym D hD hd L hd₁ H
  obtain ⟨P, S₀, normP, normS, pair, _⟩ := firstOrder hW hQ hF M hM jet27
  let S (u : Test) := S₀ H u
  let R := hermitianPartOutput T S
  have same (u : Test) : P u (H.toLp 4 volume) = T u :=
    inner_eq_of_schwartz (fun w => (pair H u w).1.trans (pairT u w).symm)
  have dual (u w : Test) : inner ℂ (w.toLp 2 volume) (S u) = conj (inner ℂ (u.toLp 2 volume) (T w)) := by
    change inner ℂ (w.toLp 2 volume) (S₀ H u) = _
    rw [(pair H u w).2.2, same]
  have symmetric := inner_hermitianPartOutput_symmetric T S dual
  have weakPart := weakDivergenceCommutatorPair_hermitianPart d T S dual
  let budget (u : Test) := Cweak * M *
    (D * schwartzGradientNorm 2 u * schwartzGradientNorm 4 H * schwartzGradientNorm 4 u +
     (L : ℝ) * schwartzGradientNorm 2 u * ‖H.toLp 4 volume‖ * schwartzGradientNorm 4 u)
  have diagonal (u : Test) :
      Complex.I * weakDivergenceCommutatorPair d R u u = ((Complex.I * weakDivergenceCommutatorPair d T u u).re : ℂ) ∧
        ‖Complex.I * weakDivergenceCommutatorPair d R u u‖ ≤ budget u := by
    have eq : Complex.I * weakDivergenceCommutatorPair d R u u =
        ((Complex.I * weakDivergenceCommutatorPair d T u u).re : ℂ) := by
      rw [weakPart]
      exact mul_I_half_sub_conj _
    refine ⟨eq, ?_⟩
    rw [eq, Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (boundWeak u)
  refine ⟨T, S, fun u w => ⟨pairT u w, (pair H u w).2.1, dual u w⟩,
    ?_, symmetric, weakPart, fun u => ⟨boundWeak u, diagonal u⟩, ?_⟩
  · intro u
    let bound := Corder * M * ‖H.toLp 4 volume‖ * highDerivativeLp4Sum u
    have forwardNorm : ‖T u‖ ≤ bound := by rw [← same]; exact normP u _
    have halfNorm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num [norm_div]
    change ‖hermitianPartOutput T S u‖ ≤ bound
    rw [hermitianPartOutput, norm_smul, halfNorm]
    calc
      _ ≤ (1 / 2 : ℝ) * (‖T u‖ + ‖S u‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
      _ ≤ (1 / 2 : ℝ) * (bound + bound) :=
        mul_le_mul_of_nonneg_left (add_le_add forwardNorm (normS H u)) (by norm_num)
      _ = _ := by ring
  · intro m u
    have eq := weakConstantWave_energy_eq d m R symmetric u
    refine ⟨eq, ?_⟩
    rw [eq]
    exact (norm_sub_le _ _).trans (add_le_add (sourcePairing_imaginary_bound _ _) (diagonal u).2)

end Burnett.A08
