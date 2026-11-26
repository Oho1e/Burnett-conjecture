import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalUpperCutoffL2

set_option autoImplicit false
set_option maxHeartbeats 7500000

noncomputable section

namespace Burnett.A08

open Burnett.A07 Burnett.A06 Burnett.A02.FrequencySplit Burnett.Fourier MeasureTheory Filter Metric Set
open scoped BigOperators ComplexConjugate ContDiff ENNReal Topology

open private inner_eq_of_schwartz from Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension
open private inner_hermitianPartOutput inner_hermitianPartOutput_symmetric from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalHermitianWeakEnergy
open private weakDivergenceCommutatorPair_eq from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalWeakDivergenceCommutator

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private abbrev Test := SchwartzMap E ℂ
private abbrev Index := Fin 4
private abbrev LP2 := FirstOrderLp 2

/-- Recovery at a fixed correction and arbitrary fixed Schwartz tests.
The three divergence terms retain the differentiated low field, the actual
coefficient commutator and the differentiated low field in the adjoint slot. -/
structure UpperCutoffWeakRecovery (d : Index → Index → SchwartzMap E ℝ)
    (R : Test → LP2) (A : Index → Test → LP2) : Prop where
  strong (u : Test) :
    Tendsto (fun Λ : ℝ => symmetricUpperCutoffOutput R Λ u) atTop (𝓝 (R u))
  terms (a b : Index) (u w : Test) :
    Tendsto (fun Λ : ℝ => inner ℂ ((realSchwartzMultiply (d a b) (coordinateDerivative a w)).toLp 2 volume)
      (symmetricUpperCutoffOutput (A b) Λ u)) atTop
      (𝓝 (inner ℂ ((realSchwartzMultiply (d a b) (coordinateDerivative a w)).toLp 2 volume) (A b u))) ∧
    Tendsto (fun Λ : ℝ => inner ℂ ((coordinateDerivative a w).toLp 2 volume)
      (coefficientCommutatorOutput (d a b) (symmetricUpperCutoffOutput R Λ) (coordinateDerivative b u))) atTop
      (𝓝 (inner ℂ ((coordinateDerivative a w).toLp 2 volume)
        (coefficientCommutatorOutput (d a b) R (coordinateDerivative b u)))) ∧
    Tendsto (fun Λ : ℝ => -inner ℂ (symmetricUpperCutoffOutput (A a) Λ w)
      ((realSchwartzMultiply (d a b) (coordinateDerivative b u)).toLp 2 volume)) atTop
      (𝓝 (-inner ℂ (A a w) ((realSchwartzMultiply (d a b) (coordinateDerivative b u)).toLp 2 volume)))
  weakLimit (u w : Test) :
    Tendsto (fun Λ : ℝ => weakDivergenceCommutatorPair d (symmetricUpperCutoffOutput R Λ) u w) atTop
      (𝓝 (weakDivergenceCommutatorPair d R u w))
  weakCutoffIdentity (Λ : ℝ) (u w : Test) :
    weakDivergenceCommutatorPair d (symmetricUpperCutoffOutput R Λ) u w =
      ∑ a : Index, ∑ b : Index,
        (inner ℂ ((realSchwartzMultiply (d a b) (coordinateDerivative a w)).toLp 2 volume)
            (symmetricUpperCutoffOutput (A b) Λ u) +
          inner ℂ ((coordinateDerivative a w).toLp 2 volume)
            (coefficientCommutatorOutput (d a b) (symmetricUpperCutoffOutput R Λ) (coordinateDerivative b u)) -
          inner ℂ (symmetricUpperCutoffOutput (A a) Λ w)
            ((realSchwartzMultiply (d a b) (coordinateDerivative b u)).toLp 2 volume))
  weakIdentity (u w : Test) :
    weakDivergenceCommutatorPair d R u w =
      ∑ a : Index, ∑ b : Index,
        (inner ℂ ((realSchwartzMultiply (d a b) (coordinateDerivative a w)).toLp 2 volume) (A b u) +
          inner ℂ ((coordinateDerivative a w).toLp 2 volume)
            (coefficientCommutatorOutput (d a b) R (coordinateDerivative b u)) -
          inner ℂ (A a w) ((realSchwartzMultiply (d a b) (coordinateDerivative b u)).toLp 2 volume))
  waveBound (m : Index → Index → ℝ) (u : Test) (Λ : ℝ) :
    ‖Complex.I * weakConstantWaveCommutatorPair m
      (fun v => symmetricUpperCutoffOutput R Λ v - R v) u u‖ ≤
      2 * ‖(constantWave m u).toLp 2 volume‖ * ‖symmetricUpperCutoffOutput R Λ u - R u‖
  waveLimit (m : Index → Index → ℝ) (u : Test) :
    Tendsto (fun Λ : ℝ => Complex.I * weakConstantWaveCommutatorPair m
      (fun v => symmetricUpperCutoffOutput R Λ v - R v) u u) atTop (𝓝 0)

/-- Remove the actual symmetric upper cutoff on the fixed-index paper
correction and its tested low derivatives. -/
theorem symmetricUpperCutoff_weakRecovery
    (d : Index → Index → SchwartzMap E ℝ) (hd : ∀ a b, d a b = d b a)
    (R : Test → LP2) (A : Index → Test → LP2) (C : ℝ) (CA : Index → ℝ)
    (symR : ∀ u w : Test, inner ℂ (w.toLp 2 volume) (R u) = inner ℂ (R w) (u.toLp 2 volume))
    (symA : ∀ a (u w : Test), inner ℂ (w.toLp 2 volume) (A a u) = inner ℂ (A a w) (u.toLp 2 volume))
    (orderR : ∀ u : Test, ‖R u‖ ≤ C * highDerivativeLp4Sum u)
    (orderA : ∀ a (u : Test), ‖A a u‖ ≤ CA a * highDerivativeLp4Sum u)
    (derivative : ∀ a (u w : Test),
      -inner ℂ ((coordinateDerivative a w).toLp 2 volume) (R u) -
          inner ℂ (w.toLp 2 volume) (R (coordinateDerivative a u)) = inner ℂ (w.toLp 2 volume) (A a u)) :
    UpperCutoffWeakRecovery d R A := by
  have strong := symmetricUpperCutoffOutput_tendsto R C symR orderR
  have strongA (a : Index) := symmetricUpperCutoffOutput_tendsto (A a) (CA a) (symA a) (orderA a)
  have cutoffSym := symmetricUpperCutoffOutput_symmetric R symR
  have cutoffSymA (a : Index) := symmetricUpperCutoffOutput_symmetric (A a) (symA a)
  have cutoffDerivative (Λ : ℝ) (a : Index) (u w : Test) :
      -inner ℂ ((coordinateDerivative a w).toLp 2 volume) (symmetricUpperCutoffOutput R Λ u) -
          inner ℂ (w.toLp 2 volume) (symmetricUpperCutoffOutput R Λ (coordinateDerivative a u)) =
        inner ℂ (w.toLp 2 volume) (symmetricUpperCutoffOutput (A a) Λ u) := by
    simp only [inner_symmetricUpperCutoffOutput, ← coordinateDerivative_upperFrequencyCutoff]
    exact derivative a (upperFrequencyCutoff Λ u) (upperFrequencyCutoff Λ w)
  refine ⟨strong, ?_, ?_,
    fun Λ => weakDivergenceCommutatorPair_eq d hd _ _ _ _ (cutoffSym Λ) (cutoffDerivative Λ)
      (fun a => cutoffSymA a Λ),
    weakDivergenceCommutatorPair_eq d hd R R A A symR derivative symA, ?_, ?_⟩
  · intro a b u w
    have coefficient (g : SchwartzMap E ℝ) (v : Test) :
        Tendsto (fun Λ : ℝ => coefficientCommutatorOutput g (symmetricUpperCutoffOutput R Λ) v) atTop
          (𝓝 (coefficientCommutatorOutput g R v)) := by
      let L : LP2 →L[ℂ] LP2 := symbolCLM (realSchwartzCoefficient g)
      exact (L.continuous.continuousAt.tendsto.comp (strong v)).sub (strong (realSchwartzMultiply g v))
    exact ⟨tendsto_const_nhds.inner (strongA b u),
      tendsto_const_nhds.inner (coefficient (d a b) (coordinateDerivative b u)),
      ((strongA a w).inner tendsto_const_nhds).neg⟩
  · intro u w
    exact (tendsto_const_nhds.inner (strong u)).sub (tendsto_const_nhds.inner (strong (schwartzDivergence d u)))
  · intro m u Λ
    let err (v : Test) := symmetricUpperCutoffOutput R Λ v - R v
    let v := (constantWave m u).toLp 2 volume
    have errSym (g h : Test) : inner ℂ (h.toLp 2 volume) (err g) = inner ℂ (err h) (g.toLp 2 volume) := by
      simp only [err, inner_sub_right, inner_sub_left, cutoffSym Λ g h, symR g h]
    change ‖Complex.I * weakConstantWaveCommutatorPair m err u u‖ ≤ 2 * ‖v‖ * ‖err u‖
    rw [norm_mul, Complex.norm_I, one_mul, weakConstantWaveCommutatorPair, errSym (constantWave m u) u]
    calc
      _ ≤ ‖inner ℂ v (err u)‖ + ‖inner ℂ (err u) v‖ := norm_sub_le _ _
      _ ≤ ‖v‖ * ‖err u‖ + ‖err u‖ * ‖v‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ = 2 * ‖v‖ * ‖err u‖ := by ring
  · intro m u
    have err (v : Test) : Tendsto (fun Λ : ℝ => symmetricUpperCutoffOutput R Λ v - R v) atTop (𝓝 0) := by
      simpa only [sub_self] using (strong v).sub (tendsto_const_nhds (x := R v))
    have first := (tendsto_const_nhds (x := (constantWave m u).toLp 2 volume)).inner (𝕜 := ℂ) (err u)
    have second := (tendsto_const_nhds (x := u.toLp 2 volume)).inner (𝕜 := ℂ) (err (constantWave m u))
    simpa only [weakConstantWaveCommutatorPair, inner_zero_right, sub_zero, mul_zero]
      using (first.sub second).const_mul Complex.I

private theorem hermitianPartOutput_norm_le (T S : Test → LP2) (u : Test) (K : ℝ)
    (hT : ‖T u‖ ≤ K) (hS : ‖S u‖ ≤ K) : ‖hermitianPartOutput T S u‖ ≤ K := by
  have half : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num [norm_div]
  rw [hermitianPartOutput, norm_smul, half]
  calc
    _ ≤ (1 / 2 : ℝ) * (‖T u‖ + ‖S u‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (K + K) := mul_le_mul_of_nonneg_left (add_le_add hT hS) (by norm_num)
    _ = K := by ring

/-- The exact `R = (T + T*)/2` of the original symbol, with its same low profile,
has the fixed-field symmetric upper-cutoff recovery. The output representatives
`T` and `S` can be those of the original Hermitian weak energy theorem. -/
theorem exists_originalAngular_hermitian_upperCutoff_recovery
    (η χ : ℝ → ℝ) {r ρ R₀ : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1/2) (hR : 1 ≤ R₀)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R₀, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0)
    {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)}
    (hW : IsOpen W)
    (hQ : (closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1) ×ˢ sphere (0 : RotationSpace) 1 ⊆ W)
    (hF : ContDiffOn ℝ ∞ F W) {M : ℝ} (hM : 0 ≤ M)
    (hjet : ∀ n ≤ 27, ∀ z ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1, ∀ θ : RoundSphere3,
      ‖iteratedFDeriv ℝ n F (z, (θ : RotationSpace))‖ ≤ M)
    (d : Index → Index → SchwartzMap E ℝ) (hd : ∀ a b, d a b = d b a)
    (H : Test) (T S : Test → LP2)
    (pairT : ∀ u w : Test, inner ℂ (w.toLp 2 volume) (T u) =
      radianHighPair (originalRegularizedAngularSymbol η χ F) H u w)
    (pairS : ∀ u w : Test, inner ℂ (w.toLp 2 volume) (S u) =
      radianHighPair (highAdjointSymbol (originalRegularizedAngularSymbol η χ F)) (fun x => conj (H x)) u w) :
    ∃ A : Index → Test → LP2,
      (∀ a (u w : Test), inner ℂ (w.toLp 2 volume) (A a u) =
        (radianHighPair (originalRegularizedAngularSymbol η χ F) (coordinateDerivative a H) u w +
          radianHighPair (highAdjointSymbol (originalRegularizedAngularSymbol η χ F))
            (fun x => conj (coordinateDerivative a H x)) u w) / 2) ∧
      UpperCutoffWeakRecovery d (hermitianPartOutput T S) A := by
  have hρ₁ : ρ < 1 := hsmall.trans (by norm_num)
  obtain ⟨C, _, firstOrder⟩ := exists_originalAngular_highAdjoint_firstOrder_and_coordinate_commutator
    η χ hr hρ hρ₁ hR hη hzero hone hχ hcut
  obtain ⟨P, S₀, normP, normS, pair, derivativeS₀⟩ := firstOrder hW hQ hF M hM hjet
  let forward (G u : Test) := P u (G.toLp 4 volume)
  let A (a : Index) := hermitianPartOutput (forward (coordinateDerivative a H)) (S₀ (coordinateDerivative a H))
  have sameT (u : Test) : T u = forward H u :=
    inner_eq_of_schwartz fun w => (pairT u w).trans (pair H u w).1.symm
  have sameS (u : Test) : S u = S₀ H u :=
    inner_eq_of_schwartz fun w => (pairS u w).trans (pair H u w).2.1.symm
  have dual (u w : Test) : inner ℂ (w.toLp 2 volume) (S u) = conj (inner ℂ (u.toLp 2 volume) (T w)) := by
    rw [sameS, sameT]
    exact (pair H u w).2.2
  refine ⟨A, ?_, symmetricUpperCutoff_weakRecovery d hd (hermitianPartOutput T S) A
    (C * M * ‖H.toLp 4 volume‖) (fun a => C * M * ‖(coordinateDerivative a H).toLp 4 volume‖)
    (inner_hermitianPartOutput_symmetric T S dual) ?_ ?_ ?_ ?_⟩
  · intro a u w
    dsimp only [A, forward]
    rw [inner_hermitianPartOutput, (pair (coordinateDerivative a H) u w).1,
      (pair (coordinateDerivative a H) u w).2.1]
  · intro a u w
    exact inner_hermitianPartOutput_symmetric _ _ (fun v z => (pair (coordinateDerivative a H) v z).2.2) u w
  · intro u
    exact hermitianPartOutput_norm_le T S u _ (by rw [sameT]; exact normP _ _) (by rw [sameS]; exact normS _ _)
  · intro a u
    exact hermitianPartOutput_norm_le _ _ u _ (normP _ _) (normS _ _)
  · intro a u w
    have hT : -inner ℂ ((coordinateDerivative a w).toLp 2 volume) (T u) -
        inner ℂ (w.toLp 2 volume) (T (coordinateDerivative a u)) =
          inner ℂ (w.toLp 2 volume) (forward (coordinateDerivative a H) u) := by
      change -inner ℂ ((coordinateDerivative a w).toLp 2 volume) (T u) -
        inner ℂ (w.toLp 2 volume) (T (coordinateDerivative a u)) =
          inner ℂ (w.toLp 2 volume) (P u ((coordinateDerivative a H).toLp 4 volume))
      rw [pairT, pairT, (pair (coordinateDerivative a H) u w).1]
      exact originalRegularizedAngularPair_coordinateDerivative_commutator
        η χ hr hρ hR hη hzero hone hχ hcut hW hQ hF hM hjet a H u w
    simp only [A, inner_hermitianPartOutput, sameS]
    linear_combination (1 / 2 : ℂ) * hT + (1 / 2 : ℂ) * derivativeS₀ a H u w

end Burnett.A08
