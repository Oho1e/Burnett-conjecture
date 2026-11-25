import Burnett.Analysis.TransportPatches.ActualThinConeLp
import Burnett.Analysis.TransportPatches.WideBaselineL2

/-! The actual thin-screen field and its two exact Fourier identities. -/
set_option autoImplicit false
set_option maxRecDepth 5100
set_option maxHeartbeats 7200000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Matrix Burnett.Fourier Burnett.RicciSymbol Burnett.V06
open Burnett.A02.FrequencySplit (E mikhlin_bounded_symbol)
open Burnett.Analysis.ProjectiveNullCaps (thinConeProfile thinConeProfile_contDiffOn thinConeProfile_degreeZero)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Microlocal.SeparablePositive (productSymbol productSymbol_apply fourierMultiplier_product)
open Burnett.P01 (ProjectionSchwartzMatrix projectionMatrixDerivative)
open Burnett.A07 (coordinateDerivative)
open scoped BigOperators ContDiff InnerProduct Matrix Topology

private theorem exists_thinConeScalar (m : Tensor2) {η : ℝ} (hη : 0 < η) (inner outer : ℝ) :
    ∃ a : BoundedSymbol E, ∀ ξ, a ξ = (thinConeProfile m η inner outer ξ : ℂ) :=
  mikhlin_bounded_symbol _ (thinConeProfile_contDiffOn m hη inner outer)
    (fun t ht ξ => thinConeProfile_degreeZero m η inner outer t ht.ne' ξ)

def thinConeScalar (m : Tensor2) {η : ℝ} (hη : 0 < η) (inner outer : ℝ) : BoundedSymbol E :=
  Classical.choose (exists_thinConeScalar m hη inner outer)

theorem thinConeScalar_apply (m : Tensor2) {η : ℝ} (hη : 0 < η) (inner outer : ℝ) (ξ : E) :
    thinConeScalar m hη inner outer ξ = (thinConeProfile m η inner outer ξ : ℂ) :=
  Classical.choose_spec (exists_thinConeScalar m hη inner outer) ξ

def frozenPhaseScalar (m : Tensor2) : BoundedSymbol E := Classical.choose
  (mikhlin_bounded_symbol (normalizedFrozenPhase m) (normalizedFrozenPhase_contDiffOn m) (normalizedFrozenPhase_degreeZero m))

theorem frozenPhaseScalar_apply (m : Tensor2) (ξ : E) :
    frozenPhaseScalar m ξ = (normalizedFrozenPhase m ξ : ℂ) := Classical.choose_spec
  (mikhlin_bounded_symbol (normalizedFrozenPhase m) (normalizedFrozenPhase_contDiffOn m) (normalizedFrozenPhase_degreeZero m)) ξ

def thinScreenAngular (m : Tensor2) (wideInner wideOuter : ℝ)
    (hm : WideScreenFrequencySmooth wideInner wideOuter m) {η : ℝ} (hη : 0 < η)
    (inner outer : ℝ) : RealOrderedAngularMatrix where
  matrix ξ := thinConeProfile m η inner outer ξ • (wideScreenAngular wideInner wideOuter m hm).matrix ξ
  smooth k j := (thinConeProfile_contDiffOn m hη inner outer).mul ((wideScreenAngular wideInner wideOuter m hm).smooth k j)
  degree t ht ξ := by rw [thinConeProfile_degreeZero m η inner outer t ht.ne' ξ,
    (wideScreenAngular wideInner wideOuter m hm).degree t ht ξ]

def actualThinScreenMultiplier (m : Tensor2) (wideInner wideOuter : ℝ)
    (hm : WideScreenFrequencySmooth wideInner wideOuter m) {η : ℝ} (hη : 0 < η)
    (inner outer : ℝ) : ClassicalMatrixMultiplier OrderedPair :=
  (thinScreenAngular m wideInner wideOuter hm hη inner outer).afterOriginalProjection

private theorem angularOutput_mulScalar (T S : RealOrderedAngularMatrix) (a : BoundedSymbol E)
    (eq : ∀ k i ξ, T.complex ξ k i = a ξ * S.complex ξ k i)
    (u : OrderedPair → ComplexL2 E) (k : OrderedPair) :
    T.output u k = fourierMultiplier a (S.output u k) := by
  simp only [RealOrderedAngularMatrix.output, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← fourierMultiplier_product]
  rw [fourierMultiplier_congr_ae (T.coefficient k i) (productSymbol a (S.coefficient k i))
    (Eventually.of_forall fun ξ => by rw [T.coefficient_apply, productSymbol_apply, S.coefficient_apply, eq])]

private theorem fourierMultiplier_add_apply_from_symbol (a b c : BoundedSymbol E)
    (h : ∀ ξ, c ξ = a ξ + b ξ) (f : ComplexL2 E) :
    fourierMultiplier a f + fourierMultiplier b f = fourierMultiplier c f := by
  apply (fourierL2Equiv (V := E)).injective
  simp only [map_add, fourier_fourierMultiplier]
  apply Lp.ext
  let g := fourierL2Equiv f
  filter_upwards [Lp.coeFn_add (symbolL2 a g) (symbolL2 b g), symbolL2_ae a g, symbolL2_ae b g, symbolL2_ae c g]
    with ξ hAdd hA hB hC
  change (symbolL2 a g + symbolL2 b g) ξ = symbolL2 c g ξ
  rw [hAdd, Pi.add_apply, hA, hB, hC, h ξ, add_mul]

private theorem fourierMultiplier_eq_smul_of_constant (a : BoundedSymbol E) (c : ℂ)
    (h : ∀ ξ, a ξ = c) (f : ComplexL2 E) : fourierMultiplier a f = c • f := by
  apply (fourierL2Equiv (V := E)).injective
  simp only [map_smul, fourier_fourierMultiplier]
  apply Lp.ext
  let g := fourierL2Equiv f
  filter_upwards [Lp.coeFn_smul c g, symbolL2_ae a g] with ξ hS hG
  change symbolL2 a g ξ = (c • g) ξ
  rw [hS, Pi.smul_apply, smul_eq_mul, hG, h ξ]

private theorem identityAngular_output (f : OrderedPair → ComplexL2 E) (k : OrderedPair) :
    RealOrderedAngularMatrix.identity.output f k = f k := by
  unfold RealOrderedAngularMatrix.output
  rw [Finset.sum_eq_single k]
  · have h := fourierMultiplier_eq_smul_of_constant (RealOrderedAngularMatrix.identity.coefficient k k) 1
      (fun ξ => by rw [RealOrderedAngularMatrix.coefficient_apply, RealOrderedAngularMatrix.identity_complex]; simp)
      (f k)
    rwa [one_smul] at h
  · intro i _ hi
    have hCoeff (ξ : E) : RealOrderedAngularMatrix.identity.coefficient k i ξ = 0 := by
      rw [RealOrderedAngularMatrix.coefficient_apply, RealOrderedAngularMatrix.identity_complex]
      simp [Ne.symm hi]
    have h := fourierMultiplier_eq_smul_of_constant (RealOrderedAngularMatrix.identity.coefficient k i) 0 hCoeff (f i)
    rwa [zero_smul] at h
  · simp

private theorem wideErrors_add_screen (m : Tensor2) (wideInner wideOuter : ℝ)
    (hm : WideScreenFrequencySmooth wideInner wideOuter m) (f : OrderedPair → ComplexL2 E) (k : OrderedPair) :
    (frozenScreenErrorAngular wideInner wideOuter m hm).output f k + (wideScreenAngular wideInner wideOuter m hm).output f k =
      f k := by
  rw [← identityAngular_output f k]
  unfold RealOrderedAngularMatrix.output
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply fourierMultiplier_add_apply_from_symbol
  intro ξ
  simp only [RealOrderedAngularMatrix.coefficient_apply, RealOrderedAngularMatrix.complex,
    RealOrderedAngularMatrix.identity, frozenScreenErrorAngular, Matrix.sub_apply, Complex.ofReal_sub, sub_add_cancel]

private theorem thin_plus_complement (f : ComplexL2 E) (m : Tensor2) {η : ℝ} (hη : 0 < η) (i o : ℝ) :
    fourierMultiplier (thinComplementScalar m hη i o) f + fourierMultiplier (thinConeScalar m hη i o) f = f := by
  apply (fourierL2Equiv (V := E)).injective
  simp only [map_add, fourier_fourierMultiplier]
  apply Lp.ext
  let g := fourierL2Equiv f
  let a := thinComplementScalar m hη i o
  let b := thinConeScalar m hη i o
  filter_upwards [Lp.coeFn_add (symbolL2 a g) (symbolL2 b g), symbolL2_ae a g, symbolL2_ae b g] with ξ hAdd hA hB
  change (symbolL2 a g + symbolL2 b g) ξ = g ξ
  rw [hAdd, Pi.add_apply, hA, hB, ← add_mul]
  change (thinComplementScalar m hη i o ξ + thinConeScalar m hη i o ξ) * g ξ = g ξ
  simp only [thinComplementScalar_apply, thinConeScalar_apply, Complex.ofReal_sub, Complex.ofReal_one, sub_add_cancel, one_mul]

private theorem fourierMultiplier_commute_scalar (a b : BoundedSymbol E) (f : ComplexL2 E) :
    fourierMultiplier a (fourierMultiplier b f) = fourierMultiplier b (fourierMultiplier a f) := by
  rw [← fourierMultiplier_product, ← fourierMultiplier_product]
  rw [fourierMultiplier_congr_ae (productSymbol a b) (productSymbol b a)
    (Eventually.of_forall fun ξ => by rw [productSymbol_apply, productSymbol_apply, mul_comm])]

/-- The actual combined gradient splits into the thin complement and the
thin-filtered wide error. The normalized phase commutes with the thin scalar. -/
theorem actualThinScreen_gradient_identities
    (m : Tensor2) (wideInner wideOuter : ℝ) (hm : WideScreenFrequencySmooth wideInner wideOuter m)
    {η : ℝ} (hη : 0 < η) (inner outer : ℝ) (z : ProjectionSchwartzMatrix) (d : Index) (k : OrderedPair) :
    let U := multiplierCoordinateDerivative originalProjectedMatrixMultiplier z d k
    let V := multiplierCoordinateDerivative (actualThinScreenMultiplier m wideInner wideOuter hm hη inner outer) z d k
    let E₁ := multiplierCoordinateDerivative (actualFrozenScreenErrorMultiplier wideInner wideOuter m hm) z d k
    let E₂ := multiplierCoordinateDerivative (actualFrozenPhaseErrorMultiplier wideInner wideOuter m hm) z d k
    let C := multiplierCoordinateDerivative (actualThinConeComplementMultiplier m hη inner outer) z d k
    let S := fourierMultiplier (thinConeScalar m hη inner outer)
    U - V = C + S E₁ ∧ fourierMultiplier (frozenPhaseScalar m) V = S E₂ := by
  intro U V E₁ E₂ C S
  let inc (i : OrderedPair) := ((projectionMatrixDerivative d z) i.1 i.2).toLp 2 volume
  let u := originalProjectedMatrixMultiplier.output inc
  let W := (wideScreenAngular wideInner wideOuter m hm).output u k
  have hOrig : originalProjectedMatrixMultiplier.output inc = originalOrderedProjectedField inc :=
    funext (originalProjectedMatrixMultiplier_output inc)
  have hV : V = S W := by
    change (thinScreenAngular m wideInner wideOuter hm hη inner outer).afterOriginalProjection.output inc k = _
    rw [RealOrderedAngularMatrix.afterOriginalProjection_output, ← hOrig]
    apply angularOutput_mulScalar
    intro k i ξ
    simp only [RealOrderedAngularMatrix.complex, thinScreenAngular, Matrix.smul_apply,
      smul_eq_mul, Complex.ofReal_mul, thinConeScalar_apply]
  have hErrors := actualFrozenWideErrors_originalProjectedOutput wideInner wideOuter m hm inc k
  have hA : E₁ + W = U := by
    change (actualFrozenScreenErrorMultiplier wideInner wideOuter m hm).output inc k + W = u k
    rw [hErrors.1]
    exact wideErrors_add_screen m wideInner wideOuter hm u k
  have hC : C = fourierMultiplier (thinComplementScalar m hη inner outer) U := by
    change (actualThinConeComplementMultiplier m hη inner outer).output inc k = _
    rw [actualThinConeComplementMultiplier_output, show U = originalOrderedProjectedField inc k from
      originalProjectedMatrixMultiplier_output inc k]
    rfl
  have hE₂ : E₂ = fourierMultiplier (frozenPhaseScalar m) W := by
    change (actualFrozenPhaseErrorMultiplier wideInner wideOuter m hm).output inc k = _
    rw [hErrors.2]
    apply angularOutput_mulScalar
    intro k i ξ
    simp only [RealOrderedAngularMatrix.complex, frozenPhaseErrorAngular, Matrix.smul_apply,
      smul_eq_mul, Complex.ofReal_mul, frozenPhaseScalar_apply]
  constructor
  · have hThinAdd : C + S U = U := by rw [hC]; exact thin_plus_complement U m hη inner outer
    have hWideAdd := congrArg S hA
    rw [map_add] at hWideAdd
    rw [hV]
    calc
      U - S W = (C + S U) - S W := by
        nth_rewrite 1 [← hThinAdd]
        rfl
      _ = C + S E₁ := by rw [← hWideAdd]; abel
  · rw [hV, hE₂]
    exact fourierMultiplier_commute_scalar _ _ _

/-- The specified gradient is the weak derivative of the actual thin-screen field. -/
theorem actualThinScreen_weak_derivative
    (m : Tensor2) (wideInner wideOuter : ℝ) (hm : WideScreenFrequencySmooth wideInner wideOuter m)
    {η : ℝ} (hη : 0 < η) (thinInner thinOuter : ℝ) (z : ProjectionSchwartzMatrix)
    (f : SchwartzMap E ℂ) (d : Index) (k : OrderedPair) :
    let T := actualThinScreenMultiplier m wideInner wideOuter hm hη thinInner thinOuter
    inner ℂ ((coordinateDerivative d f).toLp 2 volume) (T.output (fun i => (z i.1 i.2).toLp 2 volume) k) =
      -inner ℂ (f.toLp 2 volume) (multiplierCoordinateDerivative T z d k) := by
  exact ClassicalMatrixMultiplier.output_weak_coordinateDerivative _ (fun i => z i.1 i.2) f d k

end Burnett.C02
