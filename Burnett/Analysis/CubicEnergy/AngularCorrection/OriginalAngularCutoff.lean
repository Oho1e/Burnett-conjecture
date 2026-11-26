import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalAngularModeBounds

set_option autoImplicit false
set_option maxHeartbeats 11000000

noncomputable section

namespace Burnett.A08

open Burnett.A07 Burnett.A06 Burnett.A02.FrequencySplit MeasureTheory Filter Metric Set
open scoped BigOperators ComplexConjugate ContDiff ENNReal Topology

open private inner_eq_of_schwartz from Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension
open private inner_hermitianPartOutput inner_hermitianPartOutput_symmetric from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalHermitianWeakEnergy
open private hermitianPartOutput_norm_le from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalUpperCutoffWeakRecovery

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private abbrev Test := SchwartzMap E ℂ
private abbrev LP2 := FirstOrderLp 2

/-- Every actual spherical harmonic through degree `L`, with its original multiplicity. -/
def angularDegreeFinset (L : ℕ) : Finset HarmonicMode :=
  (Finset.range (L + 1)).sigma fun l => (Finset.univ : Finset (Fin ((l + 1)^2)))

/-- A fixed original profile, with one forward and one high-adjoint
representative for each of its actual spherical modes. -/
structure OriginalAngularCutoff (η χ : ℝ → ℝ) (F : Joint × RotationSpace → ℂ) (M C₀ C₁ : ℝ) where
  forward : HarmonicMode → Test → Test → LP2
  adjoint : HarmonicMode → Test → Test → LP2
  data : OriginalAngularModeBounds η χ F M C₀ C₁ forward adjoint
  nonnegM : 0 ≤ M
  nonnegOrder : 0 ≤ C₀
  nonnegRough : 0 ≤ C₁
  originalSeries (H u w : Test) : HasSum (fun i => radianHighPair (angularModeSymbol η χ F i) H u w)
    (radianHighPair (originalRegularizedAngularSymbol η χ F) H u w)

namespace OriginalAngularCutoff

variable {η χ : ℝ → ℝ} {F : Joint × RotationSpace → ℂ} {M C₀ C₁ : ℝ}

def partialForward (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ) (H u : Test) : LP2 :=
  ∑ i ∈ angularDegreeFinset L, P.forward i H u

def partialAdjoint (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ) (H u : Test) : LP2 :=
  ∑ i ∈ angularDegreeFinset L, P.adjoint i H u

def fullForward (P : OriginalAngularCutoff η χ F M C₀ C₁) (H u : Test) : LP2 :=
  ∑' i, P.forward i H u

def fullAdjoint (P : OriginalAngularCutoff η χ F M C₀ C₁) (H u : Test) : LP2 :=
  ∑' i, P.adjoint i H u

def partialHermitian (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ) (H u : Test) : LP2 :=
  hermitianPartOutput (P.partialForward L H) (P.partialAdjoint L H) u

def fullHermitian (P : OriginalAngularCutoff η χ F M C₀ C₁) (H u : Test) : LP2 :=
  hermitianPartOutput (P.fullForward H) (P.fullAdjoint H) u

private theorem forwardBounds (P : OriginalAngularCutoff η χ F M C₀ C₁) (H u : Test) :
    HarmonicOperatorSeriesEstimate (fun i => P.forward i H u)
      (C₀ * M * ‖H.toLp 4 volume‖ * highDerivativeLp4Sum u) :=
  harmonic_series_estimate _ (mul_nonneg (mul_nonneg (mul_nonneg P.nonnegOrder P.nonnegM) (norm_nonneg _))
    (highDerivativeLp4Sum_nonneg u)) (fun i => P.data.forwardNorm i H u)

private theorem adjointBounds (P : OriginalAngularCutoff η χ F M C₀ C₁) (H u : Test) :
    HarmonicOperatorSeriesEstimate (fun i => P.adjoint i H u)
      (C₀ * M * ‖H.toLp 4 volume‖ * highDerivativeLp4Sum u) :=
  harmonic_series_estimate _ (mul_nonneg (mul_nonneg (mul_nonneg P.nonnegOrder P.nonnegM) (norm_nonneg _))
    (highDerivativeLp4Sum_nonneg u)) (fun i => P.data.adjointNorm i H u)

theorem partialPairs (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ) (H u w : Test) :
    inner ℂ (w.toLp 2 volume) (P.partialForward L H u) =
      ∑ i ∈ angularDegreeFinset L, radianHighPair (angularModeSymbol η χ F i) H u w ∧
    inner ℂ (w.toLp 2 volume) (P.partialAdjoint L H u) =
      ∑ i ∈ angularDegreeFinset L, radianHighPair (highAdjointSymbol (angularModeSymbol η χ F i))
        (fun x => conj (H x)) u w := by
  exact ⟨by simp only [partialForward, inner_sum, P.data.forwardPair],
    by simp only [partialAdjoint, inner_sum, P.data.adjointPair]⟩

theorem fullPairs (P : OriginalAngularCutoff η χ F M C₀ C₁) (H u w : Test) :
    inner ℂ (w.toLp 2 volume) (P.fullForward H u) =
      radianHighPair (originalRegularizedAngularSymbol η χ F) H u w ∧
    inner ℂ (w.toLp 2 volume) (P.fullAdjoint H u) =
      radianHighPair (highAdjointSymbol (originalRegularizedAngularSymbol η χ F)) (fun x => conj (H x)) u w := by
  have forward := (innerSL ℂ (w.toLp 2 volume)).hasSum (P.forwardBounds H u).summable.hasSum
  have adjoint := (innerSL ℂ (w.toLp 2 volume)).hasSum (P.adjointBounds H u).summable.hasSum
  have adjointSeries := Complex.conjCLE.toContinuousLinearMap.hasSum (P.originalSeries H w u)
  refine ⟨?_, ?_⟩
  · have test : HasSum (fun i => radianHighPair (angularModeSymbol η χ F i) H u w)
        (inner ℂ (w.toLp 2 volume) (P.fullForward H u)) := by
      simpa only [innerSL_apply, P.data.forwardPair, fullForward] using forward
    exact test.unique (P.originalSeries H u w)
  · rw [radianHighPair_highAdjoint]
    have test : HasSum (fun i => conj (radianHighPair (angularModeSymbol η χ F i) H w u))
        (inner ℂ (w.toLp 2 volume) (P.fullAdjoint H u)) := by
      simpa only [innerSL_apply, P.data.adjointPair, radianHighPair_highAdjoint, fullAdjoint] using adjoint
    exact test.unique adjointSeries

/-- Any representatives already realizing the two original tested pairings
agree with the full sums of the same modes. -/
theorem fullHermitian_eq_of_pairs (P : OriginalAngularCutoff η χ F M C₀ C₁) (H : Test)
    (T S : Test → LP2)
    (hT : ∀ u w : Test, inner ℂ (w.toLp 2 volume) (T u) =
      radianHighPair (originalRegularizedAngularSymbol η χ F) H u w)
    (hS : ∀ u w : Test, inner ℂ (w.toLp 2 volume) (S u) =
      radianHighPair (highAdjointSymbol (originalRegularizedAngularSymbol η χ F)) (fun x => conj (H x)) u w) :
    P.fullHermitian H = hermitianPartOutput T S := by
  have fwd : P.fullForward H = T := funext fun u =>
    inner_eq_of_schwartz fun w => (P.fullPairs H u w).1.trans (hT u w).symm
  have adj : P.fullAdjoint H = S := funext fun u =>
    inner_eq_of_schwartz fun w => (P.fullPairs H u w).2.trans (hS u w).symm
  unfold fullHermitian
  rw [fwd, adj]

theorem partialHermitian_norm (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ) (H u : Test) :
    ‖P.partialHermitian L H u‖ ≤ 2 * (C₀ * M * ‖H.toLp 4 volume‖) * highDerivativeLp4Sum u := by
  have fwd := (P.forwardBounds H u).finiteBound (angularDegreeFinset L)
  have adj := (P.adjointBounds H u).finiteBound (angularDegreeFinset L)
  exact hermitianPartOutput_norm_le _ _ u _
    (by simpa only [partialForward, mul_assoc] using fwd)
    (by simpa only [partialAdjoint, mul_assoc] using adj)

theorem partialPairs_tail (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ) (H u : Test) :
    let tail := C₀ * M * ‖H.toLp 4 volume‖ * highDerivativeLp4Sum u / ((L : ℝ) + 1)^2
    ‖P.partialForward L H u - P.fullForward H u‖ ≤ tail ∧
    ‖P.partialAdjoint L H u - P.fullAdjoint H u‖ ≤ tail := by
  exact ⟨by simpa only [partialForward, fullForward, angularDegreeFinset, Finset.sum_sigma, norm_sub_rev]
      using (P.forwardBounds H u).tailBound L,
    by simpa only [partialAdjoint, fullAdjoint, angularDegreeFinset, Finset.sum_sigma, norm_sub_rev]
      using (P.adjointBounds H u).tailBound L⟩

theorem partialHermitian_tail (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ) (H u : Test) :
    ‖P.partialHermitian L H u - P.fullHermitian H u‖ ≤
      C₀ * M * ‖H.toLp 4 volume‖ * highDerivativeLp4Sum u / ((L : ℝ) + 1)^2 := by
  have split : P.partialHermitian L H u - P.fullHermitian H u =
      hermitianPartOutput (fun v => P.partialForward L H v - P.fullForward H v)
        (fun v => P.partialAdjoint L H v - P.fullAdjoint H v) u := by
    simp only [partialHermitian, fullHermitian, hermitianPartOutput]
    rw [← smul_sub]
    congr 1
    abel
  rw [split]
  exact hermitianPartOutput_norm_le _ _ _ _ (P.partialPairs_tail L H u).1 (P.partialPairs_tail L H u).2

theorem partialHermitian_symmetric (P : OriginalAngularCutoff η χ F M C₀ C₁)
    (L : ℕ) (H u w : Test) :
    inner ℂ (w.toLp 2 volume) (P.partialHermitian L H u) =
      inner ℂ (P.partialHermitian L H w) (u.toLp 2 volume) := by
  apply inner_hermitianPartOutput_symmetric
  intro v z
  rw [(P.partialPairs L H v z).2, (P.partialPairs L H z v).1]
  simp only [radianHighPair_highAdjoint, map_sum]

theorem fullHermitian_symmetric (P : OriginalAngularCutoff η χ F M C₀ C₁) (H u w : Test) :
    inner ℂ (w.toLp 2 volume) (P.fullHermitian H u) =
      inner ℂ (P.fullHermitian H w) (u.toLp 2 volume) := by
  apply inner_hermitianPartOutput_symmetric
  intro v z
  rw [(P.fullPairs H v z).2, (P.fullPairs H z v).1, radianHighPair_highAdjoint]

private theorem modeHermitian_derivative (P : OriginalAngularCutoff η χ F M C₀ C₁)
    (i : HarmonicMode) (a : Fin 4) (H u w : Test) :
    -inner ℂ ((coordinateDerivative a w).toLp 2 volume)
        (hermitianPartOutput (P.forward i H) (P.adjoint i H) u) -
      inner ℂ (w.toLp 2 volume)
        (hermitianPartOutput (P.forward i H) (P.adjoint i H) (coordinateDerivative a u)) =
        inner ℂ (w.toLp 2 volume)
          (hermitianPartOutput (P.forward i (coordinateDerivative a H)) (P.adjoint i (coordinateDerivative a H)) u) := by
  have fwd := P.data.derivativePair i a H u w
  have adj := congrArg (conj : ℂ → ℂ) (P.data.derivativePair i a H w u)
  simp only [map_neg, map_sub] at adj
  simp only [inner_hermitianPartOutput, P.data.forwardPair, P.data.adjointPair, radianHighPair_highAdjoint]
  linear_combination (1 / 2 : ℂ) * fwd + (1 / 2 : ℂ) * adj

private theorem partialHermitian_sum (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ) (H u : Test) :
    P.partialHermitian L H u =
      ∑ i ∈ angularDegreeFinset L, hermitianPartOutput (P.forward i H) (P.adjoint i H) u := by
  simp only [partialHermitian, partialForward, partialAdjoint, hermitianPartOutput]
  rw [← Finset.smul_sum, Finset.sum_add_distrib]

theorem partialHermitian_derivative (P : OriginalAngularCutoff η χ F M C₀ C₁)
    (L : ℕ) (a : Fin 4) (H u w : Test) :
    -inner ℂ ((coordinateDerivative a w).toLp 2 volume) (P.partialHermitian L H u) -
        inner ℂ (w.toLp 2 volume) (P.partialHermitian L H (coordinateDerivative a u)) =
      inner ℂ (w.toLp 2 volume) (P.partialHermitian L (coordinateDerivative a H) u) := by
  simp only [partialHermitian_sum, inner_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
    modeHermitian_derivative]

/-- First remove the upper cutoff with the actual degree-`L` Hermitian sum
and its differentiated low field held fixed. -/
theorem partialHermitian_upperRecovery (P : OriginalAngularCutoff η χ F M C₀ C₁)
    (d : Fin 4 → Fin 4 → SchwartzMap E ℝ) (hd : ∀ a b, d a b = d b a) (L : ℕ) (H : Test) :
    UpperCutoffWeakRecovery d (P.partialHermitian L H)
      (fun a => P.partialHermitian L (coordinateDerivative a H)) :=
  symmetricUpperCutoff_weakRecovery d hd _ _
    (2 * (C₀ * M * ‖H.toLp 4 volume‖)) (fun a => 2 * (C₀ * M * ‖(coordinateDerivative a H).toLp 4 volume‖))
    (P.partialHermitian_symmetric L H) (fun a => P.partialHermitian_symmetric L (coordinateDerivative a H))
    (P.partialHermitian_norm L H) (fun a => P.partialHermitian_norm L (coordinateDerivative a H))
    (fun a => P.partialHermitian_derivative L a H)

end OriginalAngularCutoff

/-- The finite-degree Hermitian correction from the actual paper symbol.
The same modes sum to both original tested Fourier pairings. -/
theorem exists_originalAngular_hermitian_angular_cutoff
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1/2) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
    ∃ (K : ℕ) (C₀ C₁ : ℝ), 27 ≤ K ∧ 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      ∀ {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)}, IsOpen W →
      Q ×ˢ sphere (0 : RotationSpace) 1 ⊆ W → ContDiffOn ℝ ∞ F W →
      ∀ M : ℝ, 0 ≤ M →
      (∀ n ≤ K, ∀ p ∈ Q, ∀ x : RoundSphere3, ‖iteratedFDeriv ℝ n F (p, (x : RotationSpace))‖ ≤ M) →
      Nonempty (OriginalAngularCutoff η χ F M C₀ C₁) := by
  obtain ⟨K, C₀, C₁, hK, hC₀, hC₁, modes⟩ := exists_originalAngularMode_bounds
    η χ hr hρ hsmall hR hη hzero hone hχ hcut
  refine ⟨K, C₀, C₁, hK, hC₀, hC₁, ?_⟩
  intro F W hW hQW hF M hM hjet
  obtain ⟨T, S, bounds⟩ := modes hW hQW hF M hM hjet
  exact ⟨⟨T, S, bounds, hM, hC₀, hC₁,
    originalRegularizedAngularPair_hasSum_of_smoothProfile η χ hr hρ hR hη hzero hone hχ hcut
      hW hQW hF hM (fun n hn => hjet n (hn.trans hK))⟩⟩

end Burnett.A08
