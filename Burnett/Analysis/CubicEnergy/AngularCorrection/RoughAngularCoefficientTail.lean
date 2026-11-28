import Burnett.Analysis.CubicEnergy.AngularCorrection.LipschitzWeakCoefficientPair

set_option autoImplicit false
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.A08

open Filter MeasureTheory Burnett.A06 Burnett.A07 Burnett.A02.FrequencySplit Burnett.Fourier
open scoped BigOperators ComplexConjugate ENNReal NNReal Topology

local instance roughAngularCoefficientTailLpTwo : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance roughAngularCoefficientTailLpFour : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private abbrev Test := SchwartzMap E ℂ
private abbrev LP2 := FirstOrderLp 2

open private coefficientProductInner_tendsto coefficientProduct_sub_const
  from Burnett.Analysis.CubicEnergy.AngularCorrection.LipschitzWeakCoefficientPair

/-- The coefficient commutator of a forward action and its high adjoint,
tested after physical multiplication on the two Schwartz vectors. -/
def testedHighCoefficientPair (T S : Test → LP2) (multiply : Test → LP2) (u w : Test) : ℂ :=
  inner ℂ (multiply w) (T u) - inner ℂ (S w) (multiply u)

theorem testedHighCoefficientPair_sub (T S T' S' multiply : Test → LP2) (u w : Test) :
    testedHighCoefficientPair (fun v => T v - T' v) (fun v => S v - S' v) multiply u w =
      testedHighCoefficientPair T S multiply u w - testedHighCoefficientPair T' S' multiply u w := by
  simp only [testedHighCoefficientPair, inner_sub_right, inner_sub_left]
  abel

namespace OriginalAngularCutoff

variable {η χ : ℝ → ℝ} {F : Joint × RotationSpace → ℂ} {M C₀ C₁ : ℝ}

/-- The exact difference between the degree cutoff and the full forward series. -/
def forwardAngularTail (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ) (H u : Test) : LP2 :=
  P.partialForward L H u - P.fullForward H u

/-- The exact difference of the high adjoints of the same series. -/
def adjointAngularTail (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ) (H u : Test) : LP2 :=
  P.partialAdjoint L H u - P.fullAdjoint H u

theorem partialAdjoint_duality (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ) (H u w : Test) :
    inner ℂ (P.partialAdjoint L H w) (u.toLp 2 volume) =
      inner ℂ (w.toLp 2 volume) (P.partialForward L H u) := by
  rw [← inner_conj_symm, (P.partialPairs L H w u).2, (P.partialPairs L H u w).1, map_sum]
  simp only [radianHighPair_highAdjoint, Complex.conj_conj]

theorem fullAdjoint_duality (P : OriginalAngularCutoff η χ F M C₀ C₁) (H u w : Test) :
    inner ℂ (P.fullAdjoint H w) (u.toLp 2 volume) =
      inner ℂ (w.toLp 2 volume) (P.fullForward H u) := by
  rw [← inner_conj_symm, (P.fullPairs H w u).2, (P.fullPairs H u w).1,
    radianHighPair_highAdjoint, Complex.conj_conj]

theorem adjointAngularTail_duality (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ) (H u w : Test) :
    inner ℂ (P.adjointAngularTail L H w) (u.toLp 2 volume) =
      inner ℂ (w.toLp 2 volume) (P.forwardAngularTail L H u) := by
  simp only [forwardAngularTail, adjointAngularTail, inner_sub_right, inner_sub_left,
    P.partialAdjoint_duality, P.fullAdjoint_duality]

private theorem schwartzAngularSeries (P : OriginalAngularCutoff η χ F M C₀ C₁)
    (d : SchwartzMap E ℝ) (H u w : Test) :
    HasSum (fun i => radianHighCommutatorPair (angularModeSymbol η χ F i) d H u w)
      (radianHighCommutatorPair (originalRegularizedAngularSymbol η χ F) d H u w) := by
  have hm (v : Test) : (realSchwartzMultiply d v : E → ℂ) = fun x => (d x : ℂ) * v x :=
    funext (realSchwartzMultiply_apply d v)
  simpa only [radianHighCommutatorPair, hm] using
    (P.originalSeries H (realSchwartzMultiply d u) w).sub (P.originalSeries H u (realSchwartzMultiply d w))

private theorem schwartzCoefficientTail_eq (P : OriginalAngularCutoff η χ F M C₀ C₁)
    (L : ℕ) (d : SchwartzMap E ℝ) (H u w : Test) :
    testedHighCoefficientPair (P.forwardAngularTail L H) (P.adjointAngularTail L H)
      (fun v => (realSchwartzMultiply d v).toLp 2 volume) u w =
        radianHighCommutatorPair (originalRegularizedAngularSymbol η χ F) d H u w -
          ∑ i ∈ angularDegreeFinset L, radianHighCommutatorPair (angularModeSymbol η χ F i) d H u w := by
  have hm (v : Test) : (realSchwartzMultiply d v : E → ℂ) = fun x => (d x : ℂ) * v x :=
    funext (realSchwartzMultiply_apply d v)
  unfold forwardAngularTail adjointAngularTail
  rw [testedHighCoefficientPair_sub]
  unfold testedHighCoefficientPair
  rw [P.partialAdjoint_duality, P.fullAdjoint_duality, (P.partialPairs L H u (realSchwartzMultiply d w)).1,
    (P.partialPairs L H (realSchwartzMultiply d u) w).1, (P.fullPairs H u (realSchwartzMultiply d w)).1,
    (P.fullPairs H (realSchwartzMultiply d u) w).1]
  simp only [radianHighCommutatorPair, hm, Finset.sum_sub_distrib]
  abel

/-- The genuine tested forward coefficient commutator has both cubic mode
tails. The adjoint uses the second bound by swapping the two high slots. -/
theorem schwartzCoefficientAngularTail (P : OriginalAngularCutoff η χ F M C₀ C₁)
    (L : ℕ) (d : SchwartzMap E ℝ) (ℓ : ℝ≥0) (hLip : LipschitzWith ℓ d) (H u w : Test) :
    let value := testedHighCoefficientPair (P.forwardAngularTail L H) (P.adjointAngularTail L H)
      (fun v => (realSchwartzMultiply d v).toLp 2 volume) u w
    let C := C₁ * M * (ℓ : ℝ) * ‖H.toLp 4 volume‖
    ‖value‖ ≤ C * ‖u.toLp 4 volume‖ * ‖w.toLp 2 volume‖ / ((L : ℝ) + 1)^2 ∧
    ‖value‖ ≤ C * ‖u.toLp 2 volume‖ * ‖w.toLp 4 volume‖ / ((L : ℝ) + 1)^2 := by
  dsimp only
  rw [P.schwartzCoefficientTail_eq]
  have hC₁ := P.nonnegRough
  have hM := P.nonnegM
  let term (i : HarmonicMode) := radianHighCommutatorPair (angularModeSymbol η χ F i) d H u w
  have bound {A : ℝ} (hA : 0 ≤ A) (hterm : ∀ i, ‖term i‖ ≤ A / ((i.1 : ℝ) + 1)^5) :
      ‖radianHighCommutatorPair (originalRegularizedAngularSymbol η χ F) d H u w -
        ∑ i ∈ angularDegreeFinset L, term i‖ ≤ A / ((L : ℝ) + 1)^2 := by
    have tail := (harmonic_series_estimate term hA hterm).tailBound L
    rw [(P.schwartzAngularSeries d H u w).tsum_eq] at tail
    simpa only [angularDegreeFinset, Finset.sum_sigma] using tail
  exact ⟨bound (by positivity) (fun i => P.data.roughForward i d ℓ hLip H u w),
    bound (by positivity) (fun i => P.data.roughAdjoint i d ℓ hLip H u w)⟩

/-- Both true angular tails extend to every bounded real Lipschitz coefficient.
The density cost is chosen once, before the cutoffs, symbol, degree or fields. -/
theorem exists_boundedLipschitzCoefficientAngularTail :
    ∃ K : ℝ≥0, 1 ≤ K ∧
      ∀ {η χ : ℝ → ℝ} {F : Joint × RotationSpace → ℂ} {M C₀ C₁ : ℝ}
        (P : OriginalAngularCutoff η χ F M C₀ C₁) (L : ℕ)
        (d : E → ℝ) (D : ℝ) (hD : 0 ≤ D) (hbound : ∀ x, |d x| ≤ D)
        (ℓ : ℝ≥0) (hLip : LipschitzWith ℓ d) (H u w : Test),
        let e := boundedRealCoefficient d D hD hLip.continuous.measurable hbound
        let value := testedHighCoefficientPair (P.forwardAngularTail L H) (P.adjointAngularTail L H)
          (fun v => symbolCLM e (v.toLp 2 volume)) u w
        let C := C₁ * M * (K : ℝ) * lipschitzGradientLInfty d * ‖H.toLp 4 volume‖
        ‖value‖ ≤ C * ‖u.toLp 4 volume‖ * ‖w.toLp 2 volume‖ / ((L : ℝ) + 1)^2 ∧
        ‖value‖ ≤ C * ‖u.toLp 2 volume‖ * ‖w.toLp 4 volume‖ / ((L : ℝ) + 1)^2 := by
  obtain ⟨K,hK,density⟩ := exists_realSchwartz_normalized_Lipschitz_approximation
  refine ⟨K,hK,?_⟩
  intro η χ F M C₀ C₁ P L d D hD hbound ℓ hLip H u w e value C
  let ℓ₀ := (lipschitzGradientLInfty d).toNNReal
  have hℓ : LipschitzWith ℓ₀ d := lipschitzWith_lipschitzGradientLInfty hLip
  have hgrad : 0 ≤ lipschitzGradientLInfty d := ENNReal.toReal_nonneg
  have hCoe : ((K * ℓ₀ : ℝ≥0) : ℝ) = (K : ℝ) * lipschitzGradientLInfty d := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hgrad]
  obtain ⟨v,hv₀,hvLip,hvlim⟩ := density d ℓ₀ hℓ
  let h (x : E) := d x - d 0
  have hh (x : E) : |h x| ≤ 2 * D := by
    have hdiff : |d x - d 0| ≤ |d x| + |d 0| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (d x) (d 0)
    exact hdiff.trans (by linarith [hbound x, hbound 0])
  let e₀ := boundedRealCoefficient h (2 * D) (by positivity)
    (hLip.continuous.measurable.sub measurable_const) hh
  have shifted (x : E) : e₀ x = e x - (d 0 : ℂ) := Complex.ofReal_sub _ _
  let T := P.forwardAngularTail L H
  let S := P.adjointAngularTail L H
  have leftLim := coefficientProductInner_tendsto v h (K * ℓ₀) hvLip hv₀ hvlim e₀ (fun _ => rfl) w (T u)
  have rightLim : Tendsto (fun n => inner ℂ (S w) ((realSchwartzMultiply (v n) u).toLp 2 volume))
      atTop (𝓝 (inner ℂ (S w) (symbolCLM e₀ (u.toLp 2 volume)))) := by
    have limit := coefficientProductInner_tendsto v h (K * ℓ₀) hvLip hv₀ hvlim e₀ (fun _ => rfl) u (S w)
    simpa only [Function.comp_def, inner_conj_symm] using
      Complex.continuous_conj.continuousAt.tendsto.comp limit
  have normal : testedHighCoefficientPair T S (fun z => symbolCLM e₀ (z.toLp 2 volume)) u w = value := by
    change _ = testedHighCoefficientPair T S (fun z => symbolCLM e (z.toLp 2 volume)) u w
    simp only [testedHighCoefficientPair]
    rw [coefficientProduct_sub_const e e₀ (d 0) shifted, coefficientProduct_sub_const e e₀ (d 0) shifted]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    have dual : inner ℂ (S w) (u.toLp 2 volume) = inner ℂ (w.toLp 2 volume) (T u) :=
      P.adjointAngularTail_duality L H u w
    rw [dual]
    ring
  have pairLim : Tendsto (fun n => testedHighCoefficientPair T S
      (fun z => (realSchwartzMultiply (v n) z).toLp 2 volume) u w) atTop (𝓝 value) := by
    rw [← normal]
    exact leftLim.sub rightLim
  constructor
  · apply le_of_tendsto' pairLim.norm
    intro n
    simpa only [C, hCoe, mul_assoc] using (P.schwartzCoefficientAngularTail L (v n) (K * ℓ₀) (hvLip n) H u w).1
  · apply le_of_tendsto' pairLim.norm
    intro n
    simpa only [C, hCoe, mul_assoc] using (P.schwartzCoefficientAngularTail L (v n) (K * ℓ₀) (hvLip n) H u w).2

end OriginalAngularCutoff

end Burnett.A08
