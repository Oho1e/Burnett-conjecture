import Burnett.Analysis.PrincipalEnergy.Localization.SummableMatrixAction
import Burnett.Analysis.PrincipalEnergy.Localization.UniformSymbolFamilyPair

set_option autoImplicit false
set_option maxHeartbeats 5500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory BoundedContinuousFunction Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate NNReal

theorem UniformCompactSymbolFamily.reindex {ι σ : Type*} {a : ι → Space → Space → ℂ}
    (ha : UniformCompactSymbolFamily a) (c : σ → ι) :
    UniformCompactSymbolFamily (fun n => a (c n)) := by
  refine ⟨?_, fun n => ha.smoothFrequency (c n), fun n => ha.smoothBase (c n),
    fun n => ha.jointlyContinuous (c n), fun n => ha.differentiableMixed (c n), ?_, ?_, ?_⟩
  · obtain ⟨K, hK, hs⟩ := ha.support
    exact ⟨K, hK, fun n => hs (c n)⟩
  · intro k
    obtain ⟨C, hC, h⟩ := ha.frequencyOrder k
    exact ⟨C, hC, fun n => h (c n)⟩
  · intro k
    obtain ⟨C, hC, h⟩ := ha.pureBaseOrder k
    exact ⟨C, hC, fun n => h (c n)⟩
  · intro k
    obtain ⟨C, hC, h⟩ := ha.mixedOrder k
    exact ⟨C, hC, fun n => h (c n)⟩

private theorem UniformCompactSymbolFamily.inputs {ι : Type*} {a : ι → Space → Space → ℂ}
    (ha : UniformCompactSymbolFamily a) (i : ι) :
    FirstBaseFrequencyOrderOne (a i) ∧ CompactBaseOrderOne (a i) ∧ Continuous (uncurry (a i)) := by
  refine ⟨⟨⟨ha.smoothFrequency i, ?_⟩, ha.differentiableMixed i, ?_⟩,
    ⟨?_, ha.smoothBase i, ?_⟩, ha.jointlyContinuous i⟩
  · intro n
    obtain ⟨C, hC, h⟩ := ha.frequencyOrder n
    exact ⟨C, hC, h i⟩
  · intro n
    obtain ⟨C, hC, h⟩ := ha.mixedOrder n
    exact ⟨C, hC, h i⟩
  · obtain ⟨K, hK, h⟩ := ha.support
    exact ⟨K, hK, h i⟩
  · intro n
    obtain ⟨C, hC, h⟩ := ha.pureBaseOrder n
    exact ⟨C, hC, h i⟩

private structure MatrixCoefficientTest (κ : Type*) where
  coefficient : SchwartzMap Space ℂ
  lipschitzBound : NNReal
  valueBound : ℝ
  valueBound_nonneg : 0 ≤ valueBound
  compact : HasCompactSupport (coefficient : Space → ℂ)
  real : ∀ x, conj (coefficient x) = coefficient x
  value : ∀ᵐ x ∂(volume : Measure Space), ‖coefficient x‖ ≤ valueBound
  firstDerivative : ∀ᵐ x ∂(volume : Measure Space),
    ‖fderiv ℝ (coefficient : Space → ℂ) x‖ ≤ (lipschitzBound : ℝ)
  input : κ → SchwartzMap Space ℂ
  output : κ → SchwartzMap Space ℂ

private def MatrixCoefficientTest.scale {κ : Type*} [Fintype κ] (t : MatrixCoefficientTest κ) : ℝ :=
  (t.valueBound + (t.lipschitzBound : ℝ)) *
    ‖WithLp.toLp 2 (fun j => (t.input j).toLp 2 volume)‖ *
    ‖WithLp.toLp 2 (fun i => (t.output i).toLp 2 volume)‖

private theorem MatrixCoefficientTest.scale_nonneg {κ : Type*} [Fintype κ] (t : MatrixCoefficientTest κ) :
    0 ≤ t.scale := by
  unfold MatrixCoefficientTest.scale
  exact mul_nonneg (mul_nonneg (add_nonneg t.valueBound_nonneg t.lipschitzBound.coe_nonneg)
    (norm_nonneg _)) (norm_nonneg _)

private def MatrixCoefficientTest.pair {κ : Type*} [Fintype κ] (t : MatrixCoefficientTest κ)
    (a : κ → κ → Space → Space → ℂ) : ℂ :=
  matrixTestPair (matrixCoefficientCommutator a t.coefficient t.input) t.output

private theorem MatrixCoefficientTest.bound_normalized {κ : Type*} [Fintype κ]
    (t : MatrixCoefficientTest κ) {a : κ → κ → Space → Space → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (h : ‖t.pair a‖ ≤ C * t.scale) : ‖t.pair a / (t.scale : ℂ)‖ ≤ C := by
  by_cases h0 : t.scale = 0
  · simpa only [h0, Complex.ofReal_zero, div_zero, norm_zero] using hC
  · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg t.scale_nonneg]
    exact (div_le_iff₀ (lt_of_le_of_ne t.scale_nonneg (Ne.symm h0))).mpr h

private theorem MatrixCoefficientTest.compactBase_bound {κ : Type*} [Fintype κ]
    {a : κ → κ → Space → Space → ℂ}
    (ha : ∀ i j, FirstBaseFrequencyOrderOne (a i j) ∧ CompactBaseOrderOne (a i j) ∧
      Continuous (uncurry (a i j))) (hSym : MatrixFirstOrderFormalSymmetry a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : MatrixCoefficientTest κ, ‖t.pair a‖ ≤ C * t.scale := by
  obtain ⟨C, hC, hb⟩ := exists_compactBase_matrix_coefficientCommutator_L2_pair_bound
    (fun i j => (ha i j).1) (fun i j => (ha i j).2.1) (fun i j => (ha i j).2.2) hSym
  refine ⟨C, hC, fun t => ?_⟩
  simpa only [MatrixCoefficientTest.pair, matrixTestPair, MatrixCoefficientTest.scale, mul_assoc] using
    hb t.coefficient t.lipschitzBound t.valueBound t.valueBound_nonneg t.compact t.real t.value
      t.firstDerivative t.input t.output

/-- One actual L² commutator pairing constant works over a family with shared
compact support and shared pure and mixed order-one symbol seminorms. -/
theorem exists_uniform_compactBase_matrix_coefficientCommutator_L2_pair_bound
    {ι κ : Type*} [Fintype κ] {a : ι → κ → κ → Space → Space → ℂ}
    (ha : ∀ i j, UniformCompactSymbolFamily (fun n => a n i j))
    (hSym : ∀ n, MatrixFirstOrderFormalSymmetry (a n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0 ≤ U → HasCompactSupport (r : Space → ℂ) → (∀ x, conj (r x) = r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r : Space → ℂ) x‖ ≤ (L : ℝ)) →
      ∀ f g : κ → SchwartzMap Space ℂ,
        ‖∑ i, ∫ x, conj (g i x) * matrixCoefficientCommutator (a n) r f i x‖ ≤
          C * (U + (L : ℝ)) * ‖WithLp.toLp 2 (fun j => (f j).toLp 2 volume)‖ *
            ‖WithLp.toLp 2 (fun i => (g i).toLp 2 volume)‖ := by
  let F (n : ι) (t : MatrixCoefficientTest κ) := t.pair (a n) / (t.scale : ℂ)
  have hFixed (t : MatrixCoefficientTest κ) : ∃ M : ℝ, ∀ n, ‖F n t‖ ≤ M := by
    obtain ⟨M, hb⟩ := matrixTestPair_uniform_bound (fun n => matrixCoefficientCommutator (a n)
      t.coefficient t.input) t.output (uniformCompactMatrixFamily_commutator_bound ha t.coefficient t.input)
    refine ⟨M / t.scale, fun n => ?_⟩
    rw [show F n t = t.pair (a n) / (t.scale : ℂ) from rfl, norm_div, Complex.norm_real,
      Real.norm_of_nonneg t.scale_nonneg]
    exact div_le_div_of_nonneg_right (hb n) t.scale_nonneg
  have hSuperposition (c : ℕ → ι) (v : ℕ →ᵇ ℝ) : ∃ M : ℝ, ∀ t,
      ‖∑' n, ((((1 : ℝ)/2)^n) * v n) • F (c n) t‖ ≤ M := by
    let u (n : ℕ) := (((1 : ℝ)/2)^n) * v n
    have hg : Summable (fun n : ℕ => ((1 : ℝ)/2)^n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hu : Summable (fun n => ‖u n‖) := by
      refine .of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hg.mul_right ‖v‖)
      dsimp only [u]
      rw [norm_mul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (norm_coe_le_norm v n) (by positivity)
    let b := summableMatrixSymbolSum (fun n => a (c n)) u
    have hFam (i j : κ) : UniformCompactSymbolFamily (fun n => a (c n) i j) := (ha i j).reindex c
    have hInput (i j : κ) := summableSymbolSum_compactBase_inputs (hFam i j) hu
    have hSym' : MatrixFirstOrderFormalSymmetry b :=
      summableMatrixSymbolSum_formalSymmetry hFam (fun n => hSym (c n)) hu
    obtain ⟨C, hC, hb⟩ := MatrixCoefficientTest.compactBase_bound hInput hSym'
    refine ⟨C, fun t => ?_⟩
    have hEq : t.pair b / (t.scale : ℂ) = ∑' n, u n • F (c n) t := by
      unfold MatrixCoefficientTest.pair b
      rw [matrixCoefficientCommutatorPair_summableMatrixSymbolSum hFam hu, div_eq_mul_inv,
        real_weighted_tsum_mul]
      apply tsum_congr
      intro n
      rfl
    change ‖∑' n, u n • F (c n) t‖ ≤ C
    rw [← hEq]
    exact t.bound_normalized hC (hb t)
  obtain ⟨C, hC, bound⟩ := exists_uniform_symbol_family_bound_of_superpositions F hFixed hSuperposition
  refine ⟨C, hC, fun n r L U hU hr hReal hVal hDer f g => ?_⟩
  let t : MatrixCoefficientTest κ := ⟨r, L, U, hU, hr, hReal, hVal, hDer, f, g⟩
  suffices hp : ‖t.pair (a n)‖ ≤ C * t.scale by
    simpa only [t, MatrixCoefficientTest.pair, matrixTestPair, MatrixCoefficientTest.scale, mul_assoc] using hp
  by_cases h0 : t.scale = 0
  · obtain ⟨D, _, hD⟩ := MatrixCoefficientTest.compactBase_bound (fun i j => (ha i j).inputs n) (hSym n)
    simpa only [h0, mul_zero] using hD t
  · have hb := bound n t
    rw [show F n t = t.pair (a n) / (t.scale : ℂ) from rfl, norm_div, Complex.norm_real,
      Real.norm_of_nonneg t.scale_nonneg] at hb
    exact (div_le_iff₀ (lt_of_le_of_ne t.scale_nonneg (Ne.symm h0))).mp hb

end Burnett.Analysis.CarlesonEmbedding
