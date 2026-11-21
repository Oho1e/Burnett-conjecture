import Burnett.Analysis.PrincipalEnergy.Localization.SummableSymbolAction

set_option autoImplicit false
set_option maxHeartbeats 5600000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate

/-- The original finite-component Lebesgue pairing with a Schwartz test. -/
def matrixTestPair {κ : Type*} [Fintype κ] (v : κ → Space → ℂ) (g : κ → SchwartzMap Space ℂ) : ℂ :=
  ∑ i, ∫ x, conj (g i x) * v i x

private theorem weighted_summable_of_bound {u : ℕ → ℝ} (hu : Summable (fun n => ‖u n‖))
    {z : ℕ → ℂ} {M : ℝ} (h : ∀ n, ‖z n‖ ≤ M) : Summable (fun n => u n • z n) :=
  .of_norm_bounded (hu.mul_right M) fun n => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (h n) (norm_nonneg _)

private theorem testedRow_bound {v : Space → ℂ} {M : ℝ} (h : ∀ x, ‖v x‖ ≤ M)
    (g : SchwartzMap Space ℂ) :
    ‖∫ x, conj (g x) * v x‖ ≤ M * (∫ x, ‖g x‖) := by
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (g.integrable.norm.const_mul M)
  filter_upwards with x
  rw [norm_mul, Complex.norm_conj, mul_comm M]
  exact mul_le_mul_of_nonneg_left (h x) (norm_nonneg _)

/-- A uniform pointwise bound for a fixed input gives a uniform tested
bound on the entire family. -/
theorem matrixTestPair_uniform_bound {ι κ : Type*} [Fintype κ] (v : ι → κ → Space → ℂ)
    (g : κ → SchwartzMap Space ℂ) (h : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ n x, ‖v n i x‖ ≤ M) :
    ∃ M : ℝ, ∀ n, ‖matrixTestPair (v n) g‖ ≤ M := by
  choose M _ hb using h
  refine ⟨∑ i, M i * (∫ x, ‖g i x‖), fun n => ?_⟩
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => testedRow_bound (hb i n) (g i))

/-- A summable real superposition can be taken through the finite matrix
pairing when each row has a shared pointwise bound. -/
theorem matrixTestPair_real_weighted_tsum {κ : Type*} [Fintype κ] (v : ℕ → κ → Space → ℂ)
    (g : κ → SchwartzMap Space ℂ) (hC : ∀ n i, Continuous (v n i))
    (h : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ n x, ‖v n i x‖ ≤ M)
    {u : ℕ → ℝ} (hu : Summable (fun n => ‖u n‖)) :
    matrixTestPair (fun i x => ∑' n, u n • v n i x) g = ∑' n, u n • matrixTestPair (v n) g := by
  choose M _ hb using h
  let I (i : κ) (n : ℕ) := ∫ x, conj (g i x) * v n i x
  have hRow (i : κ) : (∫ x, conj (g i x) * (∑' n, u n • v n i x)) = ∑' n, u n • I i n := by
    simp_rw [mul_real_weighted_tsum]
    refine integral_real_weighted_tsum hu (fun n x => conj (g i x) * v n i x)
      ((g i).integrable.norm.const_mul (M i))
      (fun n => ((Complex.continuous_conj.comp (g i).continuous).mul (hC n i)).aestronglyMeasurable)
      (fun n x => ?_)
    rw [norm_mul, Complex.norm_conj, mul_comm (M i)]
    exact mul_le_mul_of_nonneg_left (hb i n x) (norm_nonneg _)
  have hS (i : κ) : Summable (fun n => u n • I i n) :=
    weighted_summable_of_bound hu (fun n => testedRow_bound (hb i n) (g i))
  unfold matrixTestPair
  simp only [hRow, Finset.smul_sum]
  exact (Summable.tsum_finsetSum (fun i _ => hS i)).symm

/-- A summable real superposition of finite matrix symbols. -/
def summableMatrixSymbolSum {κ : Type*} (a : ℕ → κ → κ → Space → Space → ℂ)
    (u : ℕ → ℝ) (i j : κ) : Space → Space → ℂ :=
  summableSymbolSum (fun n => a n i j) u

theorem uniformCompactMatrixFamily_action_bound {ι κ : Type*} [Fintype κ]
    {a : ι → κ → κ → Space → Space → ℂ}
    (ha : ∀ i j, UniformCompactSymbolFamily (fun n => a n i j))
    (f : κ → SchwartzMap Space ℂ) (i : κ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n x, ‖matrixFirstOrderAction (a n) f i x‖ ≤ M := by
  choose M hM hb using fun j => uniformCompactSymbolFamily_action_bound (ha i j) (f j)
  exact ⟨∑ j, M j, Finset.sum_nonneg (fun j _ => hM j), fun n x =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hb j n x))⟩

theorem uniformCompactMatrixFamily_action_continuous {ι κ : Type*} [Fintype κ]
    {a : ι → κ → κ → Space → Space → ℂ}
    (ha : ∀ i j, UniformCompactSymbolFamily (fun n => a n i j))
    (f : κ → SchwartzMap Space ℂ) (n : ι) (i : κ) :
    Continuous (matrixFirstOrderAction (a n) f i) :=
  continuous_finset_sum _ fun j _ => firstOrderAction_continuous_for_family (ha i j) n (f j)

theorem matrixFirstOrderAction_summableMatrixSymbolSum {κ : Type*} [Fintype κ]
    {a : ℕ → κ → κ → Space → Space → ℂ}
    (ha : ∀ i j, UniformCompactSymbolFamily (fun n => a n i j))
    {u : ℕ → ℝ} (hu : Summable (fun n => ‖u n‖)) (f : κ → SchwartzMap Space ℂ) (i : κ) (x : Space) :
    matrixFirstOrderAction (summableMatrixSymbolSum a u) f i x =
      ∑' n, u n • matrixFirstOrderAction (a n) f i x := by
  have hS (j : κ) : Summable (fun n => u n • firstOrderAction (a n i j) (f j) x) := by
    obtain ⟨M, _, hb⟩ := uniformCompactSymbolFamily_action_bound (ha i j) (f j)
    exact weighted_summable_of_bound hu (fun n => hb n x)
  simp only [matrixFirstOrderAction, summableMatrixSymbolSum,
    firstOrderAction_summableSymbolSum (ha i _) hu, Finset.smul_sum]
  exact (Summable.tsum_finsetSum (fun j _ => hS j)).symm

private theorem matrixAdjointPair_eq_conj {κ : Type*} [Fintype κ]
    (a : κ → κ → Space → Space → ℂ) (f g : κ → SchwartzMap Space ℂ) :
    (∑ i, ∫ x, conj (matrixFirstOrderAction a g i x) * f i x) =
      conj (matrixTestPair (matrixFirstOrderAction a g) f) := by
  unfold matrixTestPair
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [map_mul, starRingEnd_self_apply]
  exact mul_comm _ _

/-- Real summation preserves symmetry of the actual matrix Fourier action. -/
theorem summableMatrixSymbolSum_formalSymmetry {κ : Type*} [Fintype κ]
    {a : ℕ → κ → κ → Space → Space → ℂ}
    (ha : ∀ i j, UniformCompactSymbolFamily (fun n => a n i j))
    (hSym : ∀ n, MatrixFirstOrderFormalSymmetry (a n))
    {u : ℕ → ℝ} (hu : Summable (fun n => ‖u n‖)) :
    MatrixFirstOrderFormalSymmetry (summableMatrixSymbolSum a u) := by
  intro f g
  let b := summableMatrixSymbolSum a u
  have pair (f g : κ → SchwartzMap Space ℂ) :
      matrixTestPair (matrixFirstOrderAction b f) g =
        ∑' n, u n • matrixTestPair (matrixFirstOrderAction (a n) f) g := by
    rw [show matrixFirstOrderAction b f = (fun i x => ∑' n, u n • matrixFirstOrderAction (a n) f i x) from
      funext fun i => funext (matrixFirstOrderAction_summableMatrixSymbolSum ha hu f i)]
    exact matrixTestPair_real_weighted_tsum _ g
      (uniformCompactMatrixFamily_action_continuous ha f)
      (uniformCompactMatrixFamily_action_bound ha f) hu
  change matrixTestPair (matrixFirstOrderAction b f) g = _
  rw [matrixAdjointPair_eq_conj, pair, pair]
  change _ = Complex.conjCLE (∑' n, u n • matrixTestPair (matrixFirstOrderAction (a n) g) f)
  rw [Complex.conjCLE.map_tsum]
  apply tsum_congr
  intro n
  rw [map_smul, Complex.conjCLE_apply, ← matrixAdjointPair_eq_conj]
  exact congrArg (fun z : ℂ => u n • z) (hSym n f g)

/-- The actual commutator row for a fixed coefficient and input is uniformly
bounded on the symbol family. -/
theorem uniformCompactMatrixFamily_commutator_bound {ι κ : Type*} [Fintype κ]
    {a : ι → κ → κ → Space → Space → ℂ}
    (ha : ∀ i j, UniformCompactSymbolFamily (fun n => a n i j))
    (r : SchwartzMap Space ℂ) (f : κ → SchwartzMap Space ℂ) (i : κ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n x, ‖matrixCoefficientCommutator (a n) r f i x‖ ≤ M := by
  obtain ⟨A, hA, ha₀⟩ := uniformCompactMatrixFamily_action_bound ha f i
  obtain ⟨B, hB, hb⟩ := uniformCompactMatrixFamily_action_bound ha (fun j => scalarSchwartzProduct r (f j)) i
  let S := SchwartzMap.seminorm ℝ 0 0 r
  have hS : 0 ≤ S := (norm_nonneg _).trans (SchwartzMap.norm_le_seminorm ℝ r (0 : Space))
  refine ⟨S*A+B, by positivity, fun n x => ?_⟩
  unfold matrixCoefficientCommutator
  refine (norm_sub_le _ _).trans (add_le_add ?_ (hb n x))
  rw [norm_mul]
  exact mul_le_mul (SchwartzMap.norm_le_seminorm ℝ r x) (ha₀ n x) (norm_nonneg _) hS

theorem matrixCoefficientCommutator_summableMatrixSymbolSum {κ : Type*} [Fintype κ]
    {a : ℕ → κ → κ → Space → Space → ℂ} (ha : ∀ i j, UniformCompactSymbolFamily (fun n => a n i j))
    {u : ℕ → ℝ} (hu : Summable (fun n => ‖u n‖)) (r : SchwartzMap Space ℂ)
    (f : κ → SchwartzMap Space ℂ) (i : κ) (x : Space) :
    matrixCoefficientCommutator (summableMatrixSymbolSum a u) r f i x =
      ∑' n, u n • matrixCoefficientCommutator (a n) r f i x := by
  let F := fun j => scalarSchwartzProduct r (f j)
  obtain ⟨A, _, ha₀⟩ := uniformCompactMatrixFamily_action_bound ha f i
  obtain ⟨B, _, hb⟩ := uniformCompactMatrixFamily_action_bound ha F i
  have hP : Summable (fun n => u n • (r x * matrixFirstOrderAction (a n) f i x)) :=
    weighted_summable_of_bound hu (M := ‖r x‖ * A) (fun n => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (ha₀ n x) (norm_nonneg _))
  have hQ : Summable (fun n => u n • matrixFirstOrderAction (a n) F i x) :=
    weighted_summable_of_bound hu (fun n => hb n x)
  simp only [matrixCoefficientCommutator, matrixFirstOrderAction_summableMatrixSymbolSum ha hu,
    mul_real_weighted_tsum, smul_sub]
  exact (hP.tsum_sub hQ).symm

theorem matrixCoefficientCommutatorPair_summableMatrixSymbolSum {κ : Type*} [Fintype κ]
    {a : ℕ → κ → κ → Space → Space → ℂ} (ha : ∀ i j, UniformCompactSymbolFamily (fun n => a n i j))
    {u : ℕ → ℝ} (hu : Summable (fun n => ‖u n‖)) (r : SchwartzMap Space ℂ)
    (f g : κ → SchwartzMap Space ℂ) :
    matrixTestPair (matrixCoefficientCommutator (summableMatrixSymbolSum a u) r f) g =
      ∑' n, u n • matrixTestPair (matrixCoefficientCommutator (a n) r f) g := by
  rw [show matrixCoefficientCommutator (summableMatrixSymbolSum a u) r f =
      (fun i x => ∑' n, u n • matrixCoefficientCommutator (a n) r f i x) from
    funext fun i => funext (matrixCoefficientCommutator_summableMatrixSymbolSum ha hu r f i)]
  refine matrixTestPair_real_weighted_tsum _ g (fun n i => ?_)
    (uniformCompactMatrixFamily_commutator_bound ha r f) hu
  exact (r.continuous.mul (uniformCompactMatrixFamily_action_continuous ha f n i)).sub
    (uniformCompactMatrixFamily_action_continuous ha (fun j => scalarSchwartzProduct r (f j)) n i)

end Burnett.Analysis.CarlesonEmbedding
