import Burnett.Analysis.Compactness.CountableTests
import Burnett.Analysis.Fourier.Projection

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.SeparablePositive

open MeasureTheory Filter Burnett.Fourier
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- A separable symbol is quantized by physical multiplication after its
frequency multiplier. -/
def separableOperator (a m : BoundedSymbol V) : ComplexL2 V →L[ℂ] ComplexL2 V :=
  (symbolCLM a).comp (fourierMultiplier m)

theorem separableOperator_norm_le (a m : BoundedSymbol V) (u : ComplexL2 V) :
    ‖separableOperator a m u‖ ≤ (a.bound * m.bound) * ‖u‖ := by
  change ‖symbolL2 a (fourierMultiplier m u)‖ ≤ _
  calc
    _ ≤ a.bound * ‖fourierMultiplier m u‖ := symbolL2_norm_le a _
    _ ≤ a.bound * (m.bound * ‖u‖) :=
      mul_le_mul_of_nonneg_left (fourierMultiplier_norm_le m u) a.bound_nonneg
    _ = _ := (mul_assoc _ _ _).symm

/-- Compactness in test-dependent complex disks for the actual ordered
quadratic pairings of every component on a common subsequence. -/
theorem exists_subsequence_bounded_ordered_pairings
    {J κ : Type*} [Countable J] [Countable κ]
    (T : J → ComplexL2 V →L[ℂ] ComplexL2 V) (C : J → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hT : ∀ j u, ‖T j u‖ ≤ C j * ‖u‖)
    (u : ℕ → κ → ComplexL2 V) (B : ℝ) (hB : ∀ n c, ‖u n c‖ ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : J → κ → κ → ℂ,
      (∀ j c d, ‖L j c d‖ ≤ C j * B ^ 2) ∧
      ∀ j c d, Tendsto (fun n => inner ℂ (T j (u (φ n) c)) (u (φ n) d)) atTop (𝓝 (L j c d)) := by
  let A (n : ℕ) (q : J × κ × κ) := inner ℂ (T q.1 (u n q.2.1)) (u n q.2.2)
  let K (q : J × κ × κ) := Metric.closedBall (0 : ℂ) (C q.1 * B ^ 2)
  have hA (n : ℕ) (q : J × κ × κ) : A n q ∈ K q := by
    rcases q with ⟨j, c, d⟩
    change inner ℂ (T j (u n c)) (u n d) ∈ Metric.closedBall (0 : ℂ) (C j * B ^ 2)
    rw [Metric.mem_closedBall, dist_zero_right]
    have hB0 : 0 ≤ B := (norm_nonneg (u n c)).trans (hB n c)
    calc
      _ ≤ ‖T j (u n c)‖ * ‖u n d‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ (C j * B) * B := mul_le_mul
        ((hT j (u n c)).trans (mul_le_mul_of_nonneg_left (hB n c) (hC j)))
        (hB n d) (norm_nonneg _) (mul_nonneg (hC j) hB0)
      _ = _ := by ring
  obtain ⟨L, hL, φ, hφ, hlim⟩ :=
    Burnett.Analysis.Compactness.exists_subsequence_all_tests A K (fun _ => isCompact_closedBall _ _) hA
  refine ⟨φ, hφ, fun j c d => L (j, c, d), ?_, fun j c d => hlim (j, c, d)⟩
  intro j c d
  simpa only [K, Metric.mem_closedBall, dist_zero_right] using hL (j, c, d)


end Burnett.Microlocal.SeparablePositive
