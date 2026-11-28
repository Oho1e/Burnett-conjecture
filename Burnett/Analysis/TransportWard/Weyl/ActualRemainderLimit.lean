import Burnett.Analysis.TransportWard.Weyl.ActualRemainderCoefficient

/-! The true Taylor coefficient in the original scalar order-one test pairing. -/

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 4000

noncomputable section

namespace Burnett.V03

open Filter Set MeasureTheory Burnett.Analysis.CarlesonEmbedding Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped BigOperators ComplexConjugate ContDiff Matrix.Norms.Elementwise NNReal Topology

/-- The test is scalar in every field component and is given by its exact
left-quantized action on the compact domain. The same action occurs in the
estimate. Its formal symmetry must hold on the full Schwartz domain. -/
theorem tendsto_chartMetricRemainderPrincipal_of_leftAction
    {ι : Type*} [Fintype ι] {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hs : ContDiff ℝ ∞ (Function.uncurry a))
    (hb : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ k (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hda : ∀ b : Fin 4, FirstBaseFrequencyOrderOne (baseDirectionSymbol a (coordinateDirection b)))
    (hdb : ∀ (b : Fin 4) (k : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ k (fun y => baseDirectionSymbol a (coordinateDirection b) y ξ) x‖ ≤
        C * (1 + ‖ξ‖))
    (hp : ProperKernelRelation (firstOrderKernelRelation a)) (hSym : FirstOrderFormalSymmetry a)
    (B : SchwartzMap Space ℂ → Space → ℂ)
    (hExact : ∀ v : SchwartzMap Space ℂ, HasCompactSupport (v : Space → ℂ) →
      B v = firstOrderAction a v)
    (S : ι → Mat) {U : Set Space} (hU : IsOpen U)
    {χA : Space → ℝ} (hχA : ContDiff ℝ ∞ χA) (hχAU : tsupport χA ⊆ U)
    {K : Set Mat} (hK : IsCompact K) (hKdet : K ⊆ nonsingularMetricDomain)
    (G : Space → Mat) (H : ℕ → Space → Mat)
    (hG : ContDiffOn ℝ ∞ G U) (hH : ∀ n, ContDiffOn ℝ ∞ (H n) U)
    (hseg : ∀ n, ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, fieldSegment (G x) (H n x) t ∈ K)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (W P Q F : ℝ) (hW : 0 ≤ W) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hχA₀ : ∀ x, ‖χA x‖ ≤ W) (hχA₁ : ∀ x, ‖fderiv ℝ χA x‖ ≤ W)
    (hsmall : ∀ n, ∀ x ∈ U, ‖H n x‖ ≤ ε n)
    (hbase : ∀ x ∈ U, ‖fderiv ℝ G x‖ ≤ P)
    (hweak : ∀ n, ∀ x ∈ U, ‖fderiv ℝ (H n) x‖ ≤ Q)
    (f : ℕ → CompactSchwartzComponents ι)
    (hf : ∀ n, compactMatrixCoordinateH1 (f n) ≤ F) :
    Tendsto (fun n => 2 * (∑ i, ∫ x, conj (B ((f n).val i) x) *
      compactFinitePrincipalField (chartMetricRemainderCoefficient S χA G (H n)) (f n) i x).im)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,estimate⟩ := exists_actual_matrixCoefficient_principal_energy_bound (ι := ι)
    ha hs hb hda hdb hp hSym
  obtain ⟨M,hM,coef⟩ := exists_chartMetricRemainderCoefficient_bounds S hK hKdet
  let A (n : ℕ) := chartMetricRemainderCoefficient S χA G (H n)
  let s (n : ℕ) := W * M * (ε n)^2
  let d (n : ℕ) := s n + W * (M * (ε n)^2 * P + M * ε n * Q)
  have hs' (n : ℕ) : 0 ≤ s n := by dsimp [s]; positivity
  have hd' (n : ℕ) : 0 ≤ d n := by
    have hn := hε n
    dsimp [d, s]
    positivity
  let L (n : ℕ) : ℝ≥0 := ⟨d n, hd' n⟩
  have bound (n : ℕ) (b c : Fin 4) (i j : ι) x :
      ‖A n b c i j x‖ ≤ s n ∧ ‖fderiv ℝ (A n b c i j) x‖ ≤ d n :=
    coef hU (hχA.differentiable (by simp)) hχAU (hG.differentiableOn (by simp))
      ((hH n).differentiableOn (by simp)) (hseg n) W (ε n) P Q hW (hε n) hP hQ hχA₀ hχA₁
      (hsmall n) hbase (hweak n) b c i j x
  have smooth (n : ℕ) := chartMetricRemainderCoefficient_smooth S hU hχA hχAU hG (hH n)
    (fun x hx t ht => hKdet (hseg n x hx t ht))
  have sLim : Tendsto s atTop (𝓝 0) := by
    simpa only [s, zero_pow (show 2 ≠ 0 by decide), mul_zero] using (hlim.pow 2).const_mul (W*M)
  have dLim : Tendsto d atTop (𝓝 0) := by
    have aux₂ := (((hlim.pow 2).const_mul M).mul_const P)
    have aux₁ := ((hlim.const_mul M).mul_const Q)
    simpa only [d, zero_pow (show 2 ≠ 0 by decide), mul_zero, zero_mul, add_zero] using
      sLim.add ((aux₂.add aux₁).const_mul W)
  apply squeeze_zero_norm (a := fun n => (C * (s n + d n)) * F^2)
  · intro n
    have he := estimate (A n) (smooth n) (L n) (s n) (hs' n)
      (chartMetricRemainderCoefficient_hermitian S χA G (H n))
      (fun b c i j => Eventually.of_forall fun x => (bound n b c i j x).1)
      (fun b c i j => Eventually.of_forall fun x => (bound n b c i j x).2) (f n)
    have hbEq (i : ι) := hExact ((f n).val i) ((f n).property i)
    simp only [hbEq, Real.norm_eq_abs]
    refine he.trans ?_
    change C * (s n + d n) * (compactMatrixCoordinateH1 (f n))^2 ≤ _
    have base_nonneg : 0 ≤ compactMatrixCoordinateH1 (f n) := norm_nonneg _
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ base_nonneg (hf n) 2)
      (mul_nonneg hC (add_nonneg (hs' n) (hd' n)))
  · simpa only [add_zero, mul_zero, zero_mul] using (((sLim.add dLim).const_mul C).mul_const (F^2))

end Burnett.V03
