import Burnett.Analysis.Microlocal.PhysicalDensity
import Burnett.Analysis.TransportWard.Weyl.WeylCutoffPatchLp
import Burnett.Analysis.CubicEnergy.CompleteEnergy.UniformWeightedEuclidean

set_option autoImplicit false
set_option maxHeartbeats 4400000
set_option maxRecDepth 4000

noncomputable section

namespace Burnett.V03

open Filter MeasureTheory Set Burnett.Geometry Burnett.RicciSymbol Burnett.P01
open ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence MaximalChart
open Burnett.A02.FrequencySplit
open Burnett.A02.FieldAndCoefficientReview (fieldValueArray)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ContDiff ENNReal Manifold Topology

local notation "J" => OrderedPair

private theorem norm_euclidean_le_sum {ι : Type} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    ‖v‖ ≤ ∑ i, ‖v i‖ := by
  classical
  have hExpansion : (∑ i, v i • EuclideanSpace.single i (1 : ℂ)) = v := by
    simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun ι ℂ).sum_repr v
  calc
    ‖v‖ = ‖∑ i, v i • EuclideanSpace.single i (1 : ℂ)‖ := congrArg norm hExpansion.symm
    _ ≤ ∑ i, ‖v i • EuclideanSpace.single i (1 : ℂ)‖ := norm_sum_le _ _
    _ = ∑ i, ‖v i‖ := by simp [norm_smul]

private theorem orderedValueArrayLp_le_matrix (w : ProjectionSchwartzMatrix) (p : ℝ) :
    eLpNorm (fieldValueArray (fun i : J => w i.1 i.2)) (ENNReal.ofReal p) volume ≤
      (Fintype.card J : ℝ≥0∞) * projectionMatrixLpNorm p w := by
  let N := (Fintype.card J : ℝ)
  have hN : 0 ≤ N := by positivity
  have hNnorm : ‖N‖ₑ = (Fintype.card J : ℝ≥0∞) := by
    rw [Real.enorm_eq_ofReal hN]
    simp only [N, ENNReal.ofReal_natCast]
  rw [← hNnorm, projectionMatrixLpNorm, ← eLpNorm_const_smul N]
  apply eLpNorm_mono
  intro x
  rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hN]
  refine (norm_euclidean_le_sum _).trans ?_
  change (∑ i : J, ‖w i.1 i.2 x‖) ≤ N * ‖fun i j => w i j x‖
  calc
    _ ≤ ∑ _i : J, ‖fun i j => w i j x‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_le_pi_norm (fun j => w i.1 j x) i.2).trans
        (norm_le_pi_norm (fun (a b : Index) => w a b x) i.1)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private theorem orderedGradientL3_le_matrix (w : ProjectionSchwartzMatrix) :
    euclideanFieldGradientNorm (fun i : J => w i.1 i.2) ≤
      (Fintype.card J : ℝ≥0∞) * ∑ a : Index, projectionMatrixLpNorm 3 (projectionMatrixDerivative a w) := by
  let N := (Fintype.card J : ℝ)
  let F (a : Index) (x : E) := ‖fun i j => projectionMatrixDerivative a w i j x‖
  have hN : 0 ≤ N := by positivity
  have hNnorm : ‖N‖ₑ = (Fintype.card J : ℝ≥0∞) := by
    rw [Real.enorm_eq_ofReal hN]
    simp only [N, ENNReal.ofReal_natCast]
  have hF (a : Index) : AEStronglyMeasurable (F a) volume := by
    have hCont : Continuous (fun x : E => fun i j => projectionMatrixDerivative a w i j x) :=
      continuous_pi fun i => continuous_pi fun j => (projectionMatrixDerivative a w i j).continuous
    exact hCont.norm.aestronglyMeasurable
  have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 3 := by norm_num
  have hSum (x : E) :
      ‖euclideanFieldGradient (fun i : J => w i.1 i.2) x‖ ≤ N * ∑ a, F a x := by
    refine (norm_euclidean_le_sum _).trans ?_
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    change (∑ i : J, ‖projectionMatrixDerivative a w i.1 i.2 x‖) ≤ N * F a x
    calc
      _ ≤ ∑ _i : J, F a x := by
        apply Finset.sum_le_sum
        intro i _
        exact (norm_le_pi_norm (fun j => projectionMatrixDerivative a w i.1 j x) i.2).trans
          (norm_le_pi_norm (fun (j k : Index) => projectionMatrixDerivative a w j k x) i.1)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold euclideanFieldGradientNorm
  calc
    _ ≤ eLpNorm (N • ∑ a : Index, F a) (ENNReal.ofReal 3) volume := by
      apply eLpNorm_mono
      intro x
      rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hN, Finset.sum_apply, Real.norm_of_nonneg]
      · exact hSum x
      · exact Finset.sum_nonneg fun a _ => norm_nonneg _
    _ = ‖N‖ₑ * eLpNorm (∑ a : Index, F a) (ENNReal.ofReal 3) volume :=
      eLpNorm_const_smul N (∑ a : Index, F a) (ENNReal.ofReal 3) volume
    _ ≤ ‖N‖ₑ * ∑ a : Index, eLpNorm (F a) (ENNReal.ofReal 3) volume :=
      mul_le_mul_left' (eLpNorm_sum_le (fun a _ => hF a) hq) _
    _ = _ := by simp only [hNnorm, F, eLpNorm_norm, projectionMatrixLpNorm]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The exact original ordered input satisfies the paper's full Euclidean
L³ value and gradient estimates on its fixed compact cutoff support. -/
theorem exists_originalOrderedWeylCutoff_euclidean_patchL3
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (K : Set E) (hK : IsCompact K) (hχK : tsupport (χ : E → ℝ) ⊆ K) :
    let Z n (i : J) := fixedWeylPerturbationSchwartz B g hB hg c χ hχ n i
    ∃ (e : ℕ → ℝ) (C : ℝ), (∀ n, 0 ≤ e n) ∧ 0 ≤ C ∧ Tendsto e atTop (𝓝 0) ∧
      Tendsto (fun n => euclideanFieldValueL3 (Z n)) atTop (𝓝 0) ∧
      ∀ n, eLpNorm (fieldValueArray (Z n)) (ENNReal.ofReal 3) volume ≤
        ENNReal.ofReal (e n) * volume K ^ (1 / 3 : ℝ) ∧
        euclideanFieldGradientNorm (Z n) ≤ ENNReal.ofReal C * volume K ^ (1 / 3 : ℝ) := by
  intro Z
  let w (n : ℕ) : ProjectionSchwartzMatrix := fun i j => Z n (i,j)
  obtain ⟨e, C, he, hC, heLim, hBound⟩ :=
    exists_originalWeylCutoff_matrix_patchLp r B g hB hg hn hconv hb c χ hχ K hK hχK
  have hBnd := (hBound 3 (by norm_num)).2
  let V : ℝ≥0∞ := volume K ^ (1 / 3 : ℝ)
  have hV : V ≠ ⊤ := (ENNReal.rpow_lt_top_of_nonneg (by positivity) hK.measure_lt_top.ne).ne
  let N := (Fintype.card J : ℝ)
  let L := (Fintype.card Index : ℝ)
  have hN : 0 ≤ N := by positivity
  have hL : 0 ≤ L := by positivity
  let e' (n : ℕ) := N * e n
  have he' (n : ℕ) : 0 ≤ e' n := mul_nonneg hN (he n)
  have heLim' : Tendsto e' atTop (𝓝 0) := by
    simpa only [e', mul_zero] using heLim.const_mul N
  have hVal (n : ℕ) : eLpNorm (fieldValueArray (Z n)) (ENNReal.ofReal 3) volume ≤
      ENNReal.ofReal (e' n) * V := by
    have hEq : (fun i : J => w n i.1 i.2) = Z n := by funext i; cases i; rfl
    have hStep := orderedValueArrayLp_le_matrix (w n) 3
    rw [hEq] at hStep
    refine hStep.trans ((mul_le_mul_left' (hBnd n).1 _).trans_eq ?_)
    rw [show (Fintype.card J : ℝ≥0∞) = ENNReal.ofReal N by simp [N], ← mul_assoc,
      ← ENNReal.ofReal_mul hN]
  have hGrad (n : ℕ) : euclideanFieldGradientNorm (Z n) ≤ ENNReal.ofReal (N * L * C) * V := by
    have hEq : (fun i : J => w n i.1 i.2) = Z n := by funext i; cases i; rfl
    have hStep := orderedGradientL3_le_matrix (w n)
    rw [hEq] at hStep
    have hSum := Finset.sum_le_sum (s := (Finset.univ : Finset Index))
      (fun a _ => (hBnd n).2 a)
    refine hStep.trans ((mul_le_mul_left' hSum _).trans_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      show (Fintype.card J : ℝ≥0∞) = ENNReal.ofReal N by simp [N],
      show (Fintype.card Index : ℝ≥0∞) = ENNReal.ofReal L by simp [L], ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul hN, ← ENNReal.ofReal_mul (mul_nonneg hN hL)]
  refine ⟨e', N * L * C, he', mul_nonneg (mul_nonneg hN hL) hC, heLim', ?_,
    fun n => ⟨hVal n, hGrad n⟩⟩
  have hLim : Tendsto (fun n => e' n * V.toReal) atTop (𝓝 0) := by
    simpa only [zero_mul] using heLim'.mul_const V.toReal
  refine squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => ?_) hLim
  have h := ENNReal.toReal_mono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hV.lt_top).ne (hVal n)
  simpa only [euclideanFieldValueL3, ENNReal.toReal_mul, ENNReal.toReal_ofReal (he' n)] using h

end Burnett.V03
