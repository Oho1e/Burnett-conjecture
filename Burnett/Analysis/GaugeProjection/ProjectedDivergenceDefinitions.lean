import Burnett.Analysis.GaugeProjection.MatrixLipschitzCoefficientBound

set_option autoImplicit false
set_option maxHeartbeats 2900000

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter
open Burnett.A02.FrequencySplit (E)
open Burnett.A07 (coordinateDerivative)
open Burnett.Fourier
open scoped ContDiff NNReal BigOperators

/-- The chosen smooth coordinate coefficients, with their common global
Lipschitz bound. The coefficients themselves may grow linearly. -/
structure ProjectedSourceCoefficients where
  entry : Fin 4 → Fin 4 → E → ℂ
  smooth : ∀ a b, ContDiff ℝ ∞ (entry a b)
  slope : ℝ≥0
  lipschitz : ∀ a b, LipschitzWith slope (entry a b)

/-- Regard the real inverse metric coefficients from the manuscript as
scalar coefficients on the complex Fourier fields. -/
def ProjectedSourceCoefficients.ofReal (a : Fin 4 → Fin 4 → E → ℝ)
    (hs : ∀ i j, ContDiff ℝ ∞ (a i j)) (L : ℝ≥0) (hL : ∀ i j, LipschitzWith L (a i j)) :
    ProjectedSourceCoefficients :=
  { entry := fun i j x => (a i j x : ℂ)
    smooth := fun i j => Complex.ofRealCLM.contDiff.comp (hs i j)
    slope := L
    lipschitz := fun i j => by
      simpa only [one_mul] using Complex.ofRealLI.isometry.lipschitz.comp (hL i j) }

private abbrev sourceDirection (a : Fin 4) : E := EuclideanSpace.single a 1

/-- The pointwise derivative \(\partial_a a^{ab}\) of the chosen coefficient. -/
def projectedSourceCoefficientDerivative (A : ProjectedSourceCoefficients) (a b : Fin 4) (x : E) : ℂ :=
  fderiv ℝ (A.entry a b) x (sourceDirection a)

private theorem projectedSourceCoefficientDerivative_continuous
    (A : ProjectedSourceCoefficients) (a b : Fin 4) :
    Continuous (projectedSourceCoefficientDerivative A a b) :=
  ((A.smooth a b).continuous_fderiv (by norm_num : 1 ≤ ∞)).clm_apply continuous_const

private theorem projectedSourceCoefficientDerivative_norm_le
    (A : ProjectedSourceCoefficients) (a b : Fin 4) (x : E) :
    ‖projectedSourceCoefficientDerivative A a b x‖ ≤ (A.slope : ℝ) := by
  have h := (fderiv ℝ (A.entry a b) x).le_opNorm (sourceDirection a)
  rw [EuclideanSpace.norm_single, norm_one, mul_one] at h
  exact h.trans (norm_fderiv_le_of_lipschitz ℝ (A.lipschitz a b))

private def projectedSourceDerivativeSymbol (A : ProjectedSourceCoefficients) (a b : Fin 4) : BoundedSymbol E :=
  { toFun := projectedSourceCoefficientDerivative A a b
    measurable := (projectedSourceCoefficientDerivative_continuous A a b).aestronglyMeasurable
    bound := A.slope
    bound_nonneg := A.slope.2
    norm_le := projectedSourceCoefficientDerivative_norm_le A a b }

/-- Multiplication in physical \(L^2\) by the actual coefficient derivative. -/
def projectedSourceDerivativeProduct (A : ProjectedSourceCoefficients) (a b : Fin 4)
    (u : ComplexL2 E) : ComplexL2 E :=
  symbolL2 (projectedSourceDerivativeSymbol A a b) u

theorem projectedSourceDerivativeProduct_norm_le (A : ProjectedSourceCoefficients) (a b : Fin 4)
    (u : ComplexL2 E) : ‖projectedSourceDerivativeProduct A a b u‖ ≤ (A.slope : ℝ) * ‖u‖ :=
  symbolL2_norm_le _ _

private theorem projectedSourceDerivativeProduct_ae (A : ProjectedSourceCoefficients) (a b : Fin 4)
    (u : SchwartzMap E ℂ) :
    (projectedSourceDerivativeProduct A a b (u.toLp 2 volume) : E → ℂ) =ᵐ[volume]
      fun x => projectedSourceCoefficientDerivative A a b x * u x := by
  exact (symbolL2_ae (projectedSourceDerivativeSymbol A a b) (u.toLp 2 volume)).trans
    ((u.coeFn_toLp 2 volume).mono fun x h => congrArg (projectedSourceCoefficientDerivative A a b x * ·) h)

/-- The original nondivergence expression \(Qz=\sum_{a,b} a^{ab}\partial_a\partial_bz\),
with its true coefficient products represented in \(L^2\). -/
def projectedSourceQ (A : ProjectedSourceCoefficients) (z : ProjectionSchwartzMatrix) :
    ProjectionL2Matrix :=
  ∑ a, ∑ b, fun i j =>
    projectionLipschitzCoefficientProductL2 (A.entry a b) A.slope (A.lipschitz a b)
      (coordinateDerivative a (coordinateDerivative b (z i j)))

/-- The first-order term with the actual derivatives of the same coefficients. -/
def projectedSourceCoefficientCorrection (A : ProjectedSourceCoefficients)
    (u : ProjectionSchwartzMatrix) : ProjectionL2Matrix :=
  ∑ a, ∑ b, fun i j =>
    projectedSourceDerivativeProduct A a b ((coordinateDerivative b (u i j)).toLp 2 volume)

/-- The literal classical negative divergence in the chart extended to \(\mathbb R^4\). -/
def projectedSourceDivergencePointwise (A : ProjectedSourceCoefficients)
    (u : ProjectionSchwartzMatrix) (i j : Fin 4) (x : E) : ℂ :=
  -∑ a, ∑ b, fderiv ℝ (fun y => A.entry a b y * coordinateDerivative b (u i j) y) x
    (sourceDirection a)

private theorem projectedSource_product_derivative (A : ProjectedSourceCoefficients)
    (a b : Fin 4) (w : SchwartzMap E ℂ) (x : E) :
    fderiv ℝ (fun y => A.entry a b y * coordinateDerivative b w y) x (sourceDirection a) =
      A.entry a b x * coordinateDerivative a (coordinateDerivative b w) x +
        projectedSourceCoefficientDerivative A a b x * coordinateDerivative b w x := by
  let v := coordinateDerivative b w
  change fderiv ℝ (fun y => A.entry a b y * v y) x (sourceDirection a) =
    A.entry a b x * coordinateDerivative a v x + projectedSourceCoefficientDerivative A a b x * v x
  rw [fderiv_fun_mul ((A.smooth a b).differentiable (by norm_num) x) v.differentiableAt]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    coordinateDerivative, SchwartzMap.pderivCLM_apply, projectedSourceCoefficientDerivative]
  ring

private theorem sourceLpSum_ae (g : Fin 4 → ComplexL2 E) :
    ((∑ j, g j : ComplexL2 E) : E → ℂ) =ᵐ[volume] fun x => ∑ j, g j x := by
  classical
  generalize (Finset.univ : Finset (Fin 4)) = s
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (Lp.coeFn_zero ℂ 2 (volume : Measure E))
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (g j) (∑ k ∈ s, g k), ih] with x hx hs
    simp only [Pi.add_apply] at hx
    rw [hx, hs]

private theorem sourceLpDoubleSum_ae (g : Fin 4 → Fin 4 → ComplexL2 E) :
    ((∑ a, ∑ b, g a b : ComplexL2 E) : E → ℂ) =ᵐ[volume] fun x => ∑ a, ∑ b, g a b x := by
  filter_upwards [sourceLpSum_ae (fun a => ∑ b, g a b), ae_all_iff.mpr fun a => sourceLpSum_ae (g a)]
    with x hx h
  exact hx.trans (Finset.sum_congr rfl fun a _ => h a)

theorem projectedSourceQ_ae (A : ProjectedSourceCoefficients)
    (u : ProjectionSchwartzMatrix) (i j : Fin 4) :
    (projectedSourceQ A u i j : E → ℂ) =ᵐ[volume]
      fun x => ∑ a, ∑ b, A.entry a b x * coordinateDerivative a (coordinateDerivative b (u i j)) x := by
  let v (a b : Fin 4) := coordinateDerivative a (coordinateDerivative b (u i j))
  let g (a b : Fin 4) :=
    projectionLipschitzCoefficientProductL2 (A.entry a b) A.slope (A.lipschitz a b) (v a b)
  have hg := ae_all_iff.mpr fun a : Fin 4 => ae_all_iff.mpr fun b : Fin 4 =>
    projectionLipschitzCoefficientProductL2_ae (A.entry a b) A.slope (A.lipschitz a b) (v a b)
  simp only [projectedSourceQ, Finset.sum_apply]
  filter_upwards [sourceLpDoubleSum_ae g, hg] with x hx hz
  exact hx.trans (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hz a b)

theorem projectedSourceCoefficientCorrection_ae (A : ProjectedSourceCoefficients)
    (u : ProjectionSchwartzMatrix) (i j : Fin 4) :
    (projectedSourceCoefficientCorrection A u i j : E → ℂ) =ᵐ[volume] fun x =>
      ∑ a, ∑ b, projectedSourceCoefficientDerivative A a b x * coordinateDerivative b (u i j) x := by
  let g (a b : Fin 4) :=
    projectedSourceDerivativeProduct A a b ((coordinateDerivative b (u i j)).toLp 2 volume)
  have hg := ae_all_iff.mpr fun a : Fin 4 => ae_all_iff.mpr fun b : Fin 4 =>
    projectedSourceDerivativeProduct_ae A a b (coordinateDerivative b (u i j))
  simp only [projectedSourceCoefficientCorrection, Finset.sum_apply]
  filter_upwards [sourceLpDoubleSum_ae g, hg] with x hx hz
  exact hx.trans (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hz a b)

private theorem projectedSourceDivergence_ae (A : ProjectedSourceCoefficients)
    (u : ProjectionSchwartzMatrix) (i j : Fin 4) :
    ((-(projectedSourceQ A u i j) - projectedSourceCoefficientCorrection A u i j : ComplexL2 E) :
      E → ℂ) =ᵐ[volume] projectedSourceDivergencePointwise A u i j := by
  let F := projectedSourceQ A u i j
  let G := projectedSourceCoefficientCorrection A u i j
  filter_upwards [Lp.coeFn_sub (-F) G, Lp.coeFn_neg F, projectedSourceQ_ae A u i j,
    projectedSourceCoefficientCorrection_ae A u i j] with x hfg hn hf hg
  rw [hfg, Pi.sub_apply, hn, Pi.neg_apply, hf, hg]
  simp only [projectedSourceDivergencePointwise, projectedSource_product_derivative, Finset.sum_add_distrib]
  abel

theorem projectedSourceDivergence_memLp (A : ProjectedSourceCoefficients) (u : ProjectionSchwartzMatrix)
    (i j : Fin 4) : MemLp (projectedSourceDivergencePointwise A u i j) 2 volume :=
  (Lp.memLp _).ae_eq (projectedSourceDivergence_ae A u i j)

/-- The actual negative divergence as an element of physical matrix \(L^2\). -/
def projectedSourceDivergenceL2 (A : ProjectedSourceCoefficients) (u : ProjectionSchwartzMatrix) :
    ProjectionL2Matrix :=
  fun i j => (projectedSourceDivergence_memLp A u i j).toLp (projectedSourceDivergencePointwise A u i j)

theorem projectedSourceDivergenceL2_ae (A : ProjectedSourceCoefficients) (u : ProjectionSchwartzMatrix)
    (i j : Fin 4) : (projectedSourceDivergenceL2 A u i j : E → ℂ) =ᵐ[volume]
      projectedSourceDivergencePointwise A u i j :=
  (projectedSourceDivergence_memLp A u i j).coeFn_toLp

theorem projectedSourceDivergenceL2_eq_raw (A : ProjectedSourceCoefficients) (u : ProjectionSchwartzMatrix) :
    projectedSourceDivergenceL2 A u = -projectedSourceQ A u - projectedSourceCoefficientCorrection A u := by
  funext i j
  apply Lp.ext
  exact (projectedSourceDivergence_memLp A u i j).coeFn_toLp.trans
    (projectedSourceDivergence_ae A u i j).symm

/-- When the actual nondivergence expression has a Schwartz representative,
its \(L^2\) projection and Schwartz projection agree. -/
theorem projectedSourceQ_eq_schwartz (A : ProjectedSourceCoefficients) (z q : ProjectionSchwartzMatrix)
    (hq : ∀ i j x, q i j x = ∑ a, ∑ b,
      A.entry a b x * coordinateDerivative a (coordinateDerivative b (z i j)) x) :
    projectedSourceQ A z = projectionMatrixToL2 q ∧
      projectionFullL2 (projectedSourceQ A z) = projectionMatrixToL2 (projectionFullSchwartz q) := by
  have heq : projectedSourceQ A z = projectionMatrixToL2 q := by
    funext i j
    apply Lp.ext
    filter_upwards [projectedSourceQ_ae A z i j, (q i j).coeFn_toLp 2 volume] with x h₁ h₂
    exact h₁.trans ((hq i j x).symm.trans h₂.symm)
  exact ⟨heq, heq ▸ projectionFullL2_eq_schwartz q⟩

end Burnett.P01
