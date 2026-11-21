import Burnett.Analysis.CubicEnergy.CompleteEnergy.SemilinearCubic
import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianActionLinearity
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Finset Burnett.RicciSymbol
open scoped ContDiff ComplexConjugate ENNReal

private abbrev ComponentField (J : Type*) := J → SchwartzMap E ℂ

private def derivativeEvaluation {J : Type*} (a : Index) (i : J) (x : E) :
    ComponentField J →ₗ[ℝ] ℂ where
  toFun u := energyPartial a (u i) x
  map_add' u v := by
    simp only [Pi.add_apply, energyPartial, map_add, SchwartzMap.add_apply]
  map_smul' c u := by
    let derivative : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
      SchwartzMap.pderivCLM ℂ (EuclideanSpace.single a 1)
    let D := derivative.toLinearMap.restrictScalars ℝ
    change D (c • u i) x = c • D (u i) x
    rw [map_smul, SchwartzMap.smul_apply]

private def radianTestEvaluation {J : Type*} (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (k : J) (x : E) : ComponentField J →ₗ[ℝ] ℂ where
  toFun w := conj (radianAction b (w k) x)
  map_add' u v := by
    simp only [Pi.add_apply, radian_action_add b hb hom, map_add]
  map_smul' c u := by
    change conj (radianAction b (c • u k) x) = c • conj (radianAction b (u k) x)
    simp only [radian_action_real_smul, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]

private def semilinearPointwiseMultilinear {J : Type*} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (k : J) (x : E) : MultilinearMap ℝ (fun _ : Fin 3 => ComponentField J) ℂ :=
  ∑ i : (Index × J) × (Index × J),
    (q i.1.1 i.2.1 i.1.2 i.2.2 k : ℂ) •
      (MultilinearMap.mkPiAlgebra ℝ (Fin 3) ℂ).compLinearMap
        (Fin.cons (derivativeEvaluation i.1.1 i.1.2 x)
          (Fin.cons (derivativeEvaluation i.2.1 i.2.2 x)
            (fun _ : Fin 1 => radianTestEvaluation b hb hom k x)))

private theorem semilinearPointwiseMultilinear_apply {J : Type*} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (k : J) (x : E) (v : Fin 3 → ComponentField J) :
    semilinearPointwiseMultilinear q b hb hom k x v =
      semilinearDerivativeTerm q (v 0) (v 1) k x * conj (radianAction b (v 2 k) x) := by
  rw [semilinearPointwiseMultilinear, MultilinearMap.sum_apply, semilinearDerivativeTerm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  change _ = (q i.1.1 i.2.1 i.1.2 i.2.2 k : ℂ) *
    energyPartial i.1.1 (v 0 i.1.2) x * energyPartial i.2.1 (v 1 i.2.2) x *
      conj (radianAction b (v 2 k) x)
  have atTwo :
      (Fin.cons (derivativeEvaluation i.1.1 i.1.2 x)
        (Fin.cons (derivativeEvaluation i.2.1 i.2.2 x)
          (fun _ : Fin 1 => radianTestEvaluation b hb hom k x)) :
            Fin 3 → ComponentField J →ₗ[ℝ] ℂ) (2 : Fin 3) =
        radianTestEvaluation b hb hom k x := by
    rw [show (2 : Fin 3) = (1 : Fin 2).succ from rfl, Fin.cons_succ, Fin.cons_one]
  simp only [MultilinearMap.smul_apply, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_three, Fin.cons_zero, Fin.cons_one, atTwo]
  simp [derivativeEvaluation, radianTestEvaluation, mul_assoc]

private theorem semilinearPointwiseMultilinear_integrable {J : Type*} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (k : J) (v : Fin 3 → ComponentField J) :
    Integrable (fun x => semilinearPointwiseMultilinear q b hb hom k x v) := by
  obtain ⟨_,_,bound⟩ := semilinear_Hermitian_pairing_L3_bound q b hb hom
  simp_rw [semilinearPointwiseMultilinear_apply]
  exact (bound (v 0) (v 1) (v 2)).1 k

private def semilinearPairingMultilinear {J : Type*} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x) :
    MultilinearMap ℝ (fun _ : Fin 3 => ComponentField J) ℂ where
  toFun v := ∑ k, ∫ x, semilinearPointwiseMultilinear q b hb hom k x v
  map_update_add' := by
    intro _ v i u w
    simp_rw [MultilinearMap.map_update_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    exact integral_add (semilinearPointwiseMultilinear_integrable q b hb hom k (Function.update v i u))
      (semilinearPointwiseMultilinear_integrable q b hb hom k (Function.update v i w))
  map_update_smul' := by
    intro _ v i c w
    simp_rw [MultilinearMap.map_update_smul, integral_smul, Finset.smul_sum]

/-- The exact semilinear energy admits a real trilinear map on its three
component fields. Conjugation in the test slot is taken before the imaginary part. -/
def semilinearCubicMultilinearMap {J : Type*} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x) :
    MultilinearMap ℝ (fun _ : Fin 3 => ComponentField J) ℝ :=
  (2 : ℝ) • Complex.imCLM.toLinearMap.compMultilinearMap (semilinearPairingMultilinear q b hb hom)

theorem semilinear_cubic_multilinear_apply {J : Type*} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (v : Fin 3 → ComponentField J) :
    semilinearCubicMultilinearMap q b hb hom v = semilinearCubicForm q b (v 0) (v 1) (v 2) := by
  simp [semilinearCubicMultilinearMap, semilinearPairingMultilinear, semilinearPointwiseMultilinear_apply,
    semilinearCubicForm, semilinearHermitianPairing, smul_eq_mul]

theorem semilinear_cubic_multilinear_L3_bound {J : Type*} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ v : Fin 3 → ComponentField J,
      ‖semilinearCubicMultilinearMap q b hb hom v‖ₑ ≤ K * ∏ i, semilinearGradientNorm (v i) := by
  obtain ⟨K,hK,est⟩ := semilinear_cubic_L3_bound q b hb hom
  refine ⟨K,hK,?_⟩
  intro v
  rw [semilinear_cubic_multilinear_apply, Fin.prod_univ_three]
  exact (est (v 0) (v 1) (v 2)).2

end Burnett.A02.FrequencySplit
