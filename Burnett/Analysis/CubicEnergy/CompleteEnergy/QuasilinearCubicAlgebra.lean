import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearCoefficient
import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianActionLinearity
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Finset Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate ContDiff ENNReal

private abbrev ComponentField (J : Type) := J → SchwartzMap E ℂ

private def schwartzEval (x : E) : SchwartzMap E ℂ →ₗ[ℝ] ℂ where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def partialLinear (a : Index) : SchwartzMap E ℂ →ₗ[ℝ] SchwartzMap E ℂ :=
  (SchwartzMap.pderivCLM ℂ (EuclideanSpace.single a 1) :
    SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ).toLinearMap.restrictScalars ℝ

private def coefficientLinear {J : Type} [Fintype J]
    (c : EnergyIndex J → J → ℝ) (k : EnergyIndex J) :
    ComponentField J →ₗ[ℝ] SchwartzMap E ℂ :=
  ∑ j, c k j • LinearMap.proj j

private theorem coefficientLinear_apply {J : Type} [Fintype J]
    (c : EnergyIndex J → J → ℝ) (k : EnergyIndex J) (H : ComponentField J) :
    coefficientLinear c k H = linearEnergyCoefficient c H k := by
  simp [coefficientLinear, LinearMap.sum_apply, linearEnergyCoefficient]

private def radianTestLinear {J : Type} (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (j : J) (x : E) : ComponentField J →ₗ[ℝ] ℂ where
  toFun u := conj (radianAction b (u j) x)
  map_add' u v := by
    simp only [Pi.add_apply, radian_action_add b hb hom, map_add]
  map_smul' r u := by
    change conj (radianAction b (r • u j) x) = r • conj (radianAction b (u j) x)
    simp only [radian_action_real_smul, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]

private def threeProductMap {F : Type} [AddCommMonoid F] [Module ℝ F]
    (a d e : F →ₗ[ℝ] ℂ) : MultilinearMap ℝ (fun _ : Fin 3 => F) ℂ :=
  (MultilinearMap.mkPiAlgebra ℝ (Fin 3) ℂ).compLinearMap
    (Fin.cons a (Fin.cons d (fun _ : Fin 1 => e)))

private theorem threeProductMap_apply {F : Type} [AddCommMonoid F] [Module ℝ F]
    (a d e : F →ₗ[ℝ] ℂ) (f : Fin 3 → F) : threeProductMap a d e f = a (f 0) * d (f 1) * e (f 2) := by
  have atTwo : (Fin.cons a (Fin.cons d (fun _ : Fin 1 => e)) : Fin 3 → F →ₗ[ℝ] ℂ) (2 : Fin 3) = e := by
    rw [show (2 : Fin 3) = (1 : Fin 2).succ from rfl, Fin.cons_succ, Fin.cons_one]
  simp only [threeProductMap, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    Fin.prod_univ_three, Fin.cons_zero, Fin.cons_one, atTwo]

private def quasilinearComponentMap {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (k : EnergyIndex J) (x : E) : MultilinearMap ℝ (fun _ : Fin 3 => ComponentField J) ℂ :=
  threeProductMap ((schwartzEval x).comp (coefficientLinear c k))
    ((schwartzEval x).comp ((partialLinear k.1.1).comp ((partialLinear k.1.2).comp (LinearMap.proj k.2.2))))
    (radianTestLinear b hb hom k.2.1 x)

private theorem quasilinearComponentMap_apply {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (k : EnergyIndex J) (x : E) (f : Fin 3 → ComponentField J) :
    quasilinearComponentMap c b hb hom k x f =
      linearEnergyCoefficient c (f 0) k x *
        energyPartial k.1.1 (energyPartial k.1.2 (f 1 k.2.2)) x *
          conj (radianAction b (f 2 k.2.1) x) := by
  unfold quasilinearComponentMap
  rw [threeProductMap_apply]
  change coefficientLinear c k (f 0) x * energyPartial k.1.1 (energyPartial k.1.2 (f 1 k.2.2)) x *
    conj (radianAction b (f 2 k.2.1) x) = _
  rw [coefficientLinear_apply]

private theorem quasilinearComponentMap_integrable {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (k : EnergyIndex J) (f : Fin 3 → ComponentField J) :
    Integrable (fun x => quasilinearComponentMap c b hb hom k x f) := by
  simpa only [quasilinearComponentMap_apply, energyProduct_apply] using
    radian_order_one_test_integrable b hb hom
      (energyProduct (linearEnergyCoefficient c (f 0) k) (energyPartial k.1.1 (energyPartial k.1.2 (f 1 k.2.2))))
      (f 2 k.2.1)

private def quasilinearOrderedMultilinearMap {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x) :
    MultilinearMap ℝ (fun _ : Fin 3 => ComponentField J) ℂ where
  toFun f := ∑ k, ∫ x, quasilinearComponentMap c b hb hom k x f
  map_update_add' := by
    intro _ v i u w
    simp_rw [MultilinearMap.map_update_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    exact integral_add (quasilinearComponentMap_integrable c b hb hom k (Function.update v i u))
      (quasilinearComponentMap_integrable c b hb hom k (Function.update v i w))
  map_update_smul' := by
    intro _ v i r w
    simp_rw [MultilinearMap.map_update_smul, integral_smul, Finset.smul_sum]

private theorem quasilinearOrderedMultilinearMap_apply {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (v : Fin 3 → ComponentField J) :
    quasilinearOrderedMultilinearMap c b hb hom v =
      quasilinearMixedPairing b (linearEnergyCoefficient c (v 0)) (v 1) (v 2) := by
  simp [quasilinearOrderedMultilinearMap, quasilinearComponentMap_apply, quasilinearMixedPairing]

/-- A real trilinear map obtained from the two exact quasilinear pairings
used together in the energy estimate. -/
def quasilinearSymmetricMultilinearMap {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x) :
    MultilinearMap ℝ (fun _ : Fin 3 => ComponentField J) ℝ :=
  let T := quasilinearOrderedMultilinearMap c b hb hom
  Complex.imCLM.toLinearMap.compMultilinearMap (T + T.domDomCongr (Equiv.swap (1 : Fin 3) 2))

theorem quasilinear_symmetric_multilinear_apply {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (v : Fin 3 → ComponentField J) :
    quasilinearSymmetricMultilinearMap c b hb hom v =
      quasilinearSymmetricEnergy b (linearEnergyCoefficient c (v 0)) (v 1) (v 2) := by
  have sw : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
  simp [quasilinearSymmetricMultilinearMap, quasilinearOrderedMultilinearMap_apply,
    quasilinearSymmetricEnergy, sw]

theorem quasilinear_symmetric_multilinear_diag {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (u : ComponentField J) :
    quasilinearSymmetricMultilinearMap c b hb hom (fun _ => u) =
      2 * (quasilinearPairing b (linearEnergyCoefficient c u) u).im := by
  rw [quasilinear_symmetric_multilinear_apply]
  exact quasilinearSymmetricEnergy_diag b (linearEnergyCoefficient c u) u

theorem quasilinear_symmetric_multilinear_L3_bound {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ v : Fin 3 → ComponentField J,
      (∀ j x, conj (v 0 j x) = v 0 j x) →
      ‖quasilinearSymmetricMultilinearMap c b hb hom v‖ₑ ≤ C * ∏ i, fieldEnergyGradientNorm (v i) := by
  obtain ⟨C, hC, est⟩ := quasilinear_linear_coefficient_estimate b hb hom c hc
  refine ⟨C,hC,fun v hv => ?_⟩
  rw [quasilinear_symmetric_multilinear_apply, ← ofReal_norm_eq_enorm, Real.norm_eq_abs, Fin.prod_univ_three]
  simpa only [mul_assoc] using est (v 0) (v 1) (v 2) hv

end Burnett.A02.FrequencySplit
