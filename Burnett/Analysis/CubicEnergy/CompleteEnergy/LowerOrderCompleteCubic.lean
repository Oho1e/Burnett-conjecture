import Burnett.Analysis.CubicEnergy.CompleteEnergy.LowerOrderSemilinear
import Burnett.Analysis.CubicEnergy.CompleteEnergy.CompleteCubicAlgebra

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Finset Burnett.RicciSymbol
open scoped BigOperators ContDiff ComplexConjugate ENNReal

private abbrev Fields (J : Type) := J → SchwartzMap E ℂ
private abbrev P : ℝ≥0∞ := ENNReal.ofReal 3
private abbrev DerivativeIndices (J : Type) := (Index × J) × (Index × J)

private def valueEval (x : E) : SchwartzMap E ℂ →ₗ[ℝ] ℂ where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def derivativeLinear (a : Index) : SchwartzMap E ℂ →ₗ[ℝ] SchwartzMap E ℂ :=
  (SchwartzMap.pderivCLM ℂ (EuclideanSpace.single a 1) :
    SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ).toLinearMap.restrictScalars ℝ

private def coefficientLinear {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (k : EnergyIndex J) : Fields J →ₗ[ℝ] SchwartzMap E ℂ := ∑ i, c k i • LinearMap.proj i

private theorem coefficientLinear_apply {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (k : EnergyIndex J) (u : Fields J) :
    coefficientLinear c k u = linearEnergyCoefficient c u k := by
  simp [coefficientLinear,LinearMap.sum_apply,linearEnergyCoefficient]

private def testLinear {J : Type} (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (j : J) (x : E) : Fields J →ₗ[ℝ] ℂ where
  toFun w := conj (radianAction m (w j) x)
  map_add' u v := by
    simp only [Pi.add_apply, radian_action_add_of_integrable_spectra m _ _ (spectrum _) (spectrum _), map_add]
  map_smul' r u := by
    change conj (radianAction m (r • u j) x) = r • conj (radianAction m (u j) x)
    simp only [radian_action_real_smul,Pi.smul_apply,Complex.real_smul,map_mul,Complex.conj_ofReal]

private def threeProduct {F : Type} [AddCommMonoid F] [Module ℝ F] (a b c : F →ₗ[ℝ] ℂ) :
    MultilinearMap ℝ (fun _ : Fin 3 => F) ℂ :=
  (MultilinearMap.mkPiAlgebra ℝ (Fin 3) ℂ).compLinearMap (Fin.cons a (Fin.cons b (fun _ : Fin 1 => c)))

private theorem threeProduct_apply {F : Type} [AddCommMonoid F] [Module ℝ F]
    (a b c : F →ₗ[ℝ] ℂ) (v : Fin 3 → F) : threeProduct a b c v = a (v 0) * b (v 1) * c (v 2) := by
  have atTwo : (Fin.cons a (Fin.cons b (fun _ : Fin 1 => c)) : Fin 3 → F →ₗ[ℝ] ℂ) 2 = c := by
    rw [show (2 : Fin 3) = (1 : Fin 2).succ from rfl,Fin.cons_succ,Fin.cons_one]
  simp only [threeProduct,MultilinearMap.compLinearMap_apply,MultilinearMap.mkPiAlgebra_apply,
    Fin.prod_univ_three,Fin.cons_zero,Fin.cons_one,atTwo]

private def integrateComponents {F I : Type} [AddCommMonoid F] [Module ℝ F] [Fintype I]
    (M : I → E → MultilinearMap ℝ (fun _ : Fin 3 => F) ℂ)
    (hM : ∀ i (v : Fin 3 → F), Integrable (fun x => M i x v)) :
    MultilinearMap ℝ (fun _ : Fin 3 => F) ℂ where
  toFun v := ∑ i, ∫ x, M i x v
  map_update_add' := by
    intro _ v j f g
    simp_rw [MultilinearMap.map_update_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_add (hM i (Function.update v j f)) (hM i (Function.update v j g))
  map_update_smul' := by
    intro _ v j r f
    simp_rw [MultilinearMap.map_update_smul,integral_smul,Finset.smul_sum]

private def quasiPointwise {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ) (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (k : EnergyIndex J) (x : E) : MultilinearMap ℝ (fun _ : Fin 3 => Fields J) ℂ :=
  threeProduct ((valueEval x).comp (coefficientLinear c k))
    ((valueEval x).comp ((derivativeLinear k.1.1).comp ((derivativeLinear k.1.2).comp (LinearMap.proj k.2.2))))
    (testLinear m spectrum k.2.1 x)

private theorem quasiPointwise_apply {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ) (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (k : EnergyIndex J) (x : E) (v : Fin 3 → Fields J) :
    quasiPointwise c m spectrum k x v = linearEnergyCoefficient c (v 0) k x *
      energyPartial k.1.1 (energyPartial k.1.2 (v 1 k.2.2)) x * conj (radianAction m (v 2 k.2.1) x) := by
  rw [quasiPointwise,threeProduct_apply]
  change coefficientLinear c k (v 0) x *
    energyPartial k.1.1 (energyPartial k.1.2 (v 1 k.2.2)) x * conj (radianAction m (v 2 k.2.1) x) = _
  rw [coefficientLinear_apply]

private def quasiIntegrated {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ) (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (hm : ∀ g : SchwartzMap E ℂ, MemLp (radianAction m g) P volume) :
    MultilinearMap ℝ (fun _ : Fin 3 => Fields J) ℂ :=
  integrateComponents (quasiPointwise c m spectrum) fun k v => by
    simpa only [quasiPointwise_apply,energyProduct_apply] using
      radian_test_integrable_of_L3 m
        (energyProduct (linearEnergyCoefficient c (v 0) k)
          (energyPartial k.1.1 (energyPartial k.1.2 (v 1 k.2.2)))) (v 2 k.2.1) (hm _)

private theorem quasiIntegrated_apply {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ) (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (hm : ∀ g : SchwartzMap E ℂ, MemLp (radianAction m g) P volume) (v : Fin 3 → Fields J) :
    quasiIntegrated c m spectrum hm v =
      quasilinearMixedPairing m (linearEnergyCoefficient c (v 0)) (v 1) (v 2) := by
  simp [quasiIntegrated,integrateComponents,quasiPointwise_apply,quasilinearMixedPairing]

private def semiPointwise {J : Type} [Fintype J] (q : Index → Index → J → J → J → ℝ) (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (k : J) (x : E) : MultilinearMap ℝ (fun _ : Fin 3 => Fields J) ℂ :=
  ∑ i : DerivativeIndices J, (q i.1.1 i.2.1 i.1.2 i.2.2 k : ℂ) •
    threeProduct ((valueEval x).comp ((derivativeLinear i.1.1).comp (LinearMap.proj i.1.2)))
      ((valueEval x).comp ((derivativeLinear i.2.1).comp (LinearMap.proj i.2.2))) (testLinear m spectrum k x)

private theorem semiPointwise_apply {J : Type} [Fintype J] (q : Index → Index → J → J → J → ℝ) (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (k : J) (x : E) (v : Fin 3 → Fields J) :
    semiPointwise q m spectrum k x v =
      semilinearDerivativeTerm q (v 0) (v 1) k x * conj (radianAction m (v 2 k) x) := by
  rw [semiPointwise,MultilinearMap.sum_apply,semilinearDerivativeTerm,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [MultilinearMap.smul_apply,threeProduct_apply]
  change (q i.1.1 i.2.1 i.1.2 i.2.2 k : ℂ) * (energyPartial i.1.1 (v 0 i.1.2) x *
    energyPartial i.2.1 (v 1 i.2.2) x * conj (radianAction m (v 2 k) x)) =
    (q i.1.1 i.2.1 i.1.2 i.2.2 k : ℂ) * energyPartial i.1.1 (v 0 i.1.2) x *
      energyPartial i.2.1 (v 1 i.2.2) x * conj (radianAction m (v 2 k) x)
  ring

private def semiIntegrated {J : Type} [Fintype J] (q : Index → Index → J → J → J → ℝ) (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (K : ℝ≥0∞) (bound : ∀ g : SchwartzMap E ℂ, MemLp (radianAction m g) P volume ∧
      eLpNorm (radianAction m g) P volume ≤ K*eLpNorm (g : E → ℂ) P volume) :
    MultilinearMap ℝ (fun _ : Fin 3 => Fields J) ℂ :=
  integrateComponents (semiPointwise q m spectrum) fun k v => by
    simp_rw [semiPointwise_apply]
    exact (lower_order_semilinear_hermitian_W13_bound m K bound q (v 0) (v 1) (v 2)).1 k

private theorem semiIntegrated_apply {J : Type} [Fintype J] (q : Index → Index → J → J → J → ℝ) (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (K : ℝ≥0∞) (bound : ∀ g : SchwartzMap E ℂ, MemLp (radianAction m g) P volume ∧
      eLpNorm (radianAction m g) P volume ≤ K*eLpNorm (g : E → ℂ) P volume) (v : Fin 3 → Fields J) :
    semiIntegrated q m spectrum K bound v = semilinearHermitianPairing q m (v 0) (v 1) (v 2) := by
  simp [semiIntegrated,integrateComponents,semiPointwise_apply,semilinearHermitianPairing]

/-- The two quasilinear slots are polarized together, and the actual semilinear
pairing is then added. This map is suitable for fixed lower-order corrections. -/
def lowerOrderCompleteCubicMap {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (q : Index → Index → J → J → J → ℝ) (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (K : ℝ≥0∞) (bound : ∀ g : SchwartzMap E ℂ, MemLp (radianAction m g) P volume ∧
      eLpNorm (radianAction m g) P volume ≤ K*eLpNorm (g : E → ℂ) P volume) :
    MultilinearMap ℝ (fun _ : Fin 3 => RealEnergyField J) ℝ :=
  let Q := quasiIntegrated c m spectrum (fun g => (bound g).1)
  let S := semiIntegrated q m spectrum K bound
  (Complex.imCLM.toLinearMap.compMultilinearMap (Q + Q.domDomCongr (Equiv.swap (1 : Fin 3) 2)) +
    (2 : ℝ) • Complex.imCLM.toLinearMap.compMultilinearMap S).compLinearMap
      (fun _ => (realEnergyFields J).subtype)

theorem lower_order_complete_cubic_map_apply {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (q : Index → Index → J → J → J → ℝ) (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (K : ℝ≥0∞) (bound : ∀ g : SchwartzMap E ℂ, MemLp (radianAction m g) P volume ∧
      eLpNorm (radianAction m g) P volume ≤ K*eLpNorm (g : E → ℂ) P volume)
    (v : Fin 3 → RealEnergyField J) :
    lowerOrderCompleteCubicMap c q m spectrum K bound v =
      quasilinearSymmetricEnergy m (linearEnergyCoefficient c (v 0)) (v 1) (v 2) +
        semilinearCubicForm q m (v 0) (v 1) (v 2) := by
  have sw : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
  simp [lowerOrderCompleteCubicMap,MultilinearMap.compLinearMap_apply,quasiIntegrated_apply,
    semiIntegrated_apply,quasilinearSymmetricEnergy,semilinearCubicForm,sw,smul_eq_mul]

theorem lower_order_complete_cubic_map_diag {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (q : Index → Index → J → J → J → ℝ) (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (K : ℝ≥0∞) (bound : ∀ g : SchwartzMap E ℂ, MemLp (radianAction m g) P volume ∧
      eLpNorm (radianAction m g) P volume ≤ K*eLpNorm (g : E → ℂ) P volume)
    (u : RealEnergyField J) :
    lowerOrderCompleteCubicMap c q m spectrum K bound (fun _ => u) = completeCubicEnergy c q m u := by
  rw [lower_order_complete_cubic_map_apply,quasilinearSymmetricEnergy_diag,
    semilinearCubicForm,completeCubicEnergy,Complex.add_im]
  ring

theorem lower_order_complete_cubic_map_W13_bound {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (q : Index → Index → J → J → J → ℝ) (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (K : ℝ≥0∞) (bound : ∀ g : SchwartzMap E ℂ, MemLp (radianAction m g) P volume ∧
      eLpNorm (radianAction m g) P volume ≤ K*eLpNorm (g : E → ℂ) P volume)
    (v : Fin 3 → RealEnergyField J) :
    ‖lowerOrderCompleteCubicMap c q m spectrum K bound v‖ₑ ≤
      (2*K*(∑ k, ∑ j, ‖c k j‖ₑ) + 2*semilinearCoefficientMass q*K) *
        ∏ i, fieldInhomogeneousNorm (v i : Fields J) := by
  rw [lower_order_complete_cubic_map_apply,Fin.prod_univ_three,add_mul]
  have ql := lower_order_quasilinear_W13_bound m spectrum K bound c (v 0) (v 1) (v 2)
  have sl := lower_order_semilinear_W13_bound m K bound q (v 0) (v 1) (v 2)
  exact (enorm_add_le _ _).trans (add_le_add (by simpa only [mul_assoc] using ql) sl)

end Burnett.A02.FrequencySplit
