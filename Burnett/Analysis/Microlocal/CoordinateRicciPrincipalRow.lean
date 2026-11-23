import Burnett.Analysis.GeometricPrincipalIdentity
import Burnett.Analysis.Microlocal.OriginalCoordinateCurl
import Burnett.Geometry.FlatRigidity.WeakCurvature

/-!
# Coordinate coefficients and differential row for the linearized Ricci operator
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.RicciRow

open scoped BigOperators ContDiff Manifold
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.AuxiliaryConnection Burnett.Geometry.InverseField Burnett.Geometry.BackgroundConnection
open Burnett.Analysis.GeometricPrincipalIdentity Burnett.Analysis.LocalWeakRicciIdentification

def directionalJet (W : CoordinateSpace → FirstJet) (x : CoordinateSpace)
    (q : Index) : FirstJet :=
  fun j b d => fderiv ℝ (fun y => W y j b d) x (EuclideanSpace.single q 1)

private theorem differentiableAt_koszul (W : CoordinateSpace → FirstJet) (x : CoordinateSpace)
    (hW : ∀ j b d, DifferentiableAt ℝ (fun y => W y j b d) x) (b d e : Index) :
    DifferentiableAt ℝ (fun y => koszul (W y) b d e) x := by
  simpa only [koszul, div_eq_mul_inv] using
    (((hW b d e).fun_add (hW d b e)).fun_sub (hW e b d)).mul_const (2 : ℝ)⁻¹

private theorem derivative_koszul (W : CoordinateSpace → FirstJet) (x : CoordinateSpace)
    (hW : ∀ j b d, DifferentiableAt ℝ (fun y => W y j b d) x) (q b d e : Index) :
    fderiv ℝ (fun y => koszul (W y) b d e) x (EuclideanSpace.single q 1) =
      koszul (directionalJet W x q) b d e := by
  simp only [koszul, directionalJet, div_eq_mul_inv]
  rw [fderiv_mul_const (((hW b d e).fun_add (hW d b e)).fun_sub (hW e b d)) (2 : ℝ)⁻¹,
    fderiv_fun_sub ((hW b d e).fun_add (hW d b e)) (hW e b d),
    fderiv_fun_add (hW b d e) (hW d b e)]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Differentiating the actual Christoffel contraction of a smooth inverse
metric and a first jet yields exactly two terms. -/
theorem coordinateConnectionJet_christoffel (G : CoordinateSpace → Tensor2)
    (W : CoordinateSpace → FirstJet) (x : CoordinateSpace)
    (hG : ∀ a e, DifferentiableAt ℝ (fun y => G y a e) x)
    (hW : ∀ j b d, DifferentiableAt ℝ (fun y => W y j b d) x)
    (q a b d : Index) :
    coordinateConnectionJet (fun y => christoffel (G y) (W y)) x q a b d =
      christoffel (G x) (directionalJet W x q) a b d +
      christoffel (coordinateJet G x q) (W x) a b d := by
  unfold coordinateConnectionJet christoffel
  change fderiv ℝ (fun y => ∑ e : Index, G y a e * koszul (W y) b d e) x
    (EuclideanSpace.single q 1) = _
  have hp (e : Index) : DifferentiableAt ℝ (fun y => G y a e * koszul (W y) b d e) x :=
    (hG a e).mul (differentiableAt_koszul W x hW b d e)
  rw [fderiv_fun_sum (u := Finset.univ) (fun e _ => hp e),
    ContinuousLinearMap.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [fderiv_fun_mul (hG a e) (differentiableAt_koszul W x hW b d e)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    derivative_koszul W x hW, coordinateJet]
  ring

/-- This part differentiates the first-jet components, holding the inverse
metric fixed. Its symbol is the contraction used by the Ricci kernel. -/
def divergencePrincipal (G : Tensor2) (dW : Index → FirstJet) (b d : Index) : ℝ :=
  ∑ a, (christoffel G (dW a) a b d - christoffel G (dW d) a b a)

/-- Product rule for the actual coordinate linearized Ricci operator. Both
remaining terms use the values of the first jet and differentiated fixed
background coefficients only. -/
theorem linearizedRicci_eq_divergencePrincipal_add_lower
    (g0 g1 : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace) (x : CoordinateSpace)
    (hG : ∀ a e, DifferentiableAt ℝ (fun y => matrixInverse (metricComponents g0 y) a e) x)
    (hW : ∀ j b d, DifferentiableAt ℝ (fun y => auxiliaryPerturbationJet g0 g0 g1 y j b d) x)
    (b d : Index) :
    let G := fun y => matrixInverse (metricComponents g0 y)
    let W := auxiliaryPerturbationJet g0 g0 g1
    let Γ := computedConnection g0 x
    let C := christoffel (G x) (W x)
    linearizedRicci g0 g1 x b d =
      divergencePrincipal (G x) (directionalJet W x) b d +
      (∑ a, (christoffel (coordinateJet G x a) (W x) a b d -
        christoffel (coordinateJet G x d) (W x) a b a)) +
      covariantDivergenceDifference Γ C 0 b d := by
  dsimp only
  unfold linearizedRicci linearConnection covariantDivergenceDifference divergencePrincipal covariantDerivative
  simp only [coordinateConnectionJet_christoffel _ _ x hG hW, Pi.zero_apply, zero_add]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

section Chart

open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.SmoothMetricConnection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem coordinateInverse_component_smoothOn (g0 : Field (M := M)) (h0 : IsSmooth g0)
    (hn0 : IsNondegenerate g0) (c : M) (a e : Index) :
    ContDiffOn ℝ ∞ (fun x => matrixInverse (metricComponents (coordinateBilinear g0 c) x) a e)
      (chartAt CoordinateSpace c).target := by
  apply contDiffOn_matrixInverse _ _ (contDiffOn_metricComponents g0 h0 c)
  intro x hx
  have hn := coordinateBilinear_nondegenerate g0 hn0 c hx
  have hd := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero coordinateBasis).mp hn
  have hm : BilinForm.toMatrix coordinateBasis (coordinateBilinear g0 c x) =
      metricComponents (coordinateBilinear g0 c) x := by
    ext i j
    simp only [BilinForm.toMatrix_apply, metricComponents, Burnett.Geometry.FiberMetric.covariant]
  simpa only [hm] using hd

theorem coordinatePerturbationJet_component_smoothOn (g0 g1 : Field (M := M))
    (h0 : IsSmooth g0) (h1 : IsSmooth g1) (hn0 : IsNondegenerate g0)
    (c : M) (j b d : Index) :
    ContDiffOn ℝ ∞ (fun x => auxiliaryPerturbationJet (coordinateBilinear g0 c)
      (coordinateBilinear g0 c) (coordinateBilinear g1 c) x j b d)
      (chartAt CoordinateSpace c).target := by
  let U := (chartAt CoordinateSpace c).target
  let H := fun x => metricComponents (coordinateBilinear g1 c) x -
    metricComponents (coordinateBilinear g0 c) x
  have hH (m k : Index) : ContDiffOn ℝ ∞ (fun x => H x m k) U :=
    ((contDiffOn_metricComponents g1 h1 c) m k).sub ((contDiffOn_metricComponents g0 h0 c) m k)
  have hdH := contDiffOn_coordinateJet H U (chartAt CoordinateSpace c).open_target hH j b d
  have hΓ (a m k : Index) : ContDiffOn ℝ ∞ (fun x => computedConnection
      (coordinateBilinear g0 c) x a m k) U :=
    contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp
      (contDiffOn_coordinateBilinear_connection g0 h0 hn0 c) a) m) k
  exact (hdH.sub (ContDiffOn.sum (fun e _ => (hΓ e j b).mul (hH e d)))).sub
    (ContDiffOn.sum (fun e _ => (hΓ e j d).mul (hH b e)))

theorem chart_linearizedRicci_eq_divergencePrincipal_add_lower (g0 g1 : Field (M := M))
    (h0 : IsSmooth g0) (h1 : IsSmooth g1) (hn0 : IsNondegenerate g0) (c : M)
    (x : CoordinateSpace) (hx : x ∈ (chartAt CoordinateSpace c).target) (b d : Index) :
    let g0c := coordinateBilinear g0 c
    let g1c := coordinateBilinear g1 c
    let G := fun y => matrixInverse (metricComponents g0c y)
    let W := auxiliaryPerturbationJet g0c g0c g1c
    let Γ := computedConnection g0c x
    let C := christoffel (G x) (W x)
    linearizedRicci g0c g1c x b d =
      divergencePrincipal (G x) (directionalJet W x) b d +
      (∑ a, (christoffel (coordinateJet G x a) (W x) a b d -
        christoffel (coordinateJet G x d) (W x) a b a)) +
      covariantDivergenceDifference Γ C 0 b d := by
  have hU := (chartAt CoordinateSpace c).open_target.mem_nhds hx
  exact linearizedRicci_eq_divergencePrincipal_add_lower _ _ x
    (fun a e => ((coordinateInverse_component_smoothOn g0 h0 hn0 c a e).contDiffAt hU).differentiableAt
      (by simp))
    (fun j m k => ((coordinatePerturbationJet_component_smoothOn g0 g1 h0 h1 hn0 c j m k).contDiffAt
      hU).differentiableAt (by simp)) b d

end Chart

end Burnett.Microlocal.RicciRow


set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.RicciRow

open scoped BigOperators ContDiff Manifold
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference

private theorem derivative_sum_mul (A B : Index → CoordinateSpace → ℝ)
    (x v : CoordinateSpace) (hA : ∀ e, DifferentiableAt ℝ (A e) x)
    (hB : ∀ e, DifferentiableAt ℝ (B e) x) :
    fderiv ℝ (fun y => ∑ e, A e y * B e y) x v =
      (∑ e, fderiv ℝ (A e) x v * B e x) + ∑ e, A e x * fderiv ℝ (B e) x v := by
  have hp (e : Index) : DifferentiableAt ℝ (fun y => A e y * B e y) x := (hA e).mul (hB e)
  rw [fderiv_fun_sum (u := Finset.univ) (fun e _ => hp e), ContinuousLinearMap.sum_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [fderiv_fun_mul (hA e) (hB e)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Going from a covariant first jet to the raw derivative changes the
differentiated jet by terms involving only the tensor and its first jet. -/
theorem directionalJet_covariantJet (Γ : CoordinateSpace → Connection) (H : CoordinateSpace → Tensor2)
    (x : CoordinateSpace) (q j b d : Index)
    (hΓ : DifferentiableConnectionAt Γ x)
    (hH : ∀ m k, DifferentiableAt ℝ (fun y => H y m k) x)
    (hDH : ∀ m k l, DifferentiableAt ℝ (fun y => coordinateJet H y m k l) x) :
    directionalJet (fun y => covariantJet (Γ y) (H y) (coordinateJet H y)) x q j b d =
      directionalJet (coordinateJet H) x q j b d +
        covariantJet (coordinateConnectionJet Γ x q) (H x) 0 j b d +
        covariantJet (Γ x) (coordinateJet H x q) 0 j b d := by
  let v := EuclideanSpace.single q (1 : ℝ)
  let F := fun y => coordinateJet H y j b d
  let U := fun y => ∑ e, Γ y e j b * H y e d
  let V := fun y => ∑ e, Γ y e j d * H y b e
  have hF : DifferentiableAt ℝ F x := hDH j b d
  have hU : DifferentiableAt ℝ U x :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun e _ => (hΓ e j b).mul (hH e d))
  have hV : DifferentiableAt ℝ V x :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun e _ => (hΓ e j d).mul (hH b e))
  change fderiv ℝ (fun y => F y - U y - V y) x v = _
  rw [fderiv_fun_sub (hF.fun_sub hU) hV, fderiv_fun_sub hF hU]
  simp only [ContinuousLinearMap.sub_apply, U, V]
  rw [derivative_sum_mul (fun e y => Γ y e j b) (fun e y => H y e d) x v
      (fun e => hΓ e j b) (fun e => hH e d),
    derivative_sum_mul (fun e y => Γ y e j d) (fun e y => H y b e) x v
      (fun e => hΓ e j d) (fun e => hH b e)]
  simp only [F, v, directionalJet, covariantJet, coordinateConnectionJet, coordinateJet, Pi.zero_apply]
  ring

private theorem christoffel_add (G : Tensor2) (W U : FirstJet) (a b d : Index) :
    christoffel G (W + U) a b d = christoffel G W a b d + christoffel G U a b d := by
  unfold christoffel
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [koszul, Pi.add_apply]
  ring

private theorem divergencePrincipal_add (G : Tensor2) (dW dU : Index → FirstJet) (b d : Index) :
    divergencePrincipal G (dW + dU) b d = divergencePrincipal G dW b d + divergencePrincipal G dU b d := by
  unfold divergencePrincipal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Pi.add_apply, christoffel_add]
  ring

open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.SmoothMetricConnection
open Burnett.Geometry.AuxiliaryConnection Burnett.Geometry.InverseField Burnett.Geometry.BackgroundConnection
open Burnett.Analysis.GeometricPrincipalIdentity

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- In an actual metric chart, only the leading term differentiates the
raw coordinate first jet. Every other term is a fixed background
coefficient applied to the perturbation or to its undifferentiated jet. -/
theorem chart_linearizedRicci_eq_rawPrincipal_add_lower (g0 g1 : Field (M := M))
    (h0 : IsSmooth g0) (h1 : IsSmooth g1) (hn0 : IsNondegenerate g0) (c : M)
    (x : CoordinateSpace) (hx : x ∈ (chartAt CoordinateSpace c).target) (b d : Index) :
    let g0c := coordinateBilinear g0 c
    let g1c := coordinateBilinear g1 c
    let Γ := computedConnection g0c
    let G := fun y => matrixInverse (metricComponents g0c y)
    let H := fun y => metricComponents g1c y - metricComponents g0c y
    let W := auxiliaryPerturbationJet g0c g0c g1c
    let C := christoffel (G x) (W x)
    let dWLower := fun q => covariantJet (coordinateConnectionJet Γ x q) (H x) 0 +
      covariantJet (Γ x) (coordinateJet H x q) 0
    linearizedRicci g0c g1c x b d =
      divergencePrincipal (G x) (directionalJet (coordinateJet H) x) b d +
      divergencePrincipal (G x) dWLower b d +
      (∑ a, (christoffel (coordinateJet G x a) (W x) a b d -
        christoffel (coordinateJet G x d) (W x) a b a)) +
      covariantDivergenceDifference (Γ x) C 0 b d := by
  dsimp only
  let U := (chartAt CoordinateSpace c).target
  let g0c := coordinateBilinear g0 c
  let g1c := coordinateBilinear g1 c
  let Γ := computedConnection g0c
  let G := fun y => matrixInverse (metricComponents g0c y)
  let H := fun y => metricComponents g1c y - metricComponents g0c y
  let W := auxiliaryPerturbationJet g0c g0c g1c
  let dWLower := fun q => covariantJet (coordinateConnectionJet Γ x q) (H x) 0 +
    covariantJet (Γ x) (coordinateJet H x q) 0
  have hU := (chartAt CoordinateSpace c).open_target.mem_nhds hx
  have hHs (m k : Index) : ContDiffOn ℝ ∞ (fun y => H y m k) U :=
    (contDiffOn_metricComponents g1 h1 c m k).sub (contDiffOn_metricComponents g0 h0 c m k)
  have hH (m k : Index) : DifferentiableAt ℝ (fun y => H y m k) x :=
    ((hHs m k).contDiffAt hU).differentiableAt (by simp)
  have hdH (q m k : Index) : DifferentiableAt ℝ (fun y => coordinateJet H y q m k) x :=
    ((contDiffOn_coordinateJet H U (chartAt CoordinateSpace c).open_target hHs q m k).contDiffAt
      hU).differentiableAt (by simp)
  have hΓ : DifferentiableConnectionAt Γ x := by
    intro a m k
    have h := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp
      (contDiffOn_coordinateBilinear_connection g0 h0 hn0 c) a) m) k
    exact (h.contDiffAt hU).differentiableAt (by simp)
  have hdW : directionalJet W x = directionalJet (coordinateJet H) x + dWLower := by
    funext q j m k
    change directionalJet (fun y => covariantJet (Γ y) (H y) (coordinateJet H y)) x q j m k = _
    simpa only [Pi.add_apply, dWLower, add_assoc] using
      directionalJet_covariantJet Γ H x q j m k hΓ hH hdH
  have hsplit : divergencePrincipal (G x) (directionalJet W x) b d =
      divergencePrincipal (G x) (directionalJet (coordinateJet H) x) b d +
        divergencePrincipal (G x) dWLower b d := by
    rw [hdW, divergencePrincipal_add]
  rw [chart_linearizedRicci_eq_divergencePrincipal_add_lower g0 g1 h0 h1 hn0 c x hx b d]
  dsimp only
  rw [show divergencePrincipal (matrixInverse (metricComponents g0c x))
    (directionalJet (auxiliaryPerturbationJet g0c g0c g1c) x) b d = _ from hsplit]

end Burnett.Microlocal.RicciRow


set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.RicciRow

open scoped BigOperators
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference

abbrev PrincipalTerm := Index × Index × Fin 2 × Fin 3
abbrev JetIndex := Index × (Index × Index)

def termDirection (d : Index) (s : PrincipalTerm) : Index := ![s.1, d] s.2.2.1

def termInput (b d : Index) (s : PrincipalTerm) : JetIndex :=
  let e := s.2.1
  let k := ![d, s.1] s.2.2.1
  ![(b, (k, e)), (k, (b, e)), (e, (b, k))] s.2.2.2

def termCoefficient (G : Tensor2) (s : PrincipalTerm) : ℝ :=
  (![1, -1] s.2.2.1) * (![1, 1, -1] s.2.2.2) * (G s.1 s.2.1 / 2)

/-- The two divergence terms and three Christoffel terms give the actual
finite row on the ordered coordinate gradient components. -/
theorem divergencePrincipal_eq_sum_term (G : Tensor2) (dW : Index → FirstJet) (b d : Index) :
    divergencePrincipal G dW b d = ∑ s : PrincipalTerm,
      termCoefficient G s * dW (termDirection d s)
        (termInput b d s).1 (termInput b d s).2.1 (termInput b d s).2.2 := by
  unfold divergencePrincipal christoffel
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Fin.sum_univ_two, Fin.sum_univ_three, termCoefficient, termDirection, termInput]
  simp [koszul]
  ring

end Burnett.Microlocal.RicciRow


set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.RicciRow

open Set
open scoped ContDiff BigOperators
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.X02.SobolevTestJet (D test_smooth)
open Burnett.Analysis.LocalWeakDerivative (fderiv_test_mul_local)

/-- Localizing the raw-jet entries by one fixed cutoff creates only the
explicit zeroth-order term with a derivative of the cutoff. -/
theorem localizedSum_eq_principal_add_cutoff (G : CoordinateSpace → Tensor2)
    (W : CoordinateSpace → FirstJet) (χ θ : D) {U : Set CoordinateSpace}
    (hU : IsOpen U) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ U)
    (hθ : ∀ x ∈ tsupport (χ : CoordinateSpace → ℝ), (θ : CoordinateSpace → ℝ) x = 1)
    (hW : ∀ q j k, ContDiffOn ℝ ∞ (fun x => W x q j k) U) (x : CoordinateSpace)
    (b d : Index) :
    let A := fun s : PrincipalTerm => (θ : CoordinateSpace → ℝ) x * termCoefficient (G x) s
    let v := fun s : PrincipalTerm => EuclideanSpace.single (termDirection d s) (1 : ℝ)
    let w := fun s : PrincipalTerm => fun y => W y (termInput b d s).1
      (termInput b d s).2.1 (termInput b d s).2.2
    (∑ s, A s * fderiv ℝ (fun y => (χ : CoordinateSpace → ℝ) y * w s y) x (v s)) =
      (χ : CoordinateSpace → ℝ) x * divergencePrincipal (G x) (directionalJet W x) b d +
      ∑ s, A s * fderiv ℝ (χ : CoordinateSpace → ℝ) x (v s) * w s x := by
  dsimp only
  rw [divergencePrincipal_eq_sum_term, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [fderiv_test_mul_local hU (test_smooth χ) hχ (hW _ _ _)]
  have hcut : (θ : CoordinateSpace → ℝ) x * (χ : CoordinateSpace → ℝ) x =
      (χ : CoordinateSpace → ℝ) x := by
    by_cases hxs : x ∈ tsupport (χ : CoordinateSpace → ℝ)
    · simp only [hθ x hxs, one_mul]
    · simp only [image_eq_zero_of_notMem_tsupport hxs, mul_zero]
  simp only [directionalJet]
  linear_combination
    (termCoefficient (G x) s *
      fderiv ℝ (fun y => W y (termInput b d s).1 (termInput b d s).2.1 (termInput b d s).2.2) x
        (EuclideanSpace.single (termDirection d s) 1)) * hcut

end Burnett.Microlocal.RicciRow


set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.RicciRow

open Set
open scoped ContDiff Manifold BigOperators
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.InverseField
open Burnett.Geometry.SmoothMetricConnection
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open Burnett.Analysis.HminusWeightedDual (complexTest complexTest_pderiv)
open Burnett.Analysis.LocalWeakDerivative (contDiff_test_mul_local)
open Burnett.F05.CoordinateCurl (localizedGradientTest)
open Burnett.F05.OriginalCoordinateCurl
open Burnett.Microlocal.BesselLocalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

omit [IsManifold Model ∞ M] in
theorem exists_chartOuterCutoff (c : M) (χ : D)
    (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target) :
    ∃ θ : D, tsupport (θ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target ∧
      (∀ x, 0 ≤ (θ : CoordinateSpace → ℝ) x ∧ (θ : CoordinateSpace → ℝ) x ≤ 1) ∧
      ∀ x ∈ tsupport (χ : CoordinateSpace → ℝ), (θ : CoordinateSpace → ℝ) x = 1 := by
  obtain ⟨L, _, _, hLU, θ, hs, hc, hθ, h01, h1⟩ :=
    Burnett.Geometry.FlatRigidity.exists_smooth_cutoff_on_compact_chart
      (test_compactSupport χ) (chartAt CoordinateSpace c).open_target hχ
  exact ⟨⟨θ, hs, hc⟩, hθ.trans hLU, h01, h1⟩

def backgroundInverse (g₀ : Field (M := M)) (c : M) : CoordinateSpace → Tensor2 :=
  fun x => matrixInverse (metricComponents (coordinateBilinear g₀ c) x)

def chartRawPerturbationJet (g₀ g₁ : Field (M := M)) (c : M) : CoordinateSpace → FirstJet :=
  coordinateJet (fun x => metricComponents (coordinateBilinear g₁ c) x -
    metricComponents (coordinateBilinear g₀ c) x)

theorem chartRawPerturbationJet_smoothOn (g₀ g₁ : Field (M := M))
    (h₀ : IsSmooth g₀) (h₁ : IsSmooth g₁) (c : M) (q a b : Index) :
    ContDiffOn ℝ ∞ (fun x => chartRawPerturbationJet g₀ g₁ c x q a b) (chartAt CoordinateSpace c).target :=
  contDiffOn_coordinateJet _ _ (chartAt CoordinateSpace c).open_target
    (fun i j => (contDiffOn_metricComponents g₁ h₁ c i j).sub (contDiffOn_metricComponents g₀ h₀ c i j)) q a b

theorem termCoefficient_smoothOn (G : CoordinateSpace → Tensor2) (U : Set CoordinateSpace)
    (hG : ∀ a e, ContDiffOn ℝ ∞ (fun x => G x a e) U) (s : PrincipalTerm) :
    ContDiffOn ℝ ∞ (fun x => termCoefficient (G x) s) U :=
  contDiffOn_const.mul ((hG s.1 s.2.1).div_const 2)

/-- A genuine compact, globally smooth coefficient of the first-order row. -/
def localizedRicciCoefficient (G : CoordinateSpace → Tensor2) (θ : D)
    {U : Set CoordinateSpace} (hU : IsOpen U)
    (hθ : tsupport (θ : CoordinateSpace → ℝ) ⊆ U)
    (hG : ∀ a e, ContDiffOn ℝ ∞ (fun x => G x a e) U) (s : PrincipalTerm) : D :=
  ⟨fun x => (θ : CoordinateSpace → ℝ) x * termCoefficient (G x) s,
    contDiff_test_mul_local hU (test_smooth θ) hθ (termCoefficient_smoothOn G U hG s),
    (test_compactSupport θ).mul_right⟩

theorem localizedRicciCoefficient_apply (G : CoordinateSpace → Tensor2) (θ : D)
    {U : Set CoordinateSpace} (hU : IsOpen U)
    (hθ : tsupport (θ : CoordinateSpace → ℝ) ⊆ U)
    (hG : ∀ a e, ContDiffOn ℝ ∞ (fun x => G x a e) U) (s : PrincipalTerm) (x : CoordinateSpace) :
    (localizedRicciCoefficient G θ hU hθ hG s : CoordinateSpace → ℝ) x =
      (θ : CoordinateSpace → ℝ) x * termCoefficient (G x) s := rfl

theorem localizedRicciCoefficient_tsupport (G : CoordinateSpace → Tensor2) (θ : D)
    {U : Set CoordinateSpace} (hU : IsOpen U)
    (hθ : tsupport (θ : CoordinateSpace → ℝ) ⊆ U)
    (hG : ∀ a e, ContDiffOn ℝ ∞ (fun x => G x a e) U) (s : PrincipalTerm) :
    tsupport (localizedRicciCoefficient G θ hU hθ hG s : CoordinateSpace → ℝ) ⊆
      tsupport (θ : CoordinateSpace → ℝ) := tsupport_mul_subset_left

def chartRicciCoefficient (g₀ : Field (M := M)) (h₀ : IsSmooth g₀)
    (hn₀ : IsNondegenerate g₀) (c : M) (θ : D)
    (hθ : tsupport (θ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target) :
    PrincipalTerm → D :=
  localizedRicciCoefficient (backgroundInverse g₀ c) θ (chartAt CoordinateSpace c).open_target hθ
    (coordinateInverse_component_smoothOn g₀ h₀ hn₀ c)

def ricciRowDirectionVector (d : Index) (s : PrincipalTerm) : CoordinateSpace :=
  EuclideanSpace.single (termDirection d s) 1

/-- The zeroth-order row arising from differentiating the fixed inner cutoff. -/
def ricciCutoffLower (G : CoordinateSpace → Tensor2) (W : CoordinateSpace → FirstJet)
    (χ θ : D) (b d : Index) (x : CoordinateSpace) : ℝ :=
  ∑ s : PrincipalTerm, ((θ : CoordinateSpace → ℝ) x * termCoefficient (G x) s) *
    fderiv ℝ (χ : CoordinateSpace → ℝ) x (ricciRowDirectionVector d s) *
      W x (termInput b d s).1 (termInput b d s).2.1 (termInput b d s).2.2

def chartFirstOrderRow (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n)) (hn₀ : IsNondegenerate g₀) (c : M)
    (χ θ : D)
    (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hθ : tsupport (θ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (b d : Index) (n : ℕ) : SchwartzMap CoordinateSpace ℂ :=
  firstOrderRow (chartRicciCoefficient g₀ h₀ hn₀ c θ hθ) (ricciRowDirectionVector d) (termInput b d)
    (Fin.elim0 : Fin 0 → D) (Fin.elim0 : Fin 0 → JetIndex)
    (originalGradientSchwartz g₀ g h₀ hg c χ hχ n)

theorem originalGradientSchwartz_pderiv_apply_rawJet (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n)) (c : M)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (n : ℕ) (k : JetIndex) (q : Index) (x : CoordinateSpace) :
    SchwartzMap.pderivCLM ℂ (EuclideanSpace.single q 1)
      (originalGradientSchwartz g₀ g h₀ hg c χ hχ n k) x =
      (fderiv ℝ (fun y => (χ : CoordinateSpace → ℝ) y *
        chartRawPerturbationJet g₀ (g n) c y k.1 k.2.1 k.2.2) x (EuclideanSpace.single q 1) : ℂ) := by
  let u := localizedGradientTest (chartAt CoordinateSpace c).open_target χ hχ
    (originalComponent_smoothOn g₀ g h₀ hg c n k.2) k.1
  exact complexTest_pderiv u q x

private theorem schwartz_sum_apply {ι : Type*} [Fintype ι]
    (F : ι → SchwartzMap CoordinateSpace ℂ) (x : CoordinateSpace) :
    (∑ s, F s) x = ∑ s, F s x := by
  let ev : SchwartzMap CoordinateSpace ℂ →+ ℂ :=
    { toFun := fun u => u x
      map_zero' := rfl
      map_add' := fun _ _ => SchwartzMap.add_apply }
  exact map_sum ev F Finset.univ

/-- Pointwise actual Schwartz row for the chosen original metric difference. -/
theorem chartFirstOrderRow_apply (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n)) (hn₀ : IsNondegenerate g₀) (c : M)
    (χ θ : D)
    (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hθ : tsupport (θ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hθ1 : ∀ x ∈ tsupport (χ : CoordinateSpace → ℝ), (θ : CoordinateSpace → ℝ) x = 1)
    (b d : Index) (n : ℕ) (x : CoordinateSpace) :
    let G := backgroundInverse g₀ c
    let W := chartRawPerturbationJet g₀ (g n) c
    chartFirstOrderRow g₀ g h₀ hg hn₀ c χ θ hχ hθ b d n x =
      (((χ : CoordinateSpace → ℝ) x *
        divergencePrincipal (G x) (directionalJet W x) b d + ricciCutoffLower G W χ θ b d x : ℝ) : ℂ) := by
  dsimp only
  let G := backgroundInverse g₀ c
  let W := chartRawPerturbationJet g₀ (g n) c
  let a (s : PrincipalTerm) := (θ : CoordinateSpace → ℝ) x * termCoefficient (G x) s
  let w (s : PrincipalTerm) (y : CoordinateSpace) :=
    W y (termInput b d s).1 (termInput b d s).2.1 (termInput b d s).2.2
  let v (s : PrincipalTerm) := ricciRowDirectionVector d s
  let p (s : PrincipalTerm) := fderiv ℝ (fun y => (χ : CoordinateSpace → ℝ) y * w s y) x (v s)
  change chartFirstOrderRow g₀ g h₀ hg hn₀ c χ θ hχ hθ b d n x =
    (((χ : CoordinateSpace → ℝ) x *
      divergencePrincipal (G x) (directionalJet W x) b d + ricciCutoffLower G W χ θ b d x : ℝ) : ℂ)
  calc
    _ = ∑ s : PrincipalTerm, (a s : ℂ) * (p s : ℂ) := by
      rw [chartFirstOrderRow, firstOrderRow, Fin.sum_univ_zero, add_zero, schwartz_sum_apply]
      apply Finset.sum_congr rfl
      intro s _
      change (a s : ℂ) * SchwartzMap.pderivCLM ℂ (EuclideanSpace.single (termDirection d s) 1)
        (originalGradientSchwartz g₀ g h₀ hg c χ hχ n (termInput b d s)) x = _
      rw [originalGradientSchwartz_pderiv_apply_rawJet]
      rfl
    _ = ((∑ s : PrincipalTerm, a s * p s : ℝ) : ℂ) := by
      simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    _ = _ := congrArg Complex.ofReal
      (localizedSum_eq_principal_add_cutoff G W χ θ (chartAt CoordinateSpace c).open_target hχ hθ1
        (chartRawPerturbationJet_smoothOn g₀ (g n) h₀ (hg n) c) x b d)

end Burnett.Microlocal.RicciRow
