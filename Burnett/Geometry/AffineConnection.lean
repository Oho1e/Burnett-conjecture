import Burnett.Geometry.CoordinateCovariantDerivative

/-!
# The induced tensor connection and metric compatibility in coordinates

Dual differentiation of actual scalar pairings is shown to be tensorial.
The resulting covariant-three multilinear map has exactly the existing
covariantJet and auxiliaryPerturbationJet components. The computed metric
connection preserves the actual bilinear metric pairing on varying vector
fields and has zero torsion against the actual Lie bracket.
These are local coordinate results; nonlinear chart naturality and global
Levi-Civita existence remain separate obligations.
-/

noncomputable section

namespace Burnett.Geometry.AffineConnection
open scoped BigOperators Topology
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.CoordinateCovariantDerivative
open Burnett.Geometry.BackgroundConnection

lemma component_differentiable {W : VectorField} {x : CoordinateSpace}
    (hW : DifferentiableAt ℝ W x) (a : Index) :
    DifferentiableAt ℝ (fun y => W y a) x :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Index => ℝ) a).differentiableAt.comp x hW

lemma fderiv_component {W : VectorField} {x : CoordinateSpace}
    (hW : DifferentiableAt ℝ W x) (a : Index) (v : CoordinateSpace) :
    fderiv ℝ (fun y => W y a) x v = (fderiv ℝ W x v) a := by
  have hh := ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Index => ℝ) a).hasFDerivAt.comp x hW.hasFDerivAt).fderiv
  exact congrArg (fun L : CoordinateSpace →L[ℝ] ℝ => L v) hh

lemma fderiv_product3 (f g h : CoordinateSpace → ℝ) (x v : CoordinateSpace)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) :
    fderiv ℝ (fun y => f y * g y * h y) x v =
      fderiv ℝ f x v * g x * h x + f x * fderiv ℝ g x v * h x +
        f x * g x * fderiv ℝ h x v := by
  rw [fderiv_fun_mul (hf.fun_mul hg) hh, fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The actual directional Frechet derivative of every tensor component. -/
def directionalTensor (H : CoordinateSpace → Tensor2) (x v : CoordinateSpace) : Tensor2 :=
  fun a b => fderiv ℝ (fun y => H y a b) x v

/-- Differentiating a scalar bilinear pairing uses the true derivatives of
both vector fields and the true component derivatives of the same tensor. -/
theorem fderiv_tensorForm (H : CoordinateSpace → Tensor2) (U W : VectorField)
    (x v : CoordinateSpace) (hH : DifferentiableComponentsAt H x)
    (hU : DifferentiableAt ℝ U x) (hW : DifferentiableAt ℝ W x) :
    fderiv ℝ (fun y => tensorForm (H y) (U y) (W y)) x v =
      tensorForm (H x) (fderiv ℝ U x v) (W x) +
      tensorForm (directionalTensor H x v) (U x) (W x) +
      tensorForm (H x) (U x) (fderiv ℝ W x v) := by
  have hu (a : Index) := component_differentiable hU a
  have hw (b : Index) := component_differentiable hW b
  have ht (a b : Index) := ((hu a).fun_mul (hH a b)).fun_mul (hw b)
  simp only [tensorForm_apply]
  rw [fderiv_fun_sum (u := Finset.univ) (fun a _ => DifferentiableAt.fun_sum (u := Finset.univ) (fun b _ => ht a b))]
  simp only [ContinuousLinearMap.sum_apply]
  simp_rw [fderiv_fun_sum (u := Finset.univ) (fun b _ => ht _ b), ContinuousLinearMap.sum_apply]
  simp_rw [fderiv_product3 _ _ _ x v (hu _) (hH _ _) (hw _),
    fderiv_component hU, fderiv_component hW]
  simp only [directionalTensor, Finset.sum_add_distrib]


/-- The connection correction as an actual linear map on its second vector. -/
def connectionLinear (Γ : Connection) (v : CoordinateSpace) :
    CoordinateSpace →ₗ[ℝ] CoordinateSpace where
  toFun w := connectionTerm Γ v w
  map_add' u w := connectionTerm_add_right Γ v u w
  map_smul' r w := connectionTerm_smul_right Γ r v w

@[simp] theorem connectionLinear_apply (Γ : Connection) (v w : CoordinateSpace) :
    connectionLinear Γ v w = connectionTerm Γ v w := rfl

theorem directionalTensor_add (H : CoordinateSpace → Tensor2) (x v w : CoordinateSpace) :
    directionalTensor H x (v + w) = directionalTensor H x v + directionalTensor H x w := by
  ext a b
  exact (fderiv ℝ (fun y => H y a b) x).map_add v w

theorem directionalTensor_smul (H : CoordinateSpace → Tensor2) (x v : CoordinateSpace) (r : ℝ) :
    directionalTensor H x (r • v) = r • directionalTensor H x v := by
  ext a b
  exact (fderiv ℝ (fun y => H y a b) x).map_smul r v

theorem tensorForm_add (H J : Tensor2) : tensorForm (H + J) = tensorForm H + tensorForm J :=
  (Matrix.toBilin coordinateBasis).map_add H J

theorem tensorForm_smul (r : ℝ) (H : Tensor2) : tensorForm (r • H) = r • tensorForm H :=
  (Matrix.toBilin coordinateBasis).map_smul r H

/-- The induced derivative is constructed as an actual covariant-three
multilinear map: its first argument is a vector and its value a bilinear form.
No tensoriality or comparison identity is supplied as an input. -/
def cov2Differential (Γ : CoordinateSpace → Connection) (H : CoordinateSpace → Tensor2)
    (x : CoordinateSpace) : CoordinateSpace →ₗ[ℝ] LinearMap.BilinForm ℝ CoordinateSpace where
  toFun v := tensorForm (directionalTensor H x v) -
    (tensorForm (H x)).compLeft (connectionLinear (Γ x) v) -
    (tensorForm (H x)).compRight (connectionLinear (Γ x) v)
  map_add' v w := by
    ext u z
    simp only [directionalTensor_add, tensorForm_add, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.BilinForm.compLeft_apply, LinearMap.BilinForm.compRight_apply,
      connectionLinear_apply, connectionTerm_add_left, map_add]
    ring
  map_smul' r v := by
    ext u z
    simp only [directionalTensor_smul, tensorForm_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.BilinForm.compLeft_apply, LinearMap.BilinForm.compRight_apply,
      connectionLinear_apply, connectionTerm_smul_left, map_smul, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem cov2Differential_apply (Γ : CoordinateSpace → Connection)
    (H : CoordinateSpace → Tensor2) (x v u w : CoordinateSpace) :
    cov2Differential Γ H x v u w = tensorForm (directionalTensor H x v) u w -
      tensorForm (H x) (connectionTerm (Γ x) v u) w -
      tensorForm (H x) u (connectionTerm (Γ x) v w) := rfl

/-- Genuine dual differentiation is tensorial: derivatives of both auxiliary
vector fields cancel, leaving the constructed multilinear tensor at x. -/
theorem inducedCov2_eq_cov2Differential (Γ : CoordinateSpace → Connection)
    (H : CoordinateSpace → Tensor2) (V U W : VectorField) (x : CoordinateSpace)
    (hH : DifferentiableComponentsAt H x) (hU : DifferentiableAt ℝ U x)
    (hW : DifferentiableAt ℝ W x) :
    inducedCov2 Γ H V U W x = cov2Differential Γ H x (V x) (U x) (W x) := by
  rw [inducedCov2, fderiv_tensorForm H U W x (V x) hH hU hW]
  simp only [derivative, cov2Differential_apply, map_add, LinearMap.add_apply]
  ring

/-- The full multilinear derivative has exactly the existing coordinate jet. -/
theorem cov2Differential_basis (Γ : CoordinateSpace → Connection)
    (H : CoordinateSpace → Tensor2) (x : CoordinateSpace) (b c d : Index) :
    cov2Differential Γ H x (EuclideanSpace.single b 1)
      (EuclideanSpace.single c 1) (EuclideanSpace.single d 1) =
      covariantJet (Γ x) (H x) (coordinateJet H x) b c d := by
  simp [cov2Differential_apply, tensorForm_apply, directionalTensor, coordinateJet,
    covariantJet, EuclideanSpace.single_apply, mul_comm]


/-- Vanishing of the actual components implies vanishing of the constructed
multilinear form; no component-to-tensor implication is assumed. -/
theorem cov2Differential_eq_zero_of_components (Γ : CoordinateSpace → Connection)
    (H : CoordinateSpace → Tensor2) (x : CoordinateSpace)
    (hz : ∀ b c d, covariantJet (Γ x) (H x) (coordinateJet H x) b c d = 0) :
    cov2Differential Γ H x = 0 := by
  apply coordinateBasis.ext
  intro b
  apply coordinateBasis.ext
  intro c
  apply coordinateBasis.ext
  intro d
  have hh := (cov2Differential_basis Γ H x b c d).trans (hz b c d)
  simpa [coordinateBasis, EuclideanSpace.basisFun_apply] using hh

/-- The constructed coordinate derivative preserves its actual metric.
The inverse and derivative symmetries are discharged from the same metric. -/
theorem computed_cov2Differential_eq_zero
    (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (hn : (g x).Nondegenerate)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) :
    cov2Differential (computedConnection g) (metricComponents g) x = 0 := by
  have hsx := hs.self_of_nhds
  apply cov2Differential_eq_zero_of_components
  intro b c d
  rw [computedConnection_eq_metricConnection g x hn hsx]
  exact christoffel_metric_compatible (metricComponents g x) (metricInverse (g x) hn)
    (coordinateJet (metricComponents g) x)
    (FiberMetric.covariant_symmetric _ hsx coordinateBasis)
    (coordinateJet_symmetric _ x (hs.mono (fun y hy => FiberMetric.covariant_symmetric _ hy coordinateBasis)))
    (FiberMetric.covariant_mul_contravariant _ hn hsx coordinateBasis) b c d

@[simp] theorem tensorForm_metricComponents
    (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace) (x : CoordinateSpace) :
    tensorForm (metricComponents g x) = g x := by
  have hmat : metricComponents g x = _root_.BilinForm.toMatrix coordinateBasis (g x) := by
    ext i j
    simp [metricComponents, FiberMetric.covariant]
  rw [tensorForm, hmat, Matrix.toBilin_toMatrix]

/-- Metric compatibility for genuine varying vector fields and the actual
bilinear metric pairing, not just for arrays at constant basis fields. -/
theorem computed_derivative_metric_compatible
    (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (V U W : VectorField) (x : CoordinateSpace) (hn : (g x).Nondegenerate)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hg : DifferentiableComponentsAt (metricComponents g) x)
    (hU : DifferentiableAt ℝ U x) (hW : DifferentiableAt ℝ W x) :
    fderiv ℝ (fun y => g y (U y) (W y)) x (V x) =
      g x (derivative (computedConnection g) V U x) (W x) +
      g x (U x) (derivative (computedConnection g) V W x) := by
  have hzero := inducedCov2_eq_cov2Differential (computedConnection g)
    (metricComponents g) V U W x hg hU hW
  rw [computed_cov2Differential_eq_zero g x hn hs] at hzero
  simp only [inducedCov2, tensorForm_metricComponents, LinearMap.zero_apply] at hzero
  linarith

/-- Torsion freeness is proved against the actual mathlib Lie bracket. -/
theorem computed_derivative_torsion_free
    (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (V W : VectorField) (x : CoordinateSpace)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) :
    derivative (computedConnection g) V W x - derivative (computedConnection g) W V x =
      _root_.VectorField.lieBracket ℝ V W x := by
  apply derivative_torsion_free
  exact christoffel_torsion_free _ _
    (coordinateJet_symmetric _ x (hs.mono (fun y hy => FiberMetric.covariant_symmetric _ hy coordinateBasis)))


/-- The bilinear form is the actual difference of the same two metric fields. -/
@[simp] theorem tensorForm_metricDifference
    (g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace) (x : CoordinateSpace) :
    tensorForm (metricComponents g₁ x - metricComponents g₀ x) = g₁ x - g₀ x := by
  change Matrix.toBilin coordinateBasis (metricComponents g₁ x - metricComponents g₀ x) = _
  rw [map_sub]
  exact congrArg₂ (fun A B : LinearMap.BilinForm ℝ CoordinateSpace => A - B)
    (tensorForm_metricComponents g₁ x) (tensorForm_metricComponents g₀ x)

/-- The actual dual derivative of the metric difference, not a separately
chosen component field, has precisely the existing auxiliary-jet components. -/
theorem cov2Differential_auxiliaryPerturbationJet
    (r g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (b c d : Index) :
    cov2Differential (computedConnection r)
      (fun y => metricComponents g₁ y - metricComponents g₀ y) x
      (EuclideanSpace.single b 1) (EuclideanSpace.single c 1) (EuclideanSpace.single d 1) =
      AuxiliaryConnection.auxiliaryPerturbationJet r g₀ g₁ x b c d :=
  cov2Differential_basis _ _ x b c d

/-- Scalar pairing characterization of the auxiliary derivative on actual
varying vector fields. Tensoriality and the same-field identity are proved. -/
theorem auxiliary_dual_derivative
    (r g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (V U W : VectorField) (x : CoordinateSpace)
    (hg : DifferentiableComponentsAt
      (fun y => metricComponents g₁ y - metricComponents g₀ y) x)
    (hU : DifferentiableAt ℝ U x) (hW : DifferentiableAt ℝ W x) :
    fderiv ℝ (fun y => (g₁ y - g₀ y) (U y) (W y)) x (V x) -
      (g₁ x - g₀ x) (derivative (computedConnection r) V U x) (W x) -
      (g₁ x - g₀ x) (U x) (derivative (computedConnection r) V W x) =
    cov2Differential (computedConnection r)
      (fun y => metricComponents g₁ y - metricComponents g₀ y) x (V x) (U x) (W x) := by
  have heq := inducedCov2_eq_cov2Differential (computedConnection r)
    (fun y => metricComponents g₁ y - metricComponents g₀ y) V U W x hg hU hW
  simpa only [inducedCov2, tensorForm_metricDifference] using heq

end Burnett.Geometry.AffineConnection
