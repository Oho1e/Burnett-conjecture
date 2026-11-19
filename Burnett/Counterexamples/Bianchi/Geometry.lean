import Burnett.Geometry.IntrinsicRicciTrace
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Burnett.Geometry.IntrinsicCov2
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

noncomputable section

set_option autoImplicit false
noncomputable section

namespace Burnett.Bianchi

open Matrix Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open scoped BigOperators

abbrev Spatial := Fin 3
abbrev SpatialMatrix := Matrix Spatial Spatial ℝ

/-- A four-dimensional block matrix, with the actual time index zero. -/
def block (c : ℝ) (G : SpatialMatrix) : Matrix Index Index ℝ :=
  fun a b => Fin.cases (Fin.cases c (fun _ => 0) b)
    (fun i => Fin.cases 0 (fun j => G i j) b) a

@[simp] theorem block_time_time (c : ℝ) (G : SpatialMatrix) : block c G 0 0 = c := rfl
@[simp] theorem block_time_space (c : ℝ) (G : SpatialMatrix) (j : Spatial) : block c G 0 j.succ = 0 := rfl
@[simp] theorem block_space_time (c : ℝ) (G : SpatialMatrix) (i : Spatial) : block c G i.succ 0 = 0 := rfl
@[simp] theorem block_space_space (c : ℝ) (G : SpatialMatrix) (i j : Spatial) :
    block c G i.succ j.succ = G i j := rfl

def metricFirstJet (A : SpatialMatrix) : FirstJet :=
  fun d => if d = 0 then block 0 ((2 : ℝ) • A) else 0

/-- The synchronous homogeneous connection, with no curvature conclusions built in. -/
def connection (A K : SpatialMatrix) : Connection :=
  fun a b c => Fin.cases
    (Fin.cases 0 (fun i => Fin.cases 0 (fun j => A i j) c) b)
    (fun i => Fin.cases (Fin.cases 0 (fun j => K i j) c)
      (fun j => Fin.cases (K i j) (fun _ => 0) c) b) a

@[simp] theorem connection_000 (A K : SpatialMatrix) : connection A K 0 0 0 = 0 := rfl
@[simp] theorem connection_00s (A K : SpatialMatrix) (j : Spatial) : connection A K 0 0 j.succ = 0 := rfl
@[simp] theorem connection_0s0 (A K : SpatialMatrix) (i : Spatial) : connection A K 0 i.succ 0 = 0 := rfl
@[simp] theorem connection_0ss (A K : SpatialMatrix) (i j : Spatial) : connection A K 0 i.succ j.succ = A i j := rfl
@[simp] theorem connection_s00 (A K : SpatialMatrix) (i : Spatial) : connection A K i.succ 0 0 = 0 := rfl
@[simp] theorem connection_s0s (A K : SpatialMatrix) (i j : Spatial) : connection A K i.succ 0 j.succ = K i j := rfl
@[simp] theorem connection_ss0 (A K : SpatialMatrix) (i j : Spatial) : connection A K i.succ j.succ 0 = K i j := rfl
@[simp] theorem connection_sss (A K : SpatialMatrix) (i j k : Spatial) :
    connection A K i.succ j.succ k.succ = 0 := rfl

theorem christoffel_block (B A : SpatialMatrix) (hA : ∀ i j, A i j = A j i) :
    christoffel (block (-1) B) (metricFirstJet A) = connection A (B * A) := by
  funext a b c
  refine Fin.cases ?_ (fun i => ?_) a
  all_goals refine Fin.cases ?_ (fun j => ?_) b
  all_goals refine Fin.cases ?_ (fun k => ?_) c
  all_goals simp [christoffel, koszul, metricFirstJet, Fin.sum_univ_succ, Matrix.mul_apply, hA]
  all_goals ring

def connectionFirstJet (Ad Kd : SpatialMatrix) : ConnectionJet :=
  fun d => if d = 0 then connection Ad Kd else 0

theorem ricci_time_time (A K Ad Kd : SpatialMatrix) :
    ricci (connection A K) (connectionFirstJet Ad Kd) 0 0 =
      -Matrix.trace Kd - Matrix.trace (K * K) := by
  simp [ricci, connectionFirstJet, connection, Fin.sum_univ_succ, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  ring

theorem ricci_time_space (A K Ad Kd : SpatialMatrix) (i : Spatial) :
    ricci (connection A K) (connectionFirstJet Ad Kd) 0 i.succ = 0 := by
  simp [ricci, connectionFirstJet, connection, Fin.sum_univ_succ]

theorem ricci_space_time (A K Ad Kd : SpatialMatrix) (i : Spatial) :
    ricci (connection A K) (connectionFirstJet Ad Kd) i.succ 0 = 0 := by
  simp [ricci, connectionFirstJet, connection, Fin.sum_univ_succ]

theorem ricci_space_space (A K Ad Kd : SpatialMatrix) (i j : Spatial) :
    ricci (connection A K) (connectionFirstJet Ad Kd) i.succ j.succ =
      Ad i j + Matrix.trace K * A i j - (A * K) i j - (A * K) j i := by
  simp [ricci, connectionFirstJet, connection, Fin.sum_univ_succ, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  ring

end Burnett.Bianchi



namespace Burnett.Bianchi

open Matrix Filter Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.InverseField
open scoped BigOperators Topology ContDiff

theorem block_mul (a b : ℝ) (G H : SpatialMatrix) :
    (block a G : Matrix Index Index ℝ) * block b H = block (a * b) (G * H) := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i
  all_goals refine Fin.cases ?_ (fun l => ?_) j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_succ, block]

theorem block_one : block 1 (1 : SpatialMatrix) = (1 : Matrix Index Index ℝ) := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i
  all_goals refine Fin.cases ?_ (fun l => ?_) j
  · rfl
  · change (0 : ℝ) = if (0 : Index) = l.succ then 1 else 0
    rw [if_neg (Ne.symm (Fin.succ_ne_zero l))]
  · change (0 : ℝ) = if k.succ = (0 : Index) then 1 else 0
    rw [if_neg (Fin.succ_ne_zero k)]
  · change (if k = l then (1 : ℝ) else 0) = if k.succ = l.succ then 1 else 0
    simp only [Fin.succ_inj]

theorem matrixInverse_block (G : SpatialMatrix) (hG : IsUnit G) :
    matrixInverse (block (-1) G) = block (-1) G⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [block_mul, G.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det G).mp hG)]
  norm_num only [neg_mul_neg, one_mul]
  exact block_one

/-- The genuine metric with lapse one and spatial coefficients depending only on time. -/
def metric (γ : ℝ → SpatialMatrix) (x : CoordinateSpace) : LinearMap.BilinForm ℝ CoordinateSpace :=
  Matrix.toBilin coordinateBasis (block (-1) (γ (x 0)))

theorem metric_components (γ : ℝ → SpatialMatrix) (x : CoordinateSpace) :
    metricComponents (metric γ) x = block (-1) (γ (x 0)) := by
  rw [Burnett.Geometry.ManifoldMetricTransition.metricComponents_eq_toMatrix]
  exact BilinForm.toMatrix_toBilin coordinateBasis _

theorem time_component_hasFDerivAt (γ : ℝ → SpatialMatrix) (x : CoordinateSpace)
    (D : SpatialMatrix) (hγ : ∀ i j, HasDerivAt (fun t => γ t i j) (D i j) (x 0))
    (i j : Spatial) :
    HasFDerivAt (fun y : CoordinateSpace => γ (y 0) i j)
      ((D i j) • (EuclideanSpace.proj (𝕜 := ℝ) (0 : Index))) x := by
  exact (hγ i j).comp_hasFDerivAt x (EuclideanSpace.proj (𝕜 := ℝ) (0 : Index)).hasFDerivAt

theorem metric_coordinateJet (γ : ℝ → SpatialMatrix) (A : SpatialMatrix) (x : CoordinateSpace)
    (hγ : ∀ i j, HasDerivAt (fun t => γ t i j) (2 * A i j) (x 0)) :
    coordinateJet (metricComponents (metric γ)) x = metricFirstJet A := by
  have hγ' : ∀ i j, HasDerivAt (fun t => γ t i j) (((2 : ℝ) • A) i j) (x 0) := hγ
  have hc : metricComponents (metric γ) = fun y => block (-1) (γ (y 0)) := funext (metric_components γ)
  rw [hc]
  funext d a b
  refine Fin.cases ?_ (fun i => ?_) a
  all_goals refine Fin.cases ?_ (fun j => ?_) b
  all_goals simp only [coordinateJet, block_time_time, block_time_space, block_space_time,
    block_space_space]
  · by_cases hd : d = 0 <;> simp [metricFirstJet, hd]
  · by_cases hd : d = 0 <;> simp [metricFirstJet, hd]
  · by_cases hd : d = 0 <;> simp [metricFirstJet, hd]
  · rw [(time_component_hasFDerivAt γ x ((2 : ℝ) • A) hγ' i j).fderiv]
    by_cases hd : d = 0
    · subst d
      simp [metricFirstJet, Pi.smul_apply, smul_eq_mul]
    · simp [metricFirstJet, hd, EuclideanSpace.single_apply, Ne.symm hd]

theorem computedConnection_metric (γ : ℝ → SpatialMatrix) (A : SpatialMatrix) (x : CoordinateSpace)
    (hG : IsUnit (γ (x 0))) (hA : ∀ i j, A i j = A j i)
    (hγ : ∀ i j, HasDerivAt (fun t => γ t i j) (2 * A i j) (x 0)) :
    computedConnection (metric γ) x = connection A ((γ (x 0))⁻¹ * A) := by
  rw [computedConnection, metric_coordinateJet γ A x hγ, metric_components, matrixInverse_block _ hG]
  exact christoffel_block _ A hA

end Burnett.Bianchi


namespace Burnett.Bianchi

open Matrix Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open scoped BigOperators

def rankOne (p : Spatial → ℝ) : SpatialMatrix := fun i j => p i * p j

def sourceTensor (ρ d : ℝ) (p : Spatial → ℝ) : Matrix Index Index ℝ :=
  block ρ ((ρ / d : ℝ) • rankOne p)

theorem A_K_symmetric (B A K : SpatialMatrix)
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i) (hK : K = B * A) :
    ∀ i j, (A * K) i j = (A * K) j i := by
  have hAt : Aᵀ = A := by ext i j; exact hA j i
  have hBt : Bᵀ = B := by ext i j; exact hB j i
  have ht : (A * K)ᵀ = A * K := by
    rw [hK, Matrix.transpose_mul, Matrix.transpose_mul, hAt, hBt, Matrix.mul_assoc]
  intro i j
  exact (congrArg (fun M : SpatialMatrix => M i j) ht).symm

/-- The ODE and constraint imply the required components of the actual Ricci construction. -/
theorem ricci_eq_source_of_ode (B A K Ad Kd : SpatialMatrix) (ρ d : ℝ) (p : Spatial → ℝ)
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i) (hK : K = B * A)
    (hAd : Ad = (2 : ℝ) • (A * K) - Matrix.trace K • A + (ρ / d : ℝ) • rankOne p)
    (hKd : Matrix.trace Kd = ρ - (Matrix.trace K)^2)
    (hC : (Matrix.trace K)^2 - Matrix.trace (K * K) - 2 * ρ = 0) :
    (fun a b => ricci (connection A K) (connectionFirstJet Ad Kd) a b) = sourceTensor ρ d p := by
  funext a b
  refine Fin.cases ?_ (fun i => ?_) a
  all_goals refine Fin.cases ?_ (fun j => ?_) b
  · rw [ricci_time_time, hKd]
    simp only [sourceTensor, block_time_time]
    linarith
  · simp [ricci_time_space, sourceTensor]
  · simp [ricci_space_time, sourceTensor]
  · rw [ricci_space_space, hAd]
    simp only [sourceTensor, block_space_space, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, rankOne]
    rw [← A_K_symmetric B A K hA hB hK i j]
    ring

def quadratic (T : Matrix Index Index ℝ) (v : Index → ℝ) : ℝ :=
  ∑ a, ∑ b, T a b * v a * v b

def spatialQuadratic (B : SpatialMatrix) (p : Spatial → ℝ) : ℝ :=
  ∑ i, ∑ j, B i j * p i * p j

def nullCovector (d : ℝ) (p : Spatial → ℝ) (s : ℝ) : Index → ℝ :=
  Fin.cases (-Real.sqrt d) (fun i => s * p i)

theorem nullCovector_null (B : SpatialMatrix) (p : Spatial → ℝ) (d s : ℝ)
    (hd : 0 < d) (hD : d = spatialQuadratic B p) (hs : s ^ 2 = 1) :
    quadratic (block (-1) B) (nullCovector d p s) = 0 := by
  calc
    _ = -(Real.sqrt d)^2 + s^2 * spatialQuadratic B p := by
      simp [quadratic, spatialQuadratic, block, nullCovector, Fin.sum_univ_succ]
      ring
    _ = 0 := by rw [Real.sq_sqrt hd.le, hs, one_mul, ← hD]; ring

theorem source_null_squares (ρ d : ℝ) (p : Spatial → ℝ) (hd : 0 < d) :
    sourceTensor ρ d p = fun a b => (ρ / (2 * d)) *
      (nullCovector d p 1 a * nullCovector d p 1 b +
        nullCovector d p (-1) a * nullCovector d p (-1) b) := by
  funext a b
  refine Fin.cases ?_ (fun i => ?_) a
  all_goals refine Fin.cases ?_ (fun j => ?_) b
  all_goals simp [sourceTensor, block, nullCovector, rankOne]
  all_goals field_simp [hd.ne']
  all_goals ring_nf
  all_goals simp only [Real.sq_sqrt hd.le]

theorem source_positive_semidefinite (ρ d : ℝ) (p : Spatial → ℝ)
    (hρ : 0 ≤ ρ) (hd : 0 < d) (v : Index → ℝ) : 0 ≤ quadratic (sourceTensor ρ d p) v := by
  have heq : quadratic (sourceTensor ρ d p) v =
      ρ * (v 0)^2 + (ρ / d) * (∑ i : Spatial, p i * v i.succ)^2 := by
    simp [quadratic, sourceTensor, block, rankOne, Fin.sum_univ_succ]
    ring
  rw [heq]
  exact add_nonneg (mul_nonneg hρ (sq_nonneg _)) (mul_nonneg (div_nonneg hρ hd.le) (sq_nonneg _))

def traceWith (B T : Matrix Index Index ℝ) : ℝ := ∑ a, ∑ b, B a b * T a b

theorem source_trace_zero (B : SpatialMatrix) (ρ d : ℝ) (p : Spatial → ℝ)
    (hd : 0 < d) (hD : d = spatialQuadratic B p) :
    traceWith (block (-1) B) (sourceTensor ρ d p) = 0 := by
  have heq : traceWith (block (-1) B) (sourceTensor ρ d p) =
      -ρ + (ρ / d) * spatialQuadratic B p := by
    simp [traceWith, sourceTensor, block, rankOne, spatialQuadratic, Fin.sum_univ_succ]
    ring
  rw [heq, ← hD]
  field_simp [hd.ne']
  ring

end Burnett.Bianchi


namespace Burnett.Bianchi

open Matrix Filter Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.InverseField
open scoped BigOperators Topology ContDiff

theorem time_component_direction (A : ℝ → SpatialMatrix) (D : SpatialMatrix) (x : CoordinateSpace)
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (D i j) (x 0)) (d : Index) (i j : Spatial) :
    fderiv ℝ (fun y : CoordinateSpace => A (y 0) i j) x (EuclideanSpace.single d 1) =
      if d = 0 then D i j else 0 := by
  rw [(time_component_hasFDerivAt A x D hA i j).fderiv]
  by_cases hd : d = 0
  · subst d
    simp
  · simp [hd, EuclideanSpace.single_apply, Ne.symm hd]

theorem connection_coordinateJet (A K : ℝ → SpatialMatrix) (Ad Kd : SpatialMatrix) (x : CoordinateSpace)
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (Ad i j) (x 0))
    (hK : ∀ i j, HasDerivAt (fun t => K t i j) (Kd i j) (x 0)) :
    coordinateConnectionJet (fun y => connection (A (y 0)) (K (y 0))) x = connectionFirstJet Ad Kd := by
  funext d a b c
  refine Fin.cases ?_ (fun i => ?_) a
  all_goals refine Fin.cases ?_ (fun j => ?_) b
  all_goals refine Fin.cases ?_ (fun k => ?_) c
  all_goals by_cases hd : d = 0
  all_goals simp [coordinateConnectionJet, connectionFirstJet, connection, hd,
    time_component_direction A Ad x hA, time_component_direction K Kd x hK]

theorem coordinateRicci_of_connection_germ (Γ : CoordinateSpace → Connection)
    (A K : ℝ → SpatialMatrix) (Ad Kd : SpatialMatrix) (x : CoordinateSpace)
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (Ad i j) (x 0))
    (hK : ∀ i j, HasDerivAt (fun t => K t i j) (Kd i j) (x 0))
    (heq : Γ =ᶠ[𝓝 x] fun y => connection (A (y 0)) (K (y 0))) :
    coordinateRicci Γ x = fun a b => ricci (connection (A (x 0)) (K (x 0)))
      (connectionFirstJet Ad Kd) a b := by
  have hjet : coordinateConnectionJet Γ x =
      coordinateConnectionJet (fun y => connection (A (y 0)) (K (y 0))) x := by
    funext d a b c
    have hc : (fun y => Γ y a b c) =ᶠ[𝓝 x] fun y => connection (A (y 0)) (K (y 0)) a b c :=
      heq.mono fun _ h => congrFun (congrFun (congrFun h a) b) c
    exact congrArg (fun D : CoordinateSpace →L[ℝ] ℝ => D (EuclideanSpace.single d 1)) hc.fderiv_eq
  rw [connection_coordinateJet A K Ad Kd x hA hK] at hjet
  funext a b
  change ricci (Γ x) (coordinateConnectionJet Γ x) a b = _
  rw [heq.self_of_nhds, hjet]

theorem computedConnection_metric_germ (I : Set ℝ) (hI : IsOpen I)
    (γ A K : ℝ → SpatialMatrix) (x : CoordinateSpace) (hx : x 0 ∈ I)
    (hG : ∀ t ∈ I, IsUnit (γ t)) (hA : ∀ t ∈ I, ∀ i j, A t i j = A t j i)
    (hγ : ∀ t ∈ I, ∀ i j, HasDerivAt (fun u => γ u i j) (2 * A t i j) t)
    (hK : ∀ t ∈ I, K t = (γ t)⁻¹ * A t) :
    computedConnection (metric γ) =ᶠ[𝓝 x] fun y => connection (A (y 0)) (K (y 0)) := by
  have hopen : IsOpen {y : CoordinateSpace | y 0 ∈ I} :=
    hI.preimage (EuclideanSpace.proj (𝕜 := ℝ) (0 : Index)).continuous
  filter_upwards [hopen.mem_nhds hx] with y hy
  rw [computedConnection_metric γ (A (y 0)) y (hG _ hy) (hA _ hy) (hγ _ hy), hK _ hy]

theorem inverse_symmetric (G : SpatialMatrix) (hG : ∀ i j, G i j = G j i) :
    ∀ i j, G⁻¹ i j = G⁻¹ j i := by
  have hs : Gᵀ = G := by ext i j; exact hG j i
  have hi : (G⁻¹)ᵀ = G⁻¹ := by rw [Matrix.transpose_nonsing_inv, hs]
  intro i j
  exact (congrArg (fun M : SpatialMatrix => M i j) hi).symm

/-- The actual locally computed Ricci tensor, with no nondegenerate extension assumption. -/
theorem computedRicci_eq_source (I : Set ℝ) (hI : IsOpen I)
    (γ A K : ℝ → SpatialMatrix) (x : CoordinateSpace) (hx : x 0 ∈ I)
    (hG : ∀ t ∈ I, IsUnit (γ t)) (hGs : ∀ i j, γ (x 0) i j = γ (x 0) j i)
    (hAs : ∀ t ∈ I, ∀ i j, A t i j = A t j i)
    (hγ : ∀ t ∈ I, ∀ i j, HasDerivAt (fun u => γ u i j) (2 * A t i j) t)
    (hKdef : ∀ t ∈ I, K t = (γ t)⁻¹ * A t)
    (Ad Kd : SpatialMatrix)
    (hAd : ∀ i j, HasDerivAt (fun t => A t i j) (Ad i j) (x 0))
    (hKd : ∀ i j, HasDerivAt (fun t => K t i j) (Kd i j) (x 0))
    (ρ d : ℝ) (p : Spatial → ℝ)
    (hAode : Ad = (2 : ℝ) • (A (x 0) * K (x 0)) - Matrix.trace (K (x 0)) • A (x 0) + (ρ / d : ℝ) • rankOne p)
    (hTrace : Matrix.trace Kd = ρ - (Matrix.trace (K (x 0)))^2)
    (hConstraint : (Matrix.trace (K (x 0)))^2 - Matrix.trace (K (x 0) * K (x 0)) - 2 * ρ = 0) :
    coordinateRicci (computedConnection (metric γ)) x = sourceTensor ρ d p := by
  rw [coordinateRicci_of_connection_germ _ A K Ad Kd x hAd hKd
    (computedConnection_metric_germ I hI γ A K x hx hG hAs hγ hKdef)]
  exact ricci_eq_source_of_ode _ _ _ _ _ ρ d p (hAs _ hx) (inverse_symmetric _ hGs)
    (hKdef _ hx) hAode hTrace hConstraint

def coordinateScalar (γ : ℝ → SpatialMatrix) (x : CoordinateSpace) : ℝ :=
  traceWith (matrixInverse (metricComponents (metric γ) x))
    (coordinateRicci (computedConnection (metric γ)) x)

def coordinateEinstein (γ : ℝ → SpatialMatrix) (x : CoordinateSpace) : Matrix Index Index ℝ :=
  (coordinateRicci (computedConnection (metric γ)) x : Matrix Index Index ℝ) -
    (coordinateScalar γ x / 2 : ℝ) • metricComponents (metric γ) x

theorem coordinateEinstein_eq_source_of_Ricci (γ : ℝ → SpatialMatrix) (x : CoordinateSpace)
    (hG : IsUnit (γ (x 0))) (ρ d : ℝ) (p : Spatial → ℝ) (hd : 0 < d)
    (hD : d = spatialQuadratic (γ (x 0))⁻¹ p)
    (hR : coordinateRicci (computedConnection (metric γ)) x = sourceTensor ρ d p) :
    coordinateScalar γ x = 0 ∧ coordinateEinstein γ x = sourceTensor ρ d p := by
  have hs : coordinateScalar γ x = 0 := by
    unfold coordinateScalar
    rw [metric_components, matrixInverse_block _ hG, hR]
    exact source_trace_zero _ ρ d p hd hD
  refine ⟨hs, ?_⟩
  simp only [coordinateEinstein, hs, zero_div, zero_smul, sub_zero]
  exact hR

end Burnett.Bianchi



namespace Burnett.Bianchi

open Matrix Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open scoped BigOperators

theorem block_transpose (c : ℝ) (G : SpatialMatrix) : (block c G)ᵀ = block c Gᵀ := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i
  all_goals refine Fin.cases ?_ (fun l => ?_) j
  all_goals rfl

theorem block_isUnit (B : SpatialMatrix) (hB : IsUnit B) : IsUnit (block 1 B) := by
  have hd := (Matrix.isUnit_iff_isUnit_det B).mp hB
  refine ⟨⟨block 1 B, block 1 B⁻¹, ?_, ?_⟩, rfl⟩
  · rw [block_mul, B.mul_nonsing_inv hd, one_mul, block_one]
  · rw [block_mul, B.nonsing_inv_mul hd, one_mul, block_one]

theorem block_congruence (B : SpatialMatrix) :
    (block 1 B)ᵀ * block (-1) (1 : SpatialMatrix) * block 1 B = block (-1) (Bᵀ * B) := by
  rw [block_transpose, block_mul, block_mul, Matrix.mul_one]
  norm_num

def modelMinkowski : LinearMap.BilinForm ℝ CoordinateSpace :=
  Matrix.toBilin coordinateBasis (block (-1) (1 : SpatialMatrix))

theorem modelMinkowski_apply (u v : CoordinateSpace) :
    modelMinkowski u v = -(u 0 * v 0) + ∑ i : Spatial, u i.succ * v i.succ := by
  simp [modelMinkowski, Matrix.toBilin_apply, coordinateBasis, EuclideanSpace.basisFun_repr,
    block, Fin.sum_univ_succ, Matrix.one_apply]

/-- Actual linear-equivalence characterization of the Lorentz signature (-+++). -/
def HasLorentzSignature (g : LinearMap.BilinForm ℝ CoordinateSpace) : Prop :=
  ∃ e : CoordinateSpace ≃L[ℝ] CoordinateSpace, ∀ u v,
    g u v = modelMinkowski (e u) (e v)

theorem metric_hasLorentzSignature (γ : ℝ → SpatialMatrix) (x : CoordinateSpace)
    (hG : (γ (x 0)).PosDef) : HasLorentzSignature (metric γ x) := by
  obtain ⟨B, hB, hGram⟩ := Matrix.posDef_iff_eq_conjTranspose_mul_self.mp hG
  have hGr : γ (x 0) = Bᵀ * B := by simpa using hGram
  let T := block 1 B
  have hT : IsUnit T := block_isUnit B hB
  let e : CoordinateSpace ≃L[ℝ] CoordinateSpace :=
    (Matrix.toLinearEquiv coordinateBasis T ((Matrix.isUnit_iff_isUnit_det T).mp hT)).toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  intro u v
  change Matrix.toBilin coordinateBasis (block (-1) (γ (x 0))) u v = modelMinkowski (e u) (e v)
  rw [hGr, ← block_congruence]
  rw [← Matrix.toBilin_comp coordinateBasis coordinateBasis]
  rfl

theorem spatialQuadratic_inv_pos (G : SpatialMatrix) (hG : G.PosDef) (p : Spatial → ℝ) (hp : p ≠ 0) :
    0 < spatialQuadratic G⁻¹ p := by
  have h := hG.inv.2 p hp
  simpa [spatialQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using h

end Burnett.Bianchi


namespace Burnett.Bianchi

open Matrix Filter Set Burnett.RicciSymbol
open Burnett.Geometry Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.InverseField
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldBilinear
open scoped BigOperators Topology ContDiff Manifold

theorem computedConnection_congr_germ
    (g h : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace) (x : CoordinateSpace)
    (heq : g =ᶠ[𝓝 x] h) : computedConnection g =ᶠ[𝓝 x] computedConnection h := by
  filter_upwards [heq.eventuallyEq_nhds] with y hy
  have hc : metricComponents g =ᶠ[𝓝 y] metricComponents h :=
    hy.mono fun z hz => congrArg (fun B : LinearMap.BilinForm ℝ CoordinateSpace =>
      FiberMetric.covariant B coordinateBasis) hz
  unfold computedConnection
  rw [hc.self_of_nhds, coordinateJet_congr _ _ y hc]

theorem coordinateRicci_congr_germ (Γ Δ : CoordinateSpace → Connection) (x : CoordinateSpace)
    (heq : Γ =ᶠ[𝓝 x] Δ) : coordinateRicci Γ x = coordinateRicci Δ x := by
  have hjet : coordinateConnectionJet Γ x = coordinateConnectionJet Δ x := by
    funext d a b c
    have hc : (fun y => Γ y a b c) =ᶠ[𝓝 x] fun y => Δ y a b c :=
      heq.mono fun _ h => congrFun (congrFun (congrFun h a) b) c
    exact congrArg (fun D : CoordinateSpace →L[ℝ] ℝ => D (EuclideanSpace.single d 1)) hc.fderiv_eq
  funext a b
  change ricci (Γ x) (coordinateConnectionJet Γ x) a b = ricci (Δ x) (coordinateConnectionJet Δ x) a b
  rw [heq.self_of_nhds, hjet]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M]

/-- Components of the actual intrinsic Ricci trace in the genuine preferred tangent frame. -/
def intrinsicRicciMatrix (B : Field (M := M)) (m : M) : Matrix Index Index ℝ :=
  fun a b => IntrinsicRicciTrace.ricci B m
    (tangentFrame m m (EuclideanSpace.single a 1)) (tangentFrame m m (EuclideanSpace.single b 1))

/-- Actual inverse-metric contraction of the intrinsic Ricci tensor. -/
def intrinsicScalar (B : Field (M := M)) (m : M) : ℝ :=
  traceWith (matrixInverse (metricComponents (coordinateBilinear B m) (chartAt CoordinateSpace m m)))
    (intrinsicRicciMatrix B m)

/-- The Einstein tensor is formed from the actual intrinsic Ricci tensor and its actual scalar trace. -/
def intrinsicEinstein (B : Field (M := M)) (m : M) (U V : TangentSpace Model m) : ℝ :=
  IntrinsicRicciTrace.ricci B m U V - (intrinsicScalar B m / 2) * B m U V

def intrinsicEinsteinMatrix (B : Field (M := M)) (m : M) : Matrix Index Index ℝ :=
  fun a b => intrinsicEinstein B m
    (tangentFrame m m (EuclideanSpace.single a 1)) (tangentFrame m m (EuclideanSpace.single b 1))

theorem intrinsicRicciMatrix_eq_coordinate (B : Field (M := M))
    (hB : IsSmooth B) (hSym : IsSymmetric B) (hND : IsNondegenerate B) (m : M) :
    intrinsicRicciMatrix B m = coordinateRicci (computedConnection (coordinateBilinear B m))
      (chartAt CoordinateSpace m m) := by
  funext a b
  exact IntrinsicRicciTrace.ricci_coordinate_basis B hB hSym hND m m
    (mem_chart_source CoordinateSpace m) a b

/-- Connect a locally verified synchronous metric computation to the actual intrinsic Einstein tensor. -/
theorem intrinsicEinstein_source_of_metric_germ (B : Field (M := M))
    (hB : IsSmooth B) (hSym : IsSymmetric B) (hND : IsNondegenerate B)
    (m : M) (γ : ℝ → SpatialMatrix)
    (heq : coordinateBilinear B m =ᶠ[𝓝 (chartAt CoordinateSpace m m)] metric γ)
    (hG : IsUnit (γ ((chartAt CoordinateSpace m m) 0)))
    (ρ d : ℝ) (p : Spatial → ℝ) (hd : 0 < d)
    (hD : d = spatialQuadratic (γ ((chartAt CoordinateSpace m m) 0))⁻¹ p)
    (hR : coordinateRicci (computedConnection (metric γ)) (chartAt CoordinateSpace m m) = sourceTensor ρ d p) :
    intrinsicScalar B m = 0 ∧ intrinsicEinsteinMatrix B m = sourceTensor ρ d p := by
  have hRicci : intrinsicRicciMatrix B m = sourceTensor ρ d p := by
    rw [intrinsicRicciMatrix_eq_coordinate B hB hSym hND]
    rw [coordinateRicci_congr_germ _ _ _ (computedConnection_congr_germ _ _ _ heq)]
    exact hR
  have hComp : metricComponents (coordinateBilinear B m) (chartAt CoordinateSpace m m) =
      block (-1) (γ ((chartAt CoordinateSpace m m) 0)) := by
    change FiberMetric.covariant (coordinateBilinear B m (chartAt CoordinateSpace m m)) coordinateBasis = _
    rw [heq.self_of_nhds]
    exact metric_components γ _
  have hScalar : intrinsicScalar B m = 0 := by
    unfold intrinsicScalar
    rw [hComp, matrixInverse_block _ hG, hRicci]
    exact source_trace_zero _ ρ d p hd hD
  refine ⟨hScalar, ?_⟩
  funext a b
  simp only [intrinsicEinsteinMatrix, intrinsicEinstein, hScalar, zero_div, zero_mul, sub_zero]
  exact congrFun (congrFun hRicci a) b

end Burnett.Bianchi



set_option synthInstance.maxHeartbeats 80000

namespace Burnett.Bianchi

open Matrix Filter Set Bundle Burnett.RicciSymbol
open Burnett.Geometry Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.InverseField
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldBilinear
open scoped BigOperators Topology ContDiff Manifold

def spacetime (I : Set ℝ) (hI : IsOpen I) : TopologicalSpace.Opens CoordinateSpace :=
  ⟨{x | x 0 ∈ I}, hI.preimage (EuclideanSpace.proj 0).continuous⟩

variable (I : Set ℝ) (hI : IsOpen I)

theorem spacetime_chart_apply (c m : spacetime I hI) :
    chartAt CoordinateSpace c m = (m : CoordinateSpace) := rfl

theorem spacetime_chart_source (c : spacetime I hI) :
    (chartAt CoordinateSpace c).source = univ := by
  ext m
  simp [chartAt, TopologicalSpace.Opens.instChartedSpace]

theorem spacetime_chart_target (c : spacetime I hI) :
    (chartAt CoordinateSpace c).target = {x | x 0 ∈ I} := by
  rw [← (chartAt CoordinateSpace c).image_source_eq_target, spacetime_chart_source]
  change (Subtype.val : spacetime I hI → CoordinateSpace) '' univ = _
  exact Subtype.coe_image_univ _

abbrev BilinearModel := CoordinateSpace →L[ℝ] CoordinateSpace →L[ℝ] ℝ

def metricContinuous (γ : ℝ → SpatialMatrix) (y : CoordinateSpace) : BilinearModel :=
  IntrinsicCov2.bilinearContinuous (metric γ y)

theorem spacetime_extChart_apply (c m : spacetime I hI) :
    extChartAt Model c m = (m : CoordinateSpace) := rfl

theorem spacetime_extChart_target (c : spacetime I hI) :
    (extChartAt Model c).target = {x | x 0 ∈ I} := by
  rw [extChartAt_target, spacetime_chart_target]
  simp [Model]

/-- The actual derivative-defined tangent frame on the open coordinate domain. -/
theorem spacetime_symmL (c m : spacetime I hI) :
    (trivializationAt CoordinateSpace (TangentSpace Model) c).symmL ℝ m =
      (1 : CoordinateSpace →L[ℝ] CoordinateSpace) := by
  have hm : m ∈ (chartAt CoordinateSpace c).source := by rw [spacetime_chart_source]; trivial
  rw [TangentBundle.symmL_trivializationAt_eq_core hm, tangentBundleCore_coordChange_achart]
  have hEq : (extChartAt Model m ∘ (extChartAt Model c).symm) =ᶠ[𝓝 (m : CoordinateSpace)] id := by
    filter_upwards [(spacetime I hI).isOpen.mem_nhds m.property] with y hy
    change extChartAt Model m ((extChartAt Model c).symm y) = y
    rw [spacetime_extChart_apply I hI m, ← spacetime_extChart_apply I hI c]
    exact (extChartAt Model c).right_inv (by rwa [spacetime_extChart_target])
  rw [spacetime_extChart_apply, hEq.fderivWithin_eq_of_nhds]
  simp [Model, fderivWithin_univ]
  rfl

theorem spacetime_tangentFrame (c m : spacetime I hI) (v : CoordinateSpace) :
    tangentFrame c m v = v := by
  rw [tangentFrame, spacetime_symmL]
  rfl

theorem spacetime_chartChange_fderiv (c d m : spacetime I hI) :
    fderiv ℝ ((chartAt CoordinateSpace d) ∘ (chartAt CoordinateSpace c).symm)
      (m : CoordinateSpace) = ContinuousLinearMap.id ℝ CoordinateSpace := by
  have heq : ((chartAt CoordinateSpace d) ∘ (chartAt CoordinateSpace c).symm)
      =ᶠ[𝓝 (m : CoordinateSpace)] id := by
    filter_upwards [(spacetime I hI).isOpen.mem_nhds m.property] with y hy
    change chartAt CoordinateSpace d ((chartAt CoordinateSpace c).symm y) = y
    rw [spacetime_chart_apply I hI d, ← spacetime_chart_apply I hI c]
    exact (chartAt CoordinateSpace c).right_inv (by rwa [spacetime_chart_target])
  rw [heq.fderiv_eq, fderiv_id]

def openMetric (_c : spacetime I hI) (γ : ℝ → SpatialMatrix) :
    Field (M := spacetime I hI) := fun m => metricContinuous γ (m : CoordinateSpace)

end Burnett.Bianchi


namespace Burnett.Bianchi

open Matrix Filter Set Bundle Burnett.RicciSymbol
open Burnett.Geometry Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.InverseField
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldBilinear
open scoped BigOperators Topology ContDiff Manifold

def bilinearAtom (a b : Index) : BilinearModel :=
  (EuclideanSpace.proj a : CoordinateSpace →L[ℝ] ℝ).smulRight
    (EuclideanSpace.proj b : CoordinateSpace →L[ℝ] ℝ)

theorem metricContinuous_sum (γ : ℝ → SpatialMatrix) (y : CoordinateSpace) :
    metricContinuous γ y = (-1 : ℝ) • bilinearAtom 0 0 +
      ∑ i : Spatial, ∑ j : Spatial, γ (y 0) i j • bilinearAtom i.succ j.succ := by
  ext u v
  simp [metricContinuous, IntrinsicCov2.bilinearContinuous, metric, Matrix.toBilin_apply,
    coordinateBasis, EuclideanSpace.basisFun_repr, block, Fin.sum_univ_succ, bilinearAtom]
  ring

theorem metricContinuous_contDiffAt (I : Set ℝ) (hI : IsOpen I)
    (γ : ℝ → SpatialMatrix) (hγ : ∀ i j, ContDiffOn ℝ ∞ (fun t => γ t i j) I)
    (y : CoordinateSpace) (hy : y 0 ∈ I) : ContDiffAt ℝ ∞ (metricContinuous γ) y := by
  have hp : ContDiffAt ℝ ∞ (fun x : CoordinateSpace => x 0) y :=
    (EuclideanSpace.proj 0 : CoordinateSpace →L[ℝ] ℝ).contDiff.contDiffAt
  have hs : ContDiffAt ℝ ∞ (fun x : CoordinateSpace => (-1 : ℝ) • bilinearAtom 0 0 +
      ∑ i : Spatial, ∑ j : Spatial, γ (x 0) i j • bilinearAtom i.succ j.succ) y := by
    apply contDiffAt_const.add
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    exact (((hγ i j).contDiffAt (hI.mem_nhds hy)).comp y hp).smul
      (contDiffAt_const (c := bilinearAtom i.succ j.succ))
  exact hs.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => metricContinuous_sum γ x)

theorem openMetric_isSmooth (I : Set ℝ) (hI : IsOpen I) (c : spacetime I hI)
    (γ : ℝ → SpatialMatrix) (hγ : ∀ i j, ContDiffOn ℝ ∞ (fun t => γ t i j) I) :
    IsSmooth (openMetric I hI c γ) := by
  have hc : ContMDiff Model 𝓘(ℝ, BilinearModel) ∞
      (fun m : spacetime I hI => metricContinuous γ (m : CoordinateSpace)) := by
    intro m
    apply contMDiffAt_subtype_iff.mpr
    exact (metricContinuous_contDiffAt I hI γ hγ m m.property).contMDiffAt
  intro x
  rw [contMDiffAt_section]
  convert hc x using 1
  ext u v
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    Trivialization.linearMapAt_apply, TangentSpace, spacetime_chart_source, openMetric]
  rw [spacetime_chart_apply, spacetime_chartChange_fderiv]
  rfl

end Burnett.Bianchi


namespace Burnett.Bianchi

open Matrix Filter Set Bundle Burnett.RicciSymbol
open Burnett.Geometry Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.InverseField
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldBilinear
open scoped BigOperators Topology ContDiff Manifold

theorem openMetric_frameBilinear (I : Set ℝ) (hI : IsOpen I) (c m : spacetime I hI)
    (γ : ℝ → SpatialMatrix) :
    frameBilinear (openMetric I hI c γ) c m = metric γ (m : CoordinateSpace) := by
  ext u v
  change openMetric I hI c γ m (tangentFrame c m u) (tangentFrame c m v) = _
  rw [spacetime_tangentFrame, spacetime_tangentFrame]
  rfl

theorem openMetric_coordinateBilinear (I : Set ℝ) (hI : IsOpen I)
    (c : spacetime I hI) (γ : ℝ → SpatialMatrix) (y : CoordinateSpace) (hy : y 0 ∈ I) :
    coordinateBilinear (openMetric I hI c γ) c y = metric γ y := by
  change frameBilinear (openMetric I hI c γ) c ((chartAt CoordinateSpace c).symm y) = _
  rw [openMetric_frameBilinear]
  have h := (chartAt CoordinateSpace c).right_inv
    (show y ∈ (chartAt CoordinateSpace c).target by rw [spacetime_chart_target]; exact hy)
  rw [spacetime_chart_apply] at h
  rw [h]

theorem openMetric_coordinate_germ (I : Set ℝ) (hI : IsOpen I)
    (c m : spacetime I hI) (γ : ℝ → SpatialMatrix) :
    coordinateBilinear (openMetric I hI c γ) c =ᶠ[𝓝 (m : CoordinateSpace)] metric γ := by
  filter_upwards [(spacetime I hI).isOpen.mem_nhds m.property] with y hy
  exact openMetric_coordinateBilinear I hI c γ y hy

end Burnett.Bianchi


namespace Burnett.Bianchi

open Matrix Filter Set Bundle Burnett.RicciSymbol
open Burnett.Geometry Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.InverseField
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldBilinear
open scoped BigOperators Topology ContDiff Manifold Matrix.Norms.Elementwise

theorem modelMinkowski_symmetric (u v : CoordinateSpace) : modelMinkowski u v = modelMinkowski v u := by
  simp only [modelMinkowski_apply]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem modelMinkowski_nondegenerate : modelMinkowski.Nondegenerate := by
  intro u hu
  have ht := hu (EuclideanSpace.single 0 1)
  have hs (i : Spatial) := hu (EuclideanSpace.single i.succ 1)
  have ht0 : u 0 = 0 := by simpa [modelMinkowski_apply, EuclideanSpace.single_apply] using ht
  have hs0 (i : Spatial) : u i.succ = 0 := by
    simpa [modelMinkowski_apply, EuclideanSpace.single_apply, Ne.symm (Fin.succ_ne_zero i)] using hs i
  ext a
  refine Fin.cases ?_ (fun i => ?_) a
  · exact ht0
  · exact hs0 i

theorem metric_symmetric (γ : ℝ → SpatialMatrix) (x : CoordinateSpace)
    (hG : (γ (x 0)).PosDef) : (metric γ x).IsSymm := by
  obtain ⟨e, he⟩ := metric_hasLorentzSignature γ x hG
  exact ⟨fun u v => (he u v).trans ((modelMinkowski_symmetric _ _).trans (he v u).symm)⟩

theorem metric_nondegenerate (γ : ℝ → SpatialMatrix) (x : CoordinateSpace)
    (hG : (γ (x 0)).PosDef) : (metric γ x).Nondegenerate := by
  obtain ⟨e, he⟩ := metric_hasLorentzSignature γ x hG
  intro u hu
  have hz : e u = 0 := modelMinkowski_nondegenerate _ (fun v => by
    obtain ⟨w, rfl⟩ := e.surjective v
    rw [← he]
    exact hu w)
  exact e.injective (by simpa using hz)

theorem openMetric_isSymmetric (I : Set ℝ) (hI : IsOpen I) (c : spacetime I hI)
    (γ : ℝ → SpatialMatrix) (hG : ∀ t ∈ I, (γ t).PosDef) :
    IsSymmetric (openMetric I hI c γ) := by
  intro m u v
  have hm : m ∈ (chartAt CoordinateSpace c).source := by rw [spacetime_chart_source]; trivial
  obtain ⟨a, rfl⟩ := tangentFrame_surjective c m hm u
  obtain ⟨b, rfl⟩ := tangentFrame_surjective c m hm v
  change frameBilinear (openMetric I hI c γ) c m a b = frameBilinear (openMetric I hI c γ) c m b a
  rw [openMetric_frameBilinear]
  exact (metric_symmetric γ m (hG _ m.property)).eq a b

theorem openMetric_isNondegenerate (I : Set ℝ) (hI : IsOpen I) (c : spacetime I hI)
    (γ : ℝ → SpatialMatrix) (hG : ∀ t ∈ I, (γ t).PosDef) :
    IsNondegenerate (openMetric I hI c γ) := by
  intro m u hu
  have hm : m ∈ (chartAt CoordinateSpace c).source := by rw [spacetime_chart_source]; trivial
  obtain ⟨a, rfl⟩ := tangentFrame_surjective c m hm u
  have ha : a = 0 := (metric_nondegenerate γ m (hG _ m.property)) a (fun b => by
    have hh := hu (tangentFrame c m b)
    change frameBilinear (openMetric I hI c γ) c m a b = 0 at hh
    rw [openMetric_frameBilinear] at hh
    exact hh)
  rw [ha, map_zero]

end Burnett.Bianchi


namespace Burnett.Bianchi

open Matrix Filter Set Bundle Burnett.RicciSymbol
open Burnett.Geometry Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.InverseField
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldBilinear
open scoped BigOperators Topology ContDiff Manifold Matrix.Norms.Elementwise

def FieldHasLorentzSignature {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
    [IsManifold Model ∞ M] (B : Field (M := M)) (m : M) : Prop :=
  ∃ e : TangentSpace Model m ≃L[ℝ] CoordinateSpace, ∀ u v,
    B m u v = modelMinkowski (e u) (e v)

theorem openMetric_hasLorentzSignature (I : Set ℝ) (hI : IsOpen I)
    (c m : spacetime I hI) (γ : ℝ → SpatialMatrix) (hG : (γ ((m : CoordinateSpace) 0)).PosDef) :
    FieldHasLorentzSignature (openMetric I hI c γ) m := by
  have hm : m ∈ (chartAt CoordinateSpace c).source := by rw [spacetime_chart_source]; trivial
  let eT : TangentSpace Model m ≃L[ℝ] CoordinateSpace :=
    (trivializationAt CoordinateSpace (TangentSpace Model) c).continuousLinearEquivAt ℝ m hm
  obtain ⟨e, he⟩ := metric_hasLorentzSignature γ m hG
  refine ⟨eT.trans e, ?_⟩
  intro u v
  obtain ⟨a, rfl⟩ := eT.symm.surjective u
  obtain ⟨b, rfl⟩ := eT.symm.surjective v
  simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply]
  change frameBilinear (openMetric I hI c γ) c m a b = _
  rw [openMetric_frameBilinear]
  exact he a b

end Burnett.Bianchi


namespace Burnett.Bianchi

open Matrix Filter Set Bundle Burnett.RicciSymbol
open Burnett.Geometry Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.InverseField
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldBilinear
open scoped BigOperators Topology ContDiff Manifold

theorem openMetric_coordinate_germ_at (I : Set ℝ) (hI : IsOpen I)
    (c m : spacetime I hI) (γ : ℝ → SpatialMatrix) :
    coordinateBilinear (openMetric I hI c γ) m =ᶠ[𝓝 (chartAt CoordinateSpace m m)] metric γ := by
  exact openMetric_coordinate_germ I hI m m γ

/-- The exact actual metric on the open product has the computed intrinsic Einstein tensor. -/
theorem intrinsicEinstein_openMetric_source (I : Set ℝ) (hI : IsOpen I)
    (c : spacetime I hI) (γ : ℝ → SpatialMatrix)
    (hγ : ∀ i j, ContDiffOn ℝ ∞ (fun t => γ t i j) I)
    (hG : ∀ t ∈ I, (γ t).PosDef) (m : spacetime I hI)
    (ρ d : ℝ) (p : Spatial → ℝ) (hd : 0 < d)
    (hD : d = spatialQuadratic (γ ((m : CoordinateSpace) 0))⁻¹ p)
    (hR : coordinateRicci (computedConnection (metric γ)) (m : CoordinateSpace) = sourceTensor ρ d p) :
    intrinsicScalar (openMetric I hI c γ) m = 0 ∧
      intrinsicEinsteinMatrix (openMetric I hI c γ) m = sourceTensor ρ d p := by
  exact intrinsicEinstein_source_of_metric_germ (openMetric I hI c γ)
    (openMetric_isSmooth I hI c γ hγ) (openMetric_isSymmetric I hI c γ hG)
    (openMetric_isNondegenerate I hI c γ hG) m γ
    (openMetric_coordinate_germ_at I hI c m γ)
    (hG _ m.property).isUnit ρ d p hd hD hR

end Burnett.Bianchi
