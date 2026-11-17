import Burnett.Geometry.GlobalLeviCivita
import Mathlib.Topology.Algebra.Module.Multilinear.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# IntrinsicCov2

Paper-specific intrinsic derivative and physical norm support.
See docs/statements/intrinsic-dh-geometry.md for scope and remaining obligations.
-/

set_option autoImplicit false

noncomputable section
namespace Burnett.Geometry.IntrinsicCov2
open Bundle Set Filter
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ChartVectorField Burnett.Geometry.ChartDifferential
open Burnett.Geometry.ChartConnectionNaturality

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

def dualDerivative (B H : ManifoldBilinear.Field (M := M))
    (V U W : Field (M := M)) (m : M) : ℝ :=
  let s : ℝ := mfderiv Model 𝓘(ℝ, ℝ) (fun n => H n (U n) (W n)) m (V m)
  s -
    H m (GlobalCovariantDerivative.derivative B V U m) (W m) -
    H m (U m) (GlobalCovariantDerivative.derivative B V W m)

theorem dualDerivative_eq_coordinate
    (B H : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (hH : ManifoldBilinear.IsSmooth H)
    (V U W : Field (M := M)) (hU : IsSmooth U) (hW : IsSmooth W)
    (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source) :
    dualDerivative B H V U W m =
      AffineConnection.cov2Differential (BackgroundConnection.computedConnection (coordinateBilinear B c))
        (metricComponents (coordinateBilinear H c)) (chartAt CoordinateSpace c m)
        (coordinateVector V c (chartAt CoordinateSpace c m))
        (coordinateVector U c (chartAt CoordinateSpace c m))
        (coordinateVector W c (chartAt CoordinateSpace c m)) := by
  let x := chartAt CoordinateSpace c m
  have hx : x ∈ (chartAt CoordinateSpace c).target := (chartAt CoordinateSpace c).mapsTo hm
  have hf : MDifferentiableAt Model 𝓘(ℝ, ℝ) (fun n => H n (U n) (W n)) m :=
    ((GlobalLeviCivita.contMDiff_pairing H hH U W hU hW) m).mdifferentiableAt (by
      change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have heq : ((fun n => H n (U n) (W n)) ∘ (chartAt CoordinateSpace c).symm) =ᶠ[𝓝 x]
      (fun y => coordinateBilinear H c y (coordinateVector U c y) (coordinateVector W c y)) := by
    filter_upwards [(chartAt CoordinateSpace c).open_target.mem_nhds hx] with y hy
    exact GlobalLeviCivita.pairing_comp_chart_symm H U W c hy
  have hHc : DifferentiableComponentsAt (metricComponents (coordinateBilinear H c)) x := by
    intro i j
    apply ((ManifoldBilinear.contDiffOn_metricComponents H hH c i j).contDiffAt
      ((chartAt CoordinateSpace c).open_target.mem_nhds hx)).differentiableAt
    change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top
  have hlocal := AffineConnection.inducedCov2_eq_cov2Differential
    (BackgroundConnection.computedConnection (coordinateBilinear B c))
    (metricComponents (coordinateBilinear H c)) (coordinateVector V c)
    (coordinateVector U c) (coordinateVector W c) x hHc
    (differentiableAt_coordinateVector U hU c hx) (differentiableAt_coordinateVector W hW c hx)
  unfold dualDerivative
  rw [scalar_mfderiv_eq_chart _ V c m hm hf, ← coordinateVector_at_chart V c m hm]
  rw [heq.fderiv_eq]
  rw [GlobalLeviCivita.pairing_eq_coordinate H (GlobalCovariantDerivative.derivative B V U) W c m hm,
    GlobalLeviCivita.pairing_eq_coordinate H U (GlobalCovariantDerivative.derivative B V W) c m hm,
    GlobalCovariantDerivative.coordinateVector_derivative B hB hSym hND V U hU c hx,
    GlobalCovariantDerivative.coordinateVector_derivative B hB hSym hND V W hW c hx]
  simpa only [CoordinateCovariantDerivative.inducedCov2, AffineConnection.tensorForm_metricComponents]
    using hlocal

def bilinearContinuous : LinearMap.BilinForm ℝ CoordinateSpace →ₗ[ℝ]
    (CoordinateSpace →L[ℝ] CoordinateSpace →L[ℝ] ℝ) where
  toFun L := LinearMap.toContinuousLinearMap
    { toFun := fun u => LinearMap.toContinuousLinearMap (L u)
      map_add' := fun u v => by rw [map_add, map_add]
      map_smul' := fun a u => by rw [map_smul, map_smul]; rfl }
  map_add' L K := by ext u v; rfl
  map_smul' a L := by ext u v; rfl

def trilinearContinuous (L : CoordinateSpace →ₗ[ℝ] LinearMap.BilinForm ℝ CoordinateSpace) :
    CoordinateSpace →L[ℝ] CoordinateSpace →L[ℝ] CoordinateSpace →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (bilinearContinuous.comp L)

@[simp] theorem trilinearContinuous_apply
    (L : CoordinateSpace →ₗ[ℝ] LinearMap.BilinForm ℝ CoordinateSpace)
    (v u w : CoordinateSpace) : trilinearContinuous L v u w = L v u w := rfl

def coordinateTrilinear (L : CoordinateSpace →ₗ[ℝ] LinearMap.BilinForm ℝ CoordinateSpace) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => CoordinateSpace) ℝ where
  toMultilinearMap := MultilinearMap.mk' (fun p => L (p 0) (p 1) (p 2))
    (by intro p i u v; fin_cases i <;> simp [Function.update, map_add])
    (by intro p i a u; fin_cases i <;> simp [Function.update, map_smul])
  cont := by
    change Continuous (fun p : Fin 3 → CoordinateSpace =>
      trilinearContinuous L (p 0) (p 1) (p 2))
    exact (((trilinearContinuous L).continuous.comp (continuous_apply 0)).clm_apply
      (continuous_apply 1)).clm_apply (continuous_apply 2)

@[simp] theorem coordinateTrilinear_apply
    (L : CoordinateSpace →ₗ[ℝ] LinearMap.BilinForm ℝ CoordinateSpace)
    (p : Fin 3 → CoordinateSpace) : coordinateTrilinear L p = L (p 0) (p 1) (p 2) := rfl

def tensorInChart (B H : ManifoldBilinear.Field (M := M)) (c m : M) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace Model m) ℝ :=
  (coordinateTrilinear (AffineConnection.cov2Differential
    (BackgroundConnection.computedConnection (coordinateBilinear B c))
    (metricComponents (coordinateBilinear H c)) (chartAt CoordinateSpace c m))).compContinuousLinearMap
      (fun _ => mfderiv Model Model (chartAt CoordinateSpace c) m)

def tensor (B H : ManifoldBilinear.Field (M := M)) (m : M) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace Model m) ℝ :=
  tensorInChart B H m m

theorem tensorInChart_apply_fields (B H : ManifoldBilinear.Field (M := M))
    (V U W : Field (M := M)) (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source) :
    tensorInChart B H c m ![V m, U m, W m] =
      AffineConnection.cov2Differential (BackgroundConnection.computedConnection (coordinateBilinear B c))
        (metricComponents (coordinateBilinear H c)) (chartAt CoordinateSpace c m)
        (coordinateVector V c (chartAt CoordinateSpace c m))
        (coordinateVector U c (chartAt CoordinateSpace c m))
        (coordinateVector W c (chartAt CoordinateSpace c m)) := by
  simp only [tensorInChart, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    coordinateTrilinear_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [coordinateVector_at_chart V c m hm, coordinateVector_at_chart U c m hm,
    coordinateVector_at_chart W c m hm,
    ChartDifferential.frameVector_eq_mfderiv_chart V c m hm,
    ChartDifferential.frameVector_eq_mfderiv_chart U c m hm,
    ChartDifferential.frameVector_eq_mfderiv_chart W c m hm]
  rfl

theorem tensor_apply_eq_dualDerivative (B H : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (hH : ManifoldBilinear.IsSmooth H)
    (V U W : Field (M := M)) (hU : IsSmooth U) (hW : IsSmooth W) (m : M) :
    tensor B H m ![V m, U m, W m] = dualDerivative B H V U W m := by
  rw [tensor, tensorInChart_apply_fields B H V U W m m (mem_chart_source _ m)]
  exact (dualDerivative_eq_coordinate B H hB hSym hND hH V U W hU hW m m
    (mem_chart_source _ m)).symm

theorem tensorInChart_eq_tensor_on_fields (B H : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (hH : ManifoldBilinear.IsSmooth H)
    (V U W : Field (M := M)) (hU : IsSmooth U) (hW : IsSmooth W)
    (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source) :
    tensorInChart B H c m ![V m, U m, W m] = tensor B H m ![V m, U m, W m] := by
  rw [tensorInChart_apply_fields B H V U W c m hm,
    tensor_apply_eq_dualDerivative B H hB hSym hND hH V U W hU hW m]
  exact (dualDerivative_eq_coordinate B H hB hSym hND hH V U W hU hW c m hm).symm

theorem isSmooth_difference (H₁ H₀ : ManifoldBilinear.Field (M := M))
    (h₁ : ManifoldBilinear.IsSmooth H₁) (h₀ : ManifoldBilinear.IsSmooth H₀) :
    ManifoldBilinear.IsSmooth (fun m => H₁ m - H₀ m) :=
  h₁.sub_section h₀

theorem mfderiv_chart_tangentFrame (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source)
    (v : CoordinateSpace) :
    mfderiv Model Model (chartAt CoordinateSpace c) m (tangentFrame c m v) = v := by
  apply tangentFrame_injective c m hm
  let V : Field (M := M) := fun n => tangentFrame c n v
  have h := tangentFrame_frameVector V c m hm
  rw [ChartDifferential.frameVector_eq_mfderiv_chart V c m hm] at h
  exact h

theorem auxiliary_tensor_basis (r : Metric (M := M))
    (g₁ g₀ : ManifoldBilinear.Field (M := M)) (m : M) (b c d : Index) :
    tensor r.inner (fun n => g₁ n - g₀ n) m
      ![tangentFrame m m (EuclideanSpace.single b 1),
        tangentFrame m m (EuclideanSpace.single c 1),
        tangentFrame m m (EuclideanSpace.single d 1)] =
      AuxiliaryConnection.auxiliaryPerturbationJet (coordinateMetric r m)
        (coordinateBilinear g₀ m) (coordinateBilinear g₁ m)
        (chartAt CoordinateSpace m m) b c d := by
  simp only [tensor, tensorInChart, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    coordinateTrilinear_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  change AffineConnection.cov2Differential _ _ _
      (mfderiv Model Model (chartAt CoordinateSpace m) m (tangentFrame m m (EuclideanSpace.single b 1)))
      (mfderiv Model Model (chartAt CoordinateSpace m) m (tangentFrame m m (EuclideanSpace.single c 1)))
      (mfderiv Model Model (chartAt CoordinateSpace m) m (tangentFrame m m (EuclideanSpace.single d 1))) = _
  rw [mfderiv_chart_tangentFrame m m (mem_chart_source _ m),
    mfderiv_chart_tangentFrame m m (mem_chart_source _ m),
    mfderiv_chart_tangentFrame m m (mem_chart_source _ m)]
  exact AffineConnection.cov2Differential_auxiliaryPerturbationJet (coordinateMetric r m)
    (coordinateBilinear g₀ m) (coordinateBilinear g₁ m) _ b c d

theorem auxiliary_tensor_apply_eq_dualDerivative (r : Metric (M := M))
    (g₁ g₀ : ManifoldBilinear.Field (M := M))
    (h₁ : ManifoldBilinear.IsSmooth g₁) (h₀ : ManifoldBilinear.IsSmooth g₀)
    (V U W : Field (M := M)) (hU : IsSmooth U) (hW : IsSmooth W) (m : M) :
    tensor r.inner (fun n => g₁ n - g₀ n) m ![V m, U m, W m] =
      dualDerivative r.inner (fun n => g₁ n - g₀ n) V U W m :=
  tensor_apply_eq_dualDerivative r.inner _ (ManifoldBilinear.isSmooth_inner r) r.symm
    (GlobalLeviCivita.inner_nondegenerate r) (isSmooth_difference g₁ g₀ h₁ h₀)
    V U W hU hW m

end Burnett.Geometry.IntrinsicCov2

noncomputable section
namespace Burnett.Geometry.CovariantJetNaturality
open Matrix
open scoped BigOperators Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ConnectionCoordinateChange Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition

def jetMatrix (J : FirstJet) (b : Index) : Matrix Index Index ℝ := J b

def covariantMatrix (Γ : Connection) (C : Matrix Index Index ℝ) (J : FirstJet) (b : Index) :
    Matrix Index Index ℝ :=
  jetMatrix J b - (connectionMatrix Γ b)ᵀ * C - C * connectionMatrix Γ b

theorem covariantMatrix_apply (Γ : Connection) (C : Matrix Index Index ℝ)
    (J : FirstJet) (b c d : Index) :
    covariantMatrix Γ C J b c d = covariantJet Γ C J b c d := by
  simp only [covariantMatrix, jetMatrix, covariantJet, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.transpose_apply, connectionMatrix]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem transformed_covariant_matrix (A C J K H : Matrix Index Index ℝ) (hA : IsUnit A) :
    transformedMetricDerivative A C J H -
      (transformedConnectionMatrix A K H)ᵀ * (Aᵀ * C * A) -
      (Aᵀ * C * A) * transformedConnectionMatrix A K H =
        Aᵀ * (J - Kᵀ * C - C * K) * A := by
  have ha : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hr : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ha
  have ht : (A⁻¹)ᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, hr]; simp
  have hleft : (transformedConnectionMatrix A K H)ᵀ * (Aᵀ * C * A) =
      (K * A + H)ᵀ * C * A := by
    unfold transformedConnectionMatrix
    calc
      _ = ((K * A + H)ᵀ * ((A⁻¹)ᵀ * Aᵀ)) * C * A := by
        simp only [Matrix.transpose_mul]
        noncomm_ring
      _ = _ := by rw [ht]; simp
  have hright : (Aᵀ * C * A) * transformedConnectionMatrix A K H =
      Aᵀ * C * (K * A + H) := by
    unfold transformedConnectionMatrix
    calc
      _ = (Aᵀ * C) * (A * A⁻¹) * (K * A + H) := by noncomm_ring
      _ = _ := by rw [hr]; simp
  rw [hleft, hright]
  unfold transformedMetricDerivative
  simp only [Matrix.transpose_add, Matrix.transpose_mul]
  noncomm_ring

theorem directional_covariant_matrix (A C : Matrix Index Index ℝ)
    (J : FirstJet) (Γ : Connection) (b : Index) :
    (∑ p, A p b • jetMatrix J p) -
      (directionalConnection A Γ b)ᵀ * C - C * directionalConnection A Γ b =
        ∑ p, A p b • covariantMatrix Γ C J p := by
  simp only [directionalConnection, covariantMatrix, Matrix.transpose_sum, Matrix.transpose_smul,
    Matrix.sum_mul, Matrix.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
    Finset.sum_sub_distrib]

theorem pullback_directional_covariant (A C : Matrix Index Index ℝ)
    (J : FirstJet) (Γ : Connection) (b c d : Index) :
    (Aᵀ * (∑ p, A p b • covariantMatrix Γ C J p) * A) c d =
      TensorCoordinateChange.pullback3 A (covariantJet Γ C J) b c d := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, mul_smul_comm, smul_mul_assoc,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    MetricJetNaturality.matrix_triple_entry, TensorCoordinateChange.pullback3_apply,
    covariantMatrix_apply]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem covariantJet_transformed (A C : Matrix Index Index ℝ) (J : FirstJet)
    (Γ H : Connection) (hA : IsUnit A) :
    covariantJet (transformedConnection A Γ H) (Aᵀ * C * A) (transformedJet A C J H) =
      TensorCoordinateChange.pullback3 A (covariantJet Γ C J) := by
  funext b c d
  rw [← covariantMatrix_apply]
  change (transformedMetricDerivative A C (∑ p, A p b • jetMatrix J p)
      (connectionMatrix H b) -
      (transformedConnectionMatrix A (directionalConnection A Γ b) (connectionMatrix H b))ᵀ *
        (Aᵀ * C * A) -
      (Aᵀ * C * A) *
        transformedConnectionMatrix A (directionalConnection A Γ b) (connectionMatrix H b)) c d = _
  rw [transformed_covariant_matrix A C _ _ _ hA, directional_covariant_matrix]
  exact pullback_directional_covariant A C J Γ b c d

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem coordinate_covariantJet_change (B T : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (hT : ManifoldBilinear.IsSmooth T)
    (c d : M) (x : CoordinateSpace) (hx : x ∈ (chartTransition c d).source) :
    covariantJet (BackgroundConnection.computedConnection (coordinateBilinear B c) x)
      (metricComponents (coordinateBilinear T c) x)
      (coordinateJet (metricComponents (coordinateBilinear T c)) x) =
      TensorCoordinateChange.pullback3 (derivativeMatrix (fderiv ℝ (chartTransition c d) x))
        (covariantJet (BackgroundConnection.computedConnection (coordinateBilinear B d) (chartTransition c d x))
          (metricComponents (coordinateBilinear T d) (chartTransition c d x))
          (coordinateJet (metricComponents (coordinateBilinear T d)) (chartTransition c d x))) := by
  have hΓ := ConnectionTermNaturality.coordinateBilinear_connection_change B hB hSym hND c d x hx
  have hC := coordinateBilinear_matrix_change T c d hx
  have hJ := MetricJetNaturality.coordinateBilinear_jet_change T hT c d x hx
  rw [hΓ, hJ, hC]
  exact covariantJet_transformed _ _ _ _ _ (ConnectionTermNaturality.chartJacobian_isUnit c d x hx)

end Burnett.Geometry.CovariantJetNaturality

namespace Burnett.Geometry.IntrinsicCov2
open Matrix
open Bundle Set Filter
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ChartVectorField Burnett.Geometry.ChartDifferential
open Burnett.Geometry.ChartConnectionNaturality
open Burnett.Geometry.ChartVolume
open scoped BigOperators

theorem trilinear_basis_expansion
    (L : CoordinateSpace →ₗ[ℝ] LinearMap.BilinForm ℝ CoordinateSpace)
    (F : CoordinateSpace →L[ℝ] CoordinateSpace) (b c d : Index) :
    L (F (coordinateBasis b)) (F (coordinateBasis c)) (F (coordinateBasis d)) =
      ∑ p, ∑ q, ∑ e, derivativeMatrix F p b * derivativeMatrix F q c *
        derivativeMatrix F e d * L (coordinateBasis p) (coordinateBasis q) (coordinateBasis e) := by
  have hF (i : Index) : F (coordinateBasis i) =
      ∑ p, derivativeMatrix F p i • coordinateBasis p := by
    simpa only [MetricJetNaturality.derivativeMatrix_apply, coordinateBasis,
      OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr] using
        (coordinateBasis.sum_repr (F (coordinateBasis i))).symm
  rw [hF b, hF c, hF d]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext q
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem cov2Differential_coordinateBasis (Γ : CoordinateSpace → Connection)
    (H : CoordinateSpace → Tensor2) (x : CoordinateSpace) (b c d : Index) :
    AffineConnection.cov2Differential Γ H x (coordinateBasis b) (coordinateBasis c) (coordinateBasis d) =
      covariantJet (Γ x) (H x) (coordinateJet H x) b c d := by
  simpa only [coordinateBasis, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using
    AffineConnection.cov2Differential_basis Γ H x b c d

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem coordinate_cov2Differential_change (B H : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (hH : ManifoldBilinear.IsSmooth H)
    (c d : M) (x : CoordinateSpace) (hx : x ∈ (chartTransition c d).source) :
    coordinateTrilinear (AffineConnection.cov2Differential
      (BackgroundConnection.computedConnection (coordinateBilinear B c))
      (metricComponents (coordinateBilinear H c)) x) =
    (coordinateTrilinear (AffineConnection.cov2Differential
      (BackgroundConnection.computedConnection (coordinateBilinear B d))
      (metricComponents (coordinateBilinear H d)) (chartTransition c d x))).compContinuousLinearMap
        (fun _ => fderiv ℝ (chartTransition c d) x) := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ => coordinateBasis)
  intro v
  change AffineConnection.cov2Differential _ _ x (coordinateBasis (v 0))
      (coordinateBasis (v 1)) (coordinateBasis (v 2)) =
    AffineConnection.cov2Differential _ _ (chartTransition c d x)
      (fderiv ℝ (chartTransition c d) x (coordinateBasis (v 0)))
      (fderiv ℝ (chartTransition c d) x (coordinateBasis (v 1)))
      (fderiv ℝ (chartTransition c d) x (coordinateBasis (v 2)))
  rw [cov2Differential_coordinateBasis, trilinear_basis_expansion]
  simp only [cov2Differential_coordinateBasis]
  have h := congrFun (congrFun (congrFun
    (CovariantJetNaturality.coordinate_covariantJet_change B H hB hSym hND hH c d x hx)
      (v 0)) (v 1)) (v 2)
  simpa only [TensorCoordinateChange.pullback3_apply] using h

theorem mfderiv_chart_change (c d m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source)
    (hd : m ∈ (chartAt CoordinateSpace d).source) (v : TangentSpace Model m) :
    mfderiv Model Model (chartAt CoordinateSpace d) m v =
      fderiv ℝ (chartTransition c d) (chartAt CoordinateSpace c m)
        (mfderiv Model Model (chartAt CoordinateSpace c) m v) := by
  classical
  let V : Field (M := M) := Function.update (fun _ => 0) m v
  have h := frameVector_change V c d m hc hd
  rw [ChartDifferential.frameVector_eq_mfderiv_chart V d m hd,
    ChartDifferential.frameVector_eq_mfderiv_chart V c m hc] at h
  simpa only [V, Function.update_self] using h

theorem tensorInChart_eq (B H : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (hH : ManifoldBilinear.IsSmooth H)
    (c d m : M) (hc : m ∈ (chartAt CoordinateSpace c).source)
    (hd : m ∈ (chartAt CoordinateSpace d).source) :
    tensorInChart B H c m = tensorInChart B H d m := by
  have hx : chartAt CoordinateSpace c m ∈ (chartTransition c d).source := by
    constructor
    · exact (chartAt CoordinateSpace c).mapsTo hc
    · change (chartAt CoordinateSpace c).symm (chartAt CoordinateSpace c m) ∈
        (chartAt CoordinateSpace d).source
      rw [(chartAt CoordinateSpace c).left_inv hc]
      exact hd
  have hφ : chartTransition c d (chartAt CoordinateSpace c m) = chartAt CoordinateSpace d m := by
    change chartAt CoordinateSpace d ((chartAt CoordinateSpace c).symm (chartAt CoordinateSpace c m)) = _
    rw [(chartAt CoordinateSpace c).left_inv hc]
  have hT := coordinate_cov2Differential_change B H hB hSym hND hH c d
    (chartAt CoordinateSpace c m) hx
  rw [hφ] at hT
  unfold tensorInChart
  rw [hT]
  ext p
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  exact (mfderiv_chart_change c d m hc hd (p i)).symm

theorem tensor_eq_tensorInChart (B H : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (hH : ManifoldBilinear.IsSmooth H)
    (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source) :
    tensor B H m = tensorInChart B H c m :=
  tensorInChart_eq B H hB hSym hND hH m c m (mem_chart_source _ m) hm

theorem auxiliary_tensor_basis_inChart (r : Metric (M := M))
    (g₁ g₀ : ManifoldBilinear.Field (M := M))
    (h₁ : ManifoldBilinear.IsSmooth g₁) (h₀ : ManifoldBilinear.IsSmooth g₀)
    (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source) (b e f : Index) :
    tensor r.inner (fun n => g₁ n - g₀ n) m
      ![tangentFrame c m (EuclideanSpace.single b 1),
        tangentFrame c m (EuclideanSpace.single e 1),
        tangentFrame c m (EuclideanSpace.single f 1)] =
      AuxiliaryConnection.auxiliaryPerturbationJet (coordinateMetric r c)
        (coordinateBilinear g₀ c) (coordinateBilinear g₁ c)
        (chartAt CoordinateSpace c m) b e f := by
  rw [tensor_eq_tensorInChart r.inner (fun n => g₁ n - g₀ n)
    (ManifoldBilinear.isSmooth_inner r) r.symm (GlobalLeviCivita.inner_nondegenerate r)
    (isSmooth_difference g₁ g₀ h₁ h₀) c m hm]
  simp only [tensorInChart, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    coordinateTrilinear_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  change AffineConnection.cov2Differential _ _ _
      (mfderiv Model Model (chartAt CoordinateSpace c) m (tangentFrame c m (EuclideanSpace.single b 1)))
      (mfderiv Model Model (chartAt CoordinateSpace c) m (tangentFrame c m (EuclideanSpace.single e 1)))
      (mfderiv Model Model (chartAt CoordinateSpace c) m (tangentFrame c m (EuclideanSpace.single f 1))) = _
  rw [mfderiv_chart_tangentFrame c m hm, mfderiv_chart_tangentFrame c m hm,
    mfderiv_chart_tangentFrame c m hm]
  exact AffineConnection.cov2Differential_auxiliaryPerturbationJet (coordinateMetric r c)
    (coordinateBilinear g₀ c) (coordinateBilinear g₁ c) _ b e f

end Burnett.Geometry.IntrinsicCov2
