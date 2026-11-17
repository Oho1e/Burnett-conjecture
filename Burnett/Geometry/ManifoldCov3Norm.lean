import Burnett.Geometry.IntrinsicCov2
import Burnett.Geometry.ManifoldTensorNorm
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# ManifoldCov3Norm

Paper-specific intrinsic derivative and physical norm support.
See docs/statements/intrinsic-dh-geometry.md for scope and remaining obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Burnett.Geometry.ManifoldCov3Norm
open Bundle Set Matrix
open scoped BigOperators Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldTensorNorm Burnett.Geometry.ChartVolume
open Burnett.Geometry.CovariantTensorNorm

def curried (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => CoordinateSpace) ℝ) :
    CoordinateSpace →ₗ[ℝ] LinearMap.BilinForm ℝ CoordinateSpace where
  toFun v :=
    { toFun := fun u =>
        { toFun := fun w => T ![v, u, w]
          map_add' := fun w z => ((T.toMultilinearMap.curryLeft v).curryLeft u).cons_add ![] w z
          map_smul' := fun a w => ((T.toMultilinearMap.curryLeft v).curryLeft u).cons_smul ![] a w }
      map_add' := fun u z => by
        ext w
        exact (T.toMultilinearMap.curryLeft v).cons_add ![w] u z
      map_smul' := fun a u => by
        ext w
        exact (T.toMultilinearMap.curryLeft v).cons_smul ![w] a u }
  map_add' v z := by
    ext u w
    exact T.cons_add ![u, w] v z
  map_smul' a v := by
    ext u w
    exact T.cons_smul ![u, w] a v

@[simp] theorem curried_apply (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => CoordinateSpace) ℝ)
    (v u w : CoordinateSpace) : curried T v u w = T ![v, u, w] := rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

abbrev Field := ∀ m : M, ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace Model m) ℝ

def coordinateForm (T : Field (M := M)) (c m : M) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => CoordinateSpace) ℝ :=
  (T m).compContinuousLinearMap (fun _ => tangentFrame c m)

theorem coordinateForm_apply (T : Field (M := M)) (c m : M) (v u w : CoordinateSpace) :
    coordinateForm T c m ![v, u, w] =
      T m ![tangentFrame c m v, tangentFrame c m u, tangentFrame c m w] := by
  apply congrArg (T m)
  ext i
  fin_cases i <;> rfl

def frameComponents3 (T : Field (M := M)) (c m : M) : FirstJet :=
  fun i j k => coordinateForm T c m ![coordinateBasis i, coordinateBasis j, coordinateBasis k]

theorem frameComponents3_apply (T : Field (M := M)) (c m : M) (i j k : Index) :
    frameComponents3 T c m i j k = T m
      ![tangentFrame c m (coordinateBasis i), tangentFrame c m (coordinateBasis j),
        tangentFrame c m (coordinateBasis k)] :=
  coordinateForm_apply T c m _ _ _

theorem frameComponents3_change (T : Field (M := M)) (c d m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source)
    (hd : m ∈ (chartAt CoordinateSpace d).source) :
    frameComponents3 T c m = TensorCoordinateChange.pullback3
      (derivativeMatrix (fderiv ℝ (chartTransition c d) (chartAt CoordinateSpace c m)))
      (frameComponents3 T d m) := by
  funext b e f
  rw [frameComponents3_apply,
    tangentFrame_change c d m hc hd (coordinateBasis b),
    tangentFrame_change c d m hc hd (coordinateBasis e),
    tangentFrame_change c d m hc hd (coordinateBasis f)]
  have h := IntrinsicCov2.trilinear_basis_expansion (curried (coordinateForm T d m))
    (fderiv ℝ (chartTransition c d) (chartAt CoordinateSpace c m)) b e f
  simpa only [curried_apply, coordinateForm_apply, TensorCoordinateChange.pullback3_apply,
    frameComponents3_apply] using h

def physicalNorm3 (r : Metric (M := M)) (T : Field (M := M)) (m : M) : ℝ :=
  norm3 (frameComponents r.inner m m) (frameComponents3 T m m)

theorem norm3_frame_independent (r : Metric (M := M)) (T : Field (M := M)) (c d m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source)
    (hd : m ∈ (chartAt CoordinateSpace d).source) :
    norm3 (frameComponents r.inner c m) (frameComponents3 T c m) =
      norm3 (frameComponents r.inner d m) (frameComponents3 T d m) := by
  rw [frameComponents_change r.inner c d m hc hd, frameComponents3_change T c d m hc hd]
  exact TensorCoordinateChange.norm3_pullback _ _ (transitionMatrix_isUnit c d m hc hd) _

theorem physicalNorm3_eq_frame (r : Metric (M := M)) (T : Field (M := M)) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) :
    physicalNorm3 r T m = norm3 (frameComponents r.inner c m) (frameComponents3 T c m) :=
  (norm3_frame_independent r T c m m hm (mem_chart_source _ m)).symm

theorem physicalNorm3_eq_coordinate (r : Metric (M := M)) (T : Field (M := M)) (c : M)
    {y : CoordinateSpace} (hy : y ∈ (chartAt CoordinateSpace c).target) :
    physicalNorm3 r T ((chartAt CoordinateSpace c).symm y) =
      norm3 (metricComponents (coordinateMetric r c) y)
        (frameComponents3 T c ((chartAt CoordinateSpace c).symm y)) := by
  have hm := (chartAt CoordinateSpace c).symm_mapsTo hy
  rw [physicalNorm3_eq_frame r T c _ hm, frameComponents_eq_coordinate r.inner c _ hm,
    (chartAt CoordinateSpace c).right_inv hy]
  rfl

theorem physicalNorm3_eq_ofMatrix_norm (r : Metric (M := M)) (T : Field (M := M)) (m : M) :
    physicalNorm3 r T m = @Norm.norm (((Index × Index) × Index) → ℝ)
      (Matrix.NormedAddCommGroup.ofMatrix (gram3_posDef _
        (frameComponents_inner_posDef r m m (mem_chart_source _ m)))).toNorm
      (flatten3 (frameComponents3 T m m)) :=
  norm3_eq_ofMatrix_norm _ (frameComponents_inner_posDef r m m (mem_chart_source _ m)) _

theorem physicalNorm3_nonneg (r : Metric (M := M)) (T : Field (M := M)) (m : M) :
    0 ≤ physicalNorm3 r T m := Real.sqrt_nonneg _

theorem frameComponents3_eq_zero_iff (T : Field (M := M)) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) :
    frameComponents3 T c m = 0 ↔ T m = 0 := by
  constructor
  · intro h
    have hC : coordinateForm T c m = 0 := by
      apply ContinuousMultilinearMap.toMultilinearMap_injective
      apply Module.Basis.ext_multilinear (fun _ => coordinateBasis)
      intro v
      change coordinateForm T c m (fun i => coordinateBasis (v i)) = 0
      have hv : (fun i => coordinateBasis (v i)) =
          ![coordinateBasis (v 0), coordinateBasis (v 1), coordinateBasis (v 2)] := by
        ext i
        fin_cases i <;> rfl
      rw [hv]
      exact congrFun (congrFun (congrFun h (v 0)) (v 1)) (v 2)
    ext p
    have hs := Function.Surjective.piMap
      (fun _ : Fin 3 => ManifoldBilinear.tangentFrame_surjective c m hm)
    obtain ⟨v, hv⟩ := hs p
    rw [← hv]
    change coordinateForm T c m v = 0
    exact congrArg (fun C => C v) hC
  · intro h
    funext i j k
    rw [frameComponents3_apply, h]
    rfl

theorem physicalNorm3_pos_of_ne (r : Metric (M := M)) (T : Field (M := M))
    (m : M) (hne : T m ≠ 0) : 0 < physicalNorm3 r T m := by
  have hn : frameComponents3 T m m ≠ 0 := by
    intro hz
    exact hne ((frameComponents3_eq_zero_iff T m m (mem_chart_source _ m)).mp hz)
  have hf : flatten3 (frameComponents3 T m m) ≠ 0 := by
    intro hz
    apply hn
    funext i j k
    exact congrFun hz ((i, j), k)
  have hR := frameComponents_inner_posDef r m m (mem_chart_source _ m)
  have hg := (gram3_posDef _ hR).2 (flatten3 (frameComponents3 T m m)) hf
  apply Real.sqrt_pos.mpr
  rw [energy3_eq_gramEnergy]
  simpa only [GramCoordinateBound.gramEnergy, star_trivial] using hg

theorem physicalNorm3_eq_zero_iff (r : Metric (M := M)) (T : Field (M := M)) (m : M) :
    physicalNorm3 r T m = 0 ↔ T m = 0 := by
  constructor
  · intro h
    by_contra hn
    exact (ne_of_gt (physicalNorm3_pos_of_ne r T m hn)) h
  · intro h
    have hC := (frameComponents3_eq_zero_iff T m m (mem_chart_source _ m)).mpr h
    unfold physicalNorm3
    rw [hC]
    simp [norm3, energy3]

theorem exists_uniform_component_control (r : Metric (M := M)) (c : M)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    ∃ C > 0, ∀ y ∈ K, ∀ T : Field (M := M),
      ‖frameComponents3 T c ((chartAt CoordinateSpace c).symm y)‖ ≤
        C * physicalNorm3 r T ((chartAt CoordinateSpace c).symm y) := by
  have hd (i : Index) : ContinuousOn
      (fun y => metricComponents (coordinateMetric r c) y i i) K :=
    (ManifoldMetric.contDiffOn_metricComponents r c i i).continuousOn.mono hKt
  obtain ⟨C, hC, hcontrol⟩ := exists_uniform_norm3_control
    (metricComponents (coordinateMetric r c)) K hK hd
      (fun y hy => coordinateMetric_posDef r c (hKt hy))
  refine ⟨C, hC, ?_⟩
  intro y hy T
  rw [physicalNorm3_eq_coordinate r T c (hKt hy)]
  exact hcontrol y hy _

theorem intrinsic_frameComponents3_auxiliary (r : Metric (M := M))
    (g₁ g₀ : ManifoldBilinear.Field (M := M))
    (h₁ : ManifoldBilinear.IsSmooth g₁) (h₀ : ManifoldBilinear.IsSmooth g₀)
    (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source) :
    frameComponents3 (IntrinsicCov2.tensor r.inner (fun n => g₁ n - g₀ n)) c m =
      AuxiliaryConnection.auxiliaryPerturbationJet (coordinateMetric r c)
        (coordinateBilinear g₀ c) (coordinateBilinear g₁ c) (chartAt CoordinateSpace c m) := by
  funext b e f
  rw [frameComponents3_apply]
  simpa only [coordinateBasis, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using
    IntrinsicCov2.auxiliary_tensor_basis_inChart r g₁ g₀ h₁ h₀ c m hm b e f

theorem intrinsic_physicalNorm3_eq_auxiliary (r : Metric (M := M))
    (g₁ g₀ : ManifoldBilinear.Field (M := M))
    (h₁ : ManifoldBilinear.IsSmooth g₁) (h₀ : ManifoldBilinear.IsSmooth g₀)
    (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source) :
    physicalNorm3 r (IntrinsicCov2.tensor r.inner (fun n => g₁ n - g₀ n)) m =
      norm3 (metricComponents (coordinateMetric r c) (chartAt CoordinateSpace c m))
        (AuxiliaryConnection.auxiliaryPerturbationJet (coordinateMetric r c)
          (coordinateBilinear g₀ c) (coordinateBilinear g₁ c) (chartAt CoordinateSpace c m)) := by
  rw [physicalNorm3_eq_frame r _ c m hm, frameComponents_eq_coordinate r.inner c m hm,
    intrinsic_frameComponents3_auxiliary r g₁ g₀ h₁ h₀ c m hm]
  rfl

end Burnett.Geometry.ManifoldCov3Norm
