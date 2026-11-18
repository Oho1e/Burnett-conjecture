import Burnett.Geometry.FlatRigidity.ConnectionLimit
import Burnett.Geometry.FlatRigidity.FrameCompactness
import Burnett.Geometry.IntrinsicRicciTrace

set_option autoImplicit false

noncomputable section

namespace Burnett.FlatRigidity

open Filter Metric Set MeasureTheory Matrix Burnett.RicciSymbol Burnett.Geometry
open Burnett.Geometry.FlatRigidity Burnett.FlatFrame
open ConnectionDifference BackgroundConnection
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence
open scoped ContDiff Manifold Topology NNReal Matrix.Norms.Operator

/-- The induced matrix norm in direction `d` is controlled by the four entries in each row. -/
theorem connectionMatrix_norm_le_of_entries (Γ : Connection) (d : Index) (C : ℝ≥0)
    (hΓ : ∀ a b, ‖Γ a d b‖ ≤ C) : ‖connectionMatrix Γ d‖ ≤ (4 * C : ℝ≥0) := by
  rw [Matrix.linfty_opNorm_def]
  exact_mod_cast (show (Finset.univ : Finset Index).sup
      (fun a => ∑ b : Index, ‖connectionMatrix Γ d a b‖₊) ≤ 4 * C from by
    apply Finset.sup_le
    intro a _
    calc
      _ ≤ ∑ _b : Index, C := Finset.sum_le_sum fun b _ => by
        exact_mod_cast hΓ a b
      _ = _ := by simp [Index, nsmul_eq_mul])

private def frameEntryCLM (a i : Index) : FrameMatrix →L[ℝ] ℝ :=
  let entry : FrameMatrix →ₗ[ℝ] ℝ :=
    { toFun := fun E => E a i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  entry.mkContinuous 1 fun E => by
    change ‖E a i‖ ≤ 1 * ‖E‖
    simpa only [one_mul] using matrixEntry_norm_le E a i

private theorem matrixDerivative_entry (E : CoordinateSpace → FrameMatrix) (x : CoordinateSpace)
    (hE : DifferentiableAt ℝ E x) (d : Index) :
    frameCoordinateJet E x d = fderiv ℝ E x (EuclideanSpace.single d 1) := by
  ext a i
  have h := ((frameEntryCLM a i).hasFDerivAt.comp x hE.hasFDerivAt).fderiv
  exact congrArg (fun D : CoordinateSpace →L[ℝ] ℝ => D (EuclideanSpace.single d 1)) h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The original physical control and genuine uniformly bounded parallel frames
    imply that the limit metric has zero full coordinate curvature on a smaller ball. -/
theorem computedCoordinateCurvature_zero_of_original_frames
    (r : Metric (M := M)) (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n))
    (hs₀ : IsSymmetric g₀) (hs : ∀ n, IsSymmetric (g n))
    (hn₀ : IsNondegenerate g₀) (hn : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g g₀)
    (hb : ∀ S : Set M, IsCompact S → ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - g₀ m)) ⊤
        ((ManifoldVolume.geometricMeasure g₀).restrict S) ≤ ENNReal.ofReal D)
    (p : M) (z : CoordinateSpace) {ρ R : ℝ} (hρR : ρ < R)
    (hBall : ball z R ⊆ (chartAt CoordinateSpace p).target)
    (E : ℕ → CoordinateSpace → FrameMatrix) (F I : ℝ≥0)
    (hSmooth : ∀ n, ContDiffOn ℝ ∞ (E n) (ball z R))
    (hInvertible : ∀ n x, x ∈ closedBall z ρ → IsUnit (E n x))
    (hForward : ∀ n x, x ∈ closedBall z ρ → ‖E n x‖ ≤ F)
    (hInverse : ∀ n x, x ∈ closedBall z ρ → ‖(E n x)⁻¹‖ ≤ I)
    (hParallel : ∀ n x, x ∈ ball z R → ∀ d,
      fderiv ℝ (E n) x (EuclideanSpace.single d 1) =
        -(connectionMatrix (computedConnection (coordinateBilinear (g n) p) x) d * E n x)) :
    ∀ x ∈ ball z ρ, ∀ d e : Index, coordinateRiemann (computedConnection (coordinateBilinear g₀ p)) x d e = 0 := by
  let U := ball z ρ
  let K := closedBall z ρ
  let Γₙ (n : ℕ) := computedConnection (coordinateBilinear (g n) p)
  let Γ := computedConnection (coordinateBilinear g₀ p)
  have hU : IsOpen U := isOpen_ball
  have hUK : U ⊆ K := ball_subset_closedBall
  have hKR : K ⊆ ball z R := closedBall_subset_ball hρR
  have hKChart := hKR.trans hBall
  have hUChart := hUK.trans hKChart
  have hdiff (n : ℕ) (x : CoordinateSpace) (hx : x ∈ ball z R) : DifferentiableAt ℝ (E n) x :=
    ((hSmooth n).contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
  obtain ⟨C₀, hC₀, hΓK⟩ := computedConnection_uniform_bound_of_original r g₀ g h₀ hg hs₀ hs hn₀ hn hconv hb
    p K (isCompact_closedBall z ρ) hKChart
  let C : ℝ≥0 := ⟨C₀, hC₀⟩
  have hΓmatrix (n : ℕ) (x : CoordinateSpace) (hx : x ∈ K) (d : Index) :
      ‖connectionMatrix (Γₙ n x) d‖ ≤ (4 * C : ℝ≥0) := by
    apply connectionMatrix_norm_le_of_entries
    intro a b
    rw [Real.norm_eq_abs]
    exact (ConnectionError.abs_firstJet_entry_le_norm (Γₙ n x) a d b).trans (hΓK n x hx)
  obtain ⟨φ, E₀, hφ, hUniform, _, hUnit, hLip, _⟩ := exists_uniformFrameSubsequenceOn_closedBall_of_parallel
    z ρ E (fun n x d => connectionMatrix (Γₙ n x) d) F I (4 * C)
    hInvertible hForward hInverse (fun n x hx => hdiff n x (hKR hx)) hΓmatrix
    (fun n x hx => hParallel n x (hKR hx))
  have hE₀ (a i : Index) : ContinuousOn (fun x => E₀ x a i) U :=
    (frameEntryCLM a i).continuous.comp_continuousOn (hLip.continuousOn.mono hUK)
  have hΓₙSmooth (n : ℕ) (a b c : Index) : ContDiffOn ℝ ∞ (fun x => Γₙ n x a b c) U := by
    have h := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection (g n) (hg n) (hn n) p
    exact (contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp h a) b) c).mono hUChart
  have hΓSmooth (a b c : Index) : ContDiffOn ℝ ∞ (fun x => Γ x a b c) U := by
    have h := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g₀ h₀ hn₀ p
    exact (contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp h a) b) c).mono hUChart
  have hweak : IsWeakParallelFrameOn U Γ E₀ := by
    apply isWeakParallelFrameOn_of_local_uniform_limit hU (fun n => Γₙ (φ n)) Γ (fun n => E (φ n)) E₀
      (fun n a i => (frameEntryCLM a i).contDiff.comp_contDiffOn ((hSmooth (φ n)).mono (hUK.trans hKR)))
      hE₀ (fun n a b c => (hΓₙSmooth (φ n) a b c).continuousOn) (fun a b c => (hΓSmooth a b c).continuousOn)
    · intro n x hx d
      rw [matrixDerivative_entry (E (φ n)) x (hdiff (φ n) x (hKR (hUK hx))) d]
      exact hParallel (φ n) x (hKR (hUK hx)) d
    · intro L _ hLU a i
      exact (tendstoUniformlyOn_matrixEntry hUniform a i).mono (hLU.trans hUK)
    · intro a d k L hL hLU w hw
      have hwk := computedConnection_localWeakStarOn_of_original r g₀ g h₀ hg hs₀ hs hn₀ hn hconv hb
        p a d k L hL (hLU.trans hUChart) w hw
      exact hwk.comp hφ.tendsto_atTop
    · intro L hL hLU
      refine ⟨C₀, hC₀, fun n x hx a d k => ?_⟩
      rw [Real.norm_eq_abs]
      exact (ConnectionError.abs_firstJet_entry_le_norm (Γₙ (φ n) x) a d k).trans
        (hΓK (φ n) x (hUK (hLU hx)))
  intro x hx d e
  exact coordinateRiemann_computedConnection_eq_zero_of_weak_parallel_frame hU (coordinateBilinear g₀ p)
    (fun a b => (ManifoldBilinear.contDiffOn_metricComponents g₀ h₀ p a b).mono hUChart)
    (fun y hy => ManifoldBilinear.coordinateBilinear_nondegenerate g₀ hn₀ p (hUChart hy)) E₀ hE₀
    (fun y hy => (Matrix.isUnit_iff_isUnit_det (E₀ y)).mp ((hUnit y (hUK hy)).1)) hweak x hx d e

end Burnett.FlatRigidity

namespace Burnett.Geometry.FlatRigidity

open Set
open scoped BigOperators ContDiff Manifold Topology
open Burnett.RicciSymbol
open ConnectionDifference CurvatureDifference CurvatureFiberTensor
open ManifoldMetric ManifoldMetricTransition ChartVectorField

theorem coordinateTensor_basis_eq_coordinateRiemann
    (Γ : CoordinateSpace → Connection) (y : CoordinateSpace)
    (hΓ : DifferentiableConnectionAt Γ y) (a b d e : Index) :
    coordinateTensor Γ y ![EuclideanSpace.single d 1, EuclideanSpace.single e 1,
      EuclideanSpace.single b 1] a = coordinateRiemann Γ y d e a b := by
  rw [IntrinsicRicciTrace.coordinateTensor_basis Γ y hΓ]
  simp only [CurvatureComponents.components, coordinateRiemann, connectionMatrixDerivative,
    connectionMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Finset.sum_sub_distrib]
  ring

theorem coordinateTensor_eq_zero_iff_coordinateRiemann
    (Γ : CoordinateSpace → Connection) (y : CoordinateSpace)
    (hΓ : DifferentiableConnectionAt Γ y) :
    coordinateTensor Γ y = 0 ↔ ∀ d e, coordinateRiemann Γ y d e = 0 := by
  constructor
  · intro h d e
    ext a b
    rw [← coordinateTensor_basis_eq_coordinateRiemann Γ y hΓ, h]
    rfl
  · intro h
    have hlinear : curvatureLinear Γ y = 0 := by
      refine coordinateBasis.ext fun d => coordinateBasis.ext fun e => coordinateBasis.ext fun b => ?_
      have hvalue : coordinateTensor Γ y ![EuclideanSpace.single d 1, EuclideanSpace.single e 1,
          EuclideanSpace.single b 1] = 0 := by
        ext a
        rw [coordinateTensor_basis_eq_coordinateRiemann Γ y hΓ, h d e]
        rfl
      change curvatureLinear Γ y (EuclideanSpace.single d 1) (EuclideanSpace.single e 1)
        (EuclideanSpace.single b 1) = 0 at hvalue
      have hb (i : Index) : coordinateBasis i = EuclideanSpace.single i 1 :=
        EuclideanSpace.basisFun_apply _ _ i
      simpa only [hb, LinearMap.zero_apply] using hvalue
    apply ContinuousMultilinearMap.ext
    intro p
    change curvatureLinear Γ y (p 0) (p 1) (p 2) = 0
    rw [hlinear]
    rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem tensorInChart_eq_zero_iff_coordinateTensor
    (B : ManifoldBilinear.Field (M := M)) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) :
    tensorInChart B c m = 0 ↔
      coordinateTensor (BackgroundConnection.computedConnection (coordinateBilinear B c))
        (chartAt CoordinateSpace c m) = 0 := by
  constructor
  · intro ht
    apply ContinuousMultilinearMap.ext
    intro p
    let q (i : Fin 3) := tangentFrame c m (p i)
    have hq : (fun i => mfderiv Model Model (chartAt CoordinateSpace c) m (q i)) = p :=
      funext fun i => IntrinsicRicciTrace.forward_tangentFrame c m hm (p i)
    have hz := congrArg (fun T : ContinuousMultilinearMap ℝ
      (fun _ : Fin 3 => TangentSpace Model m) (TangentSpace Model m) => T q) ht
    change tangentFrame c m (coordinateTensor
      (BackgroundConnection.computedConnection (coordinateBilinear B c))
      (chartAt CoordinateSpace c m)
      (fun i => mfderiv Model Model (chartAt CoordinateSpace c) m (q i))) = 0 at hz
    rw [hq] at hz
    have hh := congrArg (mfderiv Model Model (chartAt CoordinateSpace c) m) hz
    rw [IntrinsicRicciTrace.forward_tangentFrame c m hm, map_zero] at hh
    exact hh
  · intro h
    apply ContinuousMultilinearMap.ext
    intro p
    change tangentFrame c m (coordinateTensor
      (BackgroundConnection.computedConnection (coordinateBilinear B c))
      (chartAt CoordinateSpace c m)
      (fun i => mfderiv Model Model (chartAt CoordinateSpace c) m (p i))) = 0
    rw [h]
    simp

/-- Full intrinsic tangent-fiber curvature vanishes at every point. -/
def IsFlat (B : ManifoldBilinear.Field (M := M)) : Prop :=
  ∀ m : M, CurvatureFiberTensor.tensor B m = 0

/-- Every full coordinate curvature matrix vanishes in every preferred chart. -/
def IsCoordinateFlat (B : ManifoldBilinear.Field (M := M)) : Prop :=
  ∀ (c : M) (y : CoordinateSpace), y ∈ (chartAt CoordinateSpace c).target →
    ∀ d e : Index, coordinateRiemann
      (BackgroundConnection.computedConnection (coordinateBilinear B c)) y d e = 0

theorem tensor_eq_zero_iff_coordinateRiemann [T2Space M]
    (B : ManifoldBilinear.Field (M := M)) (hB : ManifoldBilinear.IsSmooth B)
    (hSym : ManifoldBilinear.IsSymmetric B) (hND : ManifoldBilinear.IsNondegenerate B)
    (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source) :
    CurvatureFiberTensor.tensor B m = 0 ↔
      ∀ d e, coordinateRiemann (BackgroundConnection.computedConnection (coordinateBilinear B c))
        (chartAt CoordinateSpace c m) d e = 0 := by
  rw [tensor_eq_tensorInChart B hB hSym hND c m hm]
  apply (tensorInChart_eq_zero_iff_coordinateTensor B c m hm).trans
  apply coordinateTensor_eq_zero_iff_coordinateRiemann
  have hΓ := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection B hB hND c
  have hy := (chartAt CoordinateSpace c).mapsTo hm
  intro a b d
  exact ((contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ a) b) d).contDiffAt
    ((chartAt CoordinateSpace c).open_target.mem_nhds hy)).differentiableAt (by simp)

theorem isFlat_of_local_coordinateRiemann [T2Space M]
    (B : ManifoldBilinear.Field (M := M)) (hB : ManifoldBilinear.IsSmooth B)
    (hSym : ManifoldBilinear.IsSymmetric B) (hND : ManifoldBilinear.IsNondegenerate B)
    (h : ∀ m : M, ∃ c : M, m ∈ (chartAt CoordinateSpace c).source ∧
      ∀ d e, coordinateRiemann (BackgroundConnection.computedConnection (coordinateBilinear B c))
        (chartAt CoordinateSpace c m) d e = 0) : IsFlat B := by
  intro m
  obtain ⟨c, hm, hzero⟩ := h m
  exact (tensor_eq_zero_iff_coordinateRiemann B hB hSym hND c m hm).mpr hzero

theorem isFlat_iff_coordinateFlat [T2Space M]
    (B : ManifoldBilinear.Field (M := M)) (hB : ManifoldBilinear.IsSmooth B)
    (hSym : ManifoldBilinear.IsSymmetric B) (hND : ManifoldBilinear.IsNondegenerate B) :
    IsFlat B ↔ IsCoordinateFlat B := by
  constructor
  · intro h c y hy d e
    let m := (chartAt CoordinateSpace c).symm y
    have hm : m ∈ (chartAt CoordinateSpace c).source := (chartAt CoordinateSpace c).symm_mapsTo hy
    have hzero := (tensor_eq_zero_iff_coordinateRiemann B hB hSym hND c m hm).mp (h m) d e
    simpa only [m, (chartAt CoordinateSpace c).right_inv hy] using hzero
  · intro h
    refine isFlat_of_local_coordinateRiemann B hB hSym hND fun m => ?_
    have hm := mem_chart_source CoordinateSpace m
    exact ⟨m, hm, h m _ ((chartAt CoordinateSpace m).mapsTo hm)⟩

theorem sequence_coordinateFlat_of_intrinsic [T2Space M]
    (g : ℕ → ManifoldBilinear.Field (M := M)) (hg : ∀ n, ManifoldBilinear.IsSmooth (g n))
    (hs : ∀ n, ManifoldBilinear.IsSymmetric (g n)) (hn : ∀ n, ManifoldBilinear.IsNondegenerate (g n))
    (hf : ∀ n, IsFlat (g n)) (c : M) :
    ∀ n y, y ∈ (chartAt CoordinateSpace c).target → ∀ d e,
      coordinateRiemann (BackgroundConnection.computedConnection (coordinateBilinear (g n) c))
        y d e = 0 :=
  fun n => (isFlat_iff_coordinateFlat (g n) (hg n) (hs n) (hn n)).mp (hf n) c

theorem isFlat_iff_curvature_fields_zero [T2Space M]
    (B : ManifoldBilinear.Field (M := M)) (hB : ManifoldBilinear.IsSmooth B)
    (hSym : ManifoldBilinear.IsSymmetric B) (hND : ManifoldBilinear.IsNondegenerate B) :
    IsFlat B ↔
      ∀ X Y Z : ChartVectorField.Field (M := M),
        ChartVectorField.IsSmooth X → ChartVectorField.IsSmooth Y → ChartVectorField.IsSmooth Z →
          ∀ m, IntrinsicCurvature.curvature B X Y Z m = 0 := by
  constructor
  · intro h X Y Z hX hY hZ m
    rw [← tensor_apply_fields_eq_curvature B hB hSym hND X Y Z hX hY hZ m, h m]
    rfl
  · intro h m
    apply ContinuousMultilinearMap.ext
    intro p
    obtain ⟨X, hX, hx⟩ := SmoothTangentValueExtension.exists_isSmooth_value m (p 0)
    obtain ⟨Y, hY, hy⟩ := SmoothTangentValueExtension.exists_isSmooth_value m (p 1)
    obtain ⟨Z, hZ, hz⟩ := SmoothTangentValueExtension.exists_isSmooth_value m (p 2)
    have hp : ![X m, Y m, Z m] = p := by
      funext i
      fin_cases i <;> simp [hx, hy, hz]
    rw [← hp, tensor_apply_fields_eq_curvature B hB hSym hND X Y Z hX hY hZ m]
    exact h X Y Z hX hY hZ m

end Burnett.Geometry.FlatRigidity

namespace Burnett.FlatRigidity

open Metric Matrix Burnett.RicciSymbol Burnett.Geometry
open Burnett.Geometry.FlatRigidity ConnectionDifference BackgroundConnection
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence
open scoped ContDiff Manifold Topology NNReal Matrix.Norms.Operator

/-- Smooth frames for the same open ball, with bounds for both matrices on its smaller closed ball. -/
def HasUniformCoordinateFramesOn (Γ : ℕ → CoordinateSpace → Connection) (z : CoordinateSpace) (R : ℝ) : Prop :=
  ∃ (E : ℕ → CoordinateSpace → FrameMatrix) (F I : ℝ≥0),
    (∀ n, ContDiffOn ℝ ∞ (E n) (ball z R)) ∧
    (∀ n x, x ∈ closedBall z (R / 2) → IsUnit (E n x)) ∧
    (∀ n x, x ∈ closedBall z (R / 2) → ‖E n x‖ ≤ F) ∧
    (∀ n x, x ∈ closedBall z (R / 2) → ‖(E n x)⁻¹‖ ≤ I) ∧
    ∀ n x, x ∈ ball z R → ∀ d,
      fderiv ℝ (E n) x (EuclideanSpace.single d 1) = -(connectionMatrix (Γ n x) d * E n x)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The full intrinsic flatness conclusion, with the local frame construction supplied separately. -/
theorem isFlat_of_original_uniform_coordinate_frames
    (r : Metric (M := M)) (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n))
    (hs₀ : IsSymmetric g₀) (hs : ∀ n, IsSymmetric (g n))
    (hn₀ : IsNondegenerate g₀) (hn : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g g₀)
    (hb : ∀ S : Set M, IsCompact S → ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      MeasureTheory.eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - g₀ m)) ⊤
        ((ManifoldVolume.geometricMeasure g₀).restrict S) ≤ ENNReal.ofReal D)
    (hf : ∀ p : M, ∃ R : ℝ, 0 < R ∧
      ball (chartAt CoordinateSpace p p) R ⊆ (chartAt CoordinateSpace p).target ∧
      HasUniformCoordinateFramesOn (fun n => computedConnection (coordinateBilinear (g n) p))
        (chartAt CoordinateSpace p p) R) : IsFlat g₀ := by
  apply isFlat_of_local_coordinateRiemann g₀ h₀ hs₀ hn₀
  intro p
  let z := chartAt CoordinateSpace p p
  obtain ⟨R, hR, hChart, E, F, I, hSmooth, hUnit, hForward, hInverse, hParallel⟩ := hf p
  refine ⟨p, mem_chart_source CoordinateSpace p, ?_⟩
  have hcenter : z ∈ ball z (R / 2) := mem_ball_self (by positivity)
  exact computedCoordinateCurvature_zero_of_original_frames r g₀ g h₀ hg hs₀ hs hn₀ hn hconv hb
    p z (show R / 2 < R by linarith) hChart E F I hSmooth hUnit hForward hInverse hParallel z hcenter

end Burnett.FlatRigidity
