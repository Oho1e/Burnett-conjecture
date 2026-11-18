import Burnett.Geometry.FlatRigidity.RadialFrame
import Burnett.Geometry.FlatRigidity.Intrinsic
import Burnett.Geometry.FlatRigidity.Volterra

set_option autoImplicit false

noncomputable section

namespace Burnett.FlatRigidity

open Set Metric Burnett.RicciSymbol Burnett.Geometry.FlatRigidity Burnett.Geometry.ConnectionDifference
open scoped ContDiff Matrix.Norms.Operator

def radialEndTime : RadialTimes := ⟨1, by norm_num [RadialTimes]⟩

/-- Assemble the actual coordinate frames by evaluating their displacement paths at time one. -/
theorem hasUniformCoordinateFramesOn_of_radial_endpoints
    (Γ : ℕ → CoordinateSpace → Connection) (z : CoordinateSpace) (R : ℝ) (hR : 0 < R)
    (F : ℕ → CoordinateSpace → C(RadialTimes, FrameMatrix))
    (hF : ∀ n, DifferentiableOn ℝ (F n) (ball 0 R))
    (hΓ : ∀ n d, ContDiffOn ℝ ∞ (fun x => connectionMatrix (Γ n x) d) (ball z R))
    (hNear : ∀ n v, v ∈ ball 0 R → ‖F n v radialEndTime - 1‖ ≤ 1 / 3)
    (hParallel : ∀ n v, v ∈ ball 0 R → ∀ d : Index,
      (fderiv ℝ (F n) v (EuclideanSpace.single d 1)) radialEndTime =
        -(connectionMatrix (Γ n (z + v)) d * F n v radialEndTime)) :
    HasUniformCoordinateFramesOn Γ z R := by
  let E (n : ℕ) (x : CoordinateSpace) := F n (x - z) radialEndTime
  let eval : C(RadialTimes, FrameMatrix) →L[ℝ] FrameMatrix := ContinuousMap.evalCLM (R := ℝ) radialEndTime
  have hv (x : CoordinateSpace) (hx : x ∈ ball z R) : x - z ∈ ball 0 R := by
    simpa only [mem_ball, dist_eq_norm, sub_zero] using hx
  have hderiv (n : ℕ) (x : CoordinateSpace) (hx : x ∈ ball z R) :
      HasFDerivAt (E n) (eval.comp (fderiv ℝ (F n) (x - z))) x := by
    have hd := ((hF n) (x - z) (hv x hx)).differentiableAt (isOpen_ball.mem_nhds (hv x hx))
    convert eval.hasFDerivAt.comp x (hd.hasFDerivAt.comp x (hasFDerivAt_sub_const z)) using 1
  have hDE (n : ℕ) : DifferentiableOn ℝ (E n) (ball z R) :=
    fun x hx => (hderiv n x hx).differentiableAt.differentiableWithinAt
  have hEq (n : ℕ) (x : CoordinateSpace) (hx : x ∈ ball z R) (d : Index) :
      fderiv ℝ (E n) x (EuclideanSpace.single d 1) = -(connectionMatrix (Γ n x) d * E n x) := by
    have hp := hParallel n (x - z) (hv x hx) d
    rw [(hderiv n x hx).fderiv]
    change (fderiv ℝ (F n) (x - z) (EuclideanSpace.single d 1)) radialEndTime = _
    rw [show z + (x - z) = x by abel] at hp
    exact hp
  have hNorms (n : ℕ) (x : CoordinateSpace) (hx : x ∈ closedBall z (R / 2)) :
      IsUnit (E n x) ∧ ‖E n x‖ ≤ 2 ∧ ‖(E n x)⁻¹‖ ≤ 2 :=
    isUnit_and_norm_bounds_of_norm_sub_one_le (E n x)
      (hNear n (x - z) (hv x (closedBall_subset_ball (by linarith) hx)))
  refine ⟨E, 2, 2, fun n => contDiffOn_frame_of_parallel _ isOpen_ball (Γ n) (E n) (hΓ n) (hDE n) (hEq n),
    fun n x hx => (hNorms n x hx).1, ?_, ?_, hEq⟩
  · intro n x hx
    exact_mod_cast (hNorms n x hx).2.1
  · intro n x hx
    exact_mod_cast (hNorms n x hx).2.2

end Burnett.FlatRigidity

namespace Burnett.FlatRigidity

open Filter Matrix Metric Set Burnett.RicciSymbol Burnett.Geometry
open Burnett.Geometry.FlatRigidity Burnett.Geometry.FlatFrameVolterra
open ConnectionDifference BackgroundConnection ManifoldMetric ManifoldMetricTransition
open ManifoldBilinear ManifoldMetricSequence
open scoped ContDiff Manifold Matrix.Norms.Operator Topology

/-- A solved radial path in a smooth flat connection obeys the transverse parallel equations at time one. -/
theorem solvedRadialEndpoint_parallel_of_flat
    (Γ : CoordinateSpace → Connection) (z : CoordinateSpace) (U s : Set CoordinateSpace)
    (hU : IsOpen U) (hs : IsOpen s)
    (hΓ : ∀ a d b, ContDiffOn ℝ ∞ (fun x => Γ x a d b) s)
    (hFlat : ∀ x ∈ s, ∀ a i, coordinateRiemann Γ x a i = 0)
    (hInside : ∀ v ∈ U, ∀ t ∈ RadialTimes, radialPoint z (t, v) ∈ s)
    (A : CoordinateSpace → RadialCoefficientPaths) (hA : ContDiffOn ℝ 1 A U)
    (hCap : ∀ v ∈ U, ‖A v‖ ≤ 1 / 4)
    (hEq : ∀ v ∈ U, ∀ t : RadialTimes, A v t = radialConnectionOperator Γ z v (t : ℝ))
    (v : CoordinateSpace) (hv : v ∈ U) (i : Index) :
    (fderiv ℝ (fun w => solvedPath (A w) (1 : FrameMatrix)) v (EuclideanSpace.single i 1)) radialEndTime =
      -(connectionMatrix (Γ (z + v)) i * solvedPath (A v) (1 : FrameMatrix) radialEndTime) := by
  let d := EuclideanSpace.single i (1 : ℝ)
  let b : FrameMatrix := 1
  let F (w : CoordinateSpace) : Path FrameMatrix := solvedPath (A w) b
  let Da := fderiv ℝ A v
  let Df := fderiv ℝ F v
  let q := Df d
  let E := realizePath (A v) (F v) b
  let V := realizeVariation (A v) (Da d) (F v) q
  have hSmall (w : CoordinateSpace) (hw : w ∈ U) : ‖A w‖ < 1 := (hCap w hw).trans_lt (by norm_num)
  have hFixed (w : CoordinateSpace) (hw : w ∈ U) :
      F w = ContinuousMap.const Time b + volterraCLM (A w) (F w) := solvedPath_eq (A w) b (hSmall w hw)
  have hA_diff := (hA.contDiffAt (hU.mem_nhds hv)).differentiableAt (by simp)
  have hF₁ := contDiffOn_solvedPath_of_coeff U A b hA hSmall
  have hF_diff := (hF₁.contDiffAt (hU.mem_nhds hv)).differentiableAt (by simp)
  have hFixedNear : ∀ᶠ w in 𝓝 v, F w = ContinuousMap.const Time b + volterraCLM (A w) (F w) := by
    filter_upwards [hU.mem_nhds hv] with w hw
    exact hFixed w hw
  have hQ : q = volterraCLM (A v) q + volterraCLM (Da d) (F v) :=
    fixed_point_parameter_variation A F b v Da Df hA_diff.hasFDerivAt hF_diff.hasFDerivAt hFixedNear d
  have hΓmat (a : Index) : ContDiffOn ℝ ∞ (fun x => connectionMatrix (Γ x) a) s :=
    contDiffOn_frameMatrix_of_entries fun j k => hΓ j a k
  have hΓdiff (t : ℝ) (ht : t ∈ RadialTimes) (a : Index) :
      DifferentiableAt ℝ (fun x => connectionMatrix (Γ x) a) (radialPoint z (t, v)) :=
    ((hΓmat a).contDiffAt (hs.mem_nhds (hInside v hv t ht))).differentiableAt (by simp)
  have hDomain : IsOpen {p : RadialParameter | radialPoint z p ∈ s} :=
    hs.preimage (continuous_const.add (continuous_fst.smul continuous_snd))
  have hGenDiff (t : ℝ) (ht : t ∈ RadialTimes) : DifferentiableAt ℝ (radialGenerator z Γ) (t, v) :=
    ((contDiffOn_radialGenerator_of_coordinate Γ z s hΓ).contDiffAt
      (hDomain.mem_nhds (hInside v hv t ht))).differentiableAt (by simp)
  have hM (t : ℝ) (ht : t ∈ RadialTimes) : ‖radialGenerator z Γ (t, v)‖ ≤ 1 / 4 := by
    let u : RadialTimes := ⟨t, ht⟩
    have h := (A v).norm_coe_le_norm u
    rw [hEq v hv u] at h
    exact (norm_radialGenerator_le_operator Γ z v t).trans (h.trans (hCap v hv))
  have hE (t : ℝ) (ht : t ∈ RadialTimes) : HasDerivAt E (-(radialGenerator z Γ (t, v) * E t)) t := by
    have he := realizePath_fixed_point_closed_ODE (A v) (F v) b (hFixed v hv) t ht
    have hclamp : clampTime t = (⟨t, ht⟩ : RadialTimes) := clampTime_coe ⟨t, ht⟩
    rw [hclamp, hEq v hv ⟨t, ht⟩, radialConnectionOperator_apply_generator] at he
    exact he
  have hV (t : ℝ) (ht : t ∈ RadialTimes) : HasDerivAt V
      (-(fderiv ℝ (radialGenerator z Γ) (t, v) (0, d) * E t + radialGenerator z Γ (t, v) * V t)) t := by
    have hvar := realizeVariation_closed_ODE (A v) (Da d) (F v) q b (hFixed v hv) hQ t ht
    have hclamp : clampTime t = (⟨t, ht⟩ : RadialTimes) := clampTime_coe ⟨t, ht⟩
    have hD := fderiv_radialCoefficientPaths_apply Γ z U hU A hEq v hv ⟨t, ht⟩
      hA_diff (hGenDiff t ht) d (E t)
    rw [hclamp, hEq v hv ⟨t, ht⟩, radialConnectionOperator_apply_generator] at hvar
    change HasDerivAt V (-((Da d) (⟨t, ht⟩ : RadialTimes) (E t) + radialGenerator z Γ (t, v) * V t)) t at hvar
    rw [hD] at hvar
    exact hvar
  have hV₀ : V 0 = 0 := realizeVariation_zero (A v) (Da d) (F v) q
  have hZero := radialFrameDefect_eq_zero_of_flat z Γ v i E V (1 / 4) hΓdiff (by norm_num) hM hE hV hV₀
    (fun t ht a => hFlat _ (hInside v hv t ht) a i) 1 radialEndTime.property
  have hEndpoint := radialFrame_transverse_parallel_at_one z Γ v i E V hZero
  have hETrace : E 1 = F v radialEndTime := realizePath_eq_trace (A v) (F v) b (hFixed v hv) radialEndTime
  have hVTrace : V 1 = q radialEndTime := realizeVariation_eq_trace (A v) (Da d) (F v) q hQ radialEndTime
  rw [hETrace, hVTrace] at hEndpoint
  exact hEndpoint

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The full curvature of a smoothly limiting admissible sequence of flat metrics vanishes. -/
theorem isFlat_of_original_flat_sequence
    (r : Metric (M := M)) (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n))
    (hs₀ : IsSymmetric g₀) (hs : ∀ n, IsSymmetric (g n))
    (hn₀ : IsNondegenerate g₀) (hn : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g g₀)
    (hb : ∀ S : Set M, IsCompact S → ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      MeasureTheory.eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - g₀ m)) ⊤
        ((ManifoldVolume.geometricMeasure g₀).restrict S) ≤ ENNReal.ofReal D)
    (hFlat : ∀ n, IsFlat (g n)) : IsFlat g₀ := by
  apply isFlat_of_original_uniform_coordinate_frames r g₀ g h₀ hg hs₀ hs hn₀ hn hconv hb
  intro p
  let z := chartAt CoordinateSpace p p
  let s := (chartAt CoordinateSpace p).target
  let Γ (n : ℕ) := computedConnection (coordinateBilinear (g n) p)
  have hz : z ∈ s := (chartAt CoordinateSpace p).mapsTo (mem_chart_source CoordinateSpace p)
  obtain ⟨R, hR, hChart, A, hA, hCap, hEq⟩ :=
    exists_uniform_radialCoefficientPaths_of_original r g₀ g h₀ hg hs₀ hs hn₀ hn hconv hb p z hz
  have hCovered : ball z R ⊆ s := (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hChart
  have hEntry (n : ℕ) (a d b : Index) : ContDiffOn ℝ ∞ (fun x => Γ n x a d b) s := by
    have h := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection (g n) (hg n) (hn n) p
    exact contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp h a) d) b
  have hInside (v : CoordinateSpace) (hv : v ∈ ball 0 R) (t : ℝ) (ht : t ∈ RadialTimes) :
      radialPoint z (t, v) ∈ s := by
    apply hChart
    have hv' : ‖v‖ < R := by simpa only [mem_ball, dist_zero_right] using hv
    have ht' : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    rw [radialPoint, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg v) ht').trans (by linarith)
  have hSmooth (n : ℕ) (d : Index) : ContDiffOn ℝ ∞ (fun x => connectionMatrix (Γ n x) d) (ball z R) :=
    contDiffOn_frameMatrix_of_entries fun a b => (hEntry n a d b).mono hCovered
  let F (n : ℕ) (v : CoordinateSpace) : Path FrameMatrix := solvedPath (A n v) 1
  have hF (n : ℕ) : DifferentiableOn ℝ (F n) (ball 0 R) :=
    (contDiffOn_solvedPath_of_coeff (ball 0 R) (A n) (1 : FrameMatrix) (hA n)
      (fun v hv => (hCap n v hv).trans_lt (by norm_num))).differentiableOn le_rfl
  have hNear (n : ℕ) (v : CoordinateSpace) (hv : v ∈ ball 0 R) : ‖F n v radialEndTime - 1‖ ≤ 1 / 3 := by
    simpa only [norm_one, F] using norm_solvedPath_sub_eval_le_of_quarter (A n v) (1 : FrameMatrix)
      (hCap n v hv) radialEndTime
  have hCoordFlat := sequence_coordinateFlat_of_intrinsic g hg hs hn hFlat p
  refine ⟨R, hR, hCovered, hasUniformCoordinateFramesOn_of_radial_endpoints Γ z R hR F hF hSmooth hNear ?_⟩
  intro n v hv d
  exact solvedRadialEndpoint_parallel_of_flat (Γ n) z (ball 0 R) s isOpen_ball
    (chartAt CoordinateSpace p).open_target (hEntry n) (hCoordFlat n) hInside (A n) (hA n) (hCap n) (hEq n) v hv d

end Burnett.FlatRigidity
