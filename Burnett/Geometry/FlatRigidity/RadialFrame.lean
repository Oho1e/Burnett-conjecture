import Burnett.Geometry.FlatRigidity.Intrinsic
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

set_option autoImplicit false

noncomputable section

namespace Burnett.FlatRigidity

open Metric Set Burnett.RicciSymbol Burnett.Geometry
open Burnett.Geometry.FlatRigidity ConnectionDifference BackgroundConnection
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence
open scoped BigOperators ContDiff Manifold Topology NNReal Matrix.Norms.Operator

/-- The connection coefficient contracted with the velocity of the affine radial path. -/
def radialConnectionMatrix (Γ : CoordinateSpace → Connection) (z v : CoordinateSpace) (t : ℝ) :
    FrameMatrix := ∑ d : Index, v d • connectionMatrix (Γ (z + t • v)) d

/-- Left multiplication by the radial coefficient, as an actual bounded operator on matrices. -/
def radialConnectionOperator (Γ : CoordinateSpace → Connection) (z v : CoordinateSpace) (t : ℝ) :
    FrameMatrix →L[ℝ] FrameMatrix := ContinuousLinearMap.mul ℝ FrameMatrix (radialConnectionMatrix Γ z v t)

theorem radialConnectionOperator_apply (Γ : CoordinateSpace → Connection) (z v : CoordinateSpace)
    (t : ℝ) (E : FrameMatrix) : radialConnectionOperator Γ z v t E = radialConnectionMatrix Γ z v t * E :=
  rfl

theorem norm_radialConnectionMatrix_le (Γ : CoordinateSpace → Connection) (z v : CoordinateSpace)
    (t : ℝ) (C : ℝ≥0) (hΓ : ‖Γ (z + t • v)‖ ≤ C) :
    ‖radialConnectionMatrix Γ z v t‖ ≤ 16 * (C : ℝ) * ‖v‖ := by
  have hterm (d : Index) : ‖v d • connectionMatrix (Γ (z + t • v)) d‖ ≤ ‖v‖ * (4 * (C : ℝ)) := by
    rw [norm_smul]
    have hmat : ‖connectionMatrix (Γ (z + t • v)) d‖ ≤ (4 * C : ℝ≥0) := by
      apply connectionMatrix_norm_le_of_entries
      intro a b
      rw [Real.norm_eq_abs]
      exact (ConnectionError.abs_firstJet_entry_le_norm _ a d b).trans hΓ
    exact mul_le_mul (PiLp.norm_apply_le v d) (by exact_mod_cast hmat) (norm_nonneg _) (norm_nonneg _)
  calc
    ‖radialConnectionMatrix Γ z v t‖ ≤ ∑ d : Index, ‖v d • connectionMatrix (Γ (z + t • v)) d‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d : Index, ‖v‖ * (4 * (C : ℝ)) := Finset.sum_le_sum fun d _ => hterm d
    _ = 16 * (C : ℝ) * ‖v‖ := by simp [Index, nsmul_eq_mul]; ring

/-- The radial coefficient has genuine joint smoothness in displacement and time. -/
theorem contDiffOn_radialConnectionOperator (Γ : CoordinateSpace → Connection) (z : CoordinateSpace)
    (s : Set CoordinateSpace) (hΓ : ∀ a d b, ContDiffOn ℝ ∞ (fun x => Γ x a d b) s) :
    ContDiffOn ℝ ∞ (fun q : CoordinateSpace × ℝ => radialConnectionOperator Γ z q.1 q.2)
      {q : CoordinateSpace × ℝ | z + q.2 • q.1 ∈ s} := by
  let U : Set (CoordinateSpace × ℝ) := {q | z + q.2 • q.1 ∈ s}
  have harg : ContDiff ℝ ∞ (fun q : CoordinateSpace × ℝ => z + q.2 • q.1) :=
    contDiff_const.add (contDiff_snd.smul contDiff_fst)
  have hmat (d : Index) : ContDiffOn ℝ ∞ (fun x => connectionMatrix (Γ x) d) s := by
    have heq : (fun x => connectionMatrix (Γ x) d) = fun x =>
        ∑ a : Index, ∑ b : Index, (Γ x a d b) • (Matrix.single a b 1 : FrameMatrix) := by
      funext x
      simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
        (Matrix.matrix_eq_sum_single (connectionMatrix (Γ x) d))
    rw [heq]
    exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun b _ => (hΓ a d b).smul contDiffOn_const
  change ContDiffOn ℝ ∞ (fun q : CoordinateSpace × ℝ =>
    ContinuousLinearMap.mul ℝ FrameMatrix (∑ d : Index, q.1 d • connectionMatrix (Γ (z + q.2 • q.1)) d)) U
  apply (ContinuousLinearMap.mul ℝ FrameMatrix).contDiff.comp_contDiffOn
  apply ContDiffOn.sum
  intro d _
  have hv : ContDiff ℝ ∞ (fun q : CoordinateSpace × ℝ => q.1 d) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Index => ℝ) d).contDiff.comp contDiff_fst
  exact hv.contDiffOn.smul ((hmat d).comp harg.contDiffOn (fun _ hq => hq))

/-- A frame within one third of the identity is invertible with uniform two-sided bounds. -/
theorem isUnit_and_norm_bounds_of_norm_sub_one_le (F : FrameMatrix) (hF : ‖F - 1‖ ≤ 1 / 3) :
    IsUnit F ∧ ‖F‖ ≤ 2 ∧ ‖F⁻¹‖ ≤ 2 := by
  have hdist : ‖1 - F‖ ≤ 1 / 3 := by rw [norm_sub_rev]; exact hF
  have hunit : IsUnit F := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one (hdist.trans_lt (by norm_num))
  have hOne : ‖(1 : FrameMatrix)‖ ≤ 1 := le_of_eq norm_one
  have hmul : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F ((Matrix.isUnit_iff_isUnit_det F).mp hunit)
  have hInv : F⁻¹ = 1 + (1 - F) * F⁻¹ := by
    rw [sub_mul, one_mul, hmul]
    abel
  have hInvBound : ‖F⁻¹‖ ≤ 1 + (1 / 3) * ‖F⁻¹‖ := by
    calc
      ‖F⁻¹‖ = ‖1 + (1 - F) * F⁻¹‖ := congrArg norm hInv
      _ ≤ ‖(1 : FrameMatrix)‖ + ‖(1 - F) * F⁻¹‖ := norm_add_le _ _
      _ ≤ 1 + (1 / 3) * ‖F⁻¹‖ :=
        add_le_add hOne ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hdist (norm_nonneg _)))
  refine ⟨hunit, ?_, by linarith⟩
  calc
    ‖F‖ = ‖F - 1 + 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖F - 1‖ + ‖(1 : FrameMatrix)‖ := norm_add_le _ _
    _ ≤ 2 := by linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

set_option maxHeartbeats 800000 in
/-- One radius controls the genuine radial coefficients for every input metric and each ray,
    on a time interval containing the whole transport segment. -/
theorem exists_uniform_radial_ball_of_original
    (r : Metric (M := M)) (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n))
    (hs₀ : IsSymmetric g₀) (hs : ∀ n, IsSymmetric (g n))
    (hn₀ : IsNondegenerate g₀) (hn : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g g₀)
    (hb : ∀ S : Set M, IsCompact S → ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      MeasureTheory.eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - g₀ m)) ⊤
        ((ManifoldVolume.geometricMeasure g₀).restrict S) ≤ ENNReal.ofReal D)
    (p : M) (z : CoordinateSpace) (hz : z ∈ (chartAt CoordinateSpace p).target) :
    ∃ R : ℝ, 0 < R ∧ closedBall z (2 * R) ⊆ (chartAt CoordinateSpace p).target ∧
      ∀ n (v : CoordinateSpace), ‖v‖ ≤ R → ∀ t : ℝ, |t| ≤ 2 →
        ‖radialConnectionOperator (computedConnection (coordinateBilinear (g n) p)) z v t‖ ≤ 1 / 4 := by
  obtain ⟨R₀, hR₀, hChart⟩ := Metric.isOpen_iff.mp (chartAt CoordinateSpace p).open_target z hz
  have hSmallChart := (closedBall_subset_ball (show R₀ / 2 < R₀ by linarith)).trans hChart
  obtain ⟨C₀, hC₀, hΓ⟩ := computedConnection_uniform_bound_of_original r g₀ g h₀ hg hs₀ hs hn₀ hn hconv hb
    p (closedBall z (R₀ / 2)) (isCompact_closedBall _ _) hSmallChart
  let C : ℝ≥0 := ⟨C₀, hC₀⟩
  let R := min (R₀ / 4) (1 / (64 * (C₀ + 1)))
  have hRchart : R ≤ R₀ / 4 := min_le_left _ _
  have hRpos : 0 < R := lt_min (by positivity) (by positivity)
  refine ⟨R, hRpos, (closedBall_subset_closedBall (by linarith)).trans hSmallChart, ?_⟩
  intro n v hv t ht
  have hx : z + t • v ∈ closedBall z (R₀ / 2) := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have := mul_le_mul ht hv (norm_nonneg v) (le_of_lt (by norm_num : (0 : ℝ) < 2))
    linarith
  have hvSmall : ‖v‖ ≤ 1 / (64 * (C₀ + 1)) := hv.trans (min_le_right _ _)
  have hvProduct := (le_div_iff₀ (show 0 < 64 * (C₀ + 1) by positivity)).mp hvSmall
  have hBound : 16 * (C : ℝ) * ‖v‖ ≤ 1 / 4 := by
    change 16 * C₀ * ‖v‖ ≤ 1 / 4
    nlinarith [norm_nonneg v]
  exact (ContinuousLinearMap.opNorm_mul_apply_le ℝ _ _).trans
    ((norm_radialConnectionMatrix_le _ z v t C (hΓ n _ hx)).trans hBound)

end Burnett.FlatRigidity

open Filter Set
open scoped Topology ContDiff

namespace Burnett.FlatFrame

variable {T V E : Type*} [TopologicalSpace T] [CompactSpace T]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]

private def pointwiseMap (D : C(T, V →L[ℝ] E)) : V →ₗ[ℝ] C(T, E) where
  toFun v := ⟨fun t => D t v, (ContinuousLinearMap.apply ℝ E v).continuous.comp D.continuous⟩
  map_add' x y := ContinuousMap.ext fun t => map_add (D t) x y
  map_smul' c x := ContinuousMap.ext fun t => map_smul (D t) c x

private theorem pointwiseMap_bound (D : C(T, V →L[ℝ] E)) (v : V) :
    ‖pointwiseMap D v‖ ≤ ‖D‖ * ‖v‖ := by
  apply (ContinuousMap.norm_le (pointwiseMap D v) (mul_nonneg (norm_nonneg D) (norm_nonneg v))).mpr
  intro t
  exact ((D t).le_opNorm v).trans (mul_le_mul_of_nonneg_right (D.norm_coe_le_norm t) (norm_nonneg v))

/-- Turn a continuous family of continuous linear maps into a map into continuous functions. -/
def pointwiseLinear (D : C(T, V →L[ℝ] E)) : V →L[ℝ] C(T, E) :=
  (pointwiseMap D).mkContinuous ‖D‖ (pointwiseMap_bound D)

@[simp] theorem pointwiseLinear_apply (D : C(T, V →L[ℝ] E)) (v : V) (t : T) :
    pointwiseLinear D v t = D t v := rfl

theorem norm_pointwiseLinear_le (D : C(T, V →L[ℝ] E)) : ‖pointwiseLinear D‖ ≤ ‖D‖ :=
  (pointwiseLinear D).opNorm_le_bound (norm_nonneg D) (pointwiseMap_bound D)

/-- The passage from a family of pointwise derivatives to a function-space derivative is linear. -/
def liftPointwise : C(T, V →L[ℝ] E) →L[ℝ] (V →L[ℝ] C(T, E)) := by
  let L : C(T, V →L[ℝ] E) →ₗ[ℝ] (V →L[ℝ] C(T, E)) :=
    { toFun := fun D => pointwiseLinear D
      map_add' := fun A B => ContinuousLinearMap.ext fun v => ContinuousMap.ext fun t => rfl
      map_smul' := fun c A => ContinuousLinearMap.ext fun v => ContinuousMap.ext fun t => rfl }
  refine LinearMap.mkContinuous (E := C(T, V →L[ℝ] E)) (F := V →L[ℝ] C(T, E)) L 1 ?_
  intro D
  show ‖pointwiseLinear D‖ ≤ 1 * ‖D‖
  simpa only [one_mul] using norm_pointwiseLinear_le D

@[simp] theorem liftPointwise_apply (D : C(T, V →L[ℝ] E)) (v : V) (t : T) :
    (liftPointwise (T := T) (V := V) (E := E)) D v t = D t v := rfl

theorem hasFDerivAt_of_pointwise_on_open {U : Set V} (hU : IsOpen U)
    (f : V → C(T, E)) (D : V → C(T, V →L[ℝ] E)) {v : V} (hv : v ∈ U)
    (hD : ContinuousAt D v)
    (hf : ∀ w ∈ U, ∀ t : T, HasFDerivAt (fun x => f x t) (D w t) w) :
    HasFDerivAt f ((liftPointwise (T := T) (V := V) (E := E)) (D v)) v := by
  rw [HasFDerivAt, hasFDerivAtFilter_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨a, ha, haU⟩ := Metric.isOpen_iff.mp hU v hv
  obtain ⟨b, hb, hDb⟩ := (Metric.continuousAt_iff (f := D) (a := v)).mp hD ε hε
  let ρ := min a b
  have hρ : 0 < ρ := lt_min ha hb
  have hρU : Metric.ball v ρ ⊆ U := (Metric.ball_subset_ball (min_le_left a b)).trans haU
  filter_upwards [Metric.ball_mem_nhds v hρ] with w hw
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg (w - v)))).mpr
  intro t
  have hdif (z : V) (hz : z ∈ Metric.ball v ρ) :
      HasFDerivWithinAt (fun x => f x t - D v t x) (D z t - D v t) (Metric.ball v ρ) z :=
    ((hf z (hρU hz) t).sub (D v t).hasFDerivAt).hasFDerivWithinAt
  have hbound (z : V) (hz : z ∈ Metric.ball v ρ) : ‖D z t - D v t‖ ≤ ε := by
    rw [← dist_eq_norm (D z t) (D v t)]
    exact (ContinuousMap.dist_apply_le_dist (f := D z) (g := D v) t).trans
      (hDb (Metric.mem_ball.mp ((Metric.ball_subset_ball (min_le_right a b)) hz))).le
  have h := (convex_ball v ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le hdif hbound
    (Metric.mem_ball_self hρ) hw
  have heq : f w t - f v t - D v t (w - v) =
      (f w t - D v t w) - (f v t - D v t v) := by
    rw [map_sub]
    abel
  simp only [ContinuousMap.sub_apply, liftPointwise_apply]
  rw [heq]
  exact h

theorem contDiffOn_one_of_pointwise_on_open {U : Set V} (hU : IsOpen U)
    (f : V → C(T, E)) (D : V → C(T, V →L[ℝ] E))
    (hD : ContinuousOn D U)
    (hf : ∀ w ∈ U, ∀ t : T, HasFDerivAt (fun x => f x t) (D w t) w) :
    ContDiffOn ℝ 1 f U := by
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 0) hU.uniqueDiffOn).mpr
  let L := liftPointwise (T := T) (V := V) (E := E)
  refine ⟨by simp, L ∘ D, contDiffOn_zero.mpr (L.continuous.comp_continuousOn hD), ?_⟩
  intro v hv
  exact (hasFDerivAt_of_pointwise_on_open hU f D hv (hD.continuousAt (hU.mem_nhds hv)) hf).hasFDerivWithinAt

theorem contDiffOn_one_of_joint_pointwise_on_open {U : Set V} (hU : IsOpen U)
    (f : V → C(T, E)) (D : V → C(T, V →L[ℝ] E))
    (hD : ContinuousOn (Function.uncurry fun v t => D v t) (U ×ˢ (univ : Set T)))
    (hf : ∀ w ∈ U, ∀ t : T, HasFDerivAt (fun x => f x t) (D w t) w) :
    ContDiffOn ℝ 1 f U :=
  contDiffOn_one_of_pointwise_on_open hU f D (ContinuousMap.continuousOn_of_continuousOn_uncurry D hD) hf

end Burnett.FlatFrame

namespace Burnett.FlatFrame

variable {V W E : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedAddCommGroup E]

/-- Restrict a jointly continuous function to each compact-parameter slice.
Outside the specified open-parameter set the resulting function is extended by zero. -/
def curryOn {U : Set V} {K : Set W} (f : V × W → E)
    (hf : ContinuousOn f (U ×ˢ K)) (v : V) : C(K, E) := by
  classical
  exact if hv : v ∈ U then
    ⟨fun t => f (v, t), hf.comp_continuous
      (continuous_const.prodMk continuous_subtype_val) (fun t => ⟨hv, t.property⟩)⟩
  else 0

theorem curryOn_apply {U : Set V} {K : Set W} (f : V × W → E)
    (hf : ContinuousOn f (U ×ˢ K)) {v : V} (hv : v ∈ U) (t : K) :
    curryOn f hf v t = f (v, t) := by
  simp only [curryOn, dif_pos hv]
  rfl

theorem continuousOn_curryOn {U : Set V} {K : Set W} (f : V × W → E)
    (hf : ContinuousOn f (U ×ˢ K)) : ContinuousOn (curryOn f hf) U := by
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  have hc : Continuous (fun p : V × K => (p.1, (p.2 : W))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have h : ContinuousOn (fun p : V × K => f (p.1, p.2)) (U ×ˢ (univ : Set K)) :=
    hf.comp hc.continuousOn (fun p hp => ⟨hp.1, p.2.property⟩)
  exact h.congr (fun p hp => curryOn_apply f hf hp.1 p.2)

variable [NormedSpace ℝ V] [NormedSpace ℝ W] [NormedSpace ℝ E]

/-- The derivative of a function on a product, restricted to displacement directions. -/
def spatialDerivative (f : V × W → E) (p : V × W) : V →L[ℝ] E :=
  (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ V W)

theorem contDiffOn_spatialDerivative {U : Set (V × W)} (hU : IsOpen U)
    (f : V × W → E) {n : WithTop ℕ∞} (hf : ContDiffOn ℝ (n + 1) f U) :
    ContDiffOn ℝ n (spatialDerivative f) U := by
  let P : ((V × W) →L[ℝ] E) →L[ℝ] (V →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ V (V × W) E).flip (ContinuousLinearMap.inl ℝ V W)
  exact P.contDiff.comp_contDiffOn (hf.fderiv_of_isOpen hU le_rfl)

theorem hasFDerivAt_curryOn_evaluation {U : Set V} {K : Set W} {Ω : Set (V × W)}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hsubset : U ×ˢ K ⊆ Ω)
    (f : V × W → E) (hf : ContDiffOn ℝ 1 f Ω) {v : V} (hv : v ∈ U) (t : K) :
    HasFDerivAt (fun x => curryOn f (hf.continuousOn.mono hsubset) x t)
      (spatialDerivative f (v, t)) v := by
  have hpoint : (v, (t : W)) ∈ Ω := hsubset ⟨hv, t.property⟩
  have hdf := ((hf.differentiableOn le_rfl) _ hpoint).differentiableAt (hΩ.mem_nhds hpoint)
  have hin : HasFDerivAt (fun x : V => (x, (t : W))) (ContinuousLinearMap.inl ℝ V W) v := by
    exact (hasFDerivAt_id v).prodMk (hasFDerivAt_const (t : W) v)
  apply (hdf.hasFDerivAt.comp v hin).congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hv] with x hx
  exact curryOn_apply f (hf.continuousOn.mono hsubset) hx t

theorem contDiffOn_one_curryOn_of_joint {U : Set V} {K : Set W} [CompactSpace K]
    {Ω : Set (V × W)} (hU : IsOpen U) (hΩ : IsOpen Ω) (hsubset : U ×ˢ K ⊆ Ω)
    (f : V × W → E) (hf : ContDiffOn ℝ 1 f Ω) :
    ContDiffOn ℝ 1 (curryOn f (hf.continuousOn.mono hsubset)) U := by
  have hc : ContDiffOn ℝ 0 (spatialDerivative f) Ω :=
    contDiffOn_spatialDerivative hΩ f (by simpa only [zero_add] using hf)
  let D := curryOn (spatialDerivative f) (hc.continuousOn.mono hsubset)
  apply contDiffOn_one_of_pointwise_on_open hU _ D
    (continuousOn_curryOn (spatialDerivative f) (hc.continuousOn.mono hsubset))
  intro v hv t
  have hd := hasFDerivAt_curryOn_evaluation hU hΩ hsubset f hf hv t
  rw [show D v t = spatialDerivative f (v, t) from
    curryOn_apply (spatialDerivative f) (hc.continuousOn.mono hsubset) hv t]
  exact hd

end Burnett.FlatFrame

namespace Burnett.FlatRigidity

open Set Metric Burnett.RicciSymbol Burnett.Geometry
open Burnett.FlatFrame Burnett.Geometry.FlatRigidity ConnectionDifference BackgroundConnection
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence
open scoped ContDiff Manifold Topology Matrix.Norms.Operator

abbrev RadialTimes := Icc (0 : ℝ) 1
abbrev RadialCoefficientPaths := C(RadialTimes, FrameMatrix →L[ℝ] FrameMatrix)

/-- The genuine coefficient path, smoothly parameterized by the displacement of the ray. -/
theorem exists_radialCoefficientPaths (Γ : CoordinateSpace → Connection) (z : CoordinateSpace)
    (U s : Set CoordinateSpace) (hU : IsOpen U) (hs : IsOpen s)
    (hΓ : ∀ a d b, ContDiffOn ℝ ∞ (fun x => Γ x a d b) s)
    (hInside : ∀ v ∈ U, ∀ t ∈ RadialTimes, z + t • v ∈ s) :
    ∃ A : CoordinateSpace → RadialCoefficientPaths, ContDiffOn ℝ 1 A U ∧
      ∀ v ∈ U, ∀ t : RadialTimes, A v t = radialConnectionOperator Γ z v (t : ℝ) := by
  let f (p : CoordinateSpace × ℝ) := radialConnectionOperator Γ z p.1 p.2
  let Ω : Set (CoordinateSpace × ℝ) := {p | z + p.2 • p.1 ∈ s}
  have hArg : Continuous (fun p : CoordinateSpace × ℝ => z + p.2 • p.1) :=
    continuous_const.add (continuous_snd.smul continuous_fst)
  have hΩ : IsOpen Ω := hs.preimage hArg
  have hsub : U ×ˢ RadialTimes ⊆ Ω := fun p hp => hInside p.1 hp.1 p.2 hp.2
  have hf : ContDiffOn ℝ 1 f Ω := (contDiffOn_infty.mp (contDiffOn_radialConnectionOperator Γ z s hΓ)) 1
  refine ⟨curryOn f (hf.continuousOn.mono hsub), contDiffOn_one_curryOn_of_joint hU hΩ hsub f hf, ?_⟩
  intro v hv t
  exact curryOn_apply f (hf.continuousOn.mono hsub) hv t

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- One ball and C¹ coefficient families for the actual connection of every metric in the sequence. -/
theorem exists_uniform_radialCoefficientPaths_of_original
    (r : Metric (M := M)) (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n))
    (hs₀ : IsSymmetric g₀) (hs : ∀ n, IsSymmetric (g n))
    (hn₀ : IsNondegenerate g₀) (hn : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g g₀)
    (hb : ∀ S : Set M, IsCompact S → ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      MeasureTheory.eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - g₀ m)) ⊤
        ((ManifoldVolume.geometricMeasure g₀).restrict S) ≤ ENNReal.ofReal D)
    (p : M) (z : CoordinateSpace) (hz : z ∈ (chartAt CoordinateSpace p).target) :
    ∃ R : ℝ, 0 < R ∧ closedBall z (2 * R) ⊆ (chartAt CoordinateSpace p).target ∧
      ∃ A : ℕ → CoordinateSpace → RadialCoefficientPaths,
        (∀ n, ContDiffOn ℝ 1 (A n) (ball 0 R)) ∧
        (∀ n v, v ∈ ball 0 R → ‖A n v‖ ≤ 1 / 4) ∧
        ∀ n v, v ∈ ball 0 R → ∀ t : RadialTimes,
          A n v t = radialConnectionOperator (computedConnection (coordinateBilinear (g n) p)) z v (t : ℝ) := by
  obtain ⟨R, hR, hChart, hCap⟩ := exists_uniform_radial_ball_of_original r g₀ g h₀ hg hs₀ hs hn₀ hn hconv hb p z hz
  let s := (chartAt CoordinateSpace p).target
  let Γ (n : ℕ) := computedConnection (coordinateBilinear (g n) p)
  have hInside (v : CoordinateSpace) (hv : v ∈ ball 0 R) (t : ℝ) (ht : t ∈ RadialTimes) : z + t • v ∈ s := by
    apply hChart
    have hv' : ‖v‖ < R := by simpa only [mem_ball, dist_zero_right] using hv
    have ht' : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg v) ht').trans (by linarith)
  have hΓ (n : ℕ) (a d b : Index) : ContDiffOn ℝ ∞ (fun x => Γ n x a d b) s := by
    have h := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection (g n) (hg n) (hn n) p
    exact contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp h a) d) b
  choose A hDiff hEval using fun n => exists_radialCoefficientPaths (Γ n) z (ball 0 R) s isOpen_ball
    (chartAt CoordinateSpace p).open_target (hΓ n) hInside
  refine ⟨R, hR, hChart, A, hDiff, ?_, hEval⟩
  intro n v hv
  apply (ContinuousMap.norm_le _ (show (0 : ℝ) ≤ 1 / 4 by norm_num)).mpr
  intro t
  have hv' : ‖v‖ ≤ R := (show ‖v‖ < R by simpa only [mem_ball, dist_zero_right] using hv).le
  have ht' : |(t : ℝ)| ≤ 2 := (abs_le.mpr ⟨by linarith [t.property.1], t.property.2⟩ : |(t : ℝ)| ≤ 1).trans (by norm_num)
  simpa only [hEval n v hv t] using hCap n v hv' (t : ℝ) ht'

end Burnett.FlatRigidity

namespace Burnett.Geometry.FlatRigidity

open Filter Matrix Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open scoped BigOperators ContDiff Matrix.Norms.Operator Topology

abbrev RadialParameter := ℝ × CoordinateSpace

def radialPoint (c : CoordinateSpace) (p : RadialParameter) : CoordinateSpace := c + p.1 • p.2

def radialGenerator (c : CoordinateSpace) (Γ : CoordinateSpace → Connection) (p : RadialParameter) : FrameMatrix :=
  ∑ a : Index, p.2 a • connectionMatrix (Γ (radialPoint c p)) a

private theorem matrix_entry_norm_le_operator (M : FrameMatrix) (i j : Index) : ‖M i j‖ ≤ ‖M‖ := by
  have h : ‖M i j‖₊ ≤ ∑ k, ‖M i k‖₊ :=
    Finset.single_le_sum (fun k _ => zero_le ‖M i k‖₊) (Finset.mem_univ j)
  rw [Matrix.linfty_opNorm_def]
  exact_mod_cast h.trans (Finset.le_sup (f := fun i => ∑ k, ‖M i k‖₊) (Finset.mem_univ i))

private def frameEntryCLM (i j : Index) : FrameMatrix →L[ℝ] ℝ :=
  let L : FrameMatrix →ₗ[ℝ] ℝ := ⟨⟨fun M => M i j, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  L.mkContinuous 1 (by intro M; simpa using matrix_entry_norm_le_operator M i j)

theorem contDiffOn_frameMatrix_of_entries {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ω : Set X} {F : X → FrameMatrix} {k : WithTop ℕ∞}
    (h : ∀ i j : Index, ContDiffOn ℝ k (fun x => F x i j) Ω) : ContDiffOn ℝ k F Ω := by
  have he : F = fun x => ∑ i : Index, ∑ j : Index, F x i j • (Matrix.single i j 1 : FrameMatrix) := by
    funext x
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single (F x)
  rw [he]
  exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (h i j).smul contDiffOn_const

theorem fderiv_frameMatrix_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : X → FrameMatrix} {x : X} (hF : DifferentiableAt ℝ F x) (v : X) (i j : Index) :
    fderiv ℝ F x v i j = fderiv ℝ (fun y => F y i j) x v := by
  have hh := (frameEntryCLM i j).hasFDerivAt.comp x hF.hasFDerivAt
  exact (congrArg (fun L : X →L[ℝ] ℝ => L v) hh.fderiv).symm

theorem frameCoordinateJet_eq_fderiv_matrix {E : CoordinateSpace → FrameMatrix} {x : CoordinateSpace}
    (hE : DifferentiableAt ℝ E x) (d : Index) :
    frameCoordinateJet E x d = fderiv ℝ E x (EuclideanSpace.single d 1) := by
  ext a i
  exact (fderiv_frameMatrix_entry hE _ a i).symm

private theorem radialPoint_hasFDerivAt (c : CoordinateSpace) (p : RadialParameter) :
    HasFDerivAt (radialPoint c)
      (p.1 • (ContinuousLinearMap.snd ℝ ℝ CoordinateSpace) +
        (ContinuousLinearMap.fst ℝ ℝ CoordinateSpace).smulRight p.2) p := by
  simpa only [radialPoint, zero_add] using (hasFDerivAt_const c p).add
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).fun_smul (hasFDerivAt_snd (𝕜 := ℝ) (p := p)))

private theorem fderiv_radialConnection_apply
    (c : CoordinateSpace) (Γ : CoordinateSpace → Connection) (p : RadialParameter) (a : Index)
    (hΓ : DifferentiableAt ℝ (fun y => connectionMatrix (Γ y) a) (radialPoint c p)) (w : RadialParameter) :
    fderiv ℝ (fun q => connectionMatrix (Γ (radialPoint c q)) a) p w =
      fderiv ℝ (fun y => connectionMatrix (Γ y) a) (radialPoint c p) (p.1 • w.2 + w.1 • p.2) := by
  change fderiv ℝ ((fun y => connectionMatrix (Γ y) a) ∘ radialPoint c) p w = _
  rw [(hΓ.hasFDerivAt.comp p (radialPoint_hasFDerivAt c p)).fderiv]
  rfl

private theorem fderiv_connectionMatrix_basis (Γ : CoordinateSpace → Connection) (x : CoordinateSpace)
    (a d : Index) (hΓ : DifferentiableAt ℝ (fun y => connectionMatrix (Γ y) a) x) :
    fderiv ℝ (fun y => connectionMatrix (Γ y) a) x (EuclideanSpace.single d 1) =
      connectionMatrixDerivative Γ x d a := by
  ext i j
  exact fderiv_frameMatrix_entry hΓ _ i j

theorem radialConnection_time_fderiv (c : CoordinateSpace) (Γ : CoordinateSpace → Connection)
    (p : RadialParameter) (i : Index)
    (hΓ : DifferentiableAt ℝ (fun y => connectionMatrix (Γ y) i) (radialPoint c p)) :
    fderiv ℝ (fun q => connectionMatrix (Γ (radialPoint c q)) i) p (1, 0) =
      ∑ a : Index, p.2 a • connectionMatrixDerivative Γ (radialPoint c p) a i := by
  rw [fderiv_radialConnection_apply c Γ p i hΓ]
  simp only [smul_zero, one_smul, zero_add]
  let e := (EuclideanSpace.basisFun Index ℝ).toBasis
  have hrepr (a : Index) : e.repr p.2 a = p.2 a := rfl
  have hb (a : Index) : e a = EuclideanSpace.single a 1 := EuclideanSpace.basisFun_apply _ _ a
  let L := fderiv ℝ (fun y => connectionMatrix (Γ y) i) (radialPoint c p)
  have he := (congrArg L (e.sum_repr p.2)).symm
  simpa only [L, map_sum, map_smul, hrepr, hb, fderiv_connectionMatrix_basis Γ _ i _ hΓ] using he

private theorem radialConnection_transverse_fderiv (c : CoordinateSpace) (Γ : CoordinateSpace → Connection)
    (p : RadialParameter) (a i : Index)
    (hΓ : DifferentiableAt ℝ (fun y => connectionMatrix (Γ y) a) (radialPoint c p)) :
    fderiv ℝ (fun q => connectionMatrix (Γ (radialPoint c q)) a) p (0, EuclideanSpace.single i 1) =
      p.1 • connectionMatrixDerivative Γ (radialPoint c p) i a := by
  rw [fderiv_radialConnection_apply c Γ p a hΓ]
  simp only [zero_smul, add_zero, map_smul, fderiv_connectionMatrix_basis Γ _ a _ hΓ]

private def radialComponent (a : Index) : RadialParameter →L[ℝ] ℝ :=
  (EuclideanSpace.proj a).comp (ContinuousLinearMap.snd ℝ ℝ CoordinateSpace)

theorem radialGenerator_transverse_fderiv (c : CoordinateSpace) (Γ : CoordinateSpace → Connection)
    (p : RadialParameter) (i : Index)
    (hΓ : ∀ a : Index, DifferentiableAt ℝ (fun y => connectionMatrix (Γ y) a) (radialPoint c p)) :
    fderiv ℝ (radialGenerator c Γ) p (0, EuclideanSpace.single i 1) =
      connectionMatrix (Γ (radialPoint c p)) i +
        p.1 • ∑ a : Index, p.2 a • connectionMatrixDerivative Γ (radialPoint c p) i a := by
  have h (a : Index) : DifferentiableAt ℝ (fun q => connectionMatrix (Γ (radialPoint c q)) a) p :=
    (hΓ a).comp p (radialPoint_hasFDerivAt c p).differentiableAt
  have hprod (a : Index) : DifferentiableAt ℝ
      (fun q : RadialParameter => q.2 a • connectionMatrix (Γ (radialPoint c q)) a) p :=
    (radialComponent a).differentiableAt.fun_smul (h a)
  have hc (a : Index) := (radialComponent a).hasFDerivAt (x := p)
  unfold radialGenerator
  rw [fderiv_fun_sum (u := Finset.univ) (fun a _ => hprod a), ContinuousLinearMap.sum_apply]
  have hder (a : Index) : fderiv ℝ (fun q : RadialParameter => q.2 a •
      connectionMatrix (Γ (radialPoint c q)) a) p (0, EuclideanSpace.single i 1) =
    (p.2 a • (p.1 • connectionMatrixDerivative Γ (radialPoint c p) i a)) +
      (if i = a then connectionMatrix (Γ (radialPoint c p)) a else 0) := by
    change fderiv ℝ (fun q => radialComponent a q • connectionMatrix (Γ (radialPoint c q)) a) p
      (0, EuclideanSpace.single i 1) = _
    rw [((hc a).fun_smul (h a).hasFDerivAt).fderiv, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      radialConnection_transverse_fderiv c Γ p a i (hΓ a)]
    have hEntry : radialComponent a (0, EuclideanSpace.single i 1) = if i = a then 1 else 0 := by
      simp [radialComponent, EuclideanSpace.single_apply, eq_comm]
    rw [hEntry]
    split <;> simp [radialComponent]
  simp_rw [hder]
  rw [Finset.sum_add_distrib]
  have hdiag : (∑ a : Index, if i = a then connectionMatrix (Γ (radialPoint c p)) a else 0) =
      connectionMatrix (Γ (radialPoint c p)) i := by simp
  rw [hdiag, add_comm]
  rw [Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_comm (p.2 a) p.1]

end Burnett.Geometry.FlatRigidity

namespace Burnett.Geometry.FlatRigidity

open Matrix Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open scoped BigOperators Matrix.Norms.Operator

private theorem small_linear_ode_bound {E D : ℝ → FrameMatrix} {C : ℝ} (hC : 0 ≤ C) (hC' : C < 1)
    (hE : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt E (D t) t)
    (hD : ∀ t ∈ Icc (0 : ℝ) 1, ‖D t‖ ≤ C * ‖E t‖) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖E t‖ ≤ ‖E 0‖ / (1 - C) ∧ ‖E t - E 0‖ ≤ C * (‖E 0‖ / (1 - C)) := by
  have hc : ContinuousOn E (Icc (0 : ℝ) 1) := fun t ht => (hE t ht).continuousAt.continuousWithinAt
  obtain ⟨s, hs, hMax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, by norm_num⟩ hc.norm
  have hSup (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) : ‖E a‖ ≤ ‖E s‖ := hMax ha
  have hb (a : ℝ) (ha : a ∈ Ico (0 : ℝ) 1) : ‖D a‖ ≤ C * ‖E s‖ :=
    (hD a (Ico_subset_Icc_self ha)).trans (mul_le_mul_of_nonneg_left (hSup a (Ico_subset_Icc_self ha)) hC)
  have hd (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) : ‖E a - E 0‖ ≤ C * ‖E s‖ := by
    have hh := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun b ht => (hE b ht).hasDerivWithinAt) hb a ha
    exact (by simpa only [sub_zero] using hh : ‖E a - E 0‖ ≤ C * ‖E s‖ * a).trans
      (mul_le_of_le_one_right (mul_nonneg hC (norm_nonneg _)) ha.2)
  have hsB : ‖E s‖ ≤ ‖E 0‖ / (1 - C) := by
    have h := norm_sub_le (E s - E 0) (-E 0)
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at h
    apply (le_div_iff₀ (sub_pos.mpr hC')).mpr
    linarith [hd s hs]
  exact ⟨(hSup t ht).trans hsB, (hd t ht).trans (mul_le_mul_of_nonneg_left hsB hC)⟩

theorem radialGenerator_norm_le (c : CoordinateSpace) (Γ : CoordinateSpace → Connection)
    (p : RadialParameter) {C : ℝ}
    (h : ∀ a : Index, ‖connectionMatrix (Γ (radialPoint c p)) a‖ ≤ C) :
    ‖radialGenerator c Γ p‖ ≤ 4 * ‖p.2‖ * C := by
  unfold radialGenerator
  calc
    _ ≤ ∑ a : Index, ‖p.2 a • connectionMatrix (Γ (radialPoint c p)) a‖ := norm_sum_le _ _
    _ ≤ ∑ _a : Index, ‖p.2‖ * C := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le p.2 a) (h a) (norm_nonneg _) (norm_nonneg _)
    _ = 4 * ‖p.2‖ * C := by simp [Index, mul_assoc]

theorem radialFrame_uniform_operator_bounds (c : CoordinateSpace) (Γ : CoordinateSpace → Connection)
    (v : CoordinateSpace) (E : ℝ → FrameMatrix)
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, ‖radialGenerator c Γ (t, v)‖ ≤ 1 / 4)
    (hE : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt E (-(radialGenerator c Γ (t, v) * E t)) t)
    (h0 : E 0 = 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖E t‖ ≤ 2 ∧ IsUnit (E t) ∧ ‖(E t)⁻¹‖ ≤ 2 := by
  have hb (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : ‖-(radialGenerator c Γ (s, v) * E s)‖ ≤ (1 / 4 : ℝ) * ‖E s‖ := by
    rw [norm_neg]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hA s hs) (norm_nonneg _))
  have hs := small_linear_ode_bound (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num) hE hb t ht
  rw [h0, norm_one] at hs
  have he : ‖1 - E t‖ ≤ 1 / 2 := by
    rw [norm_sub_rev]
    exact hs.2.trans (by norm_num)
  have hi : IsUnit (E t) := by
    have hh := isUnit_one_sub_of_norm_lt_one (he.trans_lt (by norm_num))
    simpa only [sub_sub_cancel] using hh
  refine ⟨hs.1.trans (by norm_num), hi, ?_⟩
  have hM : E t * (E t)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hi)
  have hEq : (1 - E t) * (E t)⁻¹ + 1 = (E t)⁻¹ := by rw [sub_mul, one_mul, hM, sub_add_cancel]
  have hle : ‖(E t)⁻¹‖ ≤ (1 / 2 : ℝ) * ‖(E t)⁻¹‖ + 1 := by
    calc
      _ = ‖(1 - E t) * (E t)⁻¹ + 1‖ := congrArg norm hEq.symm
      _ ≤ ‖(1 - E t) * (E t)⁻¹‖ + ‖(1 : FrameMatrix)‖ := norm_add_le _ _
      _ ≤ (1 / 2 : ℝ) * ‖(E t)⁻¹‖ + 1 := by
        rw [norm_one]
        exact add_le_add_right ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))) _
  linarith

end Burnett.Geometry.FlatRigidity

namespace Burnett.Geometry.FlatRigidity

open Filter Matrix Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open scoped BigOperators ContDiff Matrix.Norms.Operator Topology

private theorem hasDerivAt_matrix_time_slice {F : RadialParameter → FrameMatrix} {t : ℝ} {v : CoordinateSpace}
    (hF : DifferentiableAt ℝ F (t, v)) :
    HasDerivAt (fun s => F (s, v)) (fderiv ℝ F (t, v) (1, 0)) t := by
  have h : HasDerivAt (fun s : ℝ => (s, v)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t v)
  exact hF.hasFDerivAt.comp_hasDerivAt t h

private theorem sum_radialCurvature (c : CoordinateSpace) (Γ : CoordinateSpace → Connection)
    (p : RadialParameter) (i : Index) :
    (∑ a : Index, p.2 a • coordinateRiemann Γ (radialPoint c p) a i) =
      (∑ a : Index, p.2 a • connectionMatrixDerivative Γ (radialPoint c p) a i) -
        (∑ a : Index, p.2 a • connectionMatrixDerivative Γ (radialPoint c p) i a) +
        radialGenerator c Γ p * connectionMatrix (Γ (radialPoint c p)) i -
        connectionMatrix (Γ (radialPoint c p)) i * radialGenerator c Γ p := by
  simp only [coordinateRiemann, smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  unfold radialGenerator
  rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]

def radialFrameDefect (c : CoordinateSpace) (Γ : CoordinateSpace → Connection) (v : CoordinateSpace)
    (i : Index) (E V : ℝ → FrameMatrix) (t : ℝ) : FrameMatrix :=
  V t + t • (connectionMatrix (Γ (radialPoint c (t, v))) i * E t)

theorem radialFrameDefect_hasDerivAt (c : CoordinateSpace) (Γ : CoordinateSpace → Connection)
    (v : CoordinateSpace) (i : Index) (E V : ℝ → FrameMatrix) (t : ℝ)
    (hΓ : ∀ a : Index, DifferentiableAt ℝ (fun y => connectionMatrix (Γ y) a) (radialPoint c (t, v)))
    (hE : HasDerivAt E (-(radialGenerator c Γ (t, v) * E t)) t)
    (hV : HasDerivAt V (-(fderiv ℝ (radialGenerator c Γ) (t, v) (0, EuclideanSpace.single i 1) * E t +
      radialGenerator c Γ (t, v) * V t)) t) :
    HasDerivAt (radialFrameDefect c Γ v i E V)
      (-(radialGenerator c Γ (t, v) * radialFrameDefect c Γ v i E V t) +
        t • ((∑ a : Index, v a • coordinateRiemann Γ (radialPoint c (t, v)) a i) * E t)) t := by
  let A := radialGenerator c Γ (t, v)
  let G := fun p => connectionMatrix (Γ (radialPoint c p)) i
  let D := ∑ a : Index, v a • connectionMatrixDerivative Γ (radialPoint c (t, v)) a i
  let B := ∑ a : Index, v a • connectionMatrixDerivative Γ (radialPoint c (t, v)) i a
  have hGd : DifferentiableAt ℝ G (t, v) := (hΓ i).comp _ (radialPoint_hasFDerivAt c (t, v)).differentiableAt
  have hG : HasDerivAt (fun s => G (s, v)) D t := by
    convert hasDerivAt_matrix_time_slice hGd using 1
    exact (radialConnection_time_fderiv c Γ (t, v) i (hΓ i)).symm
  have hV' : HasDerivAt V (-((G (t, v) + t • B) * E t + A * V t)) t := by
    rw [radialGenerator_transverse_fderiv c Γ (t, v) i hΓ] at hV
    exact hV
  have hProd := (hasDerivAt_id t).fun_smul (hG.fun_mul hE)
  convert hV'.add hProd using 1
  symm
  change -((G (t, v) + t • B) * E t + A * V t) +
      (t • (D * E t + G (t, v) * (-(A * E t))) + 1 • (G (t, v) * E t)) =
    -(A * (V t + t • (G (t, v) * E t))) +
      t • ((∑ a : Index, v a • coordinateRiemann Γ (radialPoint c (t, v)) a i) * E t)
  rw [sum_radialCurvature c Γ (t, v) i]
  change -((G (t, v) + t • B) * E t + A * V t) +
      (t • (D * E t + G (t, v) * (-(A * E t))) + 1 • (G (t, v) * E t)) =
    -(A * (V t + t • (G (t, v) * E t))) + t • ((D - B + A * G (t, v) - G (t, v) * A) * E t)
  simp only [add_mul, sub_mul, mul_add, mul_neg, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    smul_add, smul_sub, one_smul, mul_assoc, smul_neg]
  abel

theorem radialFrameDefect_eq_zero_of_flat (c : CoordinateSpace) (Γ : CoordinateSpace → Connection)
    (v : CoordinateSpace) (i : Index) (E V : ℝ → FrameMatrix) (M : ℝ)
    (hΓ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a : Index,
      DifferentiableAt ℝ (fun y => connectionMatrix (Γ y) a) (radialPoint c (t, v)))
    (hM : M < 1)
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, ‖radialGenerator c Γ (t, v)‖ ≤ M)
    (hE : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt E (-(radialGenerator c Γ (t, v) * E t)) t)
    (hV : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt V (-(fderiv ℝ (radialGenerator c Γ) (t, v) (0, EuclideanSpace.single i 1) * E t +
        radialGenerator c Γ (t, v) * V t)) t)
    (hV₀ : V 0 = 0)
    (hFlat : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a : Index, coordinateRiemann Γ (radialPoint c (t, v)) a i = 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, radialFrameDefect c Γ v i E V t = 0 := by
  let W := radialFrameDefect c Γ v i E V
  have hW (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt W (-(radialGenerator c Γ (t, v) * W t)) t := by
    have hh := radialFrameDefect_hasDerivAt c Γ v i E V t (hΓ t ht) (hE t ht) (hV t ht)
    simpa only [W, hFlat t ht, smul_zero, Finset.sum_const_zero, zero_mul, add_zero] using hh
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hA 0 (by norm_num))
  have hB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖-(radialGenerator c Γ (t, v) * W t)‖ ≤ M * ‖W t‖ := by
    rw [norm_neg]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hA t ht) (norm_nonneg _))
  have hz : W 0 = 0 := by simp [W, radialFrameDefect, hV₀]
  intro t ht
  apply norm_le_zero_iff.mp
  simpa only [hz, norm_zero, zero_div] using (small_linear_ode_bound hM₀ hM hW hB t ht).1

theorem radialFrame_transverse_parallel_at_one (c : CoordinateSpace) (Γ : CoordinateSpace → Connection)
    (v : CoordinateSpace) (i : Index) (E V : ℝ → FrameMatrix)
    (hW : radialFrameDefect c Γ v i E V 1 = 0) :
    V 1 = -(connectionMatrix (Γ (c + v)) i * E 1) := by
  apply eq_neg_of_add_eq_zero_left
  simpa [radialFrameDefect, radialPoint] using hW

end Burnett.Geometry.FlatRigidity

namespace Burnett.FlatRigidity

open Set Metric Burnett.RicciSymbol Burnett.Geometry.FlatRigidity Burnett.Geometry.ConnectionDifference
open scoped ContDiff Matrix.Norms.Operator Topology

theorem radialConnectionOperator_apply_generator (Γ : CoordinateSpace → Connection) (z v : CoordinateSpace)
    (t : ℝ) (E : FrameMatrix) :
    radialConnectionOperator Γ z v t E = radialGenerator z Γ (t, v) * E := rfl

theorem norm_radialGenerator_le_operator (Γ : CoordinateSpace → Connection) (z v : CoordinateSpace) (t : ℝ) :
    ‖radialGenerator z Γ (t, v)‖ ≤ ‖radialConnectionOperator Γ z v t‖ := by
  simpa only [radialConnectionOperator_apply_generator, Matrix.mul_one, norm_one, mul_one] using
    (radialConnectionOperator Γ z v t).le_opNorm (1 : FrameMatrix)

theorem contDiffOn_radialGenerator_of_coordinate (Γ : CoordinateSpace → Connection) (z : CoordinateSpace)
    (s : Set CoordinateSpace) (hΓ : ∀ a d b, ContDiffOn ℝ ∞ (fun x => Γ x a d b) s) :
    ContDiffOn ℝ ∞ (radialGenerator z Γ) {p : RadialParameter | radialPoint z p ∈ s} := by
  have h := (contDiffOn_radialConnectionOperator Γ z s hΓ).clm_apply (g := fun _ => (1 : FrameMatrix))
    contDiffOn_const
  have hswap : ContDiff ℝ ∞ (fun p : RadialParameter => (p.2, p.1)) := contDiff_snd.prodMk contDiff_fst
  have h' := h.comp hswap.contDiffOn (fun _ hp => hp)
  exact h'.congr (fun p _ => by simp only [radialConnectionOperator_apply_generator, Matrix.mul_one]; rfl)

/-- The displacement derivative of the coefficient path is the actual differentiated connection action. -/
theorem fderiv_radialCoefficientPaths_apply (Γ : CoordinateSpace → Connection) (z : CoordinateSpace)
    (U : Set CoordinateSpace) (hU : IsOpen U) (A : CoordinateSpace → RadialCoefficientPaths)
    (hEq : ∀ v ∈ U, ∀ t : RadialTimes, A v t = radialConnectionOperator Γ z v (t : ℝ))
    (v : CoordinateSpace) (hv : v ∈ U) (t : RadialTimes) (hA : DifferentiableAt ℝ A v)
    (hΓ : DifferentiableAt ℝ (radialGenerator z Γ) ((t : ℝ), v)) (d : CoordinateSpace) (E : FrameMatrix) :
    (fderiv ℝ A v d) t E = (fderiv ℝ (radialGenerator z Γ) ((t : ℝ), v) (0, d)) * E := by
  let eval : RadialCoefficientPaths →L[ℝ] (FrameMatrix →L[ℝ] FrameMatrix) := ContinuousMap.evalCLM (R := ℝ) t
  have hEvalMap : HasFDerivAt eval eval (A v) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := RadialCoefficientPaths)
      (F := FrameMatrix →L[ℝ] FrameMatrix) (x := A v) eval
  have hA' : HasFDerivAt A (fderiv ℝ A v) v :=
    DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := CoordinateSpace) (F := RadialCoefficientPaths) hA
  have hEval : HasFDerivAt (fun w => eval (A w)) (eval.comp (fderiv ℝ A v)) v :=
    HasFDerivAt.comp (𝕜 := ℝ) (E := CoordinateSpace) (F := RadialCoefficientPaths)
      (G := FrameMatrix →L[ℝ] FrameMatrix) v hEvalMap hA'
  have hLine : HasFDerivAt (fun w : CoordinateSpace => ((t : ℝ), w))
      (ContinuousLinearMap.inr ℝ ℝ CoordinateSpace) v :=
    (hasFDerivAt_const (t : ℝ) v).prodMk (hasFDerivAt_id v)
  have hGen := (ContinuousLinearMap.mul ℝ FrameMatrix).hasFDerivAt.comp v (hΓ.hasFDerivAt.comp v hLine)
  have hGen' := hGen.congr_of_eventuallyEq (f₁ := fun w => eval (A w)) (by
    filter_upwards [hU.mem_nhds hv] with w hw
    exact hEq w hw t)
  exact congrArg (fun op : CoordinateSpace →L[ℝ] (FrameMatrix →L[ℝ] FrameMatrix) => op d E)
    (hEval.fderiv.symm.trans hGen'.fderiv)

end Burnett.FlatRigidity

namespace Burnett.FlatRigidity

open Set Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference Burnett.Geometry.FlatRigidity
open scoped BigOperators ContDiff Matrix.Norms.Operator

/-- The full parallel equations upgrade a differentiable frame to a smooth one. -/
theorem contDiffOn_frame_of_parallel (U : Set CoordinateSpace) (hU : IsOpen U)
    (Γ : CoordinateSpace → Connection) (E : CoordinateSpace → FrameMatrix)
    (hΓ : ∀ d : Index, ContDiffOn ℝ ∞ (fun x => connectionMatrix (Γ x) d) U)
    (hE : DifferentiableOn ℝ E U)
    (hParallel : ∀ x ∈ U, ∀ d : Index,
      fderiv ℝ E x (EuclideanSpace.single d 1) = -(connectionMatrix (Γ x) d * E x)) :
    ContDiffOn ℝ ∞ E U := by
  let B := EuclideanSpace.basisFun Index ℝ
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero => exact contDiffOn_zero.mpr hE.continuousOn
  | succ n ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨hE, by simp, contDiffOn_clm_apply.mpr fun y => ?_⟩
    have hsmooth : ContDiffOn ℝ n (fun x =>
        ∑ d : Index, (B.repr y d) • -(connectionMatrix (Γ x) d * E x)) U :=
      ContDiffOn.sum fun d _ => contDiffOn_const.smul (((contDiffOn_infty.mp (hΓ d) n).mul ih).neg)
    apply hsmooth.congr
    intro x hx
    calc
      fderiv ℝ E x y = fderiv ℝ E x (∑ d : Index, B.repr y d • B d) :=
        congrArg (fderiv ℝ E x) (B.sum_repr y).symm
      _ = _ := by simp only [map_sum, map_smul, B, EuclideanSpace.basisFun_apply, hParallel x hx]

end Burnett.FlatRigidity
