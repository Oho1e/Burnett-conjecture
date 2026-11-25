import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicParameterCoefficient
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 7800000

noncomputable section

namespace Burnett.A06

open Filter Metric MeasureTheory Set
open scoped ContDiff Topology

local instance : CompactSpace RoundSphere3 := Metric.sphere.compactSpace _ _
local instance : IsFiniteMeasure roundSphere3Measure :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure RotationSpace).toSphere))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {U : Set E} {V : Set RotationSpace}

/-- The actual paper coefficient of the real symbol at a parameter p. -/
def jointSphereHarmonicCoefficient (F : E × RotationSpace → ℝ) (i : SphereHarmonicIndex) (p : E) : ℝ :=
  ∫ x : RoundSphere3, F (p, x) * sphereHarmonicFamily i x ∂roundSphere3Measure

/-- A parameter derivative of the original joint symbol in a fixed direction. -/
def jointAngularParameterDerivative (v : E) (F : E × RotationSpace → ℝ) (q : E × RotationSpace) : ℝ :=
  fderiv ℝ F q (v, 0)

private def jointCoefficientDerivativeIntegrand (F : E × RotationSpace → ℝ)
    (i : SphereHarmonicIndex) (p : E) (x : RoundSphere3) : E →L[ℝ] ℝ :=
  sphereHarmonicFamily i x •
    ((fderiv ℝ F (p, x)).comp (ContinuousLinearMap.inl ℝ E RotationSpace))

omit [NormedSpace ℝ E] in
private theorem jointAngular_fixed_angle_continuous (F : E × RotationSpace → ℝ)
    (hF : ContinuousOn F (U ×ˢ V)) (hV : sphere (0 : RotationSpace) 1 ⊆ V)
    {p : E} (hp : p ∈ U) : Continuous fun x : RoundSphere3 => F (p, x) :=
  hF.comp_continuous (continuous_const.prodMk continuous_subtype_val) (fun x => ⟨hp, hV x.property⟩)

private theorem jointAngularDerivativeIntegrand_continuous
    {F : E × RotationSpace → ℝ} (hF : ContDiffOn ℝ 1 F (U ×ˢ V))
    (hU : IsOpen U) (hV : IsOpen V) (hs : sphere (0 : RotationSpace) 1 ⊆ V)
    (i : SphereHarmonicIndex) {p : E} (hp : p ∈ U) :
    Continuous (jointCoefficientDerivativeIntegrand F i p) := by
  have hD : ContinuousOn (fderiv ℝ F) (U ×ˢ V) :=
    (hF.fderiv_of_isOpen (hU.prod hV) (m := 0) (by norm_num)).continuousOn
  have hc : Continuous fun x : RoundSphere3 => fderiv ℝ F (p,x) :=
    hD.comp_continuous (continuous_const.prodMk continuous_subtype_val) (fun x => ⟨hp,hs x.property⟩)
  exact (sphereHarmonicFamily i).continuous.smul
    (hc.clm_comp_const (ContinuousLinearMap.inl ℝ E RotationSpace))

/-- Differentiation under the actual sphere integral using a compact angular
set and one common parameter neighborhood. -/
theorem jointSphereHarmonicCoefficient_hasFDerivAt [FiniteDimensional ℝ E]
    {F : E × RotationSpace → ℝ} (hF : ContDiffOn ℝ 1 F (U ×ˢ V))
    (hU : IsOpen U) (hV : IsOpen V) (hs : sphere (0 : RotationSpace) 1 ⊆ V)
    (i : SphereHarmonicIndex) {p : E} (hp : p ∈ U) :
    HasFDerivAt (jointSphereHarmonicCoefficient F i)
      (∫ x, jointCoefficientDerivativeIntegrand F i p x ∂roundSphere3Measure) p := by
  obtain ⟨r,hr,hB⟩ := Metric.isOpen_iff.mp hU p hp
  let ε := r/2
  have hε : 0 < ε := half_pos hr
  have hC : closedBall p ε ⊆ U := (closedBall_subset_ball (half_lt_self hr)).trans hB
  have hpB : ball p ε ⊆ U := ball_subset_closedBall.trans hC
  let W := closedBall p ε ×ˢ sphere (0 : RotationSpace) 1
  have hW : IsCompact W := (isCompact_closedBall p ε).prod (isCompact_sphere _ _)
  have hWU : W ⊆ U ×ˢ V := fun _ h => ⟨hC h.1,hs h.2⟩
  have hD : ContinuousOn (fderiv ℝ F) (U ×ˢ V) :=
    (hF.fderiv_of_isOpen (hU.prod hV) (m := 0) (by norm_num)).continuousOn
  obtain ⟨B,hBnd⟩ := hW.exists_bound_of_continuousOn (hD.mono hWU)
  let Y := sphereHarmonicFamily i
  let I := ContinuousLinearMap.inl ℝ E RotationSpace
  let M := ‖Y‖ * (max 0 B * ‖I‖)
  let G (q : E) (x : RoundSphere3) := F (q,x) * Y x
  have cG {q : E} (hq : q ∈ U) : Continuous (G q) :=
    (jointAngular_fixed_angle_continuous F hF.continuousOn hs hq).mul Y.continuous
  have hDmeas : AEStronglyMeasurable (jointCoefficientDerivativeIntegrand F i p) roundSphere3Measure :=
    (jointAngularDerivativeIntegrand_continuous hF hU hV hs i hp).aestronglyMeasurable
  have hGmeas : ∀ᶠ q in 𝓝 p, AEStronglyMeasurable (G q) roundSphere3Measure := by
    filter_upwards [show U ∈ 𝓝 p from hU.mem_nhds hp] with _ hq
    exact (cG hq).aestronglyMeasurable
  have hGint : Integrable (G p) roundSphere3Measure :=
    (cG hp).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hGB : ∀ᵐ x ∂roundSphere3Measure, ∀ q ∈ ball p ε,
      ‖jointCoefficientDerivativeIntegrand F i q x‖ ≤ M := by
    refine Eventually.of_forall fun x q hq => ?_
    have hqW : (q,(x : RotationSpace)) ∈ W := ⟨ball_subset_closedBall hq,x.property⟩
    have h : ‖fderiv ℝ F (q,x)‖ ≤ max 0 B := (hBnd _ hqW).trans (le_max_right _ _)
    calc
      _ = ‖Y x‖ * ‖(fderiv ℝ F (q,x)).comp I‖ := norm_smul _ _
      _ ≤ ‖Y‖ * (max 0 B * ‖I‖) :=
        mul_le_mul (Y.norm_coe_le_norm x)
          (((fderiv ℝ F (q,x)).opNorm_comp_le I).trans
            (mul_le_mul_of_nonneg_right h (norm_nonneg I)))
          (norm_nonneg _) (norm_nonneg Y)
  have hDiff : ∀ᵐ x ∂roundSphere3Measure, ∀ q ∈ ball p ε,
      HasFDerivAt (fun a => G a x) (jointCoefficientDerivativeIntegrand F i q x) q := by
    refine Eventually.of_forall fun x q hq => ?_
    have hq' : (q,(x : RotationSpace)) ∈ U ×ˢ V := ⟨hpB hq,hs x.property⟩
    have ha : HasFDerivAt (fun a : E => (a,(x : RotationSpace))) I q :=
      (hasFDerivAt_id q).prodMk (hasFDerivAt_const (x : RotationSpace) q)
    have hdiff := (hF.contDiffAt ((hU.prod hV).mem_nhds hq')).differentiableAt le_rfl
    exact (hdiff.hasFDerivAt.comp q ha).mul_const (Y x)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le hε hGmeas hGint hDmeas hGB
    (integrable_const M) hDiff

/-- The evaluated first parameter derivative is the original coefficient
integral applied to the actual joint directional derivative. -/
theorem jointSphereHarmonicCoefficient_fderiv_apply [FiniteDimensional ℝ E]
    {F : E × RotationSpace → ℝ} (hF : ContDiffOn ℝ 1 F (U ×ˢ V))
    (hU : IsOpen U) (hV : IsOpen V) (hs : sphere (0 : RotationSpace) 1 ⊆ V)
    (i : SphereHarmonicIndex) {p : E} (hp : p ∈ U) (v : E) :
    fderiv ℝ (jointSphereHarmonicCoefficient F i) p v =
      jointSphereHarmonicCoefficient (jointAngularParameterDerivative v F) i p := by
  have hc := jointAngularDerivativeIntegrand_continuous hF hU hV hs i hp
  have hint : Integrable (jointCoefficientDerivativeIntegrand F i p) roundSphere3Measure :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [(jointSphereHarmonicCoefficient_hasFDerivAt hF hU hV hs i hp).fderiv,
    ContinuousLinearMap.integral_apply hint v]
  simp only [jointCoefficientDerivativeIntegrand, jointSphereHarmonicCoefficient,
    jointAngularParameterDerivative, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, smul_eq_mul, mul_comm]

theorem jointAngularParameterDerivative_contDiffOn {F : E × RotationSpace → ℝ}
    (n : ℕ) (hF : ContDiffOn ℝ (n+1 : ℕ) F (U ×ˢ V))
    (hU : IsOpen U) (hV : IsOpen V) (v : E) :
    ContDiffOn ℝ n (jointAngularParameterDerivative v F) (U ×ˢ V) := by
  exact (ContinuousLinearMap.apply ℝ ℝ (v,(0 : RotationSpace))).contDiff.comp_contDiffOn
    (hF.fderiv_of_isOpen (hU.prod hV) (by simp only [Nat.cast_add, Nat.cast_one, le_refl]))

/-- The actual coefficient inherits every parameter regularity used in the
mixed estimate, with one derivative available for differentiation under the
integral. -/
theorem jointSphereHarmonicCoefficient_contDiffOn [FiniteDimensional ℝ E]
    {F : E × RotationSpace → ℝ} (n : ℕ) (hF : ContDiffOn ℝ (n+1 : ℕ) F (U ×ˢ V))
    (hU : IsOpen U) (hV : IsOpen V) (hs : sphere (0 : RotationSpace) 1 ⊆ V)
    (i : SphereHarmonicIndex) :
    ContDiffOn ℝ n (jointSphereHarmonicCoefficient F i) U := by
  induction n generalizing F with
  | zero =>
    apply contDiffOn_zero.mpr
    intro p hp
    exact (jointSphereHarmonicCoefficient_hasFDerivAt hF hU hV hs i hp).continuousAt.continuousWithinAt
  | succ n ih =>
    have hF₁ : ContDiffOn ℝ 1 F (U ×ˢ V) :=
      hF.of_le (by exact_mod_cast (show 1 ≤ n.succ+1 by omega))
    have hd : DifferentiableOn ℝ (jointSphereHarmonicCoefficient F i) U := fun _ hp =>
      (jointSphereHarmonicCoefficient_hasFDerivAt hF₁ hU hV hs i hp).differentiableAt.differentiableWithinAt
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_apply hU.uniqueDiffOn]
    refine ⟨hd,by simp,fun v => ?_⟩
    have h : ContDiffOn ℝ (n+1 : ℕ) (jointAngularParameterDerivative v F) (U ×ˢ V) :=
      jointAngularParameterDerivative_contDiffOn (n+1) hF hU hV v
    refine (ih h).congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hU hp, jointSphereHarmonicCoefficient_fderiv_apply hF₁ hU hV hs i hp]

end Burnett.A06
