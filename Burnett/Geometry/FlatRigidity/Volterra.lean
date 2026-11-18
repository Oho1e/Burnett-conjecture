import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.FlatFrameVolterra

open Set MeasureTheory intervalIntegral
open scoped Topology




abbrev Time := Icc (0 : ℝ) 1
abbrev Path (E : Type*) [TopologicalSpace E] := C(Time, E)

def clampTime (t : ℝ) : Time := projIcc 0 1 (by norm_num) t

theorem continuous_clampTime : Continuous clampTime :=
  continuous_projIcc (h := (by norm_num : (0 : ℝ) ≤ 1))

@[simp] theorem clampTime_coe (t : Time) : clampTime t = t :=
  projIcc_of_mem (by norm_num) t.property

section Banach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Coeff (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := C(Time, E →L[ℝ] E)

def extendPath (f : Path E) (t : ℝ) : E := f (clampTime t)

omit [NormedSpace ℝ E] in
theorem extendPath_continuous (f : Path E) : Continuous (extendPath f) :=
  f.continuous.comp continuous_clampTime

omit [NormedSpace ℝ E] in
@[simp] theorem extendPath_coe (f : Path E) (t : Time) : extendPath f t = f t := by
  simp only [extendPath, clampTime_coe]

def primitivePath (f : Path E) : Path E :=
  ⟨fun t => ∫ s in (0 : ℝ)..(t : ℝ), extendPath f s,
    (intervalIntegral.continuous_primitive
      (fun a b => (extendPath_continuous f).intervalIntegrable a b) 0).comp continuous_subtype_val⟩

@[simp] theorem primitivePath_zero (f : Path E) : primitivePath f ⟨0, by norm_num⟩ = 0 := by
  simp [primitivePath]

theorem primitivePath_norm_le (f : Path E) : ‖primitivePath f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  change ‖∫ s in (0 : ℝ)..(t : ℝ), extendPath f s‖ ≤ ‖f‖
  calc
    _ ≤ ‖f‖ * |(t : ℝ) - 0| := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun s _ => f.norm_coe_le_norm (clampTime s))
    _ ≤ ‖f‖ := by
      rw [sub_zero, abs_of_nonneg t.property.1]
      exact mul_le_of_le_one_right (norm_nonneg _) t.property.2

def primitiveLinear : Path E →ₗ[ℝ] Path E where
  toFun := primitivePath
  map_add' f g := by
    ext t
    change (∫ s in (0 : ℝ)..(t : ℝ), extendPath f s + extendPath g s) =
      (∫ s in (0 : ℝ)..(t : ℝ), extendPath f s) + ∫ s in (0 : ℝ)..(t : ℝ), extendPath g s
    exact intervalIntegral.integral_add ((extendPath_continuous f).intervalIntegrable _ _)
      ((extendPath_continuous g).intervalIntegrable _ _)
  map_smul' c f := by
    ext t
    change (∫ s in (0 : ℝ)..(t : ℝ), c • extendPath f s) =
      c • ∫ s in (0 : ℝ)..(t : ℝ), extendPath f s
    exact intervalIntegral.integral_smul c _

def primitiveCLM : Path E →L[ℝ] Path E :=
  (primitiveLinear (E := E)).mkContinuous 1 (fun f => by simpa using primitivePath_norm_le f)

@[simp] theorem primitiveCLM_apply (f : Path E) (t : Time) :
    primitiveCLM (E := E) f t = ∫ s in (0 : ℝ)..(t : ℝ), extendPath f s := rfl

theorem primitiveCLM_norm_le : ‖primitiveCLM (E := E)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) (fun f => by simpa using primitivePath_norm_le f)

def pointwisePath (A : Coeff E) (f : Path E) : Path E :=
  ⟨fun t => A t (f t), A.continuous.clm_apply f.continuous⟩

theorem pointwisePath_norm_le (A : Coeff E) (f : Path E) :
    ‖pointwisePath A f‖ ≤ ‖A‖ * ‖f‖ := by
  apply (ContinuousMap.norm_le (pointwisePath A f) (mul_nonneg (norm_nonneg A) (norm_nonneg f))).mpr
  intro t
  exact (A t).le_opNorm (f t) |>.trans
    (mul_le_mul (A.norm_coe_le_norm t) (f.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))

def pointwiseLinear (A : Coeff E) : Path E →ₗ[ℝ] Path E where
  toFun := pointwisePath A
  map_add' f g := by ext t; exact (A t).map_add _ _
  map_smul' c f := by ext t; exact (A t).map_smul c _

def pointwiseCLM (A : Coeff E) : Path E →L[ℝ] Path E :=
  (pointwiseLinear A).mkContinuous ‖A‖ (pointwisePath_norm_le A)

@[simp] theorem pointwiseCLM_apply (A : Coeff E) (f : Path E) (t : Time) :
    pointwiseCLM A f t = A t (f t) := rfl

theorem pointwiseCLM_norm_le (A : Coeff E) : ‖pointwiseCLM A‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le (pointwiseLinear A) (norm_nonneg A) (pointwisePath_norm_le A)

/-- The actual bounded Volterra operator for a fixed coefficient path. -/
def volterraCLM (A : Coeff E) : Path E →L[ℝ] Path E :=
  -((primitiveCLM (E := E)).comp (pointwiseCLM A))

@[simp] theorem volterraCLM_apply (A : Coeff E) (f : Path E) (t : Time) :
    volterraCLM A f t = -(∫ s in (0 : ℝ)..(t : ℝ), A (clampTime s) (f (clampTime s))) := rfl

theorem volterraCLM_coeff_norm_le (A : Coeff E) : ‖volterraCLM A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg f))).mpr
  intro t
  rw [volterraCLM_apply, norm_neg]
  calc
    _ ≤ (‖A‖ * ‖f‖) * |(t : ℝ) - 0| := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun s _ => ((A (clampTime s)).le_opNorm (f (clampTime s))).trans
        (mul_le_mul (A.norm_coe_le_norm _) (f.norm_coe_le_norm _) (norm_nonneg (f (clampTime s))) (norm_nonneg A)))
    _ ≤ ‖A‖ * ‖f‖ := by
      rw [sub_zero, abs_of_nonneg t.property.1]
      exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg A) (norm_nonneg f)) t.property.2

theorem volterraCLM_add (A B : Coeff E) : volterraCLM (A + B) = volterraCLM A + volterraCLM B := by
  ext f t
  change -(primitiveCLM (E := E) (pointwisePath (A + B) f)) t =
    -(primitiveCLM (E := E) (pointwisePath A f)) t + -(primitiveCLM (E := E) (pointwisePath B f)) t
  have he : pointwisePath (A + B) f = pointwisePath A f + pointwisePath B f := rfl
  rw [he, map_add]
  simp only [ContinuousMap.add_apply, neg_add]

theorem volterraCLM_smul (c : ℝ) (A : Coeff E) : volterraCLM (c • A) = c • volterraCLM A := by
  ext f t
  change -(primitiveCLM (E := E) (pointwisePath (c • A) f)) t =
    c • (-(primitiveCLM (E := E) (pointwisePath A f)) t)
  have he : pointwisePath (c • A) f = c • pointwisePath A f := rfl
  rw [he, map_smul]
  simp only [ContinuousMap.smul_apply, smul_neg]

theorem volterraCLM_sub (A B : Coeff E) : volterraCLM (A - B) = volterraCLM A - volterraCLM B := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ B, volterraCLM_add, volterraCLM_smul]
  ext f t
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousMap.add_apply, neg_one_smul,
    ContinuousLinearMap.neg_apply, ContinuousMap.neg_apply, sub_eq_add_neg]

theorem volterraCLM_sub_norm_le (A B : Coeff E) : ‖volterraCLM A - volterraCLM B‖ ≤ ‖A - B‖ := by
  rw [← volterraCLM_sub]
  exact volterraCLM_coeff_norm_le (A - B)

theorem volterraCLM_apply_sub_norm_le (A B : Coeff E) (f : Path E) :
    ‖(volterraCLM A - volterraCLM B) f‖ ≤ ‖A - B‖ * ‖f‖ :=
  ((volterraCLM A - volterraCLM B).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (volterraCLM_sub_norm_le A B) (norm_nonneg f))

def coefficientVolterraCLM : Coeff E →L[ℝ] (Path E →L[ℝ] Path E) := by
  let L : Coeff E →ₗ[ℝ] (Path E →L[ℝ] Path E) :=
    { toFun := volterraCLM
      map_add' := volterraCLM_add
      map_smul' := volterraCLM_smul }
  refine LinearMap.mkContinuous (E := Coeff E) (F := Path E →L[ℝ] Path E) L 1 ?_
  intro A
  change ‖volterraCLM A‖ ≤ 1 * ‖A‖
  simpa only [one_mul] using volterraCLM_coeff_norm_le A

@[simp] theorem coefficientVolterraCLM_apply (A : Coeff E) :
    coefficientVolterraCLM (E := E) A = volterraCLM A := rfl

theorem volterraCLM_contDiff {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun A : Coeff E => volterraCLM A) :=
  ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Coeff E) (F := Path E →L[ℝ] Path E)
    (n := n) (coefficientVolterraCLM (E := E))

theorem evaluation_contDiff {n : WithTop ℕ∞} (t : Time) :
    ContDiff ℝ n (fun f : Path E => f t) :=
  ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Path E) (F := E) (n := n)
    (ContinuousMap.evalCLM (R := ℝ) t)

variable [CompleteSpace E]

theorem primitiveCLM_hasDerivAt (f : Path E) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (extendPath (primitiveCLM (E := E) f)) (extendPath f t) t := by
  have hc := extendPath_continuous f
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  apply hi.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  change (∫ u in (0 : ℝ)..(clampTime s : ℝ), extendPath f u) =
    ∫ u in (0 : ℝ)..s, extendPath f u
  have hp : (clampTime s : ℝ) = s := by
    exact congrArg Subtype.val (projIcc_of_mem (by norm_num) (Ioo_subset_Icc_self hs))
  rw [hp]

omit [CompleteSpace E] in
theorem fixed_point_center (A : Coeff E) (f : Path E) (E0 : E)
    (hf : f = ContinuousMap.const Time E0 + volterraCLM (E := E) A f) :
    f ⟨0, by norm_num⟩ = E0 := by
  have he := congrArg (fun g : Path E => g ⟨0, by norm_num⟩) hf
  simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply, volterraCLM_apply,
    intervalIntegral.integral_same, neg_zero, add_zero] using he

theorem fixed_point_hasDerivAt (A : Coeff E) (f : Path E) (E0 : E)
    (hf : f = ContinuousMap.const Time E0 + volterraCLM (E := E) A f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (extendPath f) (-(A (clampTime t) (f (clampTime t)))) t := by
  have hp := (primitiveCLM_hasDerivAt (pointwisePath A f) ht).neg.const_add E0
  have he : extendPath f = fun s : ℝ => E0 - extendPath (primitiveCLM (E := E) (pointwisePath A f)) s := by
    funext s
    have hv := congrArg (fun g : Path E => g (clampTime s)) hf
    simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply, volterraCLM_apply,
      extendPath, primitiveCLM_apply, pointwisePath, sub_eq_add_neg] using hv
  rw [he]
  simpa only [sub_eq_add_neg, extendPath, pointwisePath, ContinuousMap.coe_mk, Pi.neg_apply] using hp

/-- The genuine real-time integral realization, not the clamped trace of a path. -/
def realizePath (A : Coeff E) (f : Path E) (b : E) (t : ℝ) : E :=
  b - ∫ s in (0 : ℝ)..t, A (clampTime s) (f (clampTime s))

omit [CompleteSpace E] in
@[simp] theorem realizePath_zero (A : Coeff E) (f : Path E) (b : E) :
    realizePath A f b 0 = b := by simp [realizePath]

theorem realizePath_hasDerivAt (A : Coeff E) (f : Path E) (b : E) (t : ℝ) :
    HasDerivAt (realizePath A f b) (-(A (clampTime t) (f (clampTime t)))) t := by
  have hc := extendPath_continuous (pointwisePath A f)
  have hp := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).neg.const_add b
  change HasDerivAt (fun r : ℝ => b - ∫ s in (0 : ℝ)..r, A (clampTime s) (f (clampTime s)))
    (-(A (clampTime t) (f (clampTime t)))) t
  simp only [sub_eq_add_neg]
  simpa only [extendPath, pointwisePath, ContinuousMap.coe_mk, Pi.neg_apply] using hp

omit [CompleteSpace E] in
theorem realizePath_eq_trace (A : Coeff E) (f : Path E) (b : E)
    (hf : f = ContinuousMap.const Time b + volterraCLM A f) (t : Time) :
    realizePath A f b t = f t := by
  have he := congrArg (fun g : Path E => g t) hf
  simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply, volterraCLM_apply,
    realizePath, sub_eq_add_neg] using he.symm

/-- A true path fixed point has an ordinary derivative satisfying the ODE even at both endpoints. -/
theorem realizePath_fixed_point_closed_ODE (A : Coeff E) (f : Path E) (b : E)
    (hf : f = ContinuousMap.const Time b + volterraCLM A f) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (realizePath A f b) (-(A (clampTime t) (realizePath A f b t))) t := by
  have hco : (clampTime t : ℝ) = t :=
    congrArg Subtype.val (projIcc_of_mem (by norm_num) ht)
  have he : f (clampTime t) = realizePath A f b t := by
    simpa only [hco] using (realizePath_eq_trace A f b hf (clampTime t)).symm
  simpa only [he] using realizePath_hasDerivAt A f b t

end Banach
end Burnett.Geometry.FlatFrameVolterra

namespace Burnett.Geometry.FlatFrameVolterra
open Set Filter MeasureTheory intervalIntegral
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
section Parameters

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [CompleteSpace E] in
/-- Differentiate the actual path fixed-point equation in the endpoint parameter. -/
theorem fixed_point_parameter_variation (A : V → Coeff E) (F : V → Path E) (b : E)
    (v : V) (DA : V →L[ℝ] Coeff E) (DF : V →L[ℝ] Path E)
    (hA : HasFDerivAt A DA v) (hF : HasFDerivAt F DF v)
    (hfp : F =ᶠ[𝓝 v] (fun w => ContinuousMap.const Time b + volterraCLM (A w) (F w))) :
    ∀ h : V, DF h = volterraCLM (A v) (DF h) + volterraCLM (DA h) (F v) := by
  let C : Coeff E →L[ℝ] (Path E →L[ℝ] Path E) := coefficientVolterraCLM
  have hC0 : HasFDerivAt (fun a : Coeff E => volterraCLM a) C (A v) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := Coeff E) (F := Path E →L[ℝ] Path E)
      (x := A v) C
  have hC : HasFDerivAt (fun w => volterraCLM (A w)) (C.comp DA) v := by
    simpa only [Function.comp_def] using
      HasFDerivAt.comp (𝕜 := ℝ) (E := V) (F := Coeff E) (G := Path E →L[ℝ] Path E)
        (f := A) (g := fun a : Coeff E => volterraCLM a) v hC0 hA
  have hp : HasFDerivAt (fun w => volterraCLM (A w) (F w))
      ((volterraCLM (A v)).comp DF + (C.comp DA).flip (F v)) v := by
    exact hC.clm_apply hF
  have hq := hp.const_add (ContinuousMap.const Time b)
  have he := hF.unique (hq.congr_of_eventuallyEq hfp)
  intro h
  have hv := congrArg (fun L : V →L[ℝ] Path E => L h) he
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, C, coefficientVolterraCLM_apply] using hv

omit [CompleteSpace E] in
/-- At any fixed closed-time point, the true integral realization has the path derivative. -/
theorem realizePath_parameter_hasFDerivAt (A : V → Coeff E) (F : V → Path E) (b : E)
    (v : V) (DF : V →L[ℝ] Path E) (hF : HasFDerivAt F DF v)
    (hfp : F =ᶠ[𝓝 v] (fun w => ContinuousMap.const Time b + volterraCLM (A w) (F w)))
    (t : Time) :
    HasFDerivAt (fun w => realizePath (A w) (F w) b (t : ℝ))
      ((ContinuousMap.evalCLM (R := ℝ) t).comp DF) v := by
  have he : (fun w => realizePath (A w) (F w) b (t : ℝ)) =ᶠ[𝓝 v] (fun w => F w t) := by
    filter_upwards [hfp] with w hw
    exact realizePath_eq_trace (A w) (F w) b hw t
  have hp : HasFDerivAt (fun w => F w t) ((ContinuousMap.evalCLM (R := ℝ) t).comp DF) v := by
    exact (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := Path E) (F := E)
      (x := F v) (ContinuousMap.evalCLM (R := ℝ) t)).comp v hF
  exact hp.congr_of_eventuallyEq he

end Parameters

/-- The real-time realization of the actual endpoint-variation equation. -/
def realizeVariation (A D : Coeff E) (f q : Path E) (t : ℝ) : E :=
  -(∫ s in (0 : ℝ)..t, D (clampTime s) (f (clampTime s)) + A (clampTime s) (q (clampTime s)))

omit [CompleteSpace E] in
@[simp] theorem realizeVariation_zero (A D : Coeff E) (f q : Path E) :
    realizeVariation A D f q 0 = 0 := by simp [realizeVariation]

theorem realizeVariation_hasDerivAt (A D : Coeff E) (f q : Path E) (t : ℝ) :
    HasDerivAt (realizeVariation A D f q)
      (-(D (clampTime t) (f (clampTime t)) + A (clampTime t) (q (clampTime t)))) t := by
  have hc := (extendPath_continuous (pointwisePath D f)).add (extendPath_continuous (pointwisePath A q))
  have hp := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).neg
  change HasDerivAt (fun r : ℝ => -(∫ s in (0 : ℝ)..r,
    D (clampTime s) (f (clampTime s)) + A (clampTime s) (q (clampTime s)))) _ t
  simpa only [extendPath, pointwisePath, ContinuousMap.coe_mk, Pi.neg_apply] using hp

omit [CompleteSpace E] in
theorem realizeVariation_eq_trace (A D : Coeff E) (f q : Path E)
    (hq : q = volterraCLM A q + volterraCLM D f) (t : Time) :
    realizeVariation A D f q t = q t := by
  have hx := congrArg (fun g : Path E => g t) hq
  simp only [ContinuousMap.add_apply, volterraCLM_apply] at hx
  change -(∫ s in (0 : ℝ)..(t : ℝ),
    D (clampTime s) (f (clampTime s)) + A (clampTime s) (q (clampTime s))) = q t
  have hi := intervalIntegral.integral_add (μ := volume) (a := (0 : ℝ)) (b := (t : ℝ))
    ((extendPath_continuous (pointwisePath D f)).intervalIntegrable 0 (t : ℝ))
    ((extendPath_continuous (pointwisePath A q)).intervalIntegrable 0 (t : ℝ))
  change (∫ s in (0 : ℝ)..(t : ℝ), D (clampTime s) (f (clampTime s)) + A (clampTime s) (q (clampTime s))) =
    (∫ s in (0 : ℝ)..(t : ℝ), D (clampTime s) (f (clampTime s))) +
    ∫ s in (0 : ℝ)..(t : ℝ), A (clampTime s) (q (clampTime s)) at hi
  rw [hi, hx]
  abel

/-- The endpoint variation satisfies a genuine ordinary ODE at every closed-time point. -/
theorem realizeVariation_closed_ODE (A D : Coeff E) (f q : Path E) (b : E)
    (hf : f = ContinuousMap.const Time b + volterraCLM A f)
    (hq : q = volterraCLM A q + volterraCLM D f) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (realizeVariation A D f q)
      (-(D (clampTime t) (realizePath A f b t) + A (clampTime t) (realizeVariation A D f q t))) t := by
  have hco : (clampTime t : ℝ) = t :=
    congrArg Subtype.val (projIcc_of_mem (by norm_num) ht)
  have he : f (clampTime t) = realizePath A f b t := by
    simpa only [hco] using (realizePath_eq_trace A f b hf (clampTime t)).symm
  have hv : q (clampTime t) = realizeVariation A D f q t := by
    simpa only [hco] using (realizeVariation_eq_trace A D f q hq (clampTime t)).symm
  simpa only [he, hv] using realizeVariation_hasDerivAt A D f q t

end Burnett.Geometry.FlatFrameVolterra

namespace Burnett.Geometry.FlatFrameVolterra

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The exact inverse on the unit ball of the Banach algebra of operators. -/
noncomputable def solveSmallOperator (A : E →L[ℝ] E) (b : E) : E :=
  (Ring.inverse (1 - A)) b

theorem solveSmallOperator_sub_eq (A : E →L[ℝ] E) (b : E) (hA : ‖A‖ < 1) :
    solveSmallOperator A b - A (solveSmallOperator A b) = b := by
  have h := Ring.mul_inverse_cancel (1 - A) (isUnit_one_sub_of_norm_lt_one hA)
  exact congrArg (fun S : E →L[ℝ] E => S b) h

theorem solveSmallOperator_eq_add (A : E →L[ℝ] E) (b : E) (hA : ‖A‖ < 1) :
    solveSmallOperator A b = b + A (solveSmallOperator A b) :=
  sub_eq_iff_eq_add.mp (solveSmallOperator_sub_eq A b hA)

theorem eq_solveSmallOperator (A : E →L[ℝ] E) (b x : E) (hA : ‖A‖ < 1)
    (hx : x = b + A x) : x = solveSmallOperator A b := by
  have hsub : (1 - A) x = b := sub_eq_iff_eq_add.mpr hx
  have h := Ring.inverse_mul_cancel (1 - A) (isUnit_one_sub_of_norm_lt_one hA)
  have hx' : (Ring.inverse (1 - A)) ((1 - A) x) = x :=
    congrArg (fun S : E →L[ℝ] E => S x) h
  rw [hsub] at hx'
  exact hx'.symm

theorem norm_solveSmallOperator_le (A : E →L[ℝ] E) (b : E) (hA : ‖A‖ < 1) :
    ‖solveSmallOperator A b‖ ≤ ‖b‖ / (1 - ‖A‖) := by
  have hnorm : ‖solveSmallOperator A b‖ ≤ ‖b‖ + ‖A‖ * ‖solveSmallOperator A b‖ := by
    calc
      ‖solveSmallOperator A b‖ = ‖b + A (solveSmallOperator A b)‖ :=
        congrArg norm (solveSmallOperator_eq_add A b hA)
      _ ≤ ‖b‖ + ‖A (solveSmallOperator A b)‖ := norm_add_le _ _
      _ ≤ ‖b‖ + ‖A‖ * ‖solveSmallOperator A b‖ :=
        add_le_add_left (A.le_opNorm _) _
  apply (le_div_iff₀ (sub_pos.mpr hA)).2
  rw [mul_sub, mul_one, mul_comm ‖solveSmallOperator A b‖]
  exact sub_le_iff_le_add.mpr hnorm

theorem norm_solveSmallOperator_sub_le (A : E →L[ℝ] E) (b : E) (hA : ‖A‖ < 1) :
    ‖solveSmallOperator A b - b‖ ≤ ‖A‖ * (‖b‖ / (1 - ‖A‖)) := by
  have hsub : solveSmallOperator A b - b = A (solveSmallOperator A b) :=
    sub_eq_iff_eq_add.mpr ((solveSmallOperator_eq_add A b hA).trans (add_comm _ _))
  rw [hsub]
  exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_solveSmallOperator_le A b hA) (norm_nonneg A))

theorem contDiffAt_solveSmallOperator (A : E →L[ℝ] E) (b : E) (hA : ‖A‖ < 1) :
    ContDiffAt ℝ ∞ (fun S : E →L[ℝ] E => solveSmallOperator S b) A := by
  let u := (isUnit_one_sub_of_norm_lt_one hA).unit
  have hinv : ContDiffAt ℝ ∞ Ring.inverse (1 - A) := contDiffAt_ringInverse ℝ u
  have hone : ContDiffAt ℝ ∞ (fun S : E →L[ℝ] E => 1 - S) A := contDiffAt_const.sub contDiffAt_id
  exact (hinv.comp A hone).clm_apply contDiffAt_const

end Burnett.Geometry.FlatFrameVolterra

namespace Burnett.Geometry.FlatFrameVolterra

open scoped ContDiff

section Banach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A single genuine solution for the entire time interval, with prescribed initial value. -/
noncomputable def solvedPath (A : Coeff E) (b : E) : Path E :=
  solveSmallOperator (volterraCLM A) (ContinuousMap.const Time b)

theorem solvedPath_eq (A : Coeff E) (b : E) (hA : ‖A‖ < 1) :
    solvedPath A b = ContinuousMap.const Time b + volterraCLM A (solvedPath A b) :=
  solveSmallOperator_eq_add _ _ ((volterraCLM_coeff_norm_le A).trans_lt hA)

theorem solvedPath_zero (A : Coeff E) (b : E) (hA : ‖A‖ < 1) :
    solvedPath A b ⟨0, by norm_num [Time]⟩ = b := by
  let t₀ : Time := ⟨0, by norm_num [Time]⟩
  have h := congrArg (fun f : Path E => f t₀) (solvedPath_eq A b hA)
  simpa [t₀] using h

theorem contDiffAt_solvedPath (A : Coeff E) (b : E) (hA : ‖A‖ < 1) :
    ContDiffAt ℝ ∞ (fun B : Coeff E => solvedPath B b) A :=
  (contDiffAt_solveSmallOperator _ _ ((volterraCLM_coeff_norm_le A).trans_lt hA)).comp A
    ((volterraCLM_contDiff (E := E) (n := ∞)).contDiffAt)

theorem contDiffOn_solvedPath_of_coeff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : Set V) (A : V → Coeff E) (b : E) (hA : ContDiffOn ℝ 1 A U)
    (hCap : ∀ v ∈ U, ‖A v‖ < 1) : ContDiffOn ℝ 1 (fun v => solvedPath (A v) b) U := by
  intro v hv
  have hSolve : ContDiffAt ℝ 1 (fun B : Coeff E => solvedPath B b) (A v) :=
    (contDiffAt_solvedPath (A v) b (hCap v hv)).of_le (by simp)
  exact hSolve.comp_contDiffWithinAt v (hA v hv)

theorem norm_solvedPath_sub_eval_le_of_quarter (A : Coeff E) (b : E) (hA : ‖A‖ ≤ 1 / 4)
    (t : Time) : ‖solvedPath A b t - b‖ ≤ ‖b‖ / 3 := by
  let S := volterraCLM A
  let g : Path E := ContinuousMap.const Time b
  have hS : ‖S‖ ≤ 1 / 4 := (volterraCLM_coeff_norm_le A).trans hA
  have hSlt : ‖S‖ < 1 := hS.trans_lt (by norm_num)
  have hg : ‖g‖ ≤ ‖b‖ := (ContinuousMap.norm_le _ (norm_nonneg b)).mpr (fun _ => le_rfl)
  have hdiv : ‖g‖ / (1 - ‖S‖) ≤ (4 / 3) * ‖b‖ := by
    apply (div_le_iff₀ (sub_pos.mpr hSlt)).2
    exact hg.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hS) (norm_nonneg b)])
  calc
    ‖solvedPath A b t - b‖ ≤ ‖solvedPath A b - g‖ := (solvedPath A b - g).norm_coe_le_norm t
    _ ≤ ‖S‖ * (‖g‖ / (1 - ‖S‖)) := norm_solveSmallOperator_sub_le S g hSlt
    _ ≤ (1 / 4) * ((4 / 3) * ‖b‖) :=
      mul_le_mul hS hdiv (div_nonneg (norm_nonneg _) (sub_nonneg.mpr hSlt.le)) (by norm_num)
    _ = ‖b‖ / 3 := by ring

end Banach

end Burnett.Geometry.FlatFrameVolterra
