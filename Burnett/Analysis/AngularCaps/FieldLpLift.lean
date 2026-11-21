import Burnett.Analysis.AngularCaps.CapMultiplierLp

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Burnett.Analysis.CapFourier

open MeasureTheory Filter
open scoped ENNReal

/-- The fixed Euclidean fiber norm used for the manuscript's finite arrays. -/
abbrev FieldLp (ι : Type*) [Fintype ι] (p : ℝ≥0∞) :=
  Lp (EuclideanSpace ℂ ι) p (volume : Measure Space)

variable {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def fieldCoordinateLp (i : ι) : FieldLp ι p →L[ℂ] ComplexLp p :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).compLpL p volume

private def fieldInjection (i : ι) : ℂ →L[ℂ] EuclideanSpace ℂ ι := by
  classical
  exact (ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single i 1)

private def fieldInjectionLp (i : ι) : ComplexLp p →L[ℂ] FieldLp ι p :=
  (fieldInjection i).compLpL p volume

omit [Fact (1 ≤ p)] in
/-- Assemble scalar fields using the Euclidean norm on their finite array. -/
theorem fieldArray_memLp (g : ι → Space → ℂ) (hg : ∀ i, MemLp (g i) p volume) :
    MemLp (fun x => (WithLp.toLp 2 (fun i => g i x) : EuclideanSpace ℂ ι))
      p volume := by
  classical
  let G (i : ι) : Space → EuclideanSpace ℂ ι := fieldInjection i ∘ g i
  have hsum : (∑ i, G i) = fun x => WithLp.toLp 2 (fun i => g i x) := by
    funext x
    rw [Finset.sum_apply]
    change (∑ i, g i x • EuclideanSpace.single i (1 : ℂ)) = WithLp.toLp 2 (fun i => g i x)
    simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun ι ℂ).sum_repr (WithLp.toLp 2 (fun i => g i x))
  rw [← hsum]
  exact memLp_finset_sum' _ fun i _ => (fieldInjection i).comp_memLp' (hg i)

theorem fieldCoordinateLp_ae (i : ι) (f : FieldLp ι p) :
    (fieldCoordinateLp i f : Space → ℂ) =ᵐ[volume] fun x => f x i :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL f

theorem fieldCoordinateLp_toLp (i : ι) {f : Space → EuclideanSpace ℂ ι}
    (hf : MemLp f p volume) :
    fieldCoordinateLp i (hf.toLp f) =
      ((EuclideanSpace.proj (𝕜 := ℂ) i).comp_memLp' hf).toLp (fun x => f x i) := by
  apply Lp.ext
  filter_upwards [fieldCoordinateLp_ae i (hf.toLp f), hf.coeFn_toLp,
    ((EuclideanSpace.proj (𝕜 := ℂ) i).comp_memLp' hf).coeFn_toLp] with x hproj hval hcoord
  exact hproj.trans ((congrArg (fun v : EuclideanSpace ℂ ι => v i) hval).trans hcoord.symm)

theorem fieldCoordinateLp_norm_le (i : ι) (f : FieldLp ι p) :
    ‖fieldCoordinateLp i f‖ ≤ ‖f‖ := by
  have hproj : ‖EuclideanSpace.proj (𝕜 := ℂ) i‖ ≤ 1 :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).opNorm_le_bound (by norm_num) fun v => by
      simpa only [one_mul] using PiLp.norm_apply_le v i
  calc
    _ ≤ ‖EuclideanSpace.proj (𝕜 := ℂ) i‖ * ‖f‖ :=
      (EuclideanSpace.proj (𝕜 := ℂ) i).norm_compLp_le f
    _ ≤ ‖f‖ := by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hproj (norm_nonneg f)

private theorem fieldInjectionLp_norm_le (i : ι) (f : ComplexLp p) :
    ‖fieldInjectionLp (ι := ι) i f‖ ≤ ‖f‖ := by
  classical
  have hinj : ‖fieldInjection i‖ ≤ 1 :=
    (fieldInjection i).opNorm_le_bound (by norm_num) fun z => by
      change ‖z • EuclideanSpace.single i (1 : ℂ)‖ ≤ 1 * ‖z‖
      simp [norm_smul]
  calc
    _ ≤ ‖fieldInjection i‖ * ‖f‖ := (fieldInjection i).norm_compLp_le f
    _ ≤ ‖f‖ := by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hinj (norm_nonneg f)

private theorem fieldCoordinateLp_injection [DecidableEq ι] (i j : ι) (f : ComplexLp p) :
    fieldCoordinateLp i (fieldInjectionLp j f) = if j = i then f else 0 := by
  classical
  have hij : (fieldCoordinateLp i (fieldInjectionLp j f) : Space → ℂ) =ᵐ[volume]
      fun x => (fieldInjection j (f x)) i := by
    filter_upwards [fieldCoordinateLp_ae i (fieldInjectionLp j f),
      (fieldInjection j).coeFn_compLpL f] with x hi hj
    exact hi.trans (congrArg (fun v : EuclideanSpace ℂ ι => v i) hj)
  by_cases h : j = i
  · rw [if_pos h]
    apply Lp.ext
    filter_upwards [hij] with x hx
    rw [hx]
    simp [fieldInjection, h]
  · rw [if_neg h]
    apply Lp.ext
    filter_upwards [hij, Lp.coeFn_zero (E := ℂ) (p := p) (μ := (volume : Measure Space))]
      with x hx hz
    rw [hx, hz]
    simp [fieldInjection, Ne.symm h]

/-- Apply the same scalar operator in every component of the Euclidean field. -/
def liftScalarLp (T : ComplexLp p →L[ℂ] ComplexLp p) :
    FieldLp ι p →L[ℂ] FieldLp ι p :=
  ∑ i, (fieldInjectionLp i).comp (T.comp (fieldCoordinateLp i))

theorem fieldCoordinateLp_liftScalarLp (T : ComplexLp p →L[ℂ] ComplexLp p)
    (f : FieldLp ι p) (i : ι) :
    fieldCoordinateLp i (liftScalarLp T f) = T (fieldCoordinateLp i f) := by
  classical
  simp [liftScalarLp, ContinuousLinearMap.sum_apply, map_sum, fieldCoordinateLp_injection]

theorem liftScalarLp_ae (T : ComplexLp p →L[ℂ] ComplexLp p) (f : FieldLp ι p) :
    (liftScalarLp T f : Space → EuclideanSpace ℂ ι) =ᵐ[volume]
      fun x => WithLp.toLp 2 (fun i => T (fieldCoordinateLp i f) x) := by
  have h (i : ι) : ∀ᵐ x ∂(volume : Measure Space),
      (liftScalarLp T f) x i = T (fieldCoordinateLp i f) x := by
    rw [← fieldCoordinateLp_liftScalarLp T f i]
    exact (fieldCoordinateLp_ae i (liftScalarLp T f)).symm
  filter_upwards [ae_all_iff.2 h] with x hx
  ext i
  exact hx i

theorem liftScalarLp_norm_le (T : ComplexLp p →L[ℂ] ComplexLp p)
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ f, ‖T f‖ ≤ C * ‖f‖) (f : FieldLp ι p) :
    ‖liftScalarLp T f‖ ≤ ((Fintype.card ι : ℝ) * C) * ‖f‖ := by
  simp only [liftScalarLp, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  calc
    _ ≤ ∑ i : ι, ‖fieldInjectionLp i (T (fieldCoordinateLp i f))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, C * ‖f‖ := Finset.sum_le_sum fun i _ =>
      (fieldInjectionLp_norm_le i _).trans
        ((hT _).trans (mul_le_mul_of_nonneg_left (fieldCoordinateLp_norm_le i f) hC))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

end Burnett.Analysis.CapFourier
