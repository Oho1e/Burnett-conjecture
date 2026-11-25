import Burnett.Analysis.FrozenTransport.V03SegmentTaylor

/-! The coefficient of the perturbed second jet and its actual spatial derivative. -/

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 300000

noncomputable section

namespace Burnett.V03

open MeasureTheory Set
open scoped ContDiff Interval Topology

variable {X V W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The negative first-order field Taylor defect is the coefficient multiplying
the full second jet of the perturbation. -/
def principalCoefficientRemainder (C : V → W) (g h : V) : W :=
  -linearTaylorRemainder C g h

theorem principalCoefficientRemainder_eq_integral [CompleteSpace W]
    (C : V → W) {U : Set V} (hU : IsOpen U) (hC : ContDiffOn ℝ ∞ C U) (g h : V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, fieldSegment g h t ∈ U) :
    principalCoefficientRemainder C g h =
      -(∫ t in (0 : ℝ)..1, (1 - t) • secondFDeriv C (fieldSegment g h t) h h) := by
  rw [principalCoefficientRemainder, linearTaylorRemainder_eq_integral C hU hC g h hseg]

theorem norm_principalCoefficientRemainder_le [CompleteSpace W]
    (C : V → W) {U : Set V} (hU : IsOpen U) (hC : ContDiffOn ℝ ∞ C U) (g h : V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, fieldSegment g h t ∈ U)
    {M₂ : ℝ} (hM₂ : ∀ t ∈ Icc (0 : ℝ) 1, ‖secondFDeriv C (fieldSegment g h t)‖ ≤ M₂) :
    ‖principalCoefficientRemainder C g h‖ ≤ M₂ * ‖h‖^2 := by
  rw [principalCoefficientRemainder, norm_neg]
  exact norm_linearTaylorRemainder_le C hU hC g h hseg hM₂

/-- The spatial derivative of the principal coefficient has one term with the
background gradient and one with the perturbation gradient. Hessian symmetry
places the background gradient in the last argument of the first remainder. -/
theorem fderiv_principalCoefficientRemainder (C : V → W) {U : Set V}
    (hU : IsOpen U) (hC : ContDiffOn ℝ ∞ C U) (g h : X → V) (x v : X)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, fieldSegment (g x) (h x) t ∈ U) :
    fderiv ℝ (fun y => principalCoefficientRemainder C (g y) (h y)) x v =
      -(linearTaylorRemainder (fderiv ℝ C) (g x) (h x) (fderiv ℝ g x v) +
        (fderiv ℝ C (g x + h x) - fderiv ℝ C (g x)) (fderiv ℝ h x v)) := by
  have hx : g x ∈ U := by simpa only [fieldSegment, zero_smul, add_zero] using hseg 0 (by simp)
  have hx' : g x + h x ∈ U := by simpa only [fieldSegment, one_smul] using hseg 1 (by simp)
  have hCX := hC.contDiffAt (hU.mem_nhds hx)
  have hC₀ := (hCX.differentiableAt (by simp)).hasFDerivAt
  have hC₁ := ((hC.contDiffAt (hU.mem_nhds hx')).differentiableAt (by simp)).hasFDerivAt
  have hDC : ContDiffOn ℝ ∞ (fderiv ℝ C) U := hC.fderiv_of_isOpen hU (by simp)
  have hD₀ := ((hDC.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hD := ((hC₁.comp x (hg.hasFDerivAt.add hh.hasFDerivAt)).sub (hC₀.comp x hg.hasFDerivAt)).sub
    ((hD₀.comp x hg.hasFDerivAt).clm_apply hh.hasFDerivAt) |>.neg
  change HasFDerivAt (fun y => principalCoefficientRemainder C (g y) (h y)) _ x at hD
  rw [hD.fderiv]
  simp only [linearTaylorRemainder, ContinuousLinearMap.neg_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    Function.comp_apply, map_add]
  have hsym := hCX.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [hsym (fderiv ℝ g x v) (h x)]
  abel

/-- Only the first spatial derivatives occur in the bound for the full spatial
Fréchet derivative of the coefficient. -/
theorem norm_fderiv_principalCoefficientRemainder_le [CompleteSpace W]
    (C : V → W) {U : Set V} (hU : IsOpen U) (hC : ContDiffOn ℝ ∞ C U)
    (g h : X → V) (x : X) (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, fieldSegment (g x) (h x) t ∈ U)
    {M₂ M₃ : ℝ}
    (hM₂ : ∀ t ∈ Icc (0 : ℝ) 1, ‖secondFDeriv C (fieldSegment (g x) (h x) t)‖ ≤ M₂)
    (hM₃₀ : 0 ≤ M₃)
    (hM₃ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v,
      ‖thirdFDeriv C (fieldSegment (g x) (h x) t) (h x) (h x) v‖ ≤ M₃ * ‖h x‖^2 * ‖v‖) :
    ‖fderiv ℝ (fun y => principalCoefficientRemainder C (g y) (h y)) x‖ ≤
      M₃ * ‖h x‖^2 * ‖fderiv ℝ g x‖ + M₂ * ‖h x‖ * ‖fderiv ℝ h x‖ := by
  have h2 : 0 ≤ M₂ :=
    (ContinuousLinearMap.opNorm_nonneg (E := V) (F := V →L[ℝ] W) (σ₁₂ := RingHom.id ℝ)
      (secondFDeriv C (fieldSegment (g x) (h x) 0))).trans (hM₂ 0 (by simp))
  have hDC : ContDiffOn ℝ ∞ (fderiv ℝ C) U := hC.fderiv_of_isOpen hU (by simp)
  let A := linearTaylorRemainder (fderiv ℝ C) (g x) (h x)
  let D := fderiv ℝ C (g x + h x) - fderiv ℝ C (g x)
  have hA (w : V) : ‖A w‖ ≤ M₃ * ‖h x‖^2 * ‖w‖ :=
    norm_linearTaylorRemainder_fderiv_apply_le C hU hC (g x) (h x) w hseg
      (fun t ht => hM₃ t ht w)
  have hD : ‖D‖ ≤ M₂ * ‖h x‖ :=
    norm_sub_le_of_first_field_bound (fderiv ℝ C) hU hDC (g x) (h x) hseg hM₂
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [fderiv_principalCoefficientRemainder C hU hC g h x v hg hh hseg, norm_neg]
  change ‖A (fderiv ℝ g x v) + D (fderiv ℝ h x v)‖ ≤ _
  calc
    _ ≤ M₃ * ‖h x‖^2 * ‖fderiv ℝ g x v‖ + ‖D‖ * ‖fderiv ℝ h x v‖ :=
      (norm_add_le _ _).trans
        (add_le_add (hA _) (ContinuousLinearMap.le_opNorm _ _))
    _ ≤ (M₃ * ‖h x‖^2) * (‖fderiv ℝ g x‖ * ‖v‖) +
        (M₂ * ‖h x‖) * (‖fderiv ℝ h x‖ * ‖v‖) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (by positivity))
        (mul_le_mul hD (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) (by positivity))
    _ = _ := by ring

end Burnett.V03
