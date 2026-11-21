import Burnett.Analysis.PrincipalEnergy.Commutator.HighConstantSubtraction

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Set Metric Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff

def translatedOscillationCutoff (χ : SchwartzMap E ℂ) (hχ : HasCompactSupport (χ : E → ℂ))
    (c : E) {R : ℝ} (hR : 0 < R) : SchwartzMap E ℂ := by
  have hS : 0 < 2*R := by positivity
  let e : E ≃ₜ E := (Homeomorph.subRight c).trans
    (Homeomorph.smulOfNeZero ((2*R)⁻¹) (inv_ne_zero hS.ne'))
  have hC : HasCompactSupport (fun y : E => χ ((2*R)⁻¹ • (y-c))) := hχ.comp_homeomorph e
  have hD : ContDiff ℝ ∞ (χ : E → ℂ) := χ.smooth _
  exact hC.toSchwartzMap (hD.comp (contDiff_const.smul (contDiff_id.sub contDiff_const)))

@[simp] theorem translatedOscillationCutoff_apply (χ : SchwartzMap E ℂ)
    (hχ : HasCompactSupport (χ : E → ℂ)) (c : E) {R : ℝ} (hR : 0 < R) (y : E) :
    translatedOscillationCutoff χ hχ c hR y = χ ((2*R)⁻¹ • (y-c)) := rfl

def localOscillationRamp (r χ : SchwartzMap E ℂ) (hχ : HasCompactSupport (χ : E → ℂ))
    (c : E) {R : ℝ} (hR : 0 < R) : SchwartzMap E ℂ :=
  let q := translatedOscillationCutoff χ hχ c hR
  scalarSchwartzProduct q r - r c • q

@[simp] theorem localOscillationRamp_apply (r χ : SchwartzMap E ℂ)
    (hχ : HasCompactSupport (χ : E → ℂ)) (c : E) {R : ℝ} (hR : 0 < R) (y : E) :
    localOscillationRamp r χ hχ c hR y = χ ((2*R)⁻¹ • (y-c)) * (r y-r c) := by
  simp only [localOscillationRamp,SchwartzMap.sub_apply,scalarSchwartzProduct_apply,
    SchwartzMap.smul_apply,translatedOscillationCutoff_apply,smul_eq_mul]
  ring

/-- The actual complementary input equals the original central value on the
doubled ball and grows from it at most at the original Lipschitz rate. -/
theorem localOscillationRamp_complement (r χ : SchwartzMap E ℂ) (L : NNReal)
    (hLip : LipschitzWith L r) (hχ : HasCompactSupport (χ : E → ℂ))
    (hOne : ∀ y : E, ‖y‖ ≤ 1 → χ y = 1) (hBound : ∀ y : E, ‖1-χ y‖ ≤ 1)
    (c : E) {R : ℝ} (hR : 0 < R) :
    let g := r - localOscillationRamp r χ hχ c hR
    (∀ y ∈ ball c (2*R), g y = r c) ∧
      ∀ y, ‖g y-r c‖ ≤ (L : ℝ) * ‖c-y‖ := by
  have hS : 0 < 2*R := by positivity
  intro g
  have hG (y : E) : g y-r c = (1-χ ((2*R)⁻¹ • (y-c))) * (r y-r c) := by
    simp only [g,SchwartzMap.sub_apply,localOscillationRamp_apply]
    ring
  refine ⟨?_,?_⟩
  · intro y hy
    have hz : ‖(2*R)⁻¹ • (y-c)‖ ≤ 1 := by
      have hDist : ‖y-c‖ ≤ 2*R := (show ‖y-c‖ < 2*R by simpa only [mem_ball,dist_eq_norm] using hy).le
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hS.le), ← div_eq_inv_mul]
      exact (div_le_one hS).mpr hDist
    apply sub_eq_zero.mp
    rw [hG,hOne _ hz,sub_self,zero_mul]
  · intro y
    rw [hG,norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (hBound _)).trans ?_
    simpa only [dist_eq_norm,norm_sub_rev y c] using hLip.dist_le_mul y c

/-- Quantitative support, amplitude and actual derivative controls for the
original scalar coefficient after subtraction and localization. -/
theorem localOscillationRamp_bounds (r χ : SchwartzMap E ℂ) (L : NNReal)
    (hLip : LipschitzWith L r) (U D : ℝ) (hD : 0 ≤ D)
    (hValue : ∀ y : E, ‖r y‖ ≤ U) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχS : tsupport (χ : E → ℂ) ⊆ closedBall 0 2) (hχVal : ∀ y : E, ‖χ y‖ ≤ 1)
    (hχDer : ∀ y : E, ‖fderiv ℝ (χ : E → ℂ) y‖ ≤ D) (c : E) {R : ℝ} (hR : 0 < R) :
    let f := localOscillationRamp r χ hχ c hR
    tsupport (f : E → ℂ) ⊆ closedBall c (4*R) ∧
      (∀ y, ‖f y‖ ≤ 2*U) ∧ (∀ y, ‖fderiv ℝ (f : E → ℂ) y‖ ≤ (1+2*D)*(L : ℝ)) := by
  have hS : 0 < 2*R := by positivity
  intro f
  have hEq : (f : E → ℂ) = fun y => χ ((2*R)⁻¹ • (y-c)) * (r y-r c) :=
    funext (localOscillationRamp_apply r χ hχ c hR)
  have hSupport : tsupport (f : E → ℂ) ⊆ closedBall c (4*R) := by
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    have hNon : χ ((2*R)⁻¹ • (y-c)) ≠ 0 := by
      intro h
      exact hy (by simp only [hEq,h,zero_mul])
    have hp : ‖(2*R)⁻¹ • (y-c)‖ ≤ 2 := by
      simpa only [mem_closedBall,dist_zero_right] using hχS (subset_closure hNon)
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hS.le), ← div_eq_inv_mul] at hp
    rw [mem_closedBall,dist_eq_norm]
    exact ((div_le_iff₀ hS).mp hp).trans_eq (by ring)
  refine ⟨hSupport,?_,?_⟩
  · intro y
    rw [hEq,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hχVal _)).trans
      ((norm_sub_le _ _).trans (by linarith [hValue y,hValue c]))
  · intro y
    by_cases hy : y ∈ closedBall c (4*R)
    · let A := (2*R)⁻¹ • ContinuousLinearMap.id ℝ E
      have hA (z : E) : A z = (2*R)⁻¹ • z := rfl
      have hA₀ : ‖A‖ ≤ (2*R)⁻¹ :=
        A.opNorm_le_bound (inv_nonneg.mpr hS.le) (fun z => by
          rw [hA,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hS.le)])
      have hAffine : HasFDerivAt (fun z : E => (2*R)⁻¹ • (z-c)) A y := by
        have hh : HasFDerivAt (fun z : E => z-c) (ContinuousLinearMap.id ℝ E) y :=
          (hasFDerivAt_id y).sub_const c
        exact A.hasFDerivAt.comp y hh
      have hχF := χ.differentiableAt.hasFDerivAt.comp y hAffine
      have hrF : HasFDerivAt (fun z : E => r z-r c) (fderiv ℝ (r : E → ℂ) y) y :=
        r.differentiableAt.hasFDerivAt.sub_const (r c)
      have hBoth := hχF.mul hrF
      have hProd : fderiv ℝ (f : E → ℂ) y =
          χ ((2*R)⁻¹ • (y-c)) • fderiv ℝ (r : E → ℂ) y +
            (r y-r c) • ((fderiv ℝ (χ : E → ℂ) ((2*R)⁻¹ • (y-c))).comp A) := by
        rw [hEq]
        exact hBoth.fderiv
      have hDiff : ‖r y-r c‖ ≤ (L : ℝ)*(4*R) :=
        (by simpa only [dist_eq_norm] using hLip.dist_le_mul y c : ‖r y-r c‖ ≤ (L : ℝ)*‖y-c‖).trans
          (mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall,dist_eq_norm] using hy) L.coe_nonneg)
      have hComp : ‖(fderiv ℝ (χ : E → ℂ) ((2*R)⁻¹ • (y-c))).comp A‖ ≤ D * (2*R)⁻¹ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (hχDer _) hA₀ (norm_nonneg _) hD)
      rw [hProd]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul,norm_smul]
      calc
        _ ≤ (L : ℝ) + ((L : ℝ)*(4*R))*(D*(2*R)⁻¹) := by
          refine add_le_add ?_ (mul_le_mul hDiff hComp (norm_nonneg _) (by positivity))
          exact (mul_le_of_le_one_left (norm_nonneg _) (hχVal _)).trans
            (norm_fderiv_le_of_lipschitz ℝ hLip)
        _ = _ := by field_simp [hR.ne']; ring
    · have hf0 : fderiv ℝ (f : E → ℂ) y = 0 := by
        by_contra hz
        exact hy (hSupport (support_fderiv_subset ℝ hz))
      rw [hf0,norm_zero]
      positivity

end Burnett.Analysis.FirstOrderDyadic
