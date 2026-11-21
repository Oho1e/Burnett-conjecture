import Burnett.Analysis.PrincipalEnergy.Quantization.LowKernelBaseDifference
import Burnett.Analysis.PrincipalEnergy.Quantization.LowFrequencyCommutator
import Burnett.Analysis.PrincipalEnergy.Quantization.SourceDifference

set_option autoImplicit false
set_option maxHeartbeats 3100000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff NNReal

private theorem continuous_bound_of_ae {f : E → ℝ} (hf : Continuous f) {C : ℝ}
    (h : ∀ᵐ x ∂(volume : Measure E), f x≤C) (x : E) : f x≤C := by
  by_contra hx
  have hU : IsOpen {y : E | C < f y} := isOpen_lt continuous_const hf
  have hNull : (volume : Measure E) {y : E | C < f y}=0 := by
    rw [ae_iff] at h
    simpa only [not_le] using h
  exact hU.measure_ne_zero volume ⟨x,lt_of_not_ge hx⟩ hNull

/-- On the smooth coefficients of the source, actual essential supremum
bounds of the function and its first derivative give the working
uniform and Lipschitz bounds with the same constants. -/
theorem smoothCoefficient_bounds_of_ae_norm_firstDerivative (r : E → ℂ) (hr : ContDiff ℝ 1 r)
    (U : ℝ) (L : NNReal) (hU : ∀ᵐ x ∂(volume : Measure E), ‖r x‖≤U)
    (hL : ∀ᵐ x ∂(volume : Measure E), ‖fderiv ℝ r x‖≤(L:ℝ)) :
    0≤U ∧ (∀ x, ‖r x‖≤U) ∧ LipschitzWith L r := by
  have hValue := continuous_bound_of_ae hr.continuous.norm hU
  have hSlope := continuous_bound_of_ae (hr.continuous_fderiv (by simp)).norm hL
  refine ⟨(norm_nonneg (r 0)).trans (hValue 0),hValue,
    lipschitzWith_of_nnnorm_fderiv_le (hr.differentiable (by simp)) (fun x => ?_)⟩
  exact_mod_cast hSlope x

private theorem low_commutator_target_bound {a : E → E → ℂ} {C D A : ℝ}
    (hD : 0≤D) (hA : 0≤A)
    (hSize : ∀ x z, z≠0 → ‖firstOrderLowKernel a x z‖≤C*(‖z‖^5)⁻¹)
    (hDer : ∀ x z, z≠0 → DifferentiableAt ℝ (firstOrderLowKernel a x) z ∧
      ‖fderiv ℝ (firstOrderLowKernel a x) z‖≤D*(‖z‖^6)⁻¹)
    (hBase : ∀ x y z, z≠0 →
      ‖firstOrderLowKernel a x z-firstOrderLowKernel a y z‖≤A*‖x-y‖*(‖z‖^6)⁻¹)
    (r : E → ℂ) (L : NNReal) (hr : LipschitzWith L r)
    (x x' y : E) (hxy : x≠y) (hGap : ‖x-x'‖≤‖x-y‖/2) :
    ‖lowCoefficientKernel a r x y-lowCoefficientKernel a r x' y‖≤
      (L:ℝ)*(C+96*D+32*A)*‖x-x'‖*(‖x-y‖^5)⁻¹ := by
  let k := firstOrderLowKernel a
  let reflected (_ z : E) := k x (-z)
  have hRSize (u z : E) (hz : z≠0) : ‖reflected u z‖≤C*(‖z‖^5)⁻¹ := by
    simpa only [reflected,k,norm_neg] using hSize x (-z) (neg_ne_zero.mpr hz)
  have hRDer (u z : E) (hz : z≠0) : DifferentiableAt ℝ (reflected u) z ∧
      ‖fderiv ℝ (reflected u) z‖≤D*(‖z‖^6)⁻¹ := by
    let N : E →L[ℝ] E := -ContinuousLinearMap.id ℝ E
    have hn : HasFDerivAt (fun w : E => -w) N z := N.hasFDerivAt
    obtain ⟨hd,hb⟩ := hDer x (-z) (neg_ne_zero.mpr hz)
    have hF : HasFDerivAt (reflected u) ((fderiv ℝ (k x) (-z)).comp N) z :=
      hd.hasFDerivAt.comp z hn
    refine ⟨hF.differentiableAt,?_⟩
    rw [hF.fderiv]
    have hN : ‖N‖≤1 := N.opNorm_le_bound zero_le_one (fun w => by
      change ‖-w‖≤1*‖w‖
      rw [norm_neg,one_mul])
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hN).trans (by simpa only [k,norm_neg] using hb))
  have hR := coefficientKernel_sourceDifference_le r hr reflected C D hD hRSize hRDer y x x'
    hxy.symm (by simpa only [norm_sub_rev y x] using hGap)
  let S := (r x-r y)*k x (x-y)-(r x'-r y)*k x (x'-y)
  have hS : ‖S‖≤(L:ℝ)*(C+96*D)*‖x-x'‖*(‖x-y‖^5)⁻¹ := by
    have hEq : coefficientKernel r reflected y x-coefficientKernel r reflected y x' = -S := by
      simp only [coefficientKernel,reflected,neg_sub,S]
      ring
    rwa [hEq,norm_neg,norm_sub_rev y x] at hR
  have hTri := norm_add_le (x'-y) (x-x')
  rw [show x'-y+(x-x')=x-y by abel] at hTri
  have hDist : ‖x-y‖/2≤‖x'-y‖ := by linarith
  have hPos : 0<‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hPos' : 0<‖x'-y‖ := (half_pos hPos).trans_le hDist
  have hLip : ‖r x'-r y‖≤(L:ℝ)*‖x'-y‖ := lipschitzWith_iff_norm_sub_le.mp hr x' y
  let T := (r x'-r y)*(k x (x'-y)-k x' (x'-y))
  have hT : ‖T‖≤(L:ℝ)*(32*A)*‖x-x'‖*(‖x-y‖^5)⁻¹ := by
    have hInv : (‖x'-y‖^5)⁻¹≤((‖x-y‖/2)^5)⁻¹ :=
      (inv_le_inv₀ (pow_pos hPos' _) (pow_pos (half_pos hPos) _)).mpr
        (pow_le_pow_left₀ (half_pos hPos).le hDist _)
    dsimp only [T]
    rw [norm_mul]
    calc
      _ ≤ ((L:ℝ)*‖x'-y‖)*(A*‖x-x'‖*(‖x'-y‖^6)⁻¹) :=
        mul_le_mul hLip (hBase x x' (x'-y) (norm_pos_iff.mp hPos')) (norm_nonneg _) (by positivity)
      _ = (L:ℝ)*A*‖x-x'‖*(‖x'-y‖^5)⁻¹ := by field_simp [hPos'.ne']
      _ ≤ (L:ℝ)*A*‖x-x'‖*((‖x-y‖/2)^5)⁻¹ :=
        mul_le_mul_of_nonneg_left hInv (mul_nonneg (mul_nonneg L.coe_nonneg hA) (norm_nonneg _))
      _ = _ := by field_simp [hPos.ne']; norm_num
  have hSplit : lowCoefficientKernel a r x y-lowCoefficientKernel a r x' y=S+T := by
    simp only [lowCoefficientKernel,S,T,k]
    ring
  rw [hSplit]
  exact (norm_add_le _ _).trans ((add_le_add hS hT).trans_eq (by ring))

/-- The actual fixed low-frequency commutator kernel has the size and both
spatial differences of the endpoint singular-integral class. -/
theorem exists_firstOrderLow_commutatorKernel_conditions {a : E → E → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) :
    ∃ K : ℝ, 0≤K ∧ ∀ (r : E → ℂ) (L : NNReal), LipschitzWith L r →
      (∀ x y : E, x≠y → ‖lowCoefficientKernel a r x y‖≤(L:ℝ)*K*(‖x-y‖^4)⁻¹) ∧
      (∀ x y y' : E, x≠y → ‖y-y'‖≤‖x-y‖/2 →
        ‖lowCoefficientKernel a r x y-lowCoefficientKernel a r x y'‖≤
          (L:ℝ)*K*‖y-y'‖*(‖x-y‖^5)⁻¹) ∧
      (∀ x x' y : E, x≠y → ‖x-x'‖≤‖x-y‖/2 →
        ‖lowCoefficientKernel a r x y-lowCoefficientKernel a r x' y‖≤
          (L:ℝ)*K*‖x-x'‖*(‖x-y‖^5)⁻¹) := by
  obtain ⟨C,D,hC,hD,hSize,hDer⟩ := exists_firstOrderLowKernel_relative_bounds ha.frequency
  obtain ⟨A,hA,hBase⟩ := exists_firstOrderLowKernel_baseDifference ha
  let K := C+96*D+32*A
  have hK : 0≤K := by dsimp only [K]; positivity
  have hCK : C≤K := by dsimp only [K]; linarith
  have hDK : C+96*D≤K := by dsimp only [K]; linarith
  refine ⟨K,hK,fun r L hr => ⟨?_,?_,low_commutator_target_bound hD hA hSize hDer hBase r L hr⟩⟩
  · intro x y hxy
    have hPos : 0<‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    rw [lowCoefficientKernel,norm_mul]
    calc
      _ ≤ ((L:ℝ)*‖x-y‖)*(C*(‖x-y‖^5)⁻¹) :=
        mul_le_mul (lipschitzWith_iff_norm_sub_le.mp hr x y) (hSize x (x-y) (sub_ne_zero.mpr hxy))
          (norm_nonneg _) (mul_nonneg L.coe_nonneg (norm_nonneg _))
      _ = (L:ℝ)*C*(‖x-y‖^4)⁻¹ := by field_simp [hPos.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCK L.coe_nonneg) (by positivity)
  · intro x y y' hxy hd
    have h := coefficientKernel_sourceDifference_le r hr (firstOrderLowKernel a) C D hD hSize hDer x y y' hxy hd
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDK L.coe_nonneg) (norm_nonneg _)) (by positivity))

end Burnett.Analysis.FirstOrderDyadic
