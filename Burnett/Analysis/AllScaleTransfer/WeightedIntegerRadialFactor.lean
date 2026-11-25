import Burnett.Analysis.AllScaleTransfer.ActualIntegerRadialPartition
import Burnett.Analysis.SignedFourierWindow.SignedWindowAllLp

set_option autoImplicit false
set_option maxHeartbeats 3400000
noncomputable section

namespace Burnett.A05
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow

open MeasureTheory
open Burnett.A02.FrequencySplit
open scoped ENNReal FourierTransform

private theorem tau_pos : 0 < tau := mul_pos (by norm_num) Real.pi_pos

private def windowScale (j : ℤ) : ℝ := tau * (2 : ℝ)^(-j)

private theorem windowScale_pos (j : ℤ) : 0 < windowScale j :=
  mul_pos tau_pos (by positivity)

/-- The manuscript's finite weighted integer radial truncation, on the
actual input Schwartz test. -/
def finiteIntegerRadialTruncation
    (J : Finset ℤ) (ε : ℤ → ℂ) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  ∑ j ∈ J, ε j • windowTest endpointHighProfile f (windowScale j)

private theorem schwartz_sum_apply {ι : Type*} (J : Finset ι) (F : ι → SchwartzMap E ℂ) (x : E) :
    (∑ j ∈ J, F j) x = ∑ j ∈ J, F j x := by
  simpa only [SchwartzMap.coe_coeHom, Finset.sum_apply] using
    congrFun (map_sum (SchwartzMap.coeHom E ℂ) F J) x

/-- Exact pointwise action by the given weighted integer windows in the
same radian frequency as the manuscript's trilinear form. -/
theorem finiteIntegerRadialTruncation_radianFourier
    (J : Finset ℤ) (ε : ℤ → ℂ) (f : SchwartzMap E ℂ) (ξ : E) :
    radianFourier (finiteIntegerRadialTruncation J ε f : E → ℂ) ξ =
      (∑ j ∈ J, ε j * (integerRadialWindow j ξ : ℂ)) * radianFourier (f : E → ℂ) ξ := by
  have convention (g : SchwartzMap E ℂ) :
      radianFourier (g : E → ℂ) ξ = 𝓕 (g : E → ℂ) (tau⁻¹ • ξ) := by
    rw [← radianFourier_scaled, smul_smul, mul_inv_cancel₀ tau_pos.ne', one_smul]
  have scale (j : ℤ) : windowScale j • (tau⁻¹ • ξ) = ((2 : ℝ)^(-j)) • ξ := by
    rw [windowScale, smul_smul, mul_comm tau, mul_assoc, mul_inv_cancel₀ tau_pos.ne', mul_one]
  rw [convention, convention f]
  change (SchwartzMap.fourierTransformCLM ℂ (finiteIntegerRadialTruncation J ε f)) (tau⁻¹ • ξ) = _
  rw [finiteIntegerRadialTruncation, map_sum, schwartz_sum_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul (SchwartzMap.fourierTransformCLM ℂ) (ε j), SchwartzMap.smul_apply, smul_eq_mul]
  change ε j * 𝓕 (windowTest endpointHighProfile f (windowScale j) : E → ℂ) (tau⁻¹ • ξ) = _
  rw [windowTest_fourier, scale, endpointHighProfile_eq_integerRadialWindow]
  ring

/-- The same Schwartz factor is the actual convolution of the finite
integer kernel, with its original coefficients. -/
theorem finiteIntegerRadialTruncation_eq_kernel
    (J : Finset ℤ) (ε : ℤ → ℂ) (f : SchwartzMap E ℂ) (x : E) :
    finiteIntegerRadialTruncation J ε f x =
      kernelApply (fun z => ∑ j ∈ J, ε j *
        shiftedSpatialKernel ((SchwartzMap.fourierTransformCLE ℂ).symm endpointHighProfile)
          (windowScale j) 0 z) f x := by
  let φ := (SchwartzMap.fourierTransformCLE ℂ).symm endpointHighProfile
  let K (j : ℤ) := shiftedSpatialKernel φ (windowScale j) 0
  have integrableTerm (j : ℤ) : Integrable (fun y : E => K j (x - y) * f y) := by
    let B := |((windowScale j)^4)⁻¹| * SchwartzMap.seminorm ℝ 0 0 φ
    refine (f.integrable.norm.const_mul B).mono' (by dsimp only [K, shiftedSpatialKernel]; fun_prop) ?_
    filter_upwards with y
    simp only [K, shiftedSpatialKernel, B, norm_mul, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ φ _) (abs_nonneg _)) (norm_nonneg _)
  have one (j : ℤ) : ε j * windowTest endpointHighProfile f (windowScale j) x =
      ∫ y : E, ε j * (K j (x - y) * f y) := by
    have h := windowTest_translate endpointHighProfile f (windowScale j) 0 (windowScale_pos j) x (0 : E)
    have hzero : windowTest endpointHighProfile f (windowScale j) x =
        shiftedWindowOperator endpointHighProfile f (windowScale j) 0 x := by
      simpa only [zero_smul, sub_zero, smul_zero] using h
    rw [hzero, shifted_window_physical _ _ _ (windowScale_pos j), ← integral_const_mul]
    rfl
  rw [finiteIntegerRadialTruncation, schwartz_sum_apply]
  simp only [SchwartzMap.smul_apply, smul_eq_mul]
  simp_rw [one]
  rw [← integral_finset_sum J (fun j _ => (integrableTerm j).const_mul (ε j))]
  unfold kernelApply
  apply integral_congr_ae
  filter_upwards with y
  simp only [K, φ, Finset.sum_mul, mul_assoc]

/-- One uniform L³ bound for each actual input factor and every finite
subset of the integer lattice carrying coefficients of norm at most one. -/
theorem exists_finiteIntegerRadialTruncation_L3_bound :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (J : Finset ℤ) (ε : ℤ → ℂ), (∀ j ∈ J, ‖ε j‖ ≤ 1) →
        ∀ f : SchwartzMap E ℂ,
          eLpNorm (finiteIntegerRadialTruncation J ε f : E → ℂ) (ENNReal.ofReal 3) volume ≤
            C * eLpNorm (f : E → ℂ) (ENNReal.ofReal 3) volume := by
  obtain ⟨C, hC, H⟩ := signed_window_all_Lp endpointHighProfile
    endpointHighProfile_properties.2.1 endpointHighProfile_properties.2.2 3 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro J ε hε f
  let N : ℤ := if hJ : J.Nonempty then J.max' hJ else 0
  have upper (j : ℤ) (hj : j ∈ J) : j ≤ N := by
    simp only [N, dif_pos (show J.Nonempty from ⟨j,hj⟩)]
    exact Finset.le_max' _ _ hj
  let k (j : ℤ) := (N-j).toNat
  have back (j : ℤ) (hj : j ∈ J) : (k j : ℤ) = N-j :=
    Int.toNat_of_nonneg (sub_nonneg.mpr (upper j hj))
  have injectiveOn : Set.InjOn k (↑J : Set ℤ) := by
    intro i hi j hj eq
    have e := congrArg (fun n : ℕ => (n : ℤ)) eq
    change (k i : ℤ) = (k j : ℤ) at e
    rw [back i hi, back j hj] at e
    omega
  let t := windowScale N
  have scale (j : ℤ) (hj : j ∈ J) : (2 : ℝ)^(k j) * t = windowScale j := by
    calc
      _ = tau * ((2 : ℝ)^(k j) * (2 : ℝ)^(-N)) := by dsimp [t, windowScale]; ring
      _ = tau * (2 : ℝ)^((k j : ℤ) + -N) := by
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = _ := by rw [back j hj, show N - j + -N = -j by omega]; rfl
  let c (n : ℕ) := if N-(n : ℤ) ∈ J then ε (N-(n : ℤ)) else 0
  have hc (n : ℕ) : ‖c n‖ ≤ 1 := by
    dsimp only [c]
    split_ifs with h
    · exact hε _ h
    · simp
  let φ := (SchwartzMap.fourierTransformCLE ℂ).symm endpointHighProfile
  have eqKernel : finiteWindowKernel φ t 0 (J.image k) c =
      fun z => ∑ j ∈ J, ε j * shiftedSpatialKernel φ (windowScale j) 0 z := by
    funext z
    unfold finiteWindowKernel
    rw [Finset.sum_image injectiveOn]
    apply Finset.sum_congr rfl
    intro j hj
    have ec : c (k j) = ε j := by
      dsimp only [c]
      rw [back j hj, show N - (N-j) = j by omega, if_pos hj]
    rw [ec, scale j hj]
  have bound := H t (windowScale_pos N) (0 : E) (J.image k) c hc (f : E → ℂ)
    (f.memLp (ENNReal.ofReal 3) volume)
  change eLpNorm (kernelApply (finiteWindowKernel φ t 0 (J.image k) c) f) _ _ ≤ _ at bound
  rw [eqKernel, ← funext (finiteIntegerRadialTruncation_eq_kernel J ε f)] at bound
  simpa only [norm_zero, add_zero, ENNReal.ofReal_one, mul_one] using bound

end Burnett.A05
