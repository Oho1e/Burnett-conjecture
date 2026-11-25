import Burnett.Analysis.Microlocal.Overlap.AngularBilateralPrincipal

/-! The actual infrared-regularized symbol sees a fixed covector along a high-frequency ray. -/
set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 3900000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Filter Set Burnett.Fourier Burnett.Microlocal.Overlap
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E radialCore radialCore_eq_zero radialCore_nonneg radialCore_le_one)
open scoped Topology

theorem norm_infraredAngularPrincipal_le (a : E → E → ℂ) (x ξ : E) :
    ‖infraredAngularPrincipal a x ξ‖ ≤ ‖a x ξ‖ := by
  rw [infraredAngularPrincipal, norm_mul,
    show (1 - (radialCore ξ : ℂ)) = ((1 - radialCore ξ : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr (radialCore_le_one ξ))]
  exact mul_le_of_le_one_left (norm_nonneg _) (sub_le_self _ (radialCore_nonneg ξ))

/-- The prescribed fixed infrared cutoff is eventually one. The unshifted
small frequency divided by the modulation scale tends to zero in the symbol. -/
theorem tendsto_infraredAngularPrincipal_along_modulation
    (a : E → E → ℂ) (x ξ η : E) (hξ : ξ ≠ 0)
    (hCont : ContinuousAt (a x) ξ) (hDegree : DegreeZero (a x)) :
    Tendsto (fun n : ℕ => infraredAngularPrincipal a x ((n : ℝ) • ξ + η)) atTop (𝓝 (a x ξ)) := by
  have hNat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hInv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hNat
  have hArg : Tendsto (fun n : ℕ => ξ + (n : ℝ)⁻¹ • η) atTop (𝓝 ξ) := by
    simpa only [zero_smul, add_zero] using (tendsto_const_nhds.add (hInv.smul_const η) :
      Tendsto (fun n : ℕ => ξ + (n : ℝ)⁻¹ • η) atTop (𝓝 (ξ + (0 : ℝ) • η)))
  have hArgT := hCont.tendsto.comp hArg
  refine hArgT.congr' ?_
  have hNorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  filter_upwards [hNat.eventually_ge_atTop 1, hNat.eventually_ge_atTop ((2 + ‖η‖) / ‖ξ‖)] with n h1 hn
  have hp : 0 < (n : ℝ) := zero_lt_one.trans_le h1
  have hBig : 2 + ‖η‖ ≤ ‖(n : ℝ) • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg hp.le]
    exact (div_le_iff₀ hNorm).mp hn
  have h2 : 2 ≤ ‖(n : ℝ) • ξ + η‖ := by
    have hub := norm_sub_le ((n : ℝ) • ξ + η) η
    rw [add_sub_cancel_right] at hub
    linarith only [hub, hBig]
  have he : (n : ℝ) • (ξ + (n : ℝ)⁻¹ • η) = (n : ℝ) • ξ + η := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
  change a x (ξ + (n : ℝ)⁻¹ • η) = infraredAngularPrincipal a x ((n : ℝ) • ξ + η)
  rw [infraredAngularPrincipal, radialCore_eq_zero _ h2, Complex.ofReal_zero, sub_zero, one_mul, ← he]
  exact (hDegree (n : ℝ) hp (ξ + (n : ℝ)⁻¹ • η)).symm

end Burnett.Microlocal.AtlasOverlapKernel
