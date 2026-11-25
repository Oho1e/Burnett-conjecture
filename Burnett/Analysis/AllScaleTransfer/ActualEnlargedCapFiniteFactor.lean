import Burnett.Analysis.AllScaleTransfer.FiniteRadialFactorSpectrum
import Burnett.Analysis.AngularCaps.CapMultiplierLp
import Burnett.Analysis.AllScaleTransfer.RadianTrilinearChange
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualSymbolInputs

set_option autoImplicit false
set_option maxHeartbeats 4100000
noncomputable section

namespace Burnett.A05

open Set Filter MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier Burnett.Analysis.ProjectiveNullCaps Burnett.Fourier
open scoped Topology ContDiff ENNReal FourierTransform

private theorem tau_pos : 0 < tau := mul_pos (by norm_num) Real.pi_pos

/-- Applying the actual enlarged cap to a finite annular Schwartz factor
has a Schwartz representative, with its exact original radian spectrum. -/
theorem exists_enlargedCap_finiteIntegerRadialTruncation_schwartz
    (m : Form) (δ : ℝ) {η : ℝ} (hη : 0 < η) (outer enlarged : ℝ)
    {w : Vec} (hw : w ≠ 0) (J : Finset ℤ) (ε : ℤ → ℂ) (f : SchwartzMap E ℂ) :
    let b := enlargedCapMultiplier m δ η outer enlarged w
    let F := finiteIntegerRadialTruncation J ε f
    ∃ g : SchwartzMap E ℂ, (∀ x, g x = radianAction b F x) ∧
      (∀ ξ, radianFourier (g : E → ℂ) ξ = (b ξ : ℂ) * radianFourier (F : E → ℂ) ξ) ∧
      tsupport (radianFourier (g : E → ℂ)) ⊆ tsupport b ∩ tsupport (radianFourier (F : E → ℂ)) := by
  intro b F
  let M := radianActionSpectrum b F
  let D : E ≃L[ℝ] E :=
    (LinearEquiv.smulOfNeZero (K := ℝ) (M := E) tau tau_pos.ne').toContinuousLinearEquiv
  let K := D ⁻¹' finiteIntegerRadialFrequencySupport J
  have hK : IsCompact K :=
    D.toHomeomorph.isCompact_preimage.mpr (finiteIntegerRadialFrequencySupport_compact J)
  have h0 : (0 : E) ∉ K := by
    change D 0 ∉ finiteIntegerRadialFrequencySupport J
    rw [map_zero]
    exact zero_notMem_finiteIntegerRadialFrequencySupport J
  have hFrequency (ξ : E) :
      M ξ = (b (D ξ) : ℂ) * radianFourier (F : E → ℂ) (D ξ) := by
    change (b (tau • ξ) : ℂ) * 𝓕 (F : E → ℂ) ξ = _
    change _ = (b (tau • ξ) : ℂ) * radianFourier (F : E → ℂ) (tau • ξ)
    rw [radianFourier_scaled]
  have hSupport : tsupport M ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro ξ hξ
    have hn := Function.mem_support.mp hξ
    rw [hFrequency] at hn
    have hF : radianFourier (F : E → ℂ) (D ξ) ≠ 0 := fun e => hn (by rw [e, mul_zero])
    exact tsupport_radianFourier_finiteIntegerRadialTruncation J ε f (subset_tsupport _ hF)
  have hCompact : HasCompactSupport M := hK.of_isClosed_subset isClosed_closure hSupport
  have hOff : ContDiffOn ℝ ∞ M puncturedFrequency :=
    radianActionSpectrum_smooth b (enlargedCapMultiplier_contDiffOn m δ hη outer enlarged hw) F
  have hSmooth : ContDiff ℝ ∞ M := by
    apply contDiff_iff_contDiffAt.mpr
    intro ξ
    by_cases hξ : ξ = 0
    · subst ξ
      have hE : M =ᶠ[𝓝 (0 : E)] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun hz => h0 (hSupport hz))
      exact contDiffAt_const.congr_of_eventuallyEq hE
    · exact hOff.contDiffAt (isOpen_puncturedFrequency.mem_nhds hξ)
  let Mtest := hCompact.toSchwartzMap hSmooth
  let g := (SchwartzMap.fourierTransformCLE ℂ).symm Mtest
  have hg (ξ : E) : 𝓕 (g : E → ℂ) ξ = M ξ :=
    congrArg (fun a : SchwartzMap E ℂ => a ξ)
      ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply Mtest)
  have hAction : (g : E → ℂ) = radianAction b F := by
    have e : (g : E → ℂ) = 𝓕⁻ M := SchwartzMap.fourierTransformCLE_symm_apply ℂ Mtest
    exact e.trans (radianActionSpectrum_inverse b F)
  have radian (v : SchwartzMap E ℂ) (ξ : E) :
      radianFourier (v : E → ℂ) ξ = 𝓕 (v : E → ℂ) (tau⁻¹ • ξ) := by
    rw [← radianFourier_scaled, smul_smul, mul_inv_cancel₀ tau_pos.ne', one_smul]
  have hFourier (ξ : E) :
      radianFourier (g : E → ℂ) ξ = (b ξ : ℂ) * radianFourier (F : E → ℂ) ξ := by
    have cancel : D (tau⁻¹ • ξ) = ξ := by
      change tau • (tau⁻¹ • ξ) = ξ
      rw [smul_smul, mul_inv_cancel₀ tau_pos.ne', one_smul]
    rw [radian g, hg, hFrequency, cancel]
  refine ⟨g, congrFun hAction, hFourier, ?_⟩
  have e : radianFourier (g : E → ℂ) = fun ξ => b ξ • radianFourier (F : E → ℂ) ξ := by
    funext ξ
    rw [hFourier, Complex.real_smul]
  rw [e]
  exact subset_inter (tsupport_smul_subset_left b _) (tsupport_smul_subset_right b _)

/-- After the actual cap change of variables, the corresponding Fourier
support lies in the pullback of the same physical cap support. -/
theorem tsupport_radianFourier_pullbackTrilinearFactor_subset
    (A : E ≃L[ℝ] E) (u : SchwartzMap E ℂ) (b : E → ℝ)
    (hSupport : tsupport (radianFourier (u : E → ℂ)) ⊆ tsupport b) :
    tsupport (radianFourier (pullbackTrilinearFactor A u : E → ℂ)) ⊆ A ⁻¹' tsupport b := by
  apply closure_minimal _ (isClosed_closure.preimage A.continuous)
  intro ξ hξ
  change A ξ ∈ tsupport b
  apply hSupport
  apply subset_tsupport
  intro hz
  have e := radianFourier_comp_inverseDual A (u : E → ℂ) ξ
  change radianFourier (pullbackTrilinearFactor A u : E → ℂ) ξ =
    linearJacobian A • radianFourier (u : E → ℂ) (A ξ) at e
  rw [hz, smul_zero] at e
  exact Function.mem_support.mp hξ e

local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The representative of this finite factor agrees with both already
identified realizations of the cap multiplier. -/
theorem finiteIntegerRadialTruncation_capLp_realization_eq
    {b : E → ℝ} {C : ℝ} (P : CapLpRealization 3 b C)
    (J : Finset ℤ) (ε : ℤ → ℂ) (f u : SchwartzMap E ℂ)
    (hAction : ∀ x, u x = radianAction b (finiteIntegerRadialTruncation J ε f) x) :
    let F := finiteIntegerRadialTruncation J ε f
    (P.action (F.toLp 3 volume) : E → ℂ) =ᵐ[volume] (u : E → ℂ) ∧
      (fourierMultiplier P.symbol (F.toLp 2 volume) : E → ℂ) =ᵐ[volume] (u : E → ℂ) := by
  intro F
  have h3 : (P.action (F.toLp 3 volume) : E → ℂ) =ᵐ[volume] (u : E → ℂ) :=
    (P.schwartz_eq F).trans (Eventually.of_forall fun x => (hAction x).symm)
  exact ⟨h3, (P.intersection_eq (F : E → ℂ) (F.memLp 2 volume) (F.memLp 3 volume)).symm.trans h3⟩

end Burnett.A05
