import Burnett.Analysis.Microlocal.Overlap.JointClassicalModulatedPairing
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Plane-wave tests recover the actual angular principal symbol from the whole-space pairing. -/
set_option autoImplicit false
set_option maxRecDepth 4500
set_option maxHeartbeats 5100000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Filter Function MeasureTheory Set Burnett.Fourier Burnett.Geometry.ConnectionDifference
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open scoped ComplexConjugate FourierTransform InnerProduct RealInnerProductSpace Topology

local notation "E" => CoordinateSpace

/-- Test along one growing frequency, keeping both ordinary compact profiles.
The limiting coefficient is exactly the classical principal symbol. -/
theorem tendsto_classicalLeftPairing_compactModulatedSchwartz
    (a : E → E → ℂ) (D : ℝ) (hD : ∀ x η, ‖a x η‖ ≤ D)
    (hP : Continuous (uncurry (infraredAngularPrincipal a))) (ξ : E) (hξ : ξ ≠ 0)
    (hCont : ∀ x, ContinuousAt (a x) ξ) (hDegree : ∀ x, DegreeZero (a x))
    (v f : SchwartzMap E ℂ) (hv : HasCompactSupport (v : E → ℂ)) (hf : HasCompactSupport (f : E → ℂ)) :
    Tendsto (fun n : ℕ => classicalLeftPairing (infraredAngularPrincipal a)
      (compactModulatedSchwartz ((n : ℝ) • ξ) v hv) (compactModulatedSchwartz ((n : ℝ) • ξ) f hf))
      atTop (𝓝 (∫ x, conj (v x) * (a x ξ * f x))) := by
  let G (n : ℕ) (z : E × E) := (Real.fourierChar ⟪z.2, z.1⟫ : ℂ) *
    (infraredAngularPrincipal a z.1 (z.2 + (n : ℝ) • ξ) * 𝓕 (f : E → ℂ) z.2)
  let H (x η : E) := (Real.fourierChar ⟪η, x⟫ : ℂ) * (a x ξ * 𝓕 (f : E → ℂ) η)
  let F := SchwartzMap.fourierTransformCLM ℂ f
  have hF : (F : E → ℂ) = 𝓕 (f : E → ℂ) := rfl
  have hGCont (n : ℕ) : Continuous (G n) := by
    have hFst : Continuous (fun z : E × E => z.1) := continuous_fst
    have hSnd : Continuous (fun z : E × E => z.2) := continuous_snd
    have hMove : Continuous (fun z : E × E => (z.1, z.2 + (n : ℝ) • ξ)) :=
      hFst.prodMk (hSnd.add continuous_const)
    have hPhase : Continuous (fun z : E × E => (Real.fourierChar ⟪z.2, z.1⟫ : ℂ)) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp (hSnd.inner hFst))
    exact hPhase.mul ((hP.comp hMove).mul (F.continuous.comp hSnd))
  have hBound (n : ℕ) (x η : E) : ‖G n (x, η)‖ ≤ D * ‖F η‖ := by
    change ‖(Real.fourierChar ⟪η, x⟫ : ℂ) *
      (infraredAngularPrincipal a x (η + (n : ℝ) • ξ) * 𝓕 (f : E → ℂ) η)‖ ≤ D * ‖F η‖
    rw [norm_mul, Circle.norm_coe, one_mul, norm_mul, ← hF]
    exact mul_le_mul_of_nonneg_right ((norm_infraredAngularPrincipal_le a _ _).trans (hD _ _)) (norm_nonneg _)
  have hInt (n : ℕ) (x : E) : Integrable (fun η => G n (x, η)) :=
    (F.integrable.norm.const_mul D).mono'
      ((hGCont n).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (Eventually.of_forall (hBound n x))
  have hInner (x : E) : Tendsto (fun n => ∫ η, G n (x, η)) atTop (𝓝 (a x ξ * f x)) := by
    have hL : Tendsto (fun n => ∫ η, G n (x, η)) atTop (𝓝 (∫ η, H x η)) := by
      apply tendsto_integral_of_dominated_convergence (fun η => D * ‖F η‖)
      · intro n
        exact (hInt n x).aestronglyMeasurable
      · exact F.integrable.norm.const_mul D
      · intro n
        exact Eventually.of_forall (hBound n x)
      · apply Eventually.of_forall
        intro η
        have h := tendsto_infraredAngularPrincipal_along_modulation a x ξ η hξ (hCont x) (hDegree x)
        have hAdd (n : ℕ) : (n : ℝ) • ξ + η = η + (n : ℝ) • ξ := add_comm _ _
        simpa only [G, H, hAdd] using
          ((h.mul_const (𝓕 (f : E → ℂ) η)).const_mul (Real.fourierChar ⟪η, x⟫ : ℂ))
    have hInv : 𝓕⁻ (𝓕 (f : E → ℂ)) x = f x := congrFun
      (f.continuous.fourier_inversion f.integrable (hF ▸ F.integrable)) x
    have heq : (∫ η, H x η) = a x ξ * f x := by
      rw [← hInv, Real.fourierIntegralInv_eq, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with η
      simp only [H, Circle.smul_def, smul_eq_mul]
      ring
    rwa [heq] at hL
  have hDom (n : ℕ) (x : E) : ‖conj (v x) * (∫ η, G n (x, η))‖ ≤
      ‖v x‖ * (D * ∫ η, ‖F η‖) := by
    rw [norm_mul, Complex.norm_conj, ← integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_integral_le_of_norm_le (F.integrable.norm.const_mul D) (Eventually.of_forall (hBound n x))) (norm_nonneg _)
  have hOuter : Tendsto (fun n => ∫ x, conj (v x) * (∫ η, G n (x, η)))
      atTop (𝓝 (∫ x, conj (v x) * (a x ξ * f x))) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖v x‖ * (D * ∫ η, ‖F η‖))
    · intro n
      exact (Complex.continuous_conj.comp v.continuous).aestronglyMeasurable.mul
        ((hGCont n).stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    · exact v.integrable.norm.mul_const _
    · intro n
      exact Eventually.of_forall (hDom n)
    · exact Eventually.of_forall (fun x => (hInner x).const_mul (conj (v x)))
  refine hOuter.congr (fun n => ?_)
  exact (classicalLeftPairing_compactModulatedSchwartz (infraredAngularPrincipal a) ((n : ℝ) • ξ) v f hv hf).symm

end Burnett.Microlocal.AtlasOverlapKernel
