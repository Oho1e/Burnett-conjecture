import Burnett.Analysis.Microlocal.Overlap.JointClassicalModulatedTests
import Burnett.Analysis.Microlocal.Overlap.JointClassicalHighFrequencySymbol
import Burnett.Analysis.Microlocal.Overlap.LocalClassicalFullSymbol

/-! The exact full-space modulation identity for the original left-quantized pairing. -/
set_option autoImplicit false
set_option maxRecDepth 3900
set_option maxHeartbeats 4300000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Filter MeasureTheory Set Burnett.Fourier Burnett.Geometry.ConnectionDifference
open Burnett.Microlocal.Overlap
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open scoped ComplexConjugate FourierTransform RealInnerProductSpace Topology

local notation "E" => CoordinateSpace

private theorem firstOrderAction_compactModulatedSchwartz (a : E → E → ℂ) (k : E)
    (f : SchwartzMap E ℂ) (hf : HasCompactSupport (f : E → ℂ)) (x : E) :
    firstOrderAction a (compactModulatedSchwartz k f hf) x =
      (Real.fourierChar ⟪x, k⟫ : ℂ) * ∫ η, (Real.fourierChar ⟪η, x⟫ : ℂ) *
        (a x (η + k) * 𝓕 (f : E → ℂ) η) := by
  let V (ω : E) : ℂ := (Real.fourierChar ⟪ω, x⟫ : ℂ) *
    (a x ω * 𝓕 (f : E → ℂ) (ω - k))
  have he : (compactModulatedSchwartz k f hf : E → ℂ) = modulate k f :=
    funext (compactModulatedSchwartz_apply k f hf)
  calc
    _ = ∫ ω, V ω := by
      simp only [V, firstOrderAction, Real.fourierIntegralInv_eq, he, fourier_modulate, Circle.smul_def, smul_eq_mul]
    _ = ∫ η, V (η + k) := (integral_add_right_eq_self V k).symm
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with η
      simp only [V, add_sub_cancel_right, inner_add_left, Real.fourierChar.map_add_eq_mul, Circle.coe_mul,
        real_inner_comm k x]
      ring

/-- The two common modulation phases cancel exactly in the actual pairing,
leaving the original symbol translated by the physical frequency increment. -/
theorem classicalLeftPairing_compactModulatedSchwartz (a : E → E → ℂ) (k : E)
    (v f : SchwartzMap E ℂ) (hv : HasCompactSupport (v : E → ℂ)) (hf : HasCompactSupport (f : E → ℂ)) :
    classicalLeftPairing a (compactModulatedSchwartz k v hv) (compactModulatedSchwartz k f hf) =
      ∫ x, conj (v x) * (∫ η, (Real.fourierChar ⟪η, x⟫ : ℂ) * (a x (η + k) * 𝓕 (f : E → ℂ) η)) := by
  unfold classicalLeftPairing
  apply integral_congr_ae
  filter_upwards with x
  rw [firstOrderAction_compactModulatedSchwartz, compactModulatedSchwartz_apply]
  let q := Real.fourierChar ⟪x, k⟫
  have hq : conj (q : ℂ) * (q : ℂ) = 1 := by
    rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  let J := ∫ η, (Real.fourierChar ⟪η, x⟫ : ℂ) * (a x (η + k) * 𝓕 (f : E → ℂ) η)
  change conj ((q : ℂ) * v x) * ((q : ℂ) * J) = conj (v x) * J
  calc
    _ = (conj (q : ℂ) * (q : ℂ)) * (conj (v x) * J) := by simp only [map_mul]; ring
    _ = _ := by rw [hq, one_mul]

end Burnett.Microlocal.AtlasOverlapKernel
