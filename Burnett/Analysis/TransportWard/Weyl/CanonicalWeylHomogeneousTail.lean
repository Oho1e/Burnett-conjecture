import Burnett.Counterexamples.Bianchi.RayIdentification
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency

set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option maxRecDepth 1900

noncomputable section

namespace Burnett.V03

open Function Filter MeasureTheory Set Burnett.Geometry ConnectionDifference Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (tau)
open Burnett.Bianchi.RayIdentification (canonicalBracket canonicalBracket_radial)
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial momentumBasis)
open scoped ContDiff Topology

local notation "E₀" => CoordinateSpace

/-- Fixed infrared modifications disappear from the canonical Poisson
symbol once the physical radian covector is above the fixed threshold. -/
theorem canonicalBracket_eq_of_infrared_match (A a β : E₀ → Covector → ℝ) (R : ℝ)
    (hMatch : ∀ y ν, R ≤ ‖(WithLp.toLp 2 ν : E₀)‖ → β y ν = a y ν)
    (x : E₀) (ζ : Covector) (hζ : R < ‖(WithLp.toLp 2 ζ : E₀)‖) :
    canonicalBracket A β x ζ = canonicalBracket A a x ζ := by
  let L : Covector ≃L[ℝ] E₀ := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm
  have hCont : Continuous (fun ν : Covector => ‖(WithLp.toLp 2 ν : E₀)‖) := L.continuous.norm
  have hFiber : β x =ᶠ[𝓝 ζ] a x := by
    filter_upwards [hCont.continuousAt.eventually (Ioi_mem_nhds hζ)] with ν hν
    exact hMatch x ν hν.le
  have hBase : (fun y => β y ζ) = (fun y => a y ζ) :=
    funext (fun y => hMatch y ζ hζ.le)
  simp only [canonicalBracket,basePartial,momentumPartial,hFiber.fderiv_eq,hBase]

/-- The principal bracket remains quadratically homogeneous in ordinary
frequency after one exact conversion into the physical radian covector. -/
theorem canonicalBracket_radian_high_eq (A a β : E₀ → Covector → ℝ) (R : ℝ)
    (hMatch : ∀ y ν, R ≤ ‖(WithLp.toLp 2 ν : E₀)‖ → β y ν = a y ν)
    (hA : ∀ x (s : ℝ), 0 < s → ∀ ξ : Covector, ξ ≠ 0 → A x (s • ξ) = s^2 * A x ξ)
    (ha : ∀ x (s : ℝ), 0 < s → ∀ ξ : Covector, ξ ≠ 0 → a x (s • ξ) = s * a x ξ)
    (x ξ : E₀) (hξ : max 1 (R + 1) ≤ ‖ξ‖) :
    (canonicalBracket A β x (fun j => (tau • ξ) j) : ℂ) =
      (tau : ℂ)^2 * (canonicalBracket A a x (WithLp.ofLp ξ) : ℂ) := by
  let η : Covector := WithLp.ofLp ξ
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have hτ₁ : 1 ≤ tau := by
    change 1 ≤ 2 * Real.pi
    linarith only [Real.two_le_pi]
  have hη : η ≠ 0 := by
    intro h
    have he : ξ = 0 := congrArg (WithLp.toLp 2) h
    have hh := (le_max_left (1 : ℝ) (R + 1)).trans hξ
    rw [he,norm_zero] at hh
    exact (by norm_num : ¬ (1 : ℝ) ≤ 0) hh
  have hE : (WithLp.toLp 2 (fun j => (tau • ξ) j) : E₀) = tau • ξ := by ext j; rfl
  have hηR : R < ‖(WithLp.toLp 2 (fun j => (tau • ξ) j) : E₀)‖ := by
    rw [hE,norm_smul,Real.norm_of_nonneg hτ.le]
    exact ((lt_add_of_pos_right R zero_lt_one).trans_le ((le_max_right _ _).trans hξ)).trans_le
      (le_mul_of_one_le_left (norm_nonneg ξ) hτ₁)
  rw [canonicalBracket_eq_of_infrared_match A a β R hMatch _ _ hηR]
  change (canonicalBracket A a x (tau • η) : ℂ) = (tau : ℂ)^2 * (canonicalBracket A a x η : ℂ)
  rw [canonicalBracket_radial univ isOpen_univ A a x (mem_univ x) η hη tau hτ
    (fun y _ ν hν => hA y tau hτ ν hν) (fun y _ ν hν => ha y tau hτ ν hν)]
  push_cast
  rfl

end Burnett.V03
