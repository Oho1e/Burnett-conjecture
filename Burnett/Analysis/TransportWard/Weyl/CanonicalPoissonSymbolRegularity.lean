import Burnett.Counterexamples.Bianchi.RayIdentification
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency

set_option autoImplicit false
set_option maxHeartbeats 2100000
set_option maxRecDepth 1900

noncomputable section

namespace Burnett.V03

open Function Filter Set Burnett.Geometry ConnectionDifference Burnett.RicciSymbol
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial momentumBasis)
open Burnett.Bianchi.RayIdentification (canonicalBracket)
open scoped ContDiff Topology BigOperators

local notation "E₀" => CoordinateSpace
local notation "P" => E₀ × Covector

private theorem basePartial_eq_jointFDeriv {F : E₀ → Covector → ℝ} (z : P) (i : Index)
    (h : DifferentiableAt ℝ (uncurry F) z) :
    basePartial i F z.1 z.2 = fderiv ℝ (uncurry F) z (Burnett.CubicExplicit.basis i,0) := by
  let L := ContinuousLinearMap.inl ℝ E₀ Covector
  have hL : HasFDerivAt (fun y : E₀ => (y,z.2)) L z.1 := by
    exact (L.hasFDerivAt.add_const (0,z.2)).congr_of_eventuallyEq (.of_forall fun _ => by simp [L])
  have hC := h.hasFDerivAt.comp z.1 hL
  change HasFDerivAt (fun y => F y z.2) _ z.1 at hC
  rw [basePartial,hC.fderiv]
  rfl

private theorem momentumPartial_eq_jointFDeriv {F : E₀ → Covector → ℝ} (z : P) (i : Index)
    (h : DifferentiableAt ℝ (uncurry F) z) :
    momentumPartial i F z.1 z.2 = fderiv ℝ (uncurry F) z (0,momentumBasis i) := by
  let L := ContinuousLinearMap.inr ℝ E₀ Covector
  have hL : HasFDerivAt (fun ξ : Covector => (z.1,ξ)) L z.2 := by
    exact (L.hasFDerivAt.add_const (z.1,0)).congr_of_eventuallyEq (.of_forall fun _ => by simp [L])
  have hC := h.hasFDerivAt.comp z.2 hL
  change HasFDerivAt (F z.1) _ z.2 at hC
  rw [momentumPartial,hC.fderiv]
  rfl

/-- The true canonical bracket stays smooth on every common open phase patch. -/
theorem canonicalBracket_contDiffOn {F G : E₀ → Covector → ℝ} {U : Set P}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ (uncurry F) U)
    (hG : ContDiffOn ℝ ∞ (uncurry G) U) :
    ContDiffOn ℝ ∞ (uncurry (canonicalBracket F G)) U := by
  have hPart (a : E₀ → Covector → ℝ) (ha : ContDiffOn ℝ ∞ (uncurry a) U) (i : Index) :
      ContDiffOn ℝ ∞ (fun z : P => basePartial i a z.1 z.2) U ∧
      ContDiffOn ℝ ∞ (fun z : P => momentumPartial i a z.1 z.2) U := by
    have hd : ContDiffOn ℝ ∞ (fderiv ℝ (uncurry a)) U := ha.fderiv_of_isOpen hU (by simp)
    have hD (z : P) (hz : z ∈ U) : DifferentiableAt ℝ (uncurry a) z :=
      (ha.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    refine ⟨?_,?_⟩
    · exact (hd.clm_apply (contDiffOn_const (c := (Burnett.CubicExplicit.basis i,0)))).congr
        (fun z hz => basePartial_eq_jointFDeriv z i (hD z hz))
    · exact (hd.clm_apply (contDiffOn_const (c := (0,momentumBasis i)))).congr
        (fun z hz => momentumPartial_eq_jointFDeriv z i (hD z hz))
  change ContDiffOn ℝ ∞ (fun z : P => ∑ i, (momentumPartial i F z.1 z.2 * basePartial i G z.1 z.2 -
    basePartial i F z.1 z.2 * momentumPartial i G z.1 z.2)) U
  exact ContDiffOn.sum fun i _ => (((hPart F hF i).2).mul (hPart G hG i).1).sub
    (((hPart F hF i).1).mul (hPart G hG i).2)

/-- A representative of the actual second-order coefficient matrix with
Schwartz extensions is globally smooth and exactly quadratic in the fiber. -/
theorem quadraticChartSymbol_smooth_and_radial (c : Fin 4 × Fin 4 → E₀ → ℝ)
    (hc : ∀ d, ContDiff ℝ ∞ (c d)) :
    let A (x : E₀) (ξ : Covector) := ∑ d : Fin 4 × Fin 4, c d x * (ξ d.1 * ξ d.2)
    ContDiff ℝ ∞ (uncurry A) ∧
      ∀ x (s : ℝ) ξ, A x (s • ξ) = s^2 * A x ξ := by
  intro A
  refine ⟨?_,fun x s ξ => ?_⟩
  · have hp (i : Fin 4) : ContDiff ℝ ∞ (fun z : P => z.2 i) :=
      (ContinuousLinearMap.proj i : Covector →L[ℝ] ℝ).contDiff.comp contDiff_snd
    exact ContDiff.sum fun d _ => ((hc d).comp contDiff_fst).mul ((hp d.1).mul (hp d.2))
  change (∑ d : Fin 4 × Fin 4, c d x * ((s • ξ) d.1 * (s • ξ) d.2)) =
    s^2 * ∑ d : Fin 4 × Fin 4, c d x * (ξ d.1 * ξ d.2)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

end Burnett.V03
