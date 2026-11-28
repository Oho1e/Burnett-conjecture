import Burnett.Counterexamples.Bianchi.RayIdentification

set_option autoImplicit false
set_option maxHeartbeats 450000

namespace Burnett.V03.Palatini

open Burnett.Geometry.ConnectionDifference (CoordinateSpace)
open Burnett.RicciSymbol (Covector)
open Burnett.Bianchi.RayIdentification (canonicalBracket)
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial)

/-- Freezing the first argument at the evaluation base point retains exactly
the momentum part of the canonical Poisson bracket. -/
theorem canonicalBracket_eq_frozen_sub_base (A t : CoordinateSpace → Covector → ℝ)
    (x : CoordinateSpace) (p : Covector) :
    canonicalBracket A t x p =
      canonicalBracket (fun _ => A x) t x p -
        ∑ k, basePartial k A x p * momentumPartial k t x p := by
  let F (k : Fin 4) := momentumPartial k A x p * basePartial k t x p
  let G (k : Fin 4) := basePartial k A x p * momentumPartial k t x p
  have hZero (k : Fin 4) : basePartial k (fun _ : CoordinateSpace => A x) x p = 0 := by
    unfold basePartial
    rw [fderiv_const_apply, ContinuousLinearMap.zero_apply]
  have hFreeze : canonicalBracket (fun _ => A x) t x p = ∑ k, F k := by
    unfold canonicalBracket
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hZero k, zero_mul, sub_zero]
    rfl
  calc
    canonicalBracket A t x p = (∑ k, (F k - G k)) := rfl
    _ = (∑ k, F k) - ∑ k, G k := Finset.sum_sub_distrib F G
    _ = _ := congrArg (fun r : ℝ => r - ∑ k, G k) hFreeze.symm

theorem add_frozenCanonicalBracket_negativeBase
    (A t : CoordinateSpace → Covector → ℝ) (x : CoordinateSpace) (p : Covector)
    {u v : ℂ} (hu : u = (canonicalBracket (fun _ => A x) t x p : ℂ))
    (hv : v = -((∑ k, basePartial k A x p * momentumPartial k t x p : ℝ) : ℂ)) :
    u + v = (canonicalBracket A t x p : ℂ) := by
  rw [hu, hv, canonicalBracket_eq_frozen_sub_base A t x p, Complex.ofReal_sub, sub_eq_add_neg]

end Burnett.V03.Palatini
