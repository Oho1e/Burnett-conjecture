import Burnett.Analysis.FrozenTransport.V03MetricActionCoefficient
import Burnett.Counterexamples.Bianchi.RayIdentification

/-! The symbol of the frozen coordinate density Euler principal field and
its Hamilton derivative with respect to a scalar test. -/

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option maxRecDepth 4700

noncomputable section

namespace Burnett.V03.Palatini

open Burnett.Geometry.ConnectionDifference (CoordinateSpace)
open Burnett.RicciSymbol
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Bianchi.RayIdentification (canonicalBracket)
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial momentumBasis)
open scoped BigOperators

local notation "J" => Fin 4 × Fin 4

/-- Fourier convention `∂a ↦ iξa` applied to the frozen actual second jets. -/
def frozenDensityPrincipalPhase {ι : Type*} (S : ι → Mat) (G : Mat) (p : Covector)
    (i j : ι) : ℝ :=
  ∑ a, ∑ b, metricActionCoefficient S (a,i) (b,j) G * (p a * p b)

private theorem frozenDensityPrincipalPhase_momentumPartial {ι : Type*} (S : ι → Mat) (G : Mat)
    (k : Fin 4) (x : CoordinateSpace) (p : Covector) (i j : ι) :
    momentumPartial k (fun _ : CoordinateSpace => fun q => frozenDensityPrincipalPhase S G q i j) x p =
      ∑ a, ∑ b, metricActionCoefficient S (a,i) (b,j) G *
        (p a * momentumBasis k b + p b * momentumBasis k a) := by
  let C (a b : Fin 4) := metricActionCoefficient S (a,i) (b,j) G
  let proj (a : Fin 4) : Covector →L[ℝ] ℝ := ContinuousLinearMap.proj a
  have hδ (a b : Fin 4) :
      HasFDerivAt (fun q : Covector => C a b * (q a * q b))
        (C a b • (p a • proj b + p b • proj a)) p :=
    (((proj a).hasFDerivAt (x := p)).mul ((proj b).hasFDerivAt (x := p))).const_mul (C a b)
  have hSum := HasFDerivAt.fun_sum fun a (_ : a ∈ Finset.univ) =>
    HasFDerivAt.fun_sum fun b (_ : b ∈ Finset.univ) => hδ a b
  change (fderiv ℝ (fun q => ∑ a, ∑ b, C a b * (q a * q b)) p) (momentumBasis k) = _
  rw [hSum.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    smul_eq_mul, C, proj, ContinuousLinearMap.proj_apply]

theorem frozenDensityPrincipalPhase_bracket {ι : Type*} (S : ι → Mat) (G : Mat)
    (test : CoordinateSpace → Covector → ℝ) (x : CoordinateSpace) (p : Covector) (i j : ι) :
    canonicalBracket (fun _ : CoordinateSpace => fun q => frozenDensityPrincipalPhase S G q i j) test x p =
      ∑ d : J, metricActionCoefficient S (d.1,i) (d.2,j) G *
        (p d.2 * basePartial d.1 test x p + p d.1 * basePartial d.2 test x p) := by
  let C (a b : Fin 4) := metricActionCoefficient S (a,i) (b,j) G
  let u (k : Fin 4) := basePartial k test x p
  have hConst (k : Fin 4) :
      basePartial k (fun _ : CoordinateSpace => fun q => frozenDensityPrincipalPhase S G q i j) x p = 0 := by
    simp only [basePartial, fderiv_const_apply, ContinuousLinearMap.zero_apply]
  calc
    _ = ∑ k, ∑ a, ∑ b, (C a b * (p a * momentumBasis k b + p b * momentumBasis k a)) * u k := by
      simp only [canonicalBracket, frozenDensityPrincipalPhase_momentumPartial,
        hConst, zero_mul, sub_zero, Finset.sum_mul, C, u]
    _ = ∑ a, ∑ b, ∑ k, (C a b * (p a * momentumBasis k b + p b * momentumBasis k a)) * u k := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := by
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [mul_assoc, ← Finset.mul_sum, add_mul, Finset.sum_add_distrib, momentumBasis,
        Pi.single_apply, mul_ite, ite_mul, one_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        C, u]
      ring

end Burnett.V03.Palatini
