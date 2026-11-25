import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicPointEvaluation
import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicCoordinateEnergy

set_option autoImplicit false
set_option maxHeartbeats 7800000

noncomputable section

namespace Burnett.A06

open MvPolynomial Metric MeasureTheory Set
open scoped BigOperators ContDiff

private def scaleCoordinateProjection (i : Fin 4) : ℝ →L[ℝ] (RotationSpace →L[ℝ] ℝ) :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.proj i)

private theorem spherePolynomialValue_fderiv_sum_coordinates (P : SpherePolynomial) :
    fderiv ℝ (spherePolynomialValue P) =
      fun x => ∑ i : Fin 4, scaleCoordinateProjection i (spherePolynomialValue (pderiv i P) x) := by
  funext x
  ext v
  have e : (∑ i : Fin 4, v i • EuclideanSpace.single i (1 : ℝ)) = v := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v
  have h := congrArg (fun y : RotationSpace => fderiv ℝ (spherePolynomialValue P) x y) e.symm
  simp only [map_sum,map_smul,smul_eq_mul,spherePolynomialValue_fderiv_coordinate] at h
  have hproj (i : Fin 4) : (EuclideanSpace.proj i : RotationSpace →L[ℝ] ℝ) v = v i := rfl
  simpa only [scaleCoordinateProjection, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, hproj, mul_comm] using h

/-- Uniform ambient polynomial jet bounds on the actual round sphere.
Differentiating once costs one power of d+1. -/
theorem exists_sphereHarmonic_ambient_jet_bound :
    ∃ A B : ℝ, 0 ≤ A ∧ 1 ≤ B ∧ ∀ (n d : ℕ) (H : sphereHarmonicSubmodule d) (x : RoundSphere3),
      ‖iteratedFDeriv ℝ n (spherePolynomialValue H.val.val) x‖ ≤
        A * B^n * ((d : ℝ) + 1)^(n+1) * ‖sphereHarmonicToLp d H‖ := by
  let A := (Real.sqrt (roundSphere3Measure.real univ))⁻¹
  let W := ∑ i : Fin 4, ‖scaleCoordinateProjection i‖
  let B := 2*W + 1
  have hA : 0 ≤ A := by positivity
  have hW : 0 ≤ W := by positivity
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  refine ⟨A,B,hA,hB,?_⟩
  intro n
  induction n with
  | zero =>
    intro d H x
    have h := norm_sphereHarmonicValue_le d H x
    have hcoef : Real.sqrt ((((d+1)^2 : ℕ) : ℝ) / roundSphere3Measure.real univ) =
        A * ((d : ℝ) + 1) := by
      rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.sqrt_div (by positivity),
        Real.sqrt_sq (by positivity), div_eq_mul_inv]
      exact mul_comm _ _
    simpa only [norm_iteratedFDeriv_zero, hcoef, pow_zero, zero_add, pow_one, mul_one] using h
  | succ n ih =>
    intro d H x
    let F (i : Fin 4) := spherePolynomialValue (pderiv i H.val.val)
    let D (i : Fin 4) := scaleCoordinateProjection i ∘ F i
    have hFs (i) : ContDiff ℝ n (F i) := contDiff_infty.mp (spherePolynomialValue_contDiff _) n
    have hDs (i) : ContDiff ℝ n (D i) := (scaleCoordinateProjection i).contDiff.comp (hFs i)
    have hdiff (i : Fin 4) : ‖iteratedFDeriv ℝ n (D i) x‖ ≤
        ‖scaleCoordinateProjection i‖ * ‖iteratedFDeriv ℝ n (F i) x‖ := by
      unfold D
      rw [(scaleCoordinateProjection i).iteratedFDeriv_comp_left (hFs i).contDiffAt le_rfl]
      exact (scaleCoordinateProjection i).norm_compContinuousMultilinearMap_le _
    let C := A * B^n * ((d : ℝ) + 1)^(n+1) * ((2*((d : ℝ)+1))*‖sphereHarmonicToLp d H‖)
    have hF (i : Fin 4) : ‖iteratedFDeriv ℝ n (F i) x‖ ≤ C := by
      have hn := ih (d-1) (sphereHarmonicCoordinateDerivative d i H) x
      have hnorm := norm_sphereHarmonicCoordinateDerivative_le d H i
      have hD : ((d-1 : ℕ) : ℝ) + 1 ≤ (d : ℝ) + 1 :=
        add_le_add_right (by exact_mod_cast Nat.sub_le d 1) _
      exact hn.trans (mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hD (n+1)) (by positivity))
        hnorm (norm_nonneg _) (by positivity))
    rw [← norm_iteratedFDeriv_fderiv, spherePolynomialValue_fderiv_sum_coordinates]
    change ‖iteratedFDeriv ℝ n (fun y => ∑ i : Fin 4, D i y) x‖ ≤ _
    rw [iteratedFDeriv_sum (fun i _ => hDs i), Finset.sum_apply]
    calc
      _ ≤ ∑ i : Fin 4, ‖iteratedFDeriv ℝ n (D i) x‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 4, ‖scaleCoordinateProjection i‖ * C :=
        Finset.sum_le_sum fun i _ => (hdiff i).trans (mul_le_mul_of_nonneg_left (hF i) (norm_nonneg (scaleCoordinateProjection i)))
      _ = (2*W) * (A * B^n * ((d : ℝ) + 1)^(n+2) * ‖sphereHarmonicToLp d H‖) := by
        rw [← Finset.sum_mul, pow_succ' ((d : ℝ) + 1) (n+1)]
        change W * C = _
        dsimp [C]
        ring
      _ ≤ B * (A * B^n * ((d : ℝ) + 1)^(n+2) * ‖sphereHarmonicToLp d H‖) :=
        mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (by positivity)
      _ = _ := by rw [pow_succ' B n]; ring

end Burnett.A06
