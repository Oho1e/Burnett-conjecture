import Burnett.Analysis.PrincipalEnergy.Freezing.BoundedSeparatedJet
import Burnett.Analysis.TransportWard.Weyl.Amplitude.LocalizedPrincipalTest
import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.RicciSymbol
open scoped BigOperators

/-- The tested principal action with arbitrary fields in its three slots. -/
def principalCubicMixedDensity {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℂ)
    (u v w : J → E → ℂ) (x : E) : ℂ :=
  ∑ a : Index, ∑ d : Index, ∑ i : J, ∑ j : J, ∑ k : J, C a d i j k x *
    (u i x * fderiv ℝ (v j) x (EuclideanSpace.single a 1) *
      fderiv ℝ (w k) x (EuclideanSpace.single d 1))

/-- Integrate the actual principal cubic expression of the manuscript. -/
def principalCubicAction {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (u : J → E → ℂ) : ℂ :=
  ∫ x, principalCubicMixedDensity (fun a d i j k => C a d i j k) u u u x

def principalCubicLinearDensity {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℂ) (u v : J → E → ℂ) (x : E) : ℂ :=
  principalCubicMixedDensity C v u u x + principalCubicMixedDensity C u v u x +
    principalCubicMixedDensity C u u v x

theorem principal_cubic_linear_density_eq_variation {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℂ) (z : J → SchwartzMap E ℂ) (w : J → E → ℂ) :
    principalCubicLinearDensity C (fun i => z i) w = principalVariationDensity C z w := by
  funext x
  simp only [principalCubicLinearDensity, principalCubicMixedDensity, principalVariationDensity,
    energyPartial, SchwartzMap.pderivCLM_apply, mul_add, Finset.sum_add_distrib]

/-- All actual mixed integrands are integrable against the Schwartz
coefficient array for fields with bounded first coordinate jets. -/
theorem principal_cubic_mixed_integrable {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (u v w : J → E → ℂ)
    (hu : ∀ i, BoundedCoordinateJet (u i)) (hv : ∀ i, BoundedCoordinateJet (v i))
    (hw : ∀ i, BoundedCoordinateJet (w i)) :
    Integrable (principalCubicMixedDensity (fun a d i j k => C a d i j k) u v w) := by
  unfold principalCubicMixedDensity
  apply integrable_finset_sum Finset.univ
  intro a _
  apply integrable_finset_sum Finset.univ
  intro d _
  apply integrable_finset_sum Finset.univ
  intro i _
  apply integrable_finset_sum Finset.univ
  intro j _
  apply integrable_finset_sum Finset.univ
  intro k _
  obtain ⟨A,hA,bu⟩ := (hu i).2.1
  obtain ⟨B,hB,bv⟩ := (hv j).2.2 a
  obtain ⟨D,_,bw⟩ := (hw k).2.2 d
  have mC := (C a d i j k).continuous.measurable
  have mU := (hu i).1.continuous.measurable
  have mV := measurable_fderiv_apply_const (𝕜 := ℝ) (f := v j) (EuclideanSpace.single a 1)
  have mW := measurable_fderiv_apply_const (𝕜 := ℝ) (f := w k) (EuclideanSpace.single d 1)
  refine ((C a d i j k).integrable.norm.mul_const (A*B*D)).mono'
    (mC.mul ((mU.mul mV).mul mW)).aestronglyMeasurable ?_
  filter_upwards with x
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (mul_le_mul (bu x) (bv x) (norm_nonneg _) hA) (bw x)
      (norm_nonneg _) (mul_nonneg hA hB)) (norm_nonneg _)

private theorem coordinate_linear_path (u v : E → ℂ)
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) (s t : ℝ) (x : E) (a : Index) :
    fderiv ℝ (fun y => s • u y + t • v y) x (EuclideanSpace.single a 1) =
      s • fderiv ℝ u x (EuclideanSpace.single a 1) +
        t • fderiv ℝ v x (EuclideanSpace.single a 1) := by
  have h := (((hu x).hasFDerivAt.const_smul s).add ((hv x).hasFDerivAt.const_smul t)).fderiv
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply] using
    congrArg (fun d : E →L[ℝ] ℂ => d (EuclideanSpace.single a 1)) h

private theorem principal_cubic_density_polynomial {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℂ) (u v : J → E → ℂ)
    (hu : ∀ i, Differentiable ℝ (u i)) (hv : ∀ i, Differentiable ℝ (v i))
    (s t : ℝ) (x : E) :
    let path (i : J) (y : E) := s • u i y + t • v i y
    principalCubicMixedDensity C path path path x =
      s^3 • principalCubicMixedDensity C u u u x +
      (s^2*t) • principalCubicLinearDensity C u v x +
      (s*t^2) • principalCubicLinearDensity C v u x +
      t^3 • principalCubicMixedDensity C v v v x := by
  dsimp only
  simp only [principalCubicLinearDensity, principalCubicMixedDensity, smul_add, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [coordinate_linear_path (u j) (v j) (hu j) (hv j) s t x a,
    coordinate_linear_path (u k) (v k) (hu k) (hv k) s t x d]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The actual action integral on the two-parameter real plane is the cubic
polynomial with its genuine mixed-slot integrals as coefficients. -/
theorem principal_cubic_action_polynomial {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (u v : J → E → ℂ)
    (hu : ∀ i, BoundedCoordinateJet (u i)) (hv : ∀ i, BoundedCoordinateJet (v i))
    (s t : ℝ) :
    principalCubicAction C (fun i y => s • u i y + t • v i y) =
      s^3 • principalCubicAction C u +
      (s^2*t) • (∫ x, principalCubicLinearDensity (fun a d i j k => C a d i j k) u v x) +
      (s*t^2) • (∫ x, principalCubicLinearDensity (fun a d i j k => C a d i j k) v u x) +
      t^3 • principalCubicAction C v := by
  let c (a d : Index) (i j k : J) : E → ℂ := C a d i j k
  let P := principalCubicMixedDensity c u u u
  let Q := principalCubicLinearDensity c u v
  let R := principalCubicLinearDensity c v u
  let S := principalCubicMixedDensity c v v v
  have hP : Integrable P := principal_cubic_mixed_integrable C u u u hu hu hu
  have hQ : Integrable Q :=
    ((principal_cubic_mixed_integrable C v u u hv hu hu).add
      (principal_cubic_mixed_integrable C u v u hu hv hu)).add
        (principal_cubic_mixed_integrable C u u v hu hu hv)
  have hR : Integrable R :=
    ((principal_cubic_mixed_integrable C u v v hu hv hv).add
      (principal_cubic_mixed_integrable C v u v hv hu hv)).add
        (principal_cubic_mixed_integrable C v v u hv hv hu)
  have hS : Integrable S := principal_cubic_mixed_integrable C v v v hv hv hv
  change (∫ x, principalCubicMixedDensity c (fun i y => s • u i y + t • v i y)
    (fun i y => s • u i y + t • v i y) (fun i y => s • u i y + t • v i y) x) =
      s^3 • (∫ x, P x) + (s^2*t) • (∫ x, Q x) + (s*t^2) • (∫ x, R x) + t^3 • (∫ x, S x)
  simp_rw [principal_cubic_density_polynomial c u v (fun i => (hu i).1) (fun i => (hv i).1)]
  change (∫ x, s^3 • P x + (s^2*t) • Q x + (s*t^2) • R x + t^3 • S x) = _
  have p : Integrable (fun x => s^3 • P x) := Integrable.smul _ hP
  have q : Integrable (fun x => (s^2*t) • Q x) := Integrable.smul _ hQ
  have r : Integrable (fun x => (s*t^2) • R x) := Integrable.smul _ hR
  have h : Integrable (fun x => t^3 • S x) := Integrable.smul _ hS
  have pq : Integrable (fun x => s^3 • P x + (s^2*t) • Q x) := p.add q
  have pqr : Integrable (fun x => s^3 • P x + (s^2*t) • Q x + (s*t^2) • R x) := pq.add r
  rw [integral_add pqr h, integral_add pq r, integral_add p q]
  simp only [integral_smul]

end Burnett.A02.FrequencySplit
