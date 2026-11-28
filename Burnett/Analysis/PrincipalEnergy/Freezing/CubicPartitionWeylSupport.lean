import Burnett.Analysis.PrincipalEnergy.Freezing.PrincipalCubicCutoffLocalization
import Burnett.Analysis.PrincipalEnergy.Freezing.CubicPartitionScalarPlacement

set_option autoImplicit false
set_option maxHeartbeats 7500000

noncomputable section

namespace Burnett.A03

open Filter Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped BigOperators Topology Burnett.A03

private theorem cutoff_coordinate_product (χ : SchwartzMap E ℂ) (u : E → ℂ)
    (hu : Differentiable ℝ u) (a : Index) (x : E) :
    fderiv ℝ (fun y => χ y * u y) x (EuclideanSpace.single a 1) =
      χ x * fderiv ℝ u x (EuclideanSpace.single a 1) + energyPartial a χ x * u x := by
  change fderiv ℝ ((χ : E → ℂ) * u) x (EuclideanSpace.single a 1) = _
  rw [fderiv_mul (χ.differentiable x) (hu x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  change χ x * fderiv ℝ u x _ + u x * energyPartial a χ x = _
  ring

/-- If the cubes of the patch cutoffs sum to one near the compact support
of the actual test output, single-cutoff-derivative terms cancel on that
support. The exact remainder contains only undifferentiated test values. -/
theorem principalVariation_cubic_partition_of_output_support {J K : Type} [Fintype J]
    (s : Finset K) (χ : K → SchwartzMap E ℂ)
    (C : Index → Index → J → J → J → E → ℂ) (z : J → SchwartzMap E ℂ)
    (w : J → E → ℂ) (hw : ∀ i, Differentiable ℝ (w i)) (L : Set E)
    (hSupport : ∀ i, tsupport (w i) ⊆ L)
    (hOne : ∀ x ∈ L, (fun y => ∑ k ∈ s, χ k y ^ 3) =ᶠ[𝓝 x] fun _ : E => (1 : ℂ)) (x : E) :
    (∑ l ∈ s, principalVariationDensity C (fun i => energyProduct (χ l) (z i))
      (fun i y => χ l y * w i y) x) = principalVariationDensity C z w x +
      ∑ a : Index, ∑ b : Index, ∑ i : J, ∑ j : J, ∑ k : J,
        C a b i j k x * (∑ l ∈ s, χ l x * energyPartial a (χ l) x * energyPartial b (χ l) x) *
          (w i x * z j x * z k x + z i x * w j x * z k x + z i x * z j x * w k x) := by
  classical
  by_cases hx : x ∈ L
  · let T := Index × Index × J × J × J
    let p (l : K) := χ l x
    let d (a : Index) (l : K) := energyPartial a (χ l) x
    let u (i : J) := z i x
    let v (i : J) := w i x
    let Du (a : Index) (i : J) := energyPartial a (z i) x
    let Dv (a : Index) (i : J) := fderiv ℝ (w i) x (EuclideanSpace.single a 1)
    let U (l : K) (a : Index) (i : J) := p l * Du a i + d a l * u i
    let V (l : K) (a : Index) (i : J) := p l * Dv a i + d a l * v i
    let c (q : T) := C q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x
    let term (q : T) (l : K) : ℂ :=
      let a := q.1; let b := q.2.1; let i := q.2.2.1; let j := q.2.2.2.1; let k := q.2.2.2.2
      U l a j * U l b k * (p l * v i) + V l a j * U l b k * (p l * u i) +
        U l a j * V l b k * (p l * u i)
    have hU (l : K) (a : Index) (i : J) : energyPartial a (energyProduct (χ l) (z i)) x = U l a i :=
      cutoff_coordinate_product (χ l) (z i) (z i).differentiable a x
    have hV (l : K) (a : Index) (i : J) :
        fderiv ℝ (fun y => χ l y * w i y) x (EuclideanSpace.single a 1) = V l a i :=
      cutoff_coordinate_product (χ l) (w i) (hw i) a x
    have hExpand (l : K) : principalVariationDensity C (fun i => energyProduct (χ l) (z i))
          (fun i y => χ l y * w i y) x = ∑ q : T, c q * term q l := by
      simp only [T, principalVariationDensity, hU, hV, energyProduct_apply, Fintype.sum_prod_type, c, term, p, u, v]
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      ring
    have hCube : ∑ l ∈ s, p l ^ 3 = 1 := (hOne x hx).self_of_nhds
    have hFirst (a : Index) : ∑ l ∈ s, p l ^ 2 * d a l = 0 :=
      cubed_partition_complex_first_derivative_zero s χ x a (hOne x hx)
    simp only [hExpand]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    simp only [T, Fintype.sum_prod_type, principalVariationDensity, c]
    simp only [← Finset.sum_add_distrib]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    dsimp only [term, U, V]
    simp only [Finset.sum_add_distrib]
    rw [sum_cubed_patch_scalar_placement s p _ _ _ _ _ _ _ hCube (hFirst _) (hFirst _),
      sum_cubed_patch_scalar_placement s p _ _ _ _ _ _ _ hCube (hFirst _) (hFirst _),
      sum_cubed_patch_scalar_placement s p _ _ _ _ _ _ _ hCube (hFirst _) (hFirst _)]
    dsimp only [u, v, Du, Dv, d, p]
    ring
  · have off (i : J) : x ∉ tsupport (w i) := fun h => hx (hSupport i h)
    have h0 (i : J) : w i x = 0 := image_eq_zero_of_notMem_tsupport (off i)
    have hD (i : J) : fderiv ℝ (w i) x = 0 := fderiv_of_notMem_tsupport ℝ (off i)
    have hCutD (k : K) (i : J) (a : Index) :
        fderiv ℝ (fun y => χ k y * w i y) x (EuclideanSpace.single a 1) = 0 := by
      rw [cutoff_coordinate_product _ _ (hw i), hD i, h0 i]
      simp
    simp only [principalVariationDensity, hCutD, h0, hD, ContinuousLinearMap.zero_apply,
      mul_zero, zero_mul, add_zero, Finset.sum_const_zero]

end Burnett.A03
