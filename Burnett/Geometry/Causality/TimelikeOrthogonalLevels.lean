import Burnett.Geometry.Cotangent.CauchyCrossingEnergy
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxRecDepth 3700

noncomputable section

namespace Burnett.Geometry.CotangentHamiltonCauchySlice

open Set Module
open scoped BigOperators ContDiff Manifold
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.CotangentCrossingTransversality

private theorem lorentz_pair_time_space {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (b : Basis Index ℝ V)
    (hb : ∀ i j, B (b i) (b j) = TensorFrame.standardInverse i j) (u v : V) :
    B u v = -(b.repr u 0 * b.repr v 0) +
      ∑ j ∈ (Finset.univ : Finset Index).erase 0, b.repr u j * b.repr v j := by
  let a (i : Index) := TensorFrame.signature i * (b.repr u i * b.repr v i)
  have hB : B u v = ∑ i, a i := by
    have he := congrArg (B u) (b.sum_repr v)
    simp only [map_sum, map_smul, smul_eq_mul] at he
    rw [← he]
    apply Finset.sum_congr rfl
    intro i _
    have hc : b.repr u i = TensorFrame.signature i * B u (b i) :=
      BasisFrame.coordinate_eq_signature_pairing B b hb u i
    have hBi : B u (b i) = TensorFrame.signature i * b.repr u i := by
      rw [hc, ← mul_assoc, BasisFrame.signature_sq, one_mul]
    rw [hBi]
    dsimp [a]
    ring
  rw [hB, ← Finset.sum_erase_add _ a (Finset.mem_univ (0 : Index))]
  have h0 : a 0 = -(b.repr u 0 * b.repr v 0) := by simp [a, TensorFrame.signature]
  rw [h0, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp [a, TensorFrame.signature, (Finset.mem_erase.mp hi).1]

/-- With Lorentz signature, every nonzero vector orthogonal to a timelike
vector is spacelike. The proof uses the actual orthonormal basis pairing. -/
theorem positive_of_timelike_orthogonal {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (b : Basis Index ℝ V)
    (hb : ∀ i j, B (b i) (b j) = TensorFrame.standardInverse i j)
    {n v : V} (hn : B n n < 0) (hv : v ≠ 0) (hOrth : B n v = 0) : 0 < B v v := by
  let S := (Finset.univ : Finset Index).erase 0
  let x (i : Index) := b.repr n i
  let y (i : Index) := b.repr v i
  let X := ∑ i ∈ S, x i ^ 2
  let Y := ∑ i ∈ S, y i ^ 2
  let Z := ∑ i ∈ S, x i * y i
  have hx : X < x 0 ^ 2 := by
    have he := lorentz_pair_time_space B b hb n n
    change B n n = -(x 0 * x 0) + ∑ i ∈ S, x i * x i at he
    simp only [← pow_two] at he
    change B n n = -(x 0 ^ 2) + X at he
    linarith
  have hxy : Z = x 0 * y 0 := by
    have he := lorentz_pair_time_space B b hb n v
    change B n v = -(x 0 * y 0) + Z at he
    linarith
  have hxpos : 0 < x 0 ^ 2 := (Finset.sum_nonneg fun _ _ => sq_nonneg _ : 0 ≤ X).trans_lt hx
  have hxne : x 0 ≠ 0 := by
    intro h
    simp [h] at hxpos
  have hY : 0 < Y := by
    by_contra! hy
    have hz (i : Index) (hi : i ∈ S) : y i = 0 := by
      have hterm : y i ^ 2 ≤ Y := Finset.single_le_sum (f := fun i => y i ^ 2) (fun _ _ => sq_nonneg _) hi
      have hsq : y i ^ 2 = 0 := le_antisymm (hterm.trans hy) (sq_nonneg _)
      rw [pow_two, mul_eq_zero] at hsq
      exact hsq.elim id id
    have hzsum : Z = 0 := Finset.sum_eq_zero (fun i hi => by rw [hz i hi, mul_zero])
    have hz0 : y 0 = 0 := (mul_eq_zero.mp (hxy.symm.trans hzsum)).resolve_left hxne
    apply hv
    apply b.repr.injective
    ext i
    change y i = (b.repr 0) i
    rw [map_zero, Finsupp.zero_apply]
    by_cases hi : i = 0
    · rwa [hi]
    · exact hz i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩)
  have hCS : Z ^ 2 ≤ X * Y := Finset.sum_mul_sq_le_sq_mul_sq S x y
  rw [hxy, mul_pow] at hCS
  have hvlt : y 0 ^ 2 < Y :=
    (mul_lt_mul_iff_right₀ hxpos).mp (hCS.trans_lt (mul_lt_mul_of_pos_right hx hY))
  have he := lorentz_pair_time_space B b hb v v
  change B v v = -(y 0 * y 0) + ∑ i ∈ S, y i * y i at he
  simp only [← pow_two] at he
  change B v v = -(y 0 ^ 2) + Y at he
  linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- The level of an actual temporal differential has a spacelike tangent
kernel and a surjective differential. -/
theorem spacelikeLevel_and_surjective_of_timelike_gradient (g : Field (M := M))
    (hL : HasLorentzSignature g) (f : M → ℝ) (m : M) (n : TangentSpace Model m)
    (hn : g m n n < 0) (hdual : ∀ v, mfderiv Model 𝓘(ℝ) f m v = g m n v) :
    SpacelikeLevelAt g f m ∧ Function.Surjective (mfderiv Model 𝓘(ℝ) f m) := by
  obtain ⟨b, hb⟩ := hL m
  let B : LinearMap.BilinForm ℝ (TangentSpace Model m) :=
    LinearMap.mk₂ ℝ (fun u v => g m u v)
      (by intros; simp [map_add]) (by intros; simp [map_smul])
      (by intros; simp [map_add]) (by intros; simp [map_smul])
  refine ⟨?_, ?_⟩
  · intro v hv hne
    have hOrth : B n v = 0 := (hdual v).symm.trans hv
    exact positive_of_timelike_orthogonal B b hb hn hne hOrth
  · let d : TangentSpace Model m →L[ℝ] ℝ := mfderiv Model 𝓘(ℝ) f m
    change Function.Surjective d
    intro y
    have hd : d n = g m n n := hdual n
    have hne : d n ≠ 0 := (hd.trans_lt hn).ne
    refine ⟨(y / d n) • n, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne]

end Burnett.Geometry.CotangentHamiltonCauchySlice
