import Burnett.Analysis.Microlocal.Overlap.ChartJetPhysicalWeight

/-! Physical contractions of factored coordinate-jet densities. -/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.Overlap

open Matrix Burnett.RicciSymbol
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.PhysicalDensity
open scoped BigOperators ComplexOrder Matrix

private theorem sum_mul_paired_slots {I J : Type*} [Fintype I] [Fintype J]
    (a : I → I → ℂ) (b : J → J → ℂ) :
    (∑ i : I × J, ∑ j : I × J, a i.1 j.1 * b i.2 j.2) =
      (∑ i, ∑ j, a i j) * (∑ u, ∑ v, b u v) := by
  simp only [Finset.sum_mul]
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

/-- With the second-slot pairing convention, the jet entry and the physical
coefficient both use the transposed amplitude slots. The derivative trace
of the factored entry equals one on the auxiliary unit section. -/
theorem orderedPhysicalJetWeight_factored (R G : Tensor2) (η : Covector)
    (ρ : Matrix JetSlot JetSlot ℂ) (S : Matrix Pair Pair ℂ)
    (hUnit : symbolNorm R η = 1)
    (hEntry : ∀ i j : JetSlot, ρ j i = (η i.1 : ℂ) * (η j.1 : ℂ) * S i.2 j.2) :
    (∑ i : JetSlot, ∑ j : JetSlot, (orderedPhysicalJetWeight R G i j : ℂ) * ρ i j) =
      (1 / 4 : ℂ) * physicalContraction G S := by
  let a (u v : Index) : ℂ := (↑(R u v * η u * η v) : ℂ)
  let b (u v : Pair) : ℂ := (1 / 4 : ℂ) * (physicalCoefficient G v u * S v u)
  have hTerm (i j : JetSlot) :
      (orderedPhysicalJetWeight R G i j : ℂ) * ρ i j = a i.1 j.1 * b i.2 j.2 := by
    rw [orderedPhysicalJetWeight_apply, hEntry j i]
    simp only [a, b, physicalCoefficient, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hA : (∑ u, ∑ v, a u v) = 1 := by
    simpa only [a, symbolNorm, Complex.ofReal_sum, Complex.ofReal_one] using
      congrArg Complex.ofReal hUnit
  have hB : (∑ u, ∑ v, b u v) = (1 / 4 : ℂ) * physicalContraction G S := by
    rw [Finset.sum_comm]
    simp only [b, physicalContraction, Finset.mul_sum]
  calc
    _ = ∑ i : JetSlot, ∑ j : JetSlot, a i.1 j.1 * b i.2 j.2 := by simp only [hTerm]
    _ = (∑ u, ∑ v, a u v) * (∑ u, ∑ v, b u v) := sum_mul_paired_slots a b
    _ = _ := by rw [hA, hB, one_mul]

/-- A positive Hermitian amplitude density with symmetric image in the null
Ricci kernel has a real nonnegative physical contraction. -/
theorem physicalContraction_of_null_amplitude (G : Tensor2) (frame : TensorFrame.LorentzFrame G)
    (η : Covector) (hη : η ≠ 0) (hNull : symbolNorm G η = 0)
    (S : Matrix Pair Pair ℂ) (hS : S.PosSemidef)
    (hK : ∀ v : Pair → ℂ, let k (a b : Index) := (S *ᵥ v) (a, b)
      IsSymmetricComplexTensor k ∧ ∀ a b, complexRicciSymbol G η k a b = 0) :
    0 ≤ (physicalContraction G S).re ∧ (physicalContraction G S).im = 0 := by
  classical
  rw [← densitySqrt_mul_self hS, physicalContraction_gram]
  let k (j : Pair) := tensorOfVector ((densitySqrt S).col j)
  have hk (j : Pair) :
      IsSymmetricComplexTensor (k j) ∧ ∀ a b, complexRicciSymbol G η (k j) a b = 0 := by
    have hj : (densitySqrt S).col j ∈ LinearMap.range S.mulVecLin := by
      rw [← range_densitySqrt hS]
      refine ⟨Pi.single j 1, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
    obtain ⟨v, hv⟩ := hj
    have hcol : (densitySqrt S).col j = S *ᵥ v := hv.symm
    simpa only [k, tensorOfVector, hcol] using hK v
  constructor
  · change 0 ≤ Complex.reAddGroupHom (∑ j, hermitianPhysicalPairing G (k j) (k j))
    rw [map_sum]
    exact Finset.sum_nonneg fun j _ =>
      LorentzHermitian.physicalPairing_self_re_nonneg G frame η (k j) (hk j).1 hη hNull (hk j).2
  · change Complex.imAddGroupHom (∑ j, hermitianPhysicalPairing G (k j) (k j)) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero fun j _ =>
      LorentzHermitian.physicalPairing_self_im_eq_zero G frame (k j)

end Burnett.Microlocal.Overlap
