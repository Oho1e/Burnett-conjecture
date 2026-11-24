import Burnett.Analysis.Microlocal.OrderedRicciJet
import Burnett.Analysis.Microlocal.PhysicalDensity

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Burnett.Microlocal.RawCovariance

open Matrix Burnett.RicciSymbol
open Burnett.Microlocal.CurlDensity (Pair JetSlot)
open Burnett.Microlocal.PhysicalDensity
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

/-- The real part of an ordered jet contraction is the same contraction of
the real and imaginary Gram columns of its factored amplitude. -/
theorem rawJetContraction_eq_nullMoment_of_factored
    (G : Tensor2) (ξ : Covector) (A : Matrix Pair Pair ℂ) (N : Matrix JetSlot JetSlot ℂ)
    (hG : IsSymmetricTensor G) (hξ : ξ ≠ 0) (hA : A.PosSemidef)
    (hFact : ∀ i j : JetSlot, N i j = (ξ i.1 : ℂ) * (ξ j.1 : ℂ) * A j.2 i.2)
    (hKer : ∀ v : Pair → ℂ, let k (a b : Index) := (A *ᵥ v) (a, b)
      IsSymmetricComplexTensor k ∧ ∀ a b, complexRicciSymbol G ξ k a b = 0)
    (b d : Index) :
    (∑ i : JetSlot, ∑ j : JetSlot, rawJetProductCoefficient G b d i j * (N i j).re) =
      if symbolNorm G ξ = 0 then
        (ξ b * ξ d) * (((1 / 4 : ℂ) * physicalContraction G A).re)
      else 0 := by
  classical
  let C := densitySqrt A
  let k (s : Pair) := tensorOfVector (C.col s)
  let Jr (s : Pair) := rankOneJet ξ (tensorRe (k s))
  let Ji (s : Pair) := rankOneJet ξ (tensorIm (k s))
  have hC : C * Cᴴ = A := densitySqrt_mul_self hA
  have hK (s : Pair) :
      IsSymmetricComplexTensor (k s) ∧ ∀ a e, complexRicciSymbol G ξ (k s) a e = 0 := by
    have hCol : C.col s ∈ LinearMap.range A.mulVecLin := by
      rw [← range_densitySqrt hA]
      refine ⟨Pi.single s 1, ?_⟩
      change C *ᵥ Pi.single s 1 = C.col s
      exact Matrix.mulVec_single_one C s
    obtain ⟨v, hv⟩ := hCol
    have hEquality : tensorOfVector (A *ᵥ v) = k s := congrArg tensorOfVector hv
    rw [← hEquality]
    exact hKer v
  have re_sum (f : Pair → ℂ) : (∑ s, f s).re = ∑ s, (f s).re :=
    map_sum Complex.reAddGroupHom f Finset.univ
  have hEntry (i j : JetSlot) : (N i j).re = ∑ s,
      (jetEntries (Jr s) i * jetEntries (Jr s) j + jetEntries (Ji s) i * jetEntries (Ji s) j) := by
    have hAji : A j.2 i.2 = ∑ s, C j.2 s * conj (C i.2 s) := by
      rw [← hC, Matrix.mul_apply]
      rfl
    rw [hFact, hAji, Finset.mul_sum, re_sum]
    apply Finset.sum_congr rfl
    intro s _
    simp only [Jr, Ji, rankOneJet, jetEntries, k, tensorOfVector, tensorRe, tensorIm, Matrix.col_apply,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, mul_zero, zero_mul, sub_zero, add_zero]
    ring
  let term (i j : JetSlot) (s : Pair) := rawJetProductCoefficient G b d i j *
    (jetEntries (Jr s) i * jetEntries (Jr s) j + jetEntries (Ji s) i * jetEntries (Ji s) j)
  have hTerm (i j : JetSlot) : rawJetProductCoefficient G b d i j * (N i j).re =
      ∑ s, term i j s := by rw [hEntry, Finset.mul_sum]
  have hSum (s : Pair) : (∑ i, ∑ j, term i j s) = (hermitianQuadraticSymbol G ξ (k s) (k s) b d).re := by
    simp only [term, mul_add, Finset.sum_add_distrib, ← rawJetCross_eq_jet_sum,
      Jr, Ji, rawJetCross, christoffel_rankOneJet]
    exact (hermitianQuadraticSymbol_diag_re G ξ (k s) b d).symm
  simp only [hTerm]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [hSum]
  by_cases hz : symbolNorm G ξ = 0
  · rw [if_pos hz]
    have hPhys : physicalContraction G A = ∑ s, hermitianPhysicalPairing G (k s) (k s) := by
      rw [← hC, physicalContraction_gram]
    rw [hPhys, Finset.mul_sum, re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [hermitianQuadraticSymbol_eq_physicalPairing_of_null_kernel G ξ (k s) (k s)
      hG (hK s).1 (hK s).1 hξ hz (hK s).2 (hK s).2]
    rw [← Complex.ofReal_mul]
    have hQuarter : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by norm_num
    rw [hQuarter]
    simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  · rw [if_neg hz]
    apply Finset.sum_eq_zero
    intro s _
    rw [hermitianQuadraticSymbol_eq_zero_of_noncharacteristic_kernel G ξ (k s) (k s) hz (hK s).2 (hK s).2]
    rfl

end Burnett.Microlocal.RawCovariance
