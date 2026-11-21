import Burnett.Analysis.PrincipalEnergy.Commutator.ActualParaproduct
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators NNReal

def bilateralWaveletScale (t : ℝ) (j : ℤ) : ℝ := t/(2:ℝ)^j

private theorem bilateral_scale_to_natural (t : ℝ) {j k : ℤ} (h : k≤j) :
    bilateralWaveletScale t j = compactWaveletScale (bilateralWaveletScale t k) (j-k).toNat := by
  rw [compactWaveletScale,bilateralWaveletScale,bilateralWaveletScale,div_div,← zpow_natCast,
    Int.toNat_of_nonneg (sub_nonneg.mpr h),← zpow_add₀ (by norm_num),show k+(j-k)=j by omega]

private theorem finite_bilateral_sum_le (F : ℝ → ℝ) (C t : ℝ) (hC : 0≤C) (ht : 0<t)
    (hFin : ∀ q : ℝ, 0<q → ∀ J : Finset ℕ, (∑ j ∈ J, F (compactWaveletScale q j)) ≤ C)
    (J : Finset ℤ) : (∑ j ∈ J, F (bilateralWaveletScale t j)) ≤ C := by
  by_cases hJ : J.Nonempty
  · let k := J.min' hJ
    let N (j : ℤ) := (j-k).toNat
    have hMin (j : ℤ) (hj : j∈J) : k≤j := J.min'_le j hj
    have hInj : Set.InjOn N (J : Set ℤ) := by
      intro j hj l hl he
      have h := congrArg (fun n : ℕ => (n : ℤ)) he
      change ((j-k).toNat : ℤ) = ((l-k).toNat : ℤ) at h
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr (hMin j hj)),
        Int.toNat_of_nonneg (sub_nonneg.mpr (hMin l hl))] at h
      omega
    let q := bilateralWaveletScale t k
    have hq : 0<q := div_pos ht (zpow_pos (by norm_num) _)
    calc
      _ = ∑ j ∈ J, F (compactWaveletScale q (N j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [bilateral_scale_to_natural t (hMin j hj)]
      _ = ∑ j ∈ J.image N, F (compactWaveletScale q j) := by rw [Finset.sum_image hInj]
      _ ≤ _ := hFin q hq _
  · rw [Finset.not_nonempty_iff_eq_empty.mp hJ,Finset.sum_empty]
    exact hC

/-- Every scale in both directions contributes to an absolutely convergent
paraproduct pairing for the actual compact-base commutator constant test. -/
theorem exists_compactBase_commutatorConstant_bilateral_paraproduct_bound
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (ψ φ : SchwartzMap Space ℂ)
    (hψ : ∀ z, 1<‖z‖ → ψ z = 0) (hMean : (∫ z, ψ z) = 0) (hφ : ∀ z, 1<‖z‖ → φ z = 0) :
    ∃ C : ℝ, 0≤C ∧ ∀ (r f g : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0 ≤ U → LipschitzWith L r → (∀ x, ‖r x‖ ≤ U) → ∀ (t : ℝ), 0<t →
        let v (j : ℤ) := compactWaveletParaproductTerm ψ φ (bilateralWaveletScale t j)
          (coefficientCommutatorConstant a r) f g
        Summable (fun j => ‖v j‖) ∧
          ‖∑' j, v j‖ ≤ C*(U+(L:ℝ))*‖f.toLp 2 volume‖*‖g.toLp 2 volume‖ := by
  obtain ⟨C,hC,hAbs⟩ := exists_compactBase_commutatorConstant_paraproduct_abs_sum_bound ha hBase hCont ψ φ hψ hMean hφ
  refine ⟨C,hC,?_⟩
  intro r f g L U hU hLip hR t ht v
  let A := C*(U+(L:ℝ))*‖f.toLp 2 volume‖*‖g.toLp 2 volume‖
  have hA : 0≤A := by dsimp only [A]; positivity
  have hFin (J : Finset ℤ) : (∑ j ∈ J, ‖v j‖) ≤ A := finite_bilateral_sum_le
    (fun s => ‖compactWaveletParaproductTerm ψ φ s (coefficientCommutatorConstant a r) f g‖)
    A t hA ht (hAbs r f g L U hU hLip hR) J
  have hSummable := summable_of_sum_le (f := fun j => ‖v j‖) (fun _ => norm_nonneg _) hFin
  exact ⟨hSummable,(norm_tsum_le_tsum_norm hSummable).trans (hSummable.tsum_le_of_sum_le hFin)⟩

end Burnett.Analysis.CarlesonEmbedding
