import Burnett.Analysis.PrincipalEnergy.Energy.CompactFourierNorms

set_option autoImplicit false
set_option maxHeartbeats 5500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped BigOperators ComplexConjugate InnerProductSpace ContDiff

/-- Scalarity here is the same complete symbol on every diagonal entry. -/
def diagonalOrderOneSymbol {ι : Type*} (a : Space → Space → ℂ) (i j : ι) : Space → Space → ℂ := by
  classical
  exact if i = j then a else fun _ _ => 0

private theorem zeroFirstBaseFrequency : FirstBaseFrequencyOrderOne (fun _ _ : Space => (0:ℂ)) := by
  constructor
  · constructor
    · exact fun _ => contDiff_const
    · intro n
      refine ⟨0, le_rfl, fun x ξ => ?_⟩
      simp [iteratedFDeriv_zero_fun]
  · intro n ξ
    simp only [iteratedFDeriv_zero_fun, Pi.zero_apply]
    exact differentiable_const _
  · intro n
    refine ⟨0, le_rfl, fun x ξ => ?_⟩
    have hz : fderiv ℝ (fun _ : Space => iteratedFDeriv ℝ n (fun _ : Space => (0:ℂ)) ξ) x = 0 :=
      fderiv_const_apply _
    rw [hz, ContinuousLinearMap.opNorm_zero, zero_mul, zero_mul]

private theorem zeroSymbol_pureBase (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ : Space,
    ‖iteratedFDeriv ℝ n (fun _ : Space => (0:ℂ)) x‖ ≤ C * (1 + ‖ξ‖) := by
  exact ⟨0, le_rfl, fun x ξ => by simp [iteratedFDeriv_zero_fun]⟩

private theorem zeroSymbol_kernelRelation :
    firstOrderKernelRelation (fun _ _ : Space => (0:ℂ)) = {p | p.1 = p.2} := by
  have hzero (x y : Space) : offDiagonalFirstOrderKernel (fun _ _ : Space => (0:ℂ)) x y = 0 := by
    simp [offDiagonalFirstOrderKernel, firstOrderLowKernel, firstOrderLowSymbol, firstOrderKernel,
      firstOrderAnnularKernel, Real.fourierIntegralInv_eq]
  simp [firstOrderKernelRelation, hzero]

private theorem zeroSymbol_proper_of_proper {a : Space → Space → ℂ}
    (ha : ProperKernelRelation (firstOrderKernelRelation a)) :
    ProperKernelRelation (firstOrderKernelRelation (fun _ _ : Space => (0:ℂ))) := by
  rw [zeroSymbol_kernelRelation]
  have hD : IsClosed {p : Space × Space | p.1 = p.2} := isClosed_eq continuous_fst continuous_snd
  have hsub : {p : Space × Space | p.1 = p.2} ⊆ firstOrderKernelRelation a := fun _ hp => Or.inl hp
  refine ⟨hD, fun K hK => ⟨?_, ?_⟩⟩
  · exact (ha.2 K hK).1.of_isClosed_subset (hD.inter (hK.isClosed.prod isClosed_univ)) (inter_subset_inter_left _ hsub)
  · exact (ha.2 K hK).2.of_isClosed_subset (hD.inter (isClosed_univ.prod hK.isClosed)) (inter_subset_inter_left _ hsub)

theorem diagonalOrderOneSymbol_data {ι : Type*} {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hs : ContDiff ℝ ∞ (uncurry a))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hp : ProperKernelRelation (firstOrderKernelRelation a)) :
    GlobalMatrixSymbolData (diagonalOrderOneSymbol (ι := ι) a) := by
  classical
  constructor
  · intro i j
    by_cases h : i = j
    · simpa only [diagonalOrderOneSymbol, if_pos h] using ha
    · simpa only [diagonalOrderOneSymbol, if_neg h] using zeroFirstBaseFrequency
  · intro i j
    by_cases h : i = j
    · simpa only [diagonalOrderOneSymbol, if_pos h] using hs
    · simp only [diagonalOrderOneSymbol, if_neg h]
      exact contDiff_const
  · intro i j n
    by_cases h : i = j
    · simpa only [diagonalOrderOneSymbol, if_pos h] using hb n
    · simpa only [diagonalOrderOneSymbol, if_neg h] using zeroSymbol_pureBase n
  · intro i j
    by_cases h : i = j
    · simpa only [diagonalOrderOneSymbol, if_pos h] using hp
    · simpa only [diagonalOrderOneSymbol, if_neg h] using zeroSymbol_proper_of_proper hp

theorem diagonalOrderOneSymbol_derivativeData {ι : Type*} {a : Space → Space → ℂ}
    (ha : ∀ b : Fin 4, FirstBaseFrequencyOrderOne (baseDirectionSymbol a (coordinateDirection b)))
    (hb : ∀ (b : Fin 4) (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => baseDirectionSymbol a (coordinateDirection b) y ξ) x‖ ≤ C * (1 + ‖ξ‖)) :
    GlobalMatrixDerivativeSymbolData (diagonalOrderOneSymbol (ι := ι) a) := by
  classical
  have hzero (b : Fin 4) : baseDirectionSymbol (fun _ _ : Space => (0:ℂ)) (coordinateDirection b) =
      fun _ _ => 0 := by
    funext x ξ
    simp [baseDirectionSymbol, fderiv_const_apply]
  constructor
  · intro i j b
    by_cases h : i = j
    · simpa only [diagonalOrderOneSymbol, if_pos h] using ha b
    · simpa only [diagonalOrderOneSymbol, if_neg h, hzero] using zeroFirstBaseFrequency
  · intro i j b n
    by_cases h : i = j
    · simpa only [diagonalOrderOneSymbol, if_pos h] using hb b n
    · simpa only [diagonalOrderOneSymbol, if_neg h, hzero] using zeroSymbol_pureBase n

theorem diagonalOrderOneSymbol_action {ι : Type*} [Fintype ι] (a : Space → Space → ℂ)
    (f : ι → SchwartzMap Space ℂ) (i : ι) (x : Space) :
    matrixFirstOrderAction (diagonalOrderOneSymbol a) f i x = firstOrderAction a (f i) x := by
  classical
  have hzero (g : SchwartzMap Space ℂ) : firstOrderAction (fun _ _ : Space => 0) g x = 0 := by
    simp [firstOrderAction, Real.fourierIntegralInv_eq]
  unfold matrixFirstOrderAction
  rw [Finset.sum_eq_single i]
  · simp [diagonalOrderOneSymbol]
  · intro j _ h
    simp only [diagonalOrderOneSymbol, if_neg (Ne.symm h), hzero]
  · intro h
    exact (h (Finset.mem_univ i)).elim

theorem diagonalOrderOneSymbol_symmetric {ι : Type*} [Fintype ι] {a : Space → Space → ℂ}
    (ha : FirstOrderFormalSymmetry a) :
    MatrixFirstOrderFormalSymmetry (diagonalOrderOneSymbol (ι := ι) a) := by
  intro f g
  simp only [diagonalOrderOneSymbol_action]
  exact Finset.sum_congr rfl fun i _ => ha (g i) (f i)

end Burnett.Analysis.CarlesonEmbedding
