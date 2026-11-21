import Burnett.Analysis.PrincipalEnergy.Localization.MovingPlateauUniformPair
import Burnett.Analysis.PrincipalEnergy.Localization.FiniteMatrixPairing

set_option autoImplicit false
set_option maxHeartbeats 5900000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate ContDiff NNReal

/-- The two constants are fixed before the finite partition, the near edges
and their centers, and the input and test supports are chosen. -/
theorem exists_actualMatrixCommutator_moving_finite_gluing_bound {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FirstBaseFrequencyOrderOne (a i j))
    (hs : ∀ i j, ContDiff ℝ ∞ (uncurry (a i j)))
    (hb : ∀ i j (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a i j y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hSym : MatrixFirstOrderFormalSymmetry a) (χ : SchwartzMap Space ℂ)
    (hχ : HasCompactSupport (χ : Space → ℂ)) (hχReal : ∀ x, conj (χ x) = χ x) :
    ∃ M N : ℝ, 0 ≤ M ∧ 0 ≤ N ∧
      ∀ {κ : Type*} [Fintype κ] [DecidableEq κ] (near far : Finset (κ × κ)),
        Disjoint near far → near ∪ far = Finset.univ →
        ∀ (α : κ → SchwartzMap Space ℂ) (center : κ × κ → Space)
          (Dout Din : ℕ) (d : ℝ), 0 < d →
        (∀ i, (near.filter fun e => e.1 = i).card ≤ Dout) →
        (∀ j, (near.filter fun e => e.2 = j).card ≤ Din) →
        (∀ i x, α i x = ((α i x).re : ℂ)) → (∀ i x, 0 ≤ (α i x).re) →
        (∀ x, ∑ i, (α i x).re ≤ 1) →
        (∀ e ∈ near, ∀ x, x ∈ tsupport (α e.1 : Space → ℂ) ∪ tsupport (α e.2 : Space → ℂ) →
          translateSchwartz (-center e) χ x = 1) →
        (∀ e ∈ far, ∀ x y, α e.1 x ≠ 0 → α e.2 y ≠ 0 → d ≤ ‖x-y‖) →
        ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
          HasCompactSupport (r : Space → ℂ) → (∀ x, conj (r x) = r x) →
          (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
          (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r : Space → ℂ) x‖ ≤ (L : ℝ)) →
          ∀ f g : ι → SchwartzMap Space ℂ,
            (∀ j, HasCompactSupport (f j : Space → ℂ)) →
            (∀ j x, f j x ≠ 0 → ∑ k, α k x = 1) →
            (∀ i x, g i x ≠ 0 → ∑ k, α k x = 1) →
            ‖actualMatrixCommutatorPair a r f g‖ ≤
              (M * (U + (L : ℝ)) * √(Dout : ℝ) * √(Din : ℝ) + N * U * d⁻¹) *
                matrixSchwartzL2Norm f * matrixSchwartzL2Norm g := by
  have hc (i j : ι) : Continuous (uncurry (a i j)) := (hs i j).continuous
  obtain ⟨M, hM, nearBound⟩ := exists_movingPlateauMatrix_uniform_physical_pair_bound ha hs hb hSym χ hχ hχReal
  obtain ⟨N, hN, farBound⟩ := exists_actualFarMatrixCutoffPair_norm_le ha hc
  refine ⟨M, N, hM, hN, ?_⟩
  intro κ _ _ near far hSplit hAll α center Dout Din d hd hOut hIn hReal hPos hSub hPlateau hGap
    r L U hr hRealR hVal hDer f g hf hOneF hOneG
  obtain ⟨hU, hSup, hLip⟩ := smoothCoefficient_bounds_of_ae_norm_firstDerivative r (r.smooth 1) U L hVal hDer
  let F (k : κ) (j : ι) := scalarSchwartzProduct (α k) (f j)
  let G (k : κ) (i : ι) := scalarSchwartzProduct (α k) (g i)
  let P (e : κ × κ) : ℂ := actualMatrixCommutatorPair a r (F e.2) (G e.1)
  let Q := M * (U + (L : ℝ))
  have hQ : 0 ≤ Q := mul_nonneg hM (add_nonneg hU L.coe_nonneg)
  have hEntry (e : κ × κ) (he : e ∈ near) :
      ‖P e‖ ≤ Q * (matrixSchwartzL2Norm (G e.1) * matrixSchwartzL2Norm (F e.2)) := by
    have hPf (j : ι) (x : Space) (hx : x ∈ tsupport (F e.2 j : Space → ℂ)) :
        translateSchwartz (-center e) χ x = 1 :=
      hPlateau e he x (Set.mem_union_right _ (tsupport_mul_subset_left hx))
    have hPg (i : ι) (x : Space) (hx : x ∈ tsupport (G e.1 i : Space → ℂ)) :
        translateSchwartz (-center e) χ x = 1 :=
      hPlateau e he x (Set.mem_union_left _ (tsupport_mul_subset_left hx))
    exact (nearBound (center e) r L U hU hr hRealR hVal hDer (F e.2) (G e.1) hPf hPg).trans_eq
      (by dsimp only [Q]; ring)
  have hF : √(∑ j, matrixSchwartzL2Norm (F j) ^ 2) ≤ matrixSchwartzL2Norm f :=
    (Real.sqrt_le_sqrt (matrixCutoff_sum_norm_sq_le α hReal hPos hSub f)).trans_eq
      (Real.sqrt_sq (norm_nonneg _))
  have hG : √(∑ i, matrixSchwartzL2Norm (G i) ^ 2) ≤ matrixSchwartzL2Norm g :=
    (Real.sqrt_le_sqrt (matrixCutoff_sum_norm_sq_le α hReal hPos hSub g)).trans_eq
      (Real.sqrt_sq (norm_nonneg _))
  have hDegree : 0 ≤ √(Dout : ℝ) * √(Din : ℝ) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hNear : ‖∑ e ∈ near, P e‖ ≤ Q * √(Dout : ℝ) * √(Din : ℝ) *
      matrixSchwartzL2Norm f * matrixSchwartzL2Norm g := by
    calc
      _ ≤ ∑ e ∈ near, ‖P e‖ := norm_sum_le _ _
      _ ≤ Q * ∑ e ∈ near, matrixSchwartzL2Norm (G e.1) * matrixSchwartzL2Norm (F e.2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hEntry
      _ ≤ Q * (√(Dout : ℝ) * √(Din : ℝ) *
          √(∑ i, matrixSchwartzL2Norm (G i) ^ 2) * √(∑ j, matrixSchwartzL2Norm (F j) ^ 2)) :=
        mul_le_mul_of_nonneg_left (finitePairs_sum_mul_le_degree near Dout Din hOut hIn
          (fun i => matrixSchwartzL2Norm (G i)) (fun j => matrixSchwartzL2Norm (F j))) hQ
      _ ≤ Q * (√(Dout : ℝ) * √(Din : ℝ) * matrixSchwartzL2Norm g * matrixSchwartzL2Norm f) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (mul_le_mul_of_nonneg_left hG hDegree) hF (Real.sqrt_nonneg _)
            (mul_nonneg hDegree (norm_nonneg _))) hQ
      _ = _ := by ring
  have hFar : ‖∑ e ∈ far, P e‖ ≤ N * U * d⁻¹ * matrixSchwartzL2Norm f * matrixSchwartzL2Norm g :=
    farBound far α hReal hPos hSub d hd hGap r f g L U hLip hU hSup hf
  have hPair : actualMatrixCommutatorPair a r f g = ∑ e ∈ near, P e + ∑ e ∈ far, P e := by
    calc
      _ = ∑ e, P e := actualMatrixCommutatorPair_eq_sum_cutoffs (fun i j => (ha i j).frequency)
        hc r α f g hOneF hOneG
      _ = _ := by rw [← hAll, Finset.sum_union hSplit]
  rw [hPair]
  exact (norm_add_le _ _).trans ((add_le_add hNear hFar).trans_eq (by dsimp only [Q]; ring))

end Burnett.Analysis.CarlesonEmbedding
