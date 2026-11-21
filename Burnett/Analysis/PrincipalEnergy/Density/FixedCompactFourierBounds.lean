import Burnett.Analysis.PrincipalEnergy.Density.CompactCutoffMultiplierBounds

set_option autoImplicit false
set_option maxHeartbeats 2900000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection Op firstOrderEnergy norm_derivative_le_firstOrderEnergy)
open scoped BigOperators ComplexConjugate InnerProductSpace ContDiff

private theorem cutoff_commutator_product {ι : Type*} [Fintype ι] (D P B Q : Op (CompactMatrixTest ι)) :
    SymmetricEnergy.comm D (P*B*Q) =
      SymmetricEnergy.comm D P * B * Q + P * SymmetricEnergy.comm D B * Q +
        P * B * SymmetricEnergy.comm D Q := by
  unfold SymmetricEnergy.comm
  noncomm_ring

/-- The actual order-one operator localized by two fixed Schwartz cutoffs
and its coordinate commutators have a common first-order bound. -/
theorem exists_compactCutoffFourier_energy_bounds {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : GlobalMatrixSymbolData a)
    (hda : GlobalMatrixDerivativeSymbolData a) (p q : SchwartzMap Space ℂ) :
    let P := compactSchwartzMultiplier (ι := ι) p
    let Q := compactSchwartzMultiplier (ι := ι) q
    let B := compactTransportOp (compactActualFourierOp ha)
    let D : Fin 4 → Op (CompactMatrixTest ι) := compactMatrixCoordinatePartial
    let C := P*B*Q
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : CompactMatrixTest ι,
      ‖C u‖ ≤ K * firstOrderEnergy D u ∧
      ∀ b, ‖SymmetricEnergy.comm (D b) C u‖ ≤ K * firstOrderEnergy D u := by
  intro P Q B D C
  obtain ⟨L₀, hL₀, normB⟩ := exists_compactActualFourierOp_h1_bound ha
  obtain ⟨L₁, hL₁, normD⟩ := exists_compactActualFourierOp_coordinate_comm_bound ha hda
  obtain ⟨M, hM, normP⟩ := exists_compactSchwartzMultiplier_energy_bounds (ι := ι) p
  obtain ⟨N, hN, normQ⟩ := exists_compactSchwartzMultiplier_energy_bounds (ι := ι) q
  let dp (b : Fin 4) := SchwartzMap.pderivCLM ℂ (coordinateDirection b) p
  let dq (b : Fin 4) := SchwartzMap.pderivCLM ℂ (coordinateDirection b) q
  choose S hS normDP using fun b => exists_compactSchwartzMultiplier_energy_bounds (ι := ι) (dp b)
  choose T hT normDQ using fun b => exists_compactSchwartzMultiplier_energy_bounds (ι := ι) (dq b)
  let E (u : CompactMatrixTest ι) := firstOrderEnergy D u
  let H := L₀+L₁+M+N+∑ b, (S b+T b)
  have hH : 0 ≤ H := by
    dsimp [H]
    exact add_nonneg (by positivity) (Finset.sum_nonneg (fun b _ => add_nonneg (hS b) (hT b)))
  have hL₀H : L₀ ≤ H := by
    dsimp only [H]
    linarith only [hL₁, hM, hN, Finset.sum_nonneg (s := Finset.univ) (fun b _ => add_nonneg (hS b) (hT b))]
  have hL₁H : L₁ ≤ H := by
    dsimp only [H]
    linarith only [hL₀, hM, hN, Finset.sum_nonneg (s := Finset.univ) (fun b _ => add_nonneg (hS b) (hT b))]
  have hMH : M ≤ H := by
    dsimp only [H]
    linarith only [hL₀, hL₁, hN, Finset.sum_nonneg (s := Finset.univ) (fun b _ => add_nonneg (hS b) (hT b))]
  have hNH : N ≤ H := by
    dsimp only [H]
    linarith only [hL₀, hL₁, hM, Finset.sum_nonneg (s := Finset.univ) (fun b _ => add_nonneg (hS b) (hT b))]
  have hST (b : Fin 4) : S b + T b ≤ H := by
    dsimp only [H]
    exact (Finset.single_le_sum (fun j _ => add_nonneg (hS j) (hT j)) (Finset.mem_univ b)).trans
      (le_add_of_nonneg_left (by positivity))
  have hEN (u : CompactMatrixTest ι) : 0 ≤ E u := Real.sqrt_nonneg _
  have hB (u : CompactMatrixTest ι) : ‖B u‖ ≤ H*E u := by
    obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective u
    change _ ≤ H*firstOrderEnergy compactMatrixCoordinatePartial (compactMatrixTestEquiv ι f)
    rw [compactMatrixFirstOrderEnergy_eq]
    exact (normB f).trans (mul_le_mul_of_nonneg_right hL₀H (norm_nonneg _))
  have hBD (u : CompactMatrixTest ι) (b : Fin 4) : ‖SymmetricEnergy.comm (D b) B u‖ ≤ H*E u := by
    obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective u
    change _ ≤ H*firstOrderEnergy compactMatrixCoordinatePartial (compactMatrixTestEquiv ι f)
    rw [compactMatrixFirstOrderEnergy_eq]
    exact (normD b f).trans (mul_le_mul_of_nonneg_right hL₁H (norm_nonneg _))
  have hP (u : CompactMatrixTest ι) : ‖P u‖ ≤ H*‖u‖ :=
    (normP u).1.trans (mul_le_mul_of_nonneg_right hMH (norm_nonneg _))
  have hQ (u : CompactMatrixTest ι) : E (Q u) ≤ H*E u :=
    (normQ u).2.trans (mul_le_mul_of_nonneg_right hNH (hEN u))
  have hDP (b : Fin 4) (u : CompactMatrixTest ι) : ‖SymmetricEnergy.comm (D b) P u‖ ≤ H*‖u‖ := by
    rw [show SymmetricEnergy.comm (D b) P = compactSchwartzMultiplier (dp b) from compactSchwartzMultiplier_comm_coordinate b p]
    exact (normDP b u).1.trans (mul_le_mul_of_nonneg_right
      ((le_add_of_nonneg_right (hT b)).trans (hST b)) (norm_nonneg _))
  have hDQ (b : Fin 4) (u : CompactMatrixTest ι) : E (SymmetricEnergy.comm (D b) Q u) ≤ H*E u := by
    rw [show SymmetricEnergy.comm (D b) Q = compactSchwartzMultiplier (dq b) from compactSchwartzMultiplier_comm_coordinate b q]
    exact (normDQ b u).2.trans (mul_le_mul_of_nonneg_right
      ((le_add_of_nonneg_left (hS b)).trans (hST b)) (hEN u))
  refine ⟨3*H^3, by positivity, fun u => ⟨?_, fun b => ?_⟩⟩
  · change ‖P (B (Q u))‖ ≤ 3*H^3*E u
    have h := (hP _).trans (mul_le_mul_of_nonneg_left
      ((hB _).trans (mul_le_mul_of_nonneg_left (hQ u) hH)) hH)
    exact h.trans (by nlinarith only [mul_nonneg (pow_nonneg hH 3) (hEN u)])
  · change ‖SymmetricEnergy.comm (D b) (P*B*Q) u‖ ≤ 3*H^3*E u
    rw [cutoff_commutator_product]
    simp only [LinearMap.add_apply, Module.End.mul_apply]
    have h₁ := (hDP b _).trans (mul_le_mul_of_nonneg_left
      ((hB _).trans (mul_le_mul_of_nonneg_left (hQ u) hH)) hH)
    have h₂ := (hP _).trans (mul_le_mul_of_nonneg_left
      ((hBD (Q u) b).trans (mul_le_mul_of_nonneg_left (hQ u) hH)) hH)
    have h₃ := (hP _).trans (mul_le_mul_of_nonneg_left
      ((hB _).trans (mul_le_mul_of_nonneg_left (hDQ b u) hH)) hH)
    exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
      ((add_le_add (add_le_add h₁ h₂) h₃).trans_eq (by ring)))

end Burnett.Analysis.CarlesonEmbedding
