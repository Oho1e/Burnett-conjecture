import Burnett.Analysis.PrincipalEnergy.Density.CompactCutoffCommutator
import Burnett.Analysis.PrincipalEnergy.Energy.CompactFiniteMultiplier
import Burnett.Analysis.PrincipalEnergy.Energy.DiagonalScalarFourier

set_option autoImplicit false
set_option maxHeartbeats 9700000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (Op)
open scoped BigOperators ComplexConjugate InnerProductSpace ContDiff

def compactFieldTransfer {ι : Type*} (i j : ι) :
    CompactSchwartzComponents ι →ₗ[ℂ] CompactSchwartzComponents ι := by
  classical
  exact
    { toFun := fun f => ⟨fun k => if k = i then f.val j else 0, fun k => by
        by_cases h : k = i
        · simpa only [if_pos h] using f.property j
        · simpa only [if_neg h] using (HasCompactSupport.zero : HasCompactSupport (0 : Space → ℂ))⟩
      map_add' := fun f g => by
        apply Subtype.ext
        funext k
        change (if k=i then f.val j + g.val j else 0) = (if k=i then f.val j else 0) + (if k=i then g.val j else 0)
        by_cases h : k=i <;> simp [h]
      map_smul' := fun c f => by
        apply Subtype.ext
        funext k
        change (if k=i then c • f.val j else 0) = c • (if k=i then f.val j else 0)
        by_cases h : k=i <;> simp [h] }

theorem compactFieldTransfer_apply {ι : Type*} (i j k : ι) (f : CompactSchwartzComponents ι) :
    (compactFieldTransfer i j f).val k = by classical exact if k=i then f.val j else 0 := by
  rfl

theorem compactFieldTransfer_norm_le {ι : Type*} [Fintype ι] (i j : ι) (u : CompactMatrixTest ι) :
    ‖compactTransportOp (compactFieldTransfer i j) u‖ ≤ ‖u‖ := by
  classical
  obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective u
  rw [compactTransportOp_apply, compactMatrixTestEquiv_norm, compactMatrixTestEquiv_norm]
  have hEq : matrixSchwartzL2Norm (compactFieldTransfer i j f).val = ‖(f.val j).toLp 2 volume‖ := by
    unfold matrixSchwartzL2Norm
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [PiLp.toLp_apply, compactFieldTransfer_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ h
      have hzero : (0 : SchwartzMap Space ℂ).toLp 2 volume = 0 :=
        map_zero (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space))
      rw [if_neg h, hzero, norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0)]
    · intro h
      exact (h (Finset.mem_univ i)).elim
  rw [hEq]
  exact PiLp.norm_apply_le (WithLp.toLp 2 (fun k => (f.val k).toLp 2 volume)) j

theorem compactFiniteMultiplier_eq_sum_fieldTransfer {ι : Type*} [Fintype ι]
    (r : ι → ι → Space → ℂ) (hr : ∀ i j, ContDiff ℝ ∞ (r i j)) :
    compactTransportOp (compactFiniteMultiplier r hr) = ∑ i, ∑ j,
      compactTransportOp (compactFieldTransfer i j) * compactTransportOp (compactScalarMultiplier (r i j) (hr i j)) := by
  classical
  apply LinearMap.ext
  intro u
  obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective u
  simp only [LinearMap.sum_apply, Module.End.mul_apply, compactTransportOp_apply, ← map_sum]
  apply congrArg (compactMatrixTestEquiv ι)
  apply Subtype.ext
  funext k
  ext x
  change (compactFiniteMultiplier r hr f).val k x =
    SchwartzMap.delta ℂ ℂ x (LinearMap.proj (R := ℂ) k ((compactSchwartzComponents ι).subtype
      (∑ i, ∑ j, compactFieldTransfer i j (compactScalarMultiplier (r i j) (hr i j) f))))
  simp only [compactFiniteMultiplier_apply, map_sum, LinearMap.proj_apply, Submodule.subtype_apply, SchwartzMap.delta_apply]
  symm
  rw [Finset.sum_eq_single k]
  · simp only [compactFieldTransfer_apply, if_true, compactScalarMultiplier_apply]
  · intro i _ hi
    simp [compactFieldTransfer_apply, Ne.symm hi]
  · intro h
    exact (h (Finset.mem_univ k)).elim

theorem compactCutoffFourier_eq_diagonal_entries {ι : Type*} [Fintype ι]
    {a : Space → Space → ℂ} (ha : GlobalMatrixSymbolData (diagonalOrderOneSymbol (ι := ι) a))
    (p q : SchwartzMap Space ℂ) (f : CompactSchwartzComponents ι) (i : ι) (x : Space) :
    (compactCutoffActualFourier ha p q f).val i x =
      p x * firstOrderAction a (scalarSchwartzProduct q (f.val i)) x := by
  rw [compactCutoffActualFourier_apply, diagonalOrderOneSymbol_action]

theorem compactCutoffFourier_commutes_fieldTransfer {ι : Type*} [Fintype ι]
    {a : Space → Space → ℂ} (ha : GlobalMatrixSymbolData (diagonalOrderOneSymbol (ι := ι) a))
    (p q : SchwartzMap Space ℂ) (i j : ι) :
    let C := compactSchwartzMultiplier p * compactTransportOp (compactActualFourierOp ha) *
      compactSchwartzMultiplier q
    let E := compactTransportOp (compactFieldTransfer i j)
    C*E = E*C := by
  classical
  intro C E
  change _ * compactTransportOp (compactFieldTransfer i j) = compactTransportOp (compactFieldTransfer i j) * _
  change (compactSchwartzMultiplier p * compactTransportOp (compactActualFourierOp ha) * compactSchwartzMultiplier q) *
    compactTransportOp (compactFieldTransfer i j) = compactTransportOp (compactFieldTransfer i j) *
      (compactSchwartzMultiplier p * compactTransportOp (compactActualFourierOp ha) * compactSchwartzMultiplier q)
  rw [← compactCutoffActualFourier_transport]
  apply LinearMap.ext
  intro u
  obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective u
  simp only [Module.End.mul_apply, compactTransportOp_apply]
  apply congrArg (compactMatrixTestEquiv ι)
  apply Subtype.ext
  funext k
  ext x
  rw [compactCutoffFourier_eq_diagonal_entries, compactFieldTransfer_apply, compactFieldTransfer_apply]
  by_cases hk : k = i
  · rw [if_pos hk, if_pos hk, compactCutoffFourier_eq_diagonal_entries]
  · rw [if_neg hk, if_neg hk]
    have hq : scalarSchwartzProduct q 0 = 0 := by ext y; simp [scalarSchwartzProduct_apply]
    have hF : FrequencyOrderOne a := by
      have h := (ha.frequency i i).frequency
      simpa [diagonalOrderOneSymbol] using h
    have hz : firstOrderAction a (0 : SchwartzMap Space ℂ) x = 0 := by
      simpa only [smul_zero, sub_self, one_mul] using
        firstOrderAction_sub_smul a hF x (0 : SchwartzMap Space ℂ) 0 1
    rw [hq, hz, mul_zero, SchwartzMap.zero_apply]

end Burnett.Analysis.CarlesonEmbedding
