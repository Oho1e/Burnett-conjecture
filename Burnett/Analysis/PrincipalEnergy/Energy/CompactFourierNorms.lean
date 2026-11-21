import Burnett.Analysis.PrincipalEnergy.Energy.CompactActualFourier

set_option autoImplicit false
set_option maxHeartbeats 7500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection coordinateH1 firstOrderEnergy Op comm)
open scoped BigOperators ComplexConjugate InnerProductSpace ContDiff

private theorem finiteL2Sum_coeFn {κ : Type*} (s : Finset κ) (f : κ → ComplexL2 Space) :
    ((∑ j ∈ s, f j : ComplexL2 Space) : Space → ℂ) =ᵐ[volume] fun x => ∑ j ∈ s, f j x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 volume
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (f j) (∑ k ∈ s, f k), ih] with x hx hy
    change _ = f j x + ∑ k ∈ s, f k x
    rw [hx, Pi.add_apply, hy]

/-- The finite Hilbert sum is bounded by the sum of the entry estimates. -/
theorem matrixSchwartzL2Norm_le_of_entry_bounds {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → SchwartzMap Space ℂ) (q : ι → κ → Space → ℂ)
    (hEq : ∀ i x, w i x = ∑ j, q i j x) (hMem : ∀ i j, MemLp (q i j) 2 volume)
    (C : ι → κ → ℝ) (E : ℝ) (hBound : ∀ i j, ‖(hMem i j).toLp (q i j)‖ ≤ C i j * E) :
    matrixSchwartzL2Norm w ≤ (∑ i, ∑ j, C i j) * E := by
  let G i j := (hMem i j).toLp (q i j)
  have hRow (i : ι) : (w i).toLp 2 volume = ∑ j, G i j := by
    apply Lp.ext
    have hG : ∀ᵐ x ∂(volume : Measure Space), ∀ j, G i j x = q i j x :=
      ae_all_iff.mpr fun j => (hMem i j).coeFn_toLp
    filter_upwards [(w i).coeFn_toLp 2 volume, finiteL2Sum_coeFn Finset.univ (G i), hG]
      with x hw hg h
    rw [hw, hg, hEq]
    exact Finset.sum_congr rfl (fun j _ => (h j).symm)
  unfold matrixSchwartzL2Norm
  calc
    _ ≤ ∑ i, ‖(w i).toLp 2 volume‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => norm_nonneg ((w i).toLp 2 volume)))).mp
      rw [PiLp.norm_sq_eq_of_L2]
      exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg ((w i).toLp 2 volume))
    _ ≤ ∑ i, ∑ j, C i j * E := by
      apply Finset.sum_le_sum
      intro i _
      rw [hRow]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hBound i j))
    _ = _ := by simp only [Finset.sum_mul]

def compactMatrixCoordinateH1 {ι : Type*} [Fintype ι] (f : CompactSchwartzComponents ι) : ℝ :=
  ‖WithLp.toLp 2 (fun i => schwartzCoordinateJet (f.val i))‖

private theorem coordinateH1_le_compactMatrixCoordinateH1 {ι : Type*} [Fintype ι]
    (f : CompactSchwartzComponents ι) (i : ι) : coordinateH1 (f.val i) ≤ compactMatrixCoordinateH1 f := by
  rw [← schwartzCoordinateJet_norm]
  exact PiLp.norm_apply_le (WithLp.toLp 2 (fun i => schwartzCoordinateJet (f.val i))) i

def compactMatrixCoordinatePartial {ι : Type*} [Fintype ι] (b : Fin 4) : Op (CompactMatrixTest ι) :=
  compactTransportOp (compactComponentDerivative b)

theorem compactMatrixFirstOrderEnergy_eq {ι : Type*} [Fintype ι] (f : CompactSchwartzComponents ι) :
    firstOrderEnergy compactMatrixCoordinatePartial (compactMatrixTestEquiv ι f) =
      compactMatrixCoordinateH1 f := by
  unfold firstOrderEnergy compactMatrixCoordinateH1 compactMatrixCoordinatePartial
  simp only [compactTransportOp_apply, compactMatrixTestEquiv_norm, matrixSchwartzL2Norm]
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity), PiLp.norm_sq_eq_of_L2]
  simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  simp only [Finset.sum_add_distrib]
  rfl

/-- Global (H^1 \to L^2) control of the actual matrix Fourier operator. -/
theorem exists_compactActualFourierOp_h1_bound {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : GlobalMatrixSymbolData a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : CompactSchwartzComponents ι,
      ‖compactTransportOp (compactActualFourierOp ha) (compactMatrixTestEquiv ι f)‖ ≤
        C * compactMatrixCoordinateH1 f := by
  choose C hC bounded using fun i j => exists_firstOrderAction_global_h1_bound_of_properSupport
    (ha.frequency i j) (ha.smooth i j) (ha.pureBase i j) (ha.proper i j)
  refine ⟨∑ i, ∑ j, C i j, Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hC i j)), ?_⟩
  intro f
  rw [compactTransportOp_apply, compactMatrixTestEquiv_norm]
  choose hMem hBound using fun i j => bounded i j (f.val j) (f.property j)
  exact matrixSchwartzL2Norm_le_of_entry_bounds
    (compactActualFourierOp ha f).val (fun i j => firstOrderAction (a i j) (f.val j))
    (compactActualFourierOp_apply ha f) hMem C (compactMatrixCoordinateH1 f)
    (fun i j => (hBound i j).trans (mul_le_mul_of_nonneg_left
      (coordinateH1_le_compactMatrixCoordinateH1 f j) (hC i j)))

structure GlobalMatrixDerivativeSymbolData {ι : Type*} (a : ι → ι → Space → Space → ℂ) : Prop where
  frequency : ∀ i j (b : Fin 4), FirstBaseFrequencyOrderOne (baseDirectionSymbol (a i j) (coordinateDirection b))
  pureBase : ∀ i j (b : Fin 4) (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
    ‖iteratedFDeriv ℝ n (fun y => baseDirectionSymbol (a i j) (coordinateDirection b) y ξ) x‖ ≤
      C * (1 + ‖ξ‖)

private theorem alongLine_deriv_eq_fderiv {v : Space → ℂ} {x : Space} (e : Space)
    (hv : DifferentiableAt ℝ v x) :
    deriv (fun t : ℝ => v (x+t • e)) 0 = fderiv ℝ v x e := by
  have hLine : HasDerivAt (fun t : ℝ => x+t • e) e 0 := by
    simpa only [one_smul] using (((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x)
  have hV : HasFDerivAt v (fderiv ℝ v x) ((fun t : ℝ => x+t • e) 0) := by
    simpa only [zero_smul, add_zero] using hv.hasFDerivAt
  exact (hV.comp_hasDerivAt 0 hLine).deriv

private theorem compactActualFourier_derivative_sub_apply {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : GlobalMatrixSymbolData a)
    (b : Fin 4) (f : CompactSchwartzComponents ι) (i : ι) (x : Space) :
    ((compactComponentDerivative b) (compactActualFourierOp ha f)).val i x -
      (compactActualFourierOp ha ((compactComponentDerivative b) f)).val i x =
        ∑ j, firstOrderAction (baseDirectionSymbol (a i j) (coordinateDirection b)) (f.val j) x := by
  have hDiff (j : ι) : DifferentiableAt ℝ (firstOrderAction (a i j) (f.val j)) x := by
    have hSmooth := firstOrderAction_contDiff_of_pureBaseOrder (ha.smooth i j) (ha.pureBase i j) (f.val j)
    exact hSmooth.differentiable (by simp) x
  change fderiv ℝ (fun y => ∑ j, firstOrderAction (a i j) (f.val j) y) x (coordinateDirection b) -
      (∑ j, firstOrderAction (a i j) (SchwartzMap.pderivCLM ℂ (coordinateDirection b) (f.val j)) x) = _
  rw [fderiv_fun_sum (fun j _ => hDiff j), ContinuousLinearMap.sum_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← alongLine_deriv_eq_fderiv (coordinateDirection b) (hDiff j)]
  exact firstOrderAction_direction_commutator_of_jointSmooth (ha.frequency i j) (ha.smooth i j)
    (f.val j) x (coordinateDirection b)

/-- The actual four coordinate commutators have global (H^1 \to L^2) control. -/
theorem exists_compactActualFourierOp_coordinate_comm_bound {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : GlobalMatrixSymbolData a)
    (hda : GlobalMatrixDerivativeSymbolData a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Fin 4) (f : CompactSchwartzComponents ι),
      ‖comm (compactMatrixCoordinatePartial b) (compactTransportOp (compactActualFourierOp ha))
        (compactMatrixTestEquiv ι f)‖ ≤ C * compactMatrixCoordinateH1 f := by
  choose C hC bounded using fun i j =>
    exists_global_coordinate_direction_action_h1_bounds (ha.frequency i j) (ha.smooth i j)
      (hda.frequency i j) (hda.pureBase i j) (ha.proper i j)
  refine ⟨∑ i, ∑ j, C i j, Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hC i j)), ?_⟩
  intro b f
  let D := compactComponentDerivative (ι := ι) b
  let B := compactActualFourierOp ha
  let W := D (B f) - B (D f)
  have hW : comm (compactMatrixCoordinatePartial b) (compactTransportOp B) (compactMatrixTestEquiv ι f) =
      compactMatrixTestEquiv ι W := by
    simp only [SymmetricEnergy.comm, LinearMap.sub_apply, Module.End.mul_apply, compactMatrixCoordinatePartial,
      compactTransportOp_apply, W, D, B, map_sub]
  rw [hW, compactMatrixTestEquiv_norm]
  let Q i j := firstOrderAction (baseDirectionSymbol (a i j) (coordinateDirection b)) (f.val j)
  have hDiff (i j : ι) :
      (fun x => deriv (fun t : ℝ => firstOrderAction (a i j) (f.val j) (x+t • coordinateDirection b)) 0 -
          firstOrderAction (a i j) (SchwartzMap.pderivCLM ℂ (coordinateDirection b) (f.val j)) x) = Q i j :=
    funext fun x => firstOrderAction_direction_commutator_of_jointSmooth
      (ha.frequency i j) (ha.smooth i j) (f.val j) x (coordinateDirection b)
  have hBounds (i j : ι) : ∃ hM : MemLp (Q i j) 2 volume,
      ‖hM.toLp (Q i j)‖ ≤ C i j * coordinateH1 (f.val j) := by
    rw [← hDiff i j]
    exact bounded i j b (f.val j) (f.property j)
  choose hM hBounds using hBounds
  refine matrixSchwartzL2Norm_le_of_entry_bounds W.val Q
    (fun i x => compactActualFourier_derivative_sub_apply ha b f i x) hM C _ (fun i j => ?_)
  exact (hBounds i j).trans (mul_le_mul_of_nonneg_left
    (coordinateH1_le_compactMatrixCoordinateH1 f j) (hC i j))

end Burnett.Analysis.CarlesonEmbedding
