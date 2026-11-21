import Burnett.Analysis.PrincipalEnergy.Energy.CompactFiniteMultiplier
import Burnett.Analysis.PrincipalEnergy.Energy.DiagonalScalarFourier

set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection Op comm principal principal_energy_bound)
open scoped BigOperators ComplexConjugate InnerProductSpace ContDiff NNReal

theorem exists_compactFiniteMultiplier_scalar_comm_bound
    {ι : Type*} [Fintype ι] {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hs : ContDiff ℝ ∞ (uncurry a))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hp : ProperKernelRelation (firstOrderKernelRelation a)) (hSym : FirstOrderFormalSymmetry a) :
    let B := compactTransportOp (compactActualFourierOp (diagonalOrderOneSymbol_data (ι := ι) ha hs hb hp))
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ι → ι → Space → ℂ) (hr : ∀ i j, ContDiff ℝ ∞ (r i j))
      (L : NNReal) (U : ℝ), 0 ≤ U →
      (∀ i j, ∀ᵐ x ∂(volume : Measure Space), ‖r i j x‖ ≤ U) →
      (∀ i j, ∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r i j) x‖ ≤ (L : ℝ)) →
      ∀ v : CompactMatrixTest ι,
        ‖comm (compactTransportOp (compactFiniteMultiplier r hr)) B v‖ ≤ C * (U+(L:ℝ)) * ‖v‖ := by
  intro B
  obtain ⟨C, hC, bound⟩ := exists_smoothFiniteCoefficientCommutator_global_L2_bound
    (ι := ι) (κ := ι) ha hs hb hSym hp
  refine ⟨C, hC, fun r hr L U hU hVal hDer v => ?_⟩
  obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective v
  let R := compactFiniteMultiplier r hr
  let T := compactActualFourierOp (diagonalOrderOneSymbol_data (ι := ι) ha hs hb hp)
  let W := R (T f) - T (R f)
  have hEq : comm (compactTransportOp R) B (compactMatrixTestEquiv ι f) =
      compactMatrixTestEquiv ι W := by
    change comm (compactTransportOp R) (compactTransportOp T) _ = _
    simp only [SymmetricEnergy.comm, LinearMap.sub_apply, Module.End.mul_apply, compactTransportOp_apply, W, map_sub]
  obtain ⟨g, hg, hBound⟩ := bound r hr L U hU hVal hDer f.val f.property
  have hLp (i : ι) : (W.val i).toLp 2 volume = g i := by
    apply Lp.ext
    filter_upwards [(W.val i).coeFn_toLp 2 volume, hg i] with x hw hG
    rw [hw, hG]
    change (R (T f)).val i x - (T (R f)).val i x = _
    rw [show (R (T f)).val i x = ∑ j, r i j x * (T f).val j x from
      compactFiniteMultiplier_apply r hr (T f) i x]
    simp only [R, T, compactActualFourierOp_apply,
      diagonalOrderOneSymbol_action, smoothFiniteCoefficientCommutator, compactFiniteMultiplier_eqSchwartzSum]
  rw [hEq, compactMatrixTestEquiv_norm, compactMatrixTestEquiv_norm]
  have hG : WithLp.toLp 2 (fun i => (W.val i).toLp 2 volume) = g := by
    apply PiLp.ext
    exact hLp
  simpa only [matrixSchwartzL2Norm, hG] using hBound

def compactFinitePrincipalField {ι : Type*} [Fintype ι]
    (r : Fin 4 → Fin 4 → ι → ι → Space → ℂ) (f : CompactSchwartzComponents ι) (i : ι) (x : Space) : ℂ :=
  ∑ b, ∑ d, ∑ j, r b d i j x *
    (SchwartzMap.pderivCLM ℂ (coordinateDirection b)
      (SchwartzMap.pderivCLM ℂ (coordinateDirection d) (f.val j))) x

private theorem compactFinitePrincipal_inner {ι : Type*} [Fintype ι] {a : ι → ι → Space → Space → ℂ}
    (ha : GlobalMatrixSymbolData a) (r : Fin 4 → Fin 4 → ι → ι → Space → ℂ)
    (hr : ∀ b d i j, ContDiff ℝ ∞ (r b d i j)) (f : CompactSchwartzComponents ι) :
    ⟪compactTransportOp (compactActualFourierOp ha) (compactMatrixTestEquiv ι f),
       principal compactMatrixCoordinatePartial
         (fun b d => compactTransportOp (compactFiniteMultiplier (r b d) (hr b d)))
         (compactMatrixTestEquiv ι f)⟫_ℂ =
      ∑ i, ∫ x, conj (matrixFirstOrderAction a f.val i x) * compactFinitePrincipalField r f i x := by
  let P : CompactSchwartzComponents ι :=
    ∑ b, ∑ d, compactFiniteMultiplier (r b d) (hr b d)
      (compactComponentDerivative b (compactComponentDerivative d f))
  have hP : principal compactMatrixCoordinatePartial
        (fun b d => compactTransportOp (compactFiniteMultiplier (r b d) (hr b d)))
        (compactMatrixTestEquiv ι f) = compactMatrixTestEquiv ι P := by
    simp only [SymmetricEnergy.principal, LinearMap.sum_apply, Module.End.mul_apply, compactMatrixCoordinatePartial,
      compactTransportOp_apply, P, map_sum]
  rw [hP, compactTransportOp_apply, compactMatrixTestEquiv_inner]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards with x
  rw [compactActualFourierOp_apply]
  congr 1
  change SchwartzMap.delta ℂ ℂ x
    (LinearMap.proj (R := ℂ) i ((compactSchwartzComponents ι).subtype P)) = _
  simp only [P, map_sum, LinearMap.proj_apply, Submodule.subtype_apply, SchwartzMap.delta_apply,
    compactFiniteMultiplier_apply, compactFinitePrincipalField]
  rfl

/-- The original Lebesgue principal energy estimate for Hermitian finite
matrix coefficients when the full original symbol is scalar. -/
theorem exists_actual_matrixCoefficient_principal_energy_bound
    {ι : Type*} [Fintype ι] {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hs : ContDiff ℝ ∞ (uncurry a))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hda : ∀ b : Fin 4, FirstBaseFrequencyOrderOne (baseDirectionSymbol a (coordinateDirection b)))
    (hdb : ∀ (b : Fin 4) (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => baseDirectionSymbol a (coordinateDirection b) y ξ) x‖ ≤
        C * (1 + ‖ξ‖))
    (hp : ProperKernelRelation (firstOrderKernelRelation a)) (hSym : FirstOrderFormalSymmetry a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin 4 → Fin 4 → ι → ι → Space → ℂ)
      (_hr : ∀ b d i j, ContDiff ℝ ∞ (r b d i j)) (L : NNReal) (U : ℝ),
      0 ≤ U →
      (∀ b d i j x, conj (r b d i j x) = r d b j i x) →
      (∀ b d i j, ∀ᵐ x ∂(volume : Measure Space), ‖r b d i j x‖ ≤ U) →
      (∀ b d i j, ∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r b d i j) x‖ ≤ (L : ℝ)) →
      ∀ f : CompactSchwartzComponents ι,
        |2 * (∑ i, ∫ x, conj (firstOrderAction a (f.val i) x) *
          compactFinitePrincipalField r f i x).im| ≤ C * (U+(L:ℝ)) * (compactMatrixCoordinateH1 f)^2 := by
  let haM := diagonalOrderOneSymbol_data (ι := ι) ha hs hb hp
  let hdaM := diagonalOrderOneSymbol_derivativeData (ι := ι) hda hdb
  obtain ⟨C₀, hC₀, hB⟩ := exists_compactActualFourierOp_h1_bound haM
  obtain ⟨C₁, hC₁, hDB⟩ := exists_compactActualFourierOp_coordinate_comm_bound haM hdaM
  obtain ⟨C₂, hC₂, hRB⟩ := exists_compactFiniteMultiplier_scalar_comm_bound (ι := ι) ha hs hb hp hSym
  let K := C₀+C₁+C₂
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hK₀ : C₀ ≤ K := by dsimp [K]; linarith
  have hK₁ : C₁ ≤ K := by dsimp [K]; linarith
  have hK₂ : C₂ ≤ K := by dsimp [K]; linarith
  let n := (Fintype.card ι : ℝ)^2
  let m := 1+n
  have hm : 0 ≤ m := by dsimp [m, n]; positivity
  refine ⟨80*K*m, by positivity, fun r hr L U hU hHerm hVal hDer f => ?_⟩
  let D : Fin 4 → Op (CompactMatrixTest ι) := compactMatrixCoordinatePartial
  let B := compactTransportOp (compactActualFourierOp haM)
  let R (b d : Fin 4) : Op (CompactMatrixTest ι) :=
    compactTransportOp (compactFiniteMultiplier (r b d) (hr b d))
  let dR (b d : Fin 4) : Op (CompactMatrixTest ι) :=
    compactTransportOp (compactFiniteMultiplier (fun i j => scalarCoordinateDerivative (r b d i j) b)
      (fun i j => scalarCoordinateDerivative_smooth (hr b d i j) b))
  let u := compactMatrixTestEquiv ι f
  let A₀ := U+(L:ℝ)
  let A := m*A₀
  have hA₀ : 0 ≤ A₀ := add_nonneg hU L.coe_nonneg
  have hA : 0 ≤ A := mul_nonneg hm hA₀
  have hAup : A₀ ≤ A := le_mul_of_one_le_left hA₀ (le_add_of_nonneg_right (sq_nonneg _))
  have hAn : n*A₀ ≤ A := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hA₀
  have hEA : Burnett.Analysis.SymmetricEnergy.firstOrderEnergy D u = compactMatrixCoordinateH1 f :=
    compactMatrixFirstOrderEnergy_eq f
  have hNorm (b d : Fin 4) (i j : ι) := smoothCoefficient_bounds_of_ae_norm_firstDerivative (r b d i j)
    ((hr b d i j).of_le (by simp)) U L (hVal b d i j) (hDer b d i j)
  have hR (b d : Fin 4) (v w : CompactMatrixTest ι) : ⟪R b d v, w⟫_ℂ = ⟪v, R d b w⟫_ℂ :=
    compactFiniteMultiplier_adjoints (r b d) (r d b) (hr b d) (hr d b) (hHerm b d) v w
  have hRNorm (b d : Fin 4) (v : CompactMatrixTest ι) : ‖R b d v‖ ≤ A*‖v‖ :=
    (compactFiniteMultiplier_norm_le (r b d) (hr b d) A₀ hA₀
      (fun i j x => ((hNorm b d i j).2.1 x).trans (le_add_of_nonneg_right L.coe_nonneg)) v).trans
      (mul_le_mul_of_nonneg_right hAn (norm_nonneg _))
  have hdRNorm (b d : Fin 4) (v : CompactMatrixTest ι) : ‖dR b d v‖ ≤ A*‖v‖ := by
    apply LE.le.trans ?_ (mul_le_mul_of_nonneg_right hAn (norm_nonneg _))
    refine compactFiniteMultiplier_norm_le _ _ A₀ hA₀ (fun i j x => ?_) v
    have he : ‖coordinateDirection b‖ = 1 := by
      simp only [coordinateDirection, EuclideanSpace.norm_single, norm_one]
    have hL : ‖fderiv ℝ (r b d i j) x‖ ≤ (L:ℝ) :=
      norm_fderiv_le_of_lipschitz ℝ (hNorm b d i j).2.2
    exact ((ContinuousLinearMap.le_opNorm (fderiv ℝ (r b d i j) x) (coordinateDirection b)).trans
      (by rw [he, mul_one]; exact hL)).trans (le_add_of_nonneg_left hU)
  have hRB' (b d : Fin 4) (v : CompactMatrixTest ι) : ‖comm (R b d) B v‖ ≤ K*A*‖v‖ :=
    (hRB (r b d) (hr b d) L U hU (hVal b d) (hDer b d) v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul hK₂ hAup hA₀ hK) (norm_nonneg _))
  have hDB' (b : Fin 4) : ‖comm (D b) B u‖ ≤ K * Burnett.Analysis.SymmetricEnergy.firstOrderEnergy D u := by
    rw [hEA]
    exact (hDB b f).trans (mul_le_mul_of_nonneg_right hK₁ (norm_nonneg _))
  have hBu : ‖B u‖ ≤ K * Burnett.Analysis.SymmetricEnergy.firstOrderEnergy D u := by
    rw [hEA]
    exact (hB f).trans (mul_le_mul_of_nonneg_right hK₀ (norm_nonneg _))
  have hEnergy := principal_energy_bound D R dR B compactMatrixDerivative_isSkew
    (compactActualFourierOp_isSymmetric haM (diagonalOrderOneSymbol_symmetric hSym)) hR
    (fun b d => compactFiniteMultiplier_leibniz (r b d) (hr b d) b)
    u A K hA hK hRNorm hdRNorm hRB' hDB' hBu
  change |2 * (⟪compactTransportOp (compactActualFourierOp haM) (compactMatrixTestEquiv ι f),
      principal compactMatrixCoordinatePartial
        (fun b d => compactTransportOp (compactFiniteMultiplier (r b d) (hr b d)))
        (compactMatrixTestEquiv ι f)⟫_ℂ).im| ≤ _ at hEnergy
  rw [compactFinitePrincipal_inner haM r hr f, hEA] at hEnergy
  simp only [diagonalOrderOneSymbol_action, Fintype.card_fin, Nat.cast_ofNat,
    show (5*(4:ℝ)^2) = (80:ℝ) by norm_num, A, A₀] at hEnergy
  simpa only [mul_assoc] using hEnergy

end Burnett.Analysis.CarlesonEmbedding
