import Burnett.Analysis.PrincipalEnergy.Energy.CompactFourierNorms
import Burnett.Analysis.PrincipalEnergy.Energy.CompactScalarMultiplier

set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection Op comm principal principal_energy_bound)
open scoped BigOperators ComplexConjugate InnerProductSpace ContDiff NNReal

theorem exists_compactScalarMultiplier_comm_bound
    {ι : Type*} [Fintype ι] {a : ι → ι → Space → Space → ℂ}
    (ha : GlobalMatrixSymbolData a) (hSym : MatrixFirstOrderFormalSymmetry a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Space → ℂ) (hr : ContDiff ℝ ∞ r) (L : NNReal) (U : ℝ),
      (∀ x, conj (r x) = r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ r x‖ ≤ (L : ℝ)) →
      ∀ v : CompactMatrixTest ι,
        ‖comm (compactTransportOp (compactScalarMultiplier r hr))
          (compactTransportOp (compactActualFourierOp ha)) v‖ ≤ C * (U+(L:ℝ)) * ‖v‖ := by
  obtain ⟨C, hC, bound⟩ := exists_smoothMatrixCoefficientCommutator_global_L2_bound
    ha.frequency ha.smooth ha.pureBase hSym ha.proper
  refine ⟨C, hC, fun r hr L U hReal hVal hDer v => ?_⟩
  obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective v
  let R := compactScalarMultiplier (ι := ι) r hr
  let B := compactActualFourierOp ha
  let W := R (B f) - B (R f)
  have hEq : comm (compactTransportOp R) (compactTransportOp B) (compactMatrixTestEquiv ι f) =
      compactMatrixTestEquiv ι W := by
    simp only [SymmetricEnergy.comm, LinearMap.sub_apply, Module.End.mul_apply, compactTransportOp_apply, W, map_sub]
  obtain ⟨hM, hBound⟩ := bound r hr L U hReal hVal hDer f.val f.property
  have hL2 (i : ι) : (W.val i).toLp 2 volume =
      (hM i).toLp (smoothMatrixCoefficientCommutator a r hr f.val f.property i) := by
    apply Lp.ext
    filter_upwards [(W.val i).coeFn_toLp 2 volume, (hM i).coeFn_toLp] with x hx hy
    rw [hx, hy]
    rfl
  rw [hEq, compactMatrixTestEquiv_norm, compactMatrixTestEquiv_norm]
  unfold matrixSchwartzL2Norm
  simp only [hL2]
  exact hBound

def compactScalarPrincipalField {ι : Type*} [Fintype ι]
    (r : Fin 4 → Fin 4 → Space → ℂ) (f : CompactSchwartzComponents ι) (i : ι) (x : Space) : ℂ :=
  ∑ b, ∑ d, r b d x *
    (SchwartzMap.pderivCLM ℂ (coordinateDirection b)
      (SchwartzMap.pderivCLM ℂ (coordinateDirection d) (f.val i))) x

private theorem compactScalarPrincipal_inner {ι : Type*} [Fintype ι] {a : ι → ι → Space → Space → ℂ}
    (ha : GlobalMatrixSymbolData a) (r : Fin 4 → Fin 4 → Space → ℂ)
    (hr : ∀ b d, ContDiff ℝ ∞ (r b d)) (f : CompactSchwartzComponents ι) :
    ⟪compactTransportOp (compactActualFourierOp ha) (compactMatrixTestEquiv ι f),
       principal compactMatrixCoordinatePartial
         (fun b d => compactTransportOp (compactScalarMultiplier (r b d) (hr b d)))
         (compactMatrixTestEquiv ι f)⟫_ℂ =
      ∑ i, ∫ x, conj (matrixFirstOrderAction a f.val i x) * compactScalarPrincipalField r f i x := by
  let P : CompactSchwartzComponents ι :=
    ∑ b, ∑ d, compactScalarMultiplier (r b d) (hr b d)
      (compactComponentDerivative b (compactComponentDerivative d f))
  have hP : principal compactMatrixCoordinatePartial
        (fun b d => compactTransportOp (compactScalarMultiplier (r b d) (hr b d)))
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

/-- The original Lebesgue principal energy estimate for real scalar
coefficients in the field indices and the actual fixed matrix Fourier action. -/
theorem exists_actual_scalarCoefficient_principal_energy_bound
    {ι : Type*} [Fintype ι] {a : ι → ι → Space → Space → ℂ}
    (ha : GlobalMatrixSymbolData a) (hda : GlobalMatrixDerivativeSymbolData a)
    (hSym : MatrixFirstOrderFormalSymmetry a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin 4 → Fin 4 → Space → ℂ)
      (_hr : ∀ b d, ContDiff ℝ ∞ (r b d)) (L : NNReal) (U : ℝ),
      0 ≤ U →
      (∀ b d x, conj (r b d x) = r b d x) →
      (∀ b d x, r b d x = r d b x) →
      (∀ b d, ∀ᵐ x ∂(volume : Measure Space), ‖r b d x‖ ≤ U) →
      (∀ b d, ∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r b d) x‖ ≤ (L : ℝ)) →
      ∀ f : CompactSchwartzComponents ι,
        |2 * (∑ i, ∫ x, conj (matrixFirstOrderAction a f.val i x) *
          compactScalarPrincipalField r f i x).im| ≤ C * (U+(L:ℝ)) * (compactMatrixCoordinateH1 f)^2 := by
  obtain ⟨C₀, hC₀, hB⟩ := exists_compactActualFourierOp_h1_bound ha
  obtain ⟨C₁, hC₁, hDB⟩ := exists_compactActualFourierOp_coordinate_comm_bound ha hda
  obtain ⟨C₂, hC₂, hRB⟩ := exists_compactScalarMultiplier_comm_bound ha hSym
  let K := C₀+C₁+C₂
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hK₀ : C₀ ≤ K := by dsimp [K]; linarith
  have hK₁ : C₁ ≤ K := by dsimp [K]; linarith
  have hK₂ : C₂ ≤ K := by dsimp [K]; linarith
  refine ⟨80*K, by positivity, fun r hr L U hU hReal hsk hVal hDer f => ?_⟩
  let D : Fin 4 → Op (CompactMatrixTest ι) := compactMatrixCoordinatePartial
  let B := compactTransportOp (compactActualFourierOp ha)
  let R (b d : Fin 4) : Op (CompactMatrixTest ι) :=
    compactTransportOp (compactScalarMultiplier (r b d) (hr b d))
  let dR (b d : Fin 4) : Op (CompactMatrixTest ι) :=
    compactTransportOp (compactScalarMultiplier (scalarCoordinateDerivative (r b d) b)
      (scalarCoordinateDerivative_smooth (hr b d) b))
  let u := compactMatrixTestEquiv ι f
  let A := U+(L:ℝ)
  have hA : 0 ≤ A := add_nonneg hU L.coe_nonneg
  have hEA : Burnett.Analysis.SymmetricEnergy.firstOrderEnergy D u = compactMatrixCoordinateH1 f :=
    compactMatrixFirstOrderEnergy_eq f
  have hNorm (b d : Fin 4) := smoothCoefficient_bounds_of_ae_norm_firstDerivative (r b d)
    ((hr b d).of_le (by simp)) U L (hVal b d) (hDer b d)
  have hR (b d : Fin 4) (v w : CompactMatrixTest ι) : ⟪R b d v, w⟫_ℂ = ⟪v, R d b w⟫_ℂ :=
    compactScalarMultiplier_adjoints (r b d) (r d b) (hr b d) (hr d b)
      (fun x => (hReal b d x).trans (hsk b d x)) v w
  have hRNorm (b d : Fin 4) (v : CompactMatrixTest ι) : ‖R b d v‖ ≤ A*‖v‖ :=
    compactScalarMultiplier_norm_le (r b d) (hr b d) A hA
      (fun x => ((hNorm b d).2.1 x).trans (le_add_of_nonneg_right L.coe_nonneg)) v
  have hdRNorm (b d : Fin 4) (v : CompactMatrixTest ι) : ‖dR b d v‖ ≤ A*‖v‖ := by
    refine compactScalarMultiplier_norm_le _ _ A hA (fun x => ?_) v
    have he : ‖coordinateDirection b‖ = 1 := by
      simp only [coordinateDirection, EuclideanSpace.norm_single, norm_one]
    have hL : ‖fderiv ℝ (r b d) x‖ ≤ (L:ℝ) := norm_fderiv_le_of_lipschitz ℝ (hNorm b d).2.2
    exact ((ContinuousLinearMap.le_opNorm (fderiv ℝ (r b d) x) (coordinateDirection b)).trans
      (by rw [he, mul_one]; exact hL)).trans (le_add_of_nonneg_left hU)
  have hRB' (b d : Fin 4) (v : CompactMatrixTest ι) : ‖comm (R b d) B v‖ ≤ K*A*‖v‖ :=
    (hRB (r b d) (hr b d) L U (hReal b d) (hVal b d) (hDer b d) v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK₂ hA) (norm_nonneg _))
  have hDB' (b : Fin 4) : ‖comm (D b) B u‖ ≤ K * Burnett.Analysis.SymmetricEnergy.firstOrderEnergy D u := by
    rw [hEA]
    exact (hDB b f).trans (mul_le_mul_of_nonneg_right hK₁ (norm_nonneg _))
  have hBu : ‖B u‖ ≤ K * Burnett.Analysis.SymmetricEnergy.firstOrderEnergy D u := by
    rw [hEA]
    exact (hB f).trans (mul_le_mul_of_nonneg_right hK₀ (norm_nonneg _))
  have hEnergy := principal_energy_bound D R dR B compactMatrixDerivative_isSkew
    (compactActualFourierOp_isSymmetric ha hSym) hR
    (fun b d => compactScalarMultiplier_leibniz (ι := ι) (r b d) (hr b d) b)
    u A K hA hK hRNorm hdRNorm hRB' hDB' hBu
  change |2 * (⟪compactTransportOp (compactActualFourierOp ha) (compactMatrixTestEquiv ι f),
      principal compactMatrixCoordinatePartial
        (fun b d => compactTransportOp (compactScalarMultiplier (r b d) (hr b d)))
        (compactMatrixTestEquiv ι f)⟫_ℂ).im| ≤ _ at hEnergy
  rw [compactScalarPrincipal_inner ha r hr f, hEA] at hEnergy
  simpa only [Fintype.card_fin, Nat.cast_ofNat, show (5*(4:ℝ)^2) = (80:ℝ) by norm_num] using hEnergy

end Burnett.Analysis.CarlesonEmbedding
