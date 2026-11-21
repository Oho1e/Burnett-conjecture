import Burnett.Analysis.PrincipalEnergy.Density.FixedChartScalarDensityEnergy
import Burnett.Analysis.PrincipalEnergy.Density.CompactCutoffFiniteCommutator
import Burnett.Analysis.PrincipalEnergy.Energy.ActualMatrixPrincipalEnergy

set_option autoImplicit false
set_option maxHeartbeats 5200000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection firstOrderEnergy Op principal principal_energy_bound)
open scoped BigOperators ComplexConjugate InnerProductSpace ContDiff NNReal

def ChartDensityScalarFormalSymmetry (W : Set Space) (ρ : Space → ℝ) (a : Space → Space → ℂ) : Prop :=
  ∀ f g : SchwartzMap Space ℂ, HasCompactSupport (f : Space → ℂ) → HasCompactSupport (g : Space → ℂ) →
    tsupport (f : Space → ℂ) ⊆ W → tsupport (g : Space → ℂ) ⊆ W →
    (∫ x, (ρ x : ℂ)*(conj (g x)*firstOrderAction a f x)) =
      ∫ x, (ρ x : ℂ)*(conj (firstOrderAction a g x)*f x)

theorem chartDensityFormalSymmetry_diagonalOrderOneSymbol {ι : Type*} [Fintype ι]
    {W : Set Space} {ρ : Space → ℝ} {a : Space → Space → ℂ}
    (hSym : ChartDensityScalarFormalSymmetry W ρ a) :
    ChartDensityMatrixFormalSymmetry W ρ (diagonalOrderOneSymbol (ι := ι) a) := by
  intro f g hf hg hF hG
  simp only [diagonalOrderOneSymbol_action]
  exact Finset.sum_congr rfl fun i _ => hSym (f i) (g i) (hf i) (hg i) (hF i) (hG i)

private theorem compactFinitePrincipalField_zero_of_offSupport {ι : Type*} [Fintype ι]
    (r : Fin 4 → Fin 4 → ι → ι → Space → ℂ) (f : CompactSchwartzComponents ι) {K : Set Space}
    (hf : ∀ i, tsupport (f.val i : Space → ℂ) ⊆ K) (i : ι) (x : Space) (hx : x ∉ K) :
    compactFinitePrincipalField r f i x = 0 := by
  unfold compactFinitePrincipalField
  apply Finset.sum_eq_zero
  intro b _
  apply Finset.sum_eq_zero
  intro d _
  refine Finset.sum_eq_zero fun j _ => ?_
  suffices hz : (SchwartzMap.pderivCLM ℂ (coordinateDirection b)
        (SchwartzMap.pderivCLM ℂ (coordinateDirection d) (f.val j))) x = 0 by rw [hz, mul_zero]
  by_contra hn
  exact hx (hf j ((coordinateSchwartzDerivative_support_subset (f.val j) d)
    ((coordinateSchwartzDerivative_support_subset
      (SchwartzMap.pderivCLM ℂ (coordinateDirection d) (f.val j)) b) (subset_closure hn))))

private theorem compactCutoffFinitePrincipal_inner {ι : Type*} [Fintype ι]
    {a c : ι → ι → Space → Space → ℂ} (ha : GlobalMatrixSymbolData a) (p q : SchwartzMap Space ℂ)
    (hAct : ∀ (f : ι → SchwartzMap Space ℂ) i x, matrixFirstOrderAction c f i x =
      p x * matrixFirstOrderAction a (fun j => scalarSchwartzProduct q (f j)) i x)
    (r : Fin 4 → Fin 4 → ι → ι → Space → ℂ) (hr : ∀ b d i j, ContDiff ℝ ∞ (r b d i j))
    (f : CompactSchwartzComponents ι) :
    ⟪((compactSchwartzMultiplier (ι := ι) p * compactTransportOp (compactActualFourierOp ha) *
       compactSchwartzMultiplier (ι := ι) q) : Op (CompactMatrixTest ι)) (compactMatrixTestEquiv ι f),
       principal compactMatrixCoordinatePartial
         (fun b d => compactTransportOp (compactFiniteMultiplier (r b d) (hr b d)))
         (compactMatrixTestEquiv ι f)⟫_ℂ =
      ∑ i, ∫ x, conj (matrixFirstOrderAction c f.val i x) * compactFinitePrincipalField r f i x := by
  let P : CompactSchwartzComponents ι :=
    ∑ b, ∑ d, compactFiniteMultiplier (r b d) (hr b d)
      (compactComponentDerivative b (compactComponentDerivative d f))
  have hP : principal compactMatrixCoordinatePartial
        (fun b d => compactTransportOp (compactFiniteMultiplier (r b d) (hr b d)))
        (compactMatrixTestEquiv ι f) = compactMatrixTestEquiv ι P := by
    simp only [SymmetricEnergy.principal, LinearMap.sum_apply, Module.End.mul_apply, compactMatrixCoordinatePartial,
      compactTransportOp_apply, P, map_sum]
  rw [hP, ← compactCutoffActualFourier_transport, compactTransportOp_apply, compactMatrixTestEquiv_inner]
  refine Finset.sum_congr rfl fun i _ => integral_congr_ae ?_
  filter_upwards with x
  rw [compactCutoffActualFourier_apply, ← hAct]
  congr 1
  change SchwartzMap.delta ℂ ℂ x
    (LinearMap.proj (R := ℂ) i ((compactSchwartzComponents ι).subtype P)) = _
  simp only [P, map_sum, LinearMap.proj_apply, Submodule.subtype_apply, SchwartzMap.delta_apply,
    compactFiniteMultiplier_apply, compactFinitePrincipalField]
  rfl

/-- The weighted finite matrix extension on the same fixed chart and
cutoffs, using scalarity of the full original Fourier symbol. -/
theorem exists_actual_fixedChartDensity_matrixCoefficient_principal_energy_bound
    {ι : Type*} [Fintype ι] {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hs : ContDiff ℝ ∞ (uncurry a))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hda : ∀ b : Fin 4, FirstBaseFrequencyOrderOne (baseDirectionSymbol a (coordinateDirection b)))
    (hdb : ∀ (b : Fin 4) (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => baseDirectionSymbol a (coordinateDirection b) y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hp : ProperKernelRelation (firstOrderKernelRelation a))
    {Ω W K : Set Space} (hΩ : IsOpen Ω) (hKW : K ⊆ W)
    (ρ θ : Space → ℝ) (hρ : ContDiffOn ℝ ∞ ρ Ω) (hpos : ∀ x ∈ Ω, 0 < ρ x)
    (hθ : ContDiff ℝ ∞ θ) (hθrange : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1) (hθcomp : HasCompactSupport θ)
    (hθsupport : tsupport θ ⊆ Ω) (hθone : ∀ x ∈ W, θ x = 1)
    (ψ : SchwartzMap Space ℂ) (hψ : HasCompactSupport (ψ : Space → ℂ))
    (hψs : tsupport (ψ : Space → ℂ) ⊆ W) (hψr : ∀ x, conj (ψ x) = ψ x)
    (hψone : ∀ x ∈ K, ψ x = 1) (hSym : ChartDensityScalarFormalSymmetry W ρ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin 4 → Fin 4 → ι → ι → Space → ℂ)
      (_hr : ∀ b d i j, ContDiff ℝ ∞ (r b d i j)) (L : NNReal) (U : ℝ),
      0 ≤ U →
      (∀ b d i j x, conj (r b d i j x) = r d b j i x) →
      (∀ b d i j, ∀ᵐ x ∂(volume : Measure Space), ‖r b d i j x‖ ≤ U) →
      (∀ b d i j, ∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r b d i j) x‖ ≤ (L : ℝ)) →
      ∀ f : CompactSchwartzComponents ι, (∀ i, tsupport (f.val i : Space → ℂ) ⊆ K) →
        |2 * (∑ i, ∫ x, (ρ x : ℂ) * (conj (firstOrderAction a (f.val i) x) *
          compactFinitePrincipalField r f i x)).im| ≤ C*(U+(L:ℝ))*(compactMatrixCoordinateH1 f)^2 := by
  let aM := diagonalOrderOneSymbol (ι := ι) a
  let haM := diagonalOrderOneSymbol_data (ι := ι) ha hs hb hp
  let hdaM := diagonalOrderOneSymbol_derivativeData (ι := ι) hda hdb
  obtain ⟨q, hq, _, _, hEq, hOff, _⟩ := exists_fixedChart_densitySqrt_extension hΩ ρ θ hρ hpos hθ hθrange
    hθcomp hθsupport hθone
  let p := fixedChartWeightedLeftPlateau q hq ψ hψ
  let c (i j : ι) := fixedChartDensityConjugateSymbol (aM i j) q ψ
  have hAct (f : ι → SchwartzMap Space ℂ) (i : ι) (x : Space) :
      matrixFirstOrderAction c f i x = p x * matrixFirstOrderAction aM (fun j => scalarSchwartzProduct ψ (f j)) i x :=
    matrixFirstOrderAction_fixedChartWeightedLocalSymbol (fun i j => (haM.frequency i j).frequency) q hq ψ hψ f i x
  have hSymC : MatrixFirstOrderFormalSymmetry c := fixedChartWeightedLocalSymbol_formalSymmetry
    (fun i j => (haM.frequency i j).frequency) (chartDensityFormalSymmetry_diagonalOrderOneSymbol hSym) q hq hEq ψ hψ hψs hψr
  have hqJets := fixedChart_densitySquare_complex_jet_bounds hθcomp q hq hOff
  have hProfile (i j : ι) := fixedChartDensityConjugateSymbol_compactProfile
    (haM.frequency i j) (haM.smooth i j) (haM.pureBase i j) q hq hqJets ψ hψ
  obtain ⟨M₀, hM₀, hOp⟩ := exists_compactCutoffFourier_energy_bounds haM hdaM p ψ
  obtain ⟨K₀, hK₀, hComm₀⟩ := exists_compactCutoffFourier_scalar_commutator_bound haM p ψ
    (fixedChartWeightedLeftPlateau_compact q hq ψ hψ) hψ hProfile hSymC hAct
  let n := (Fintype.card ι : ℝ)^2
  let m := 1+n
  let M₁ := n*(2*K₀)
  have hM₁ : 0 ≤ M₁ := mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) hK₀)
  let M := M₀+M₁
  have hM : 0 ≤ M := add_nonneg hM₀ hM₁
  have hM₀' : M₀ ≤ M := le_add_of_nonneg_right hM₁
  have hM₁' : M₁ ≤ M := le_add_of_nonneg_left hM₀
  have hm : 0 ≤ m := add_nonneg zero_le_one (sq_nonneg _)
  refine ⟨80*M*m, mul_nonneg (mul_nonneg (by norm_num) hM) hm,
    fun r hr L U hU hHerm hVal hDer f hf => ?_⟩
  let D : Fin 4 → Op (CompactMatrixTest ι) := compactMatrixCoordinatePartial
  let C : Op (CompactMatrixTest ι) :=
    compactSchwartzMultiplier p * compactTransportOp (compactActualFourierOp haM) * compactSchwartzMultiplier ψ
  let R (b d : Fin 4) : Op (CompactMatrixTest ι) := compactTransportOp (compactFiniteMultiplier (r b d) (hr b d))
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
  have hE := compactMatrixFirstOrderEnergy_eq f
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
    have he : ‖coordinateDirection b‖ = 1 := by simp only [coordinateDirection, EuclideanSpace.norm_single, norm_one]
    have hL : ‖fderiv ℝ (r b d i j) x‖ ≤ (L:ℝ) := norm_fderiv_le_of_lipschitz ℝ (hNorm b d i j).2.2
    exact ((ContinuousLinearMap.le_opNorm (fderiv ℝ (r b d i j) x) (coordinateDirection b)).trans
      (by rw [he, mul_one]; exact hL)).trans (le_add_of_nonneg_left hU)
  have hComm := compactFiniteCutoff_commutator_bound haM p ψ K₀ hComm₀
  have hRC (b d : Fin 4) (v : CompactMatrixTest ι) : ‖SymmetricEnergy.comm (R b d) C v‖ ≤ M*A*‖v‖ :=
    (hComm (r b d) (hr b d) L U (hVal b d) (hDer b d) v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul hM₁' hAup hA₀ hM) (norm_nonneg _))
  have hDC (b : Fin 4) : ‖SymmetricEnergy.comm (D b) C u‖ ≤ M*firstOrderEnergy D u :=
    ((hOp u).2 b).trans (mul_le_mul_of_nonneg_right hM₀' (Real.sqrt_nonneg _))
  have hCu : ‖C u‖ ≤ M*firstOrderEnergy D u :=
    (hOp u).1.trans (mul_le_mul_of_nonneg_right hM₀' (Real.sqrt_nonneg _))
  have hEnergy := principal_energy_bound D R dR C compactMatrixDerivative_isSkew
    (compactCutoffFourier_isSymmetric_of_symbol haM p ψ hSymC hAct) hR
    (fun b d => compactFiniteMultiplier_leibniz (r b d) (hr b d) b)
    u A M hA hM hRNorm hdRNorm hRC hDC hCu
  change |2 * (⟪C (compactMatrixTestEquiv ι f),
      principal compactMatrixCoordinatePartial
        (fun b d => compactTransportOp (compactFiniteMultiplier (r b d) (hr b d)))
        (compactMatrixTestEquiv ι f)⟫_ℂ).im| ≤ _ at hEnergy
  rw [compactCutoffFinitePrincipal_inner haM p ψ hAct r hr f, hE] at hEnergy
  have hWeighted := fixedChartDensity_weightedPairing_eq_lebesgueLocalizedAction
    (fun i j => (haM.frequency i j).frequency) ρ q (fun x hx => hEq (hKW hx))
    ψ hψone f.val hf (compactFinitePrincipalField r f) (compactFinitePrincipalField_zero_of_offSupport r f hf)
  change _ = ∑ i, ∫ x, conj (matrixFirstOrderAction c f.val i x) * compactFinitePrincipalField r f i x at hWeighted
  rw [← hWeighted] at hEnergy
  simpa only [aM, diagonalOrderOneSymbol_action, Fintype.card_fin, Nat.cast_ofNat,
    show (5*(4:ℝ)^2) = (80:ℝ) by norm_num, A, A₀, mul_assoc] using hEnergy

end Burnett.Analysis.CarlesonEmbedding
