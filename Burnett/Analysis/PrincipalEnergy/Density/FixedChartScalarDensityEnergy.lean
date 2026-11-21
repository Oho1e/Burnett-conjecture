import Burnett.Analysis.PrincipalEnergy.Density.FixedChartWeightedLocalAction
import Burnett.Analysis.PrincipalEnergy.Density.FixedCompactFourierBounds
import Burnett.Analysis.PrincipalEnergy.Density.CompactCutoffCommutator
import Burnett.Analysis.PrincipalEnergy.Energy.ActualScalarPrincipalEnergy

set_option autoImplicit false
set_option maxHeartbeats 5200000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection firstOrderEnergy Op principal principal_energy_bound)
open scoped BigOperators ComplexConjugate InnerProductSpace ContDiff NNReal

theorem compactCutoffFourier_isSymmetric_of_symbol {ι : Type*} [Fintype ι]
    {a c : ι → ι → Space → Space → ℂ} (ha : GlobalMatrixSymbolData a)
    (p q : SchwartzMap Space ℂ) (hSym : MatrixFirstOrderFormalSymmetry c)
    (hAct : ∀ (f : ι → SchwartzMap Space ℂ) i x, matrixFirstOrderAction c f i x =
      p x * matrixFirstOrderAction a (fun j => scalarSchwartzProduct q (f j)) i x) :
    (compactSchwartzMultiplier p * compactTransportOp (compactActualFourierOp ha) *
      compactSchwartzMultiplier q).IsSymmetric := by
  rw [← compactCutoffActualFourier_transport]
  intro u v
  obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective u
  obtain ⟨g, rfl⟩ := (compactMatrixTestEquiv ι).surjective v
  simp only [compactTransportOp_apply, compactMatrixTestEquiv_inner, compactCutoffActualFourier_apply, ← hAct]
  exact (hSym g.val f.val).symm

private theorem compactScalarPrincipalField_zero_of_offSupport {ι : Type*} [Fintype ι]
    (r : Fin 4 → Fin 4 → Space → ℂ) (f : CompactSchwartzComponents ι) {K : Set Space}
    (hf : ∀ i, tsupport (f.val i : Space → ℂ) ⊆ K) (i : ι) (x : Space) (hx : x ∉ K) :
    compactScalarPrincipalField r f i x = 0 := by
  unfold compactScalarPrincipalField
  apply Finset.sum_eq_zero
  intro b _
  refine Finset.sum_eq_zero fun d _ => ?_
  suffices hz : (SchwartzMap.pderivCLM ℂ (coordinateDirection b)
        (SchwartzMap.pderivCLM ℂ (coordinateDirection d) (f.val i))) x = 0 by rw [hz, mul_zero]
  by_contra hn
  exact hx (hf i ((coordinateSchwartzDerivative_support_subset (f.val i) d)
    ((coordinateSchwartzDerivative_support_subset
      (SchwartzMap.pderivCLM ℂ (coordinateDirection d) (f.val i)) b) (subset_closure hn))))

private theorem compactCutoffScalarPrincipal_inner {ι : Type*} [Fintype ι]
    {a c : ι → ι → Space → Space → ℂ} (ha : GlobalMatrixSymbolData a) (p q : SchwartzMap Space ℂ)
    (hAct : ∀ (f : ι → SchwartzMap Space ℂ) i x, matrixFirstOrderAction c f i x =
      p x * matrixFirstOrderAction a (fun j => scalarSchwartzProduct q (f j)) i x)
    (r : Fin 4 → Fin 4 → Space → ℂ) (hr : ∀ b d, ContDiff ℝ ∞ (r b d)) (f : CompactSchwartzComponents ι) :
    ⟪((compactSchwartzMultiplier (ι := ι) p * compactTransportOp (compactActualFourierOp ha) *
       compactSchwartzMultiplier (ι := ι) q) : Op (CompactMatrixTest ι)) (compactMatrixTestEquiv ι f),
       principal compactMatrixCoordinatePartial
         (fun b d => compactTransportOp (compactScalarMultiplier (r b d) (hr b d)))
         (compactMatrixTestEquiv ι f)⟫_ℂ =
      ∑ i, ∫ x, conj (matrixFirstOrderAction c f.val i x) * compactScalarPrincipalField r f i x := by
  let P : CompactSchwartzComponents ι :=
    ∑ b, ∑ d, compactScalarMultiplier (r b d) (hr b d)
      (compactComponentDerivative b (compactComponentDerivative d f))
  have hP : principal compactMatrixCoordinatePartial
        (fun b d => compactTransportOp (compactScalarMultiplier (r b d) (hr b d)))
        (compactMatrixTestEquiv ι f) = compactMatrixTestEquiv ι P := by
    simp only [SymmetricEnergy.principal, LinearMap.sum_apply, Module.End.mul_apply, compactMatrixCoordinatePartial,
      compactTransportOp_apply, P, map_sum]
  rw [hP, ← compactCutoffActualFourier_transport, compactTransportOp_apply, compactMatrixTestEquiv_inner]
  refine Finset.sum_congr rfl fun i _ => integral_congr_ae ?_
  filter_upwards with x
  rw [compactCutoffActualFourier_apply, ← hAct]
  congr 1

/-- The actual weighted scalar-coefficient principal energy estimate on the
fixed chart of the manuscript with nested smooth cutoffs. -/
theorem exists_actual_fixedChartDensity_scalarCoefficient_principal_energy_bound
    {ι : Type*} [Fintype ι] {a : ι → ι → Space → Space → ℂ}
    (ha : GlobalMatrixSymbolData a) (hda : GlobalMatrixDerivativeSymbolData a)
    {Ω W K : Set Space} (hΩ : IsOpen Ω) (hKW : K ⊆ W)
    (ρ θ : Space → ℝ) (hρ : ContDiffOn ℝ ∞ ρ Ω) (hpos : ∀ x ∈ Ω, 0 < ρ x)
    (hθ : ContDiff ℝ ∞ θ) (hθrange : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1) (hθcomp : HasCompactSupport θ)
    (hθsupport : tsupport θ ⊆ Ω) (hθone : ∀ x ∈ W, θ x = 1)
    (ψ : SchwartzMap Space ℂ) (hψ : HasCompactSupport (ψ : Space → ℂ))
    (hψs : tsupport (ψ : Space → ℂ) ⊆ W) (hψr : ∀ x, conj (ψ x) = ψ x)
    (hψone : ∀ x ∈ K, ψ x = 1) (hSym : ChartDensityMatrixFormalSymmetry W ρ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin 4 → Fin 4 → Space → ℂ)
      (_hr : ∀ b d, ContDiff ℝ ∞ (r b d)) (L : NNReal) (U : ℝ),
      0 ≤ U →
      (∀ b d x, conj (r b d x) = r b d x) →
      (∀ b d x, r b d x = r d b x) →
      (∀ b d, ∀ᵐ x ∂(volume : Measure Space), ‖r b d x‖ ≤ U) →
      (∀ b d, ∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r b d) x‖ ≤ (L : ℝ)) →
      ∀ f : CompactSchwartzComponents ι, (∀ i, tsupport (f.val i : Space → ℂ) ⊆ K) →
        |2 * (∑ i, ∫ x, (ρ x : ℂ) * (conj (matrixFirstOrderAction a f.val i x) *
          compactScalarPrincipalField r f i x)).im| ≤ C*(U+(L:ℝ))*(compactMatrixCoordinateH1 f)^2 := by
  obtain ⟨q, hq, _, _, hEq, hOff, _⟩ := exists_fixedChart_densitySqrt_extension hΩ ρ θ hρ hpos hθ hθrange
    hθcomp hθsupport hθone
  let p := fixedChartWeightedLeftPlateau q hq ψ hψ
  let c (i j : ι) := fixedChartDensityConjugateSymbol (a i j) q ψ
  have hAct (f : ι → SchwartzMap Space ℂ) (i : ι) (x : Space) :
      matrixFirstOrderAction c f i x = p x * matrixFirstOrderAction a (fun j => scalarSchwartzProduct ψ (f j)) i x :=
    matrixFirstOrderAction_fixedChartWeightedLocalSymbol (fun i j => (ha.frequency i j).frequency) q hq ψ hψ f i x
  have hSymC : MatrixFirstOrderFormalSymmetry c := fixedChartWeightedLocalSymbol_formalSymmetry
    (fun i j => (ha.frequency i j).frequency) hSym q hq hEq ψ hψ hψs hψr
  have hqJets := fixedChart_densitySquare_complex_jet_bounds hθcomp q hq hOff
  have hProfile (i j : ι) := fixedChartDensityConjugateSymbol_compactProfile
    (ha.frequency i j) (ha.smooth i j) (ha.pureBase i j) q hq hqJets ψ hψ
  obtain ⟨M₀, hM₀, hOp⟩ := exists_compactCutoffFourier_energy_bounds ha hda p ψ
  obtain ⟨M₁, hM₁, hComm⟩ := exists_compactCutoffFourier_scalar_commutator_bound ha p ψ
    (fixedChartWeightedLeftPlateau_compact q hq ψ hψ) hψ hProfile hSymC hAct
  let M := M₀+M₁
  have hM : 0 ≤ M := add_nonneg hM₀ hM₁
  have hM₀' : M₀ ≤ M := le_add_of_nonneg_right hM₁
  have hM₁' : M₁ ≤ M := le_add_of_nonneg_left hM₀
  refine ⟨80*M, mul_nonneg (by norm_num) hM, fun r hr L U hU hReal hRswap hVal hDer f hf => ?_⟩
  let D : Fin 4 → Op (CompactMatrixTest ι) := compactMatrixCoordinatePartial
  let C : Op (CompactMatrixTest ι) :=
    compactSchwartzMultiplier p * compactTransportOp (compactActualFourierOp ha) * compactSchwartzMultiplier ψ
  let R (b d : Fin 4) : Op (CompactMatrixTest ι) :=
    compactTransportOp (compactScalarMultiplier (r b d) (hr b d))
  let dR (b d : Fin 4) : Op (CompactMatrixTest ι) :=
    compactTransportOp (compactScalarMultiplier (scalarCoordinateDerivative (r b d) b)
      (scalarCoordinateDerivative_smooth (hr b d) b))
  let u := compactMatrixTestEquiv ι f
  let A := U+(L:ℝ)
  have hA : 0 ≤ A := add_nonneg hU L.coe_nonneg
  have hE := compactMatrixFirstOrderEnergy_eq f
  have hNorm (b d : Fin 4) := smoothCoefficient_bounds_of_ae_norm_firstDerivative (r b d)
    ((hr b d).of_le (by simp)) U L (hVal b d) (hDer b d)
  have hR (b d : Fin 4) (v w : CompactMatrixTest ι) : ⟪R b d v, w⟫_ℂ = ⟪v, R d b w⟫_ℂ :=
    compactScalarMultiplier_adjoints (r b d) (r d b) (hr b d) (hr d b)
      (fun x => (hReal b d x).trans (hRswap b d x)) v w
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
  have hRC (b d : Fin 4) (v : CompactMatrixTest ι) : ‖SymmetricEnergy.comm (R b d) C v‖ ≤ M*A*‖v‖ :=
    (hComm (r b d) (hr b d) L U (hReal b d) (hVal b d) (hDer b d) v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM₁' hA) (norm_nonneg _))
  have hDC (b : Fin 4) : ‖SymmetricEnergy.comm (D b) C u‖ ≤ M*firstOrderEnergy D u :=
    ((hOp u).2 b).trans (mul_le_mul_of_nonneg_right hM₀' (Real.sqrt_nonneg _))
  have hCu : ‖C u‖ ≤ M*firstOrderEnergy D u :=
    (hOp u).1.trans (mul_le_mul_of_nonneg_right hM₀' (Real.sqrt_nonneg _))
  have hEnergy := principal_energy_bound D R dR C compactMatrixDerivative_isSkew
    (compactCutoffFourier_isSymmetric_of_symbol ha p ψ hSymC hAct) hR
    (fun b d => compactScalarMultiplier_leibniz (ι := ι) (r b d) (hr b d) b)
    u A M hA hM hRNorm hdRNorm hRC hDC hCu
  change |2 * (⟪C (compactMatrixTestEquiv ι f),
      principal compactMatrixCoordinatePartial
        (fun b d => compactTransportOp (compactScalarMultiplier (r b d) (hr b d)))
        (compactMatrixTestEquiv ι f)⟫_ℂ).im| ≤ _ at hEnergy
  rw [compactCutoffScalarPrincipal_inner ha p ψ hAct r hr f, hE] at hEnergy
  have hWeighted := fixedChartDensity_weightedPairing_eq_lebesgueLocalizedAction
    (fun i j => (ha.frequency i j).frequency) ρ q (fun x hx => hEq (hKW hx))
    ψ hψone f.val hf (compactScalarPrincipalField r f) (compactScalarPrincipalField_zero_of_offSupport r f hf)
  change _ = ∑ i, ∫ x, conj (matrixFirstOrderAction c f.val i x) * compactScalarPrincipalField r f i x at hWeighted
  rw [← hWeighted] at hEnergy
  simpa only [Fintype.card_fin, Nat.cast_ofNat, show (5*(4:ℝ)^2) = (80:ℝ) by norm_num] using hEnergy

end Burnett.Analysis.CarlesonEmbedding
