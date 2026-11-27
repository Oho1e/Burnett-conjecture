import Burnett.Analysis.CubicEnergy.AngularCorrection.CorrectionGlobalRoughOutputs

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

namespace Burnett.A08

open Filter MeasureTheory Metric Set Burnett.A06 Burnett.A07 Burnett.A02.FrequencySplit Burnett.Fourier
open scoped ComplexConjugate ContDiff ENNReal NNReal Topology

open private highDerivativeLp4Sum_le_gradient schwartzGradientNorm_nonneg
  from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalWeakDivergenceCommutator

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private abbrev Test := SchwartzMap E ℂ
private abbrev LP2 := FirstOrderLp 2

/-- The original scalar analytic correction bounds with the true high-slot
adjoint. Derivatives in the high slot are understood distributionally in
the identity tested against a Schwartz function. -/
structure OriginalAnalyticCorrectionBounds (b : Joint → ℂ) (C : ℝ) where
  forward : Test → Test → LP2
  adjoint : Test → Test → LP2
  forward_pair (H u w : Test) :
    inner ℂ (w.toLp 2 volume) (forward H u) = radianHighPair b H u w
  adjoint_pair (H u w : Test) :
    inner ℂ (w.toLp 2 volume) (adjoint H u) =
      radianHighPair (highAdjointSymbol b) (fun x => conj (H x)) u w
  adjoint_duality (H u w : Test) :
    inner ℂ (w.toLp 2 volume) (forward H u) =
      inner ℂ (adjoint H w) (u.toLp 2 volume)
  first_order (H u : Test) :
    ‖forward H u‖ ≤ C * ‖H.toLp 4 volume‖ * schwartzGradientNorm 4 u ∧
    ‖adjoint H u‖ ≤ C * ‖H.toLp 4 volume‖ * schwartzGradientNorm 4 u
  coordinate_commutator (i : Fin 4) (H u w : Test) :
    (-inner ℂ ((coordinateDerivative i w).toLp 2 volume) (forward H u) -
        inner ℂ (w.toLp 2 volume) (forward H (coordinateDerivative i u)) =
      inner ℂ (w.toLp 2 volume) (forward (coordinateDerivative i H) u)) ∧
    (-inner ℂ ((coordinateDerivative i w).toLp 2 volume) (adjoint H u) -
        inner ℂ (w.toLp 2 volume) (adjoint H (coordinateDerivative i u)) =
      inner ℂ (w.toLp 2 volume) (adjoint (coordinateDerivative i H) u))
  derivative_first_order (i : Fin 4) (H u : Test) :
    ‖forward (coordinateDerivative i H) u‖ ≤
      C * ‖(coordinateDerivative i H).toLp 4 volume‖ * schwartzGradientNorm 4 u ∧
    ‖adjoint (coordinateDerivative i H) u‖ ≤
      C * ‖(coordinateDerivative i H).toLp 4 volume‖ * schwartzGradientNorm 4 u
  lipschitz_commutator (d : E → ℝ) (L : ℝ≥0) (_ : LipschitzWith L d) (H v : Test) :
    ∃ U V : LP2, ‖U‖ ≤ C * (L : ℝ) * ‖H.toLp 4 volume‖ * ‖v.toLp 4 volume‖ ∧
      ‖V‖ ≤ C * (L : ℝ) * ‖H.toLp 4 volume‖ * ‖v.toLp 4 volume‖ ∧ ∀ w : Test,
      inner ℂ (w.toLp 2 volume) U = -radianHighCommutatorPair b d H v w ∧
      inner ℂ (w.toLp 2 volume) V =
        -radianHighCommutatorPair (highAdjointSymbol b) d (fun x => conj (H x)) v w

/-- The scalar estimates of the original `lem:analytic-correction-bounds`.
The constants and the finite number of symbol derivatives are independent
of the smooth extension, the test fields and the real Lipschitz coefficient. -/
theorem exists_originalAnalyticCorrectionBounds
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1/2) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
    ∃ (K : ℕ) (C : ℝ), 27 ≤ K ∧ 0 ≤ C ∧
      ∀ {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)}, IsOpen W →
      Q ×ˢ sphere (0 : RotationSpace) 1 ⊆ W → ContDiffOn ℝ ∞ F W →
      ∀ M : ℝ, 0 ≤ M →
      (∀ n ≤ K, ∀ p ∈ Q, ∀ x : RoundSphere3, ‖iteratedFDeriv ℝ n F (p, (x : RotationSpace))‖ ≤ M) →
      Nonempty (OriginalAnalyticCorrectionBounds (originalRegularizedAngularSymbol η χ F) (C * M)) := by
  intro Q
  obtain ⟨K,C₀,C₁,hK,hC₀,hC₁,select⟩ := exists_originalAngular_hermitian_angular_cutoff
    η χ hr hρ hsmall hR hη hzero hone hχ hcut
  obtain ⟨Ccut,_,rough⟩ := exists_full_globalLipschitz_rough_outputs
  let C : ℝ := max (8*C₀) (2*C₁*(Ccut : ℝ))
  refine ⟨K,C,hK,(by positivity : 0 ≤ 8*C₀).trans (le_max_left _ _),?_⟩
  intro F W hW hQW hF M hM hjet
  obtain ⟨P⟩ := select hW hQW hF M hM hjet
  have hZ : ∀ z ∈ Q ×ˢ sphere (0 : RotationSpace) 1, ‖F z‖ ≤ M := by
    rintro ⟨p,x⟩ ⟨hp,hx⟩
    simpa only [norm_iteratedFDeriv_zero] using hjet 0 (Nat.zero_le K) p hp ⟨x,hx⟩
  obtain ⟨b,B,hB,hb,hsize,hrep⟩ := exists_borelOriginalRegularizedAngularSymbol η χ hρ
    hη.continuous hone hχ.continuous hcut hQW hF.continuousOn M hM hZ
  have orderBound (H u : Test) :
      ‖P.fullForward H u‖ ≤ C*M*‖H.toLp 4 volume‖*schwartzGradientNorm 4 u ∧
      ‖P.fullAdjoint H u‖ ≤ C*M*‖H.toLp 4 volume‖*schwartzGradientNorm 4 u := by
    have hG := highDerivativeLp4Sum_le_gradient u
    have hGrad0 : 0 ≤ schwartzGradientNorm 4 u := schwartzGradientNorm_nonneg 4 u
    have hUpper :
        2 * (C₀*M*‖H.toLp 4 volume‖*highDerivativeLp4Sum u) ≤
          C*M*‖H.toLp 4 volume‖*schwartzGradientNorm 4 u := by
      calc
        _ ≤ 2*(C₀*M*‖H.toLp 4 volume‖*(4*schwartzGradientNorm 4 u)) := by gcongr
        _ = (8*C₀)*M*‖H.toLp 4 volume‖*schwartzGradientNorm 4 u := by ring
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hM)
              (norm_nonneg _)) hGrad0
    have h := P.full_firstOrder_norms H u
    exact ⟨h.1.trans hUpper,h.2.trans hUpper⟩
  refine ⟨{
    forward := P.fullForward
    adjoint := P.fullAdjoint
    forward_pair := fun H u w => (P.fullPairs H u w).1
    adjoint_pair := fun H u w => (P.fullPairs H u w).2
    adjoint_duality := ?_
    first_order := orderBound
    coordinate_commutator := fun a H u w =>
      ⟨P.fullForward_derivative_pair a H u w, P.fullAdjoint_derivative_pair a H u w⟩
    derivative_first_order := fun i H u => orderBound (coordinateDerivative i H) u
    lipschitz_commutator := ?_ }⟩
  · intro H u w
    calc
      _ = radianHighPair (originalRegularizedAngularSymbol η χ F) H u w := (P.fullPairs H u w).1
      _ = conj (radianHighPair (highAdjointSymbol (originalRegularizedAngularSymbol η χ F))
          (fun x => conj (H x)) w u) := by rw [radianHighPair_highAdjoint, starRingEnd_self_apply]
      _ = _ := by rw [← (P.fullPairs H w u).2, inner_conj_symm]
  · intro d L hd H v
    obtain ⟨U,V,hU,hV,hPair⟩ := rough P hb hB hsize hrep d L hd H v
    have hUpper :
        2 * (C₁ * M * ((Ccut*L : ℝ≥0) : ℝ) * ‖H.toLp 4 volume‖) * ‖v.toLp 4 volume‖ ≤
          C*M*(L : ℝ)*‖H.toLp 4 volume‖*‖v.toLp 4 volume‖ := calc
      _ = (2*C₁*(Ccut : ℝ))*M*(L : ℝ)*‖H.toLp 4 volume‖*‖v.toLp 4 volume‖ := by
        push_cast
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hM) L.coe_nonneg) (norm_nonneg _))
        (norm_nonneg _)
    exact ⟨U,V,hU.trans hUpper,hV.trans hUpper,hPair⟩

end Burnett.A08
