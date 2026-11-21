import Burnett.Analysis.PrincipalEnergy.Density.CompactFieldTransfer

set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (Op)
open scoped BigOperators ComplexConjugate InnerProductSpace ContDiff NNReal

private theorem projected_coefficient_controls (Q : ℂ →L[ℝ] ℂ) (hQ : ‖Q‖ ≤ 1)
    (r : Space → ℂ) (hr : ContDiff ℝ ∞ r) (L : NNReal) (U : ℝ)
    (hU : ∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U)
    (hL : ∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ r x‖ ≤ (L : ℝ)) :
    (∀ᵐ x ∂(volume : Measure Space), ‖Q (r x)‖ ≤ U) ∧
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (Q ∘ r) x‖ ≤ (L : ℝ)) := by
  constructor
  · filter_upwards [hU] with x hx
    exact ((Q.le_opNorm (r x)).trans (mul_le_of_le_one_left (norm_nonneg _) hQ)).trans hx
  · filter_upwards [hL] with x hx
    have hd : fderiv ℝ (Q ∘ r) x = Q.comp (fderiv ℝ r x) :=
      (Q.hasFDerivAt.comp x (((hr.differentiable (by simp)) x).hasFDerivAt)).fderiv
    rw [hd]
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) hQ)).trans hx

/-- A scalar commutator estimate for real coefficients applies to complex
coefficients by their two real projections on the same actual domain. -/
theorem compactComplexScalar_commutator_bound_of_real {ι : Type*} [Fintype ι]
    (C : Op (CompactMatrixTest ι)) (K : ℝ)
    (hBound : ∀ (r : Space → ℂ) (hr : ContDiff ℝ ∞ r) (L : NNReal) (U : ℝ),
      (∀ x, conj (r x) = r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ r x‖ ≤ (L : ℝ)) →
      ∀ v : CompactMatrixTest ι,
        ‖SymmetricEnergy.comm (compactTransportOp (compactScalarMultiplier r hr)) C v‖ ≤ K*(U+(L:ℝ))*‖v‖)
    (r : Space → ℂ) (hr : ContDiff ℝ ∞ r) (L : NNReal) (U : ℝ)
    (hU : ∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U)
    (hL : ∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ r x‖ ≤ (L : ℝ))
    (u : CompactMatrixTest ι) :
    ‖SymmetricEnergy.comm (compactTransportOp (compactScalarMultiplier r hr)) C u‖ ≤ (2*K)*(U+(L:ℝ))*‖u‖ := by
  let Q := Complex.ofRealCLM.comp Complex.reCLM
  let P := Complex.ofRealCLM.comp Complex.imCLM
  have hQ : ‖Q‖ ≤ 1 := Q.opNorm_le_bound zero_le_one fun z => by
    change ‖(z.re : ℂ)‖ ≤ 1 * ‖z‖
    rw [Complex.norm_real, Real.norm_eq_abs, one_mul]
    exact Complex.abs_re_le_norm z
  have hP : ‖P‖ ≤ 1 := P.opNorm_le_bound zero_le_one fun z => by
    change ‖(z.im : ℂ)‖ ≤ 1 * ‖z‖
    rw [Complex.norm_real, Real.norm_eq_abs, one_mul]
    exact Complex.abs_im_le_norm z
  let r₀ : Space → ℂ := Q ∘ r
  let r₁ : Space → ℂ := P ∘ r
  have hr₀ : ContDiff ℝ ∞ r₀ := Q.contDiff.comp hr
  have hr₁ : ContDiff ℝ ∞ r₁ := P.contDiff.comp hr
  obtain ⟨h₀, h₀'⟩ := projected_coefficient_controls Q hQ r hr L U hU hL
  obtain ⟨h₁, h₁'⟩ := projected_coefficient_controls P hP r hr L U hU hL
  let R₀ := compactTransportOp (compactScalarMultiplier (ι := ι) r₀ hr₀)
  let R₁ := compactTransportOp (compactScalarMultiplier (ι := ι) r₁ hr₁)
  have split (x : Space) : r x = r₀ x + Complex.I * r₁ x := by
    change r x = ((r x).re : ℂ) + Complex.I * ((r x).im : ℂ)
    rw [mul_comm Complex.I, Complex.re_add_im]
  have hR : compactTransportOp (compactScalarMultiplier r hr) = R₀+Complex.I • R₁ := by
    apply LinearMap.ext
    intro v
    obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective v
    simp only [LinearMap.add_apply, LinearMap.smul_apply, R₀, R₁, compactTransportOp_apply, ← map_add, ← map_smul]
    apply congrArg (compactMatrixTestEquiv ι)
    apply Subtype.ext
    funext i
    ext x
    change r x*f.val i x = r₀ x*f.val i x+r₁ x*(Complex.I*f.val i x)
    rw [split]
    ring
  have hSplit : SymmetricEnergy.comm (compactTransportOp (compactScalarMultiplier r hr)) C u =
      SymmetricEnergy.comm R₀ C u + Complex.I • SymmetricEnergy.comm R₁ C u := by
    simp only [hR, SymmetricEnergy.comm, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, map_add, map_smul, smul_sub]
    abel
  rw [hSplit]
  calc
    _ ≤ ‖SymmetricEnergy.comm R₀ C u‖ + ‖Complex.I • SymmetricEnergy.comm R₁ C u‖ := norm_add_le _ _
    _ ≤ K*(U+(L:ℝ))*‖u‖ + K*(U+(L:ℝ))*‖u‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
      exact add_le_add (hBound r₀ hr₀ L U (fun _ => Complex.conj_ofReal _) h₀ h₀' u)
        (hBound r₁ hr₁ L U (fun _ => Complex.conj_ofReal _) h₁ h₁' u)
    _ = _ := by ring

/-- The actual finite matrix coefficient commutator follows from the
complex scalar estimates when the cutoff operator is scalar in the field. -/
theorem compactFiniteCutoff_commutator_bound {ι : Type*} [Fintype ι]
    {a : Space → Space → ℂ} (ha : GlobalMatrixSymbolData (diagonalOrderOneSymbol (ι := ι) a))
    (p q : SchwartzMap Space ℂ) (K : ℝ) :
    let C := compactSchwartzMultiplier p * compactTransportOp (compactActualFourierOp ha) *
      compactSchwartzMultiplier q
    (∀ (r : Space → ℂ) (hr : ContDiff ℝ ∞ r) (L : NNReal) (U : ℝ),
      (∀ x, conj (r x) = r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ r x‖ ≤ (L : ℝ)) →
      ∀ v : CompactMatrixTest ι,
        ‖SymmetricEnergy.comm (compactTransportOp (compactScalarMultiplier r hr)) C v‖ ≤ K*(U+(L:ℝ))*‖v‖) →
    ∀ (r : ι → ι → Space → ℂ) (hr : ∀ i j, ContDiff ℝ ∞ (r i j)) (L : NNReal) (U : ℝ),
      (∀ i j, ∀ᵐ x ∂(volume : Measure Space), ‖r i j x‖ ≤ U) →
      (∀ i j, ∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r i j) x‖ ≤ (L : ℝ)) →
      ∀ v : CompactMatrixTest ι, ‖SymmetricEnergy.comm (compactTransportOp (compactFiniteMultiplier r hr)) C v‖ ≤
        ((Fintype.card ι : ℝ)^2*(2*K))*(U+(L:ℝ))*‖v‖ := by
  intro C hBound r hr L U hU hL v
  let E (i j : ι) := compactTransportOp (compactFieldTransfer i j)
  let R (i j : ι) := compactTransportOp (compactScalarMultiplier (ι := ι) (r i j) (hr i j))
  have hSum : SymmetricEnergy.comm (compactTransportOp (compactFiniteMultiplier r hr)) C =
      ∑ i, ∑ j, E i j * SymmetricEnergy.comm (R i j) C := by
    calc
      _ = ∑ i, ∑ j, ((E i j*R i j)*C - C*(E i j*R i j)) := by
        rw [compactFiniteMultiplier_eq_sum_fieldTransfer]
        simp only [SymmetricEnergy.comm, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib, E, R]
      _ = _ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        have hc : C*E i j = E i j*C := compactCutoffFourier_commutes_fieldTransfer ha p q i j
        have hc' : C*(E i j*R i j) = E i j*(C*R i j) := by rw [← mul_assoc, hc, mul_assoc]
        rw [SymmetricEnergy.comm, mul_sub, hc', mul_assoc (E i j) (R i j) C]
  rw [hSum]
  simp only [LinearMap.sum_apply, Module.End.mul_apply]
  calc
    _ ≤ ∑ i, ∑ j, ‖E i j (SymmetricEnergy.comm (R i j) C v)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ _i : ι, ∑ _j : ι, (2*K)*(U+(L:ℝ))*‖v‖ := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      exact (compactFieldTransfer_norm_le i j _).trans
        (compactComplexScalar_commutator_bound_of_real C K hBound (r i j) (hr i j) L U (hU i j) (hL i j) v)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end Burnett.Analysis.CarlesonEmbedding
