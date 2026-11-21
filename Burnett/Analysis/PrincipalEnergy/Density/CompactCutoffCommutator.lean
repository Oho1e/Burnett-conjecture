import Burnett.Analysis.PrincipalEnergy.Density.FixedChartDensitySymbolProfile
import Burnett.Analysis.PrincipalEnergy.Density.CompactCutoffMultiplierBounds

set_option autoImplicit false
set_option maxHeartbeats 12500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate InnerProductSpace ContDiff NNReal

def compactCutoffActualFourier {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : GlobalMatrixSymbolData a)
    (p q : SchwartzMap Space ℂ) : CompactSchwartzComponents ι →ₗ[ℂ] CompactSchwartzComponents ι :=
  (compactScalarMultiplier p (p.smooth ⊤)).comp
    ((compactActualFourierOp ha).comp (compactScalarMultiplier q (q.smooth ⊤)))

theorem scalarSchwartzProduct_compactScalarMultiplier {ι : Type*} (f : CompactSchwartzComponents ι)
    (q : SchwartzMap Space ℂ) (r : Space → ℂ) (hr : ContDiff ℝ ∞ r) (j : ι)
    (rq : SchwartzMap Space ℂ) (h : ∀ x, rq x = q x*r x) :
    scalarSchwartzProduct q ((compactScalarMultiplier r hr f).val j) =
      scalarSchwartzProduct rq (f.val j) := by
  ext x
  simp only [scalarSchwartzProduct_apply, compactScalarMultiplier_apply, h, mul_assoc]

theorem compactCutoffActualFourier_apply {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : GlobalMatrixSymbolData a)
    (p q : SchwartzMap Space ℂ) (f : CompactSchwartzComponents ι) (i : ι) (x : Space) :
    (compactCutoffActualFourier ha p q f).val i x =
      p x*matrixFirstOrderAction a (fun j => scalarSchwartzProduct q (f.val j)) i x := by
  simp only [compactCutoffActualFourier, LinearMap.comp_apply, compactScalarMultiplier_apply,
    compactActualFourierOp_apply]
  rfl

theorem compactCutoffActualFourier_transport {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : GlobalMatrixSymbolData a) (p q : SchwartzMap Space ℂ) :
    compactTransportOp (compactCutoffActualFourier ha p q) =
      compactSchwartzMultiplier p * compactTransportOp (compactActualFourierOp ha) * compactSchwartzMultiplier q := by
  apply LinearMap.ext
  intro u
  obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective u
  simp only [compactTransportOp_apply, compactSchwartzMultiplier, Module.End.mul_apply,
    compactCutoffActualFourier, LinearMap.comp_apply]

/-- The compact-base estimate on the exact symbol gives an (L^2) bound
for the real scalar coefficient commutator of the physical cutoff product. -/
theorem exists_compactCutoffFourier_scalar_commutator_bound {ι : Type*} [Fintype ι]
    {a c : ι → ι → Space → Space → ℂ} (ha : GlobalMatrixSymbolData a)
    (p q : SchwartzMap Space ℂ) (hp : HasCompactSupport (p : Space → ℂ))
    (hq : HasCompactSupport (q : Space → ℂ))
    (hc : ∀ i j, FirstBaseFrequencyOrderOne (c i j) ∧ CompactBaseOrderOne (c i j) ∧
      Continuous (uncurry (c i j))) (hSym : MatrixFirstOrderFormalSymmetry c)
    (hAct : ∀ (f : ι → SchwartzMap Space ℂ) i x, matrixFirstOrderAction c f i x =
      p x * matrixFirstOrderAction a (fun j => scalarSchwartzProduct q (f j)) i x) :
    let C := compactSchwartzMultiplier p * compactTransportOp (compactActualFourierOp ha) * compactSchwartzMultiplier q
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (r : Space → ℂ) (hr : ContDiff ℝ ∞ r) (L : NNReal) (U : ℝ),
      (∀ x, conj (r x) = r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ r x‖ ≤ (L : ℝ)) →
      ∀ u : CompactMatrixTest ι,
        ‖SymmetricEnergy.comm (compactTransportOp (compactScalarMultiplier r hr)) C u‖ ≤ K*(U+(L:ℝ))*‖u‖ := by
  intro C
  obtain ⟨D, hD, paired⟩ := exists_compactBase_matrix_coefficientCommutator_L2_pair_bound
    (fun i j => (hc i j).1) (fun i j => (hc i j).2.1) (fun i j => (hc i j).2.2) hSym
  obtain ⟨S, T, hS, hT, plateau⟩ := exists_uniform_schwartz_plateau_on_compact
  let V := tsupport (p : Space → ℂ) ∪ tsupport (q : Space → ℂ)
  obtain ⟨θ, hθ, hθr, hθV, hθD, hθOne⟩ := plateau V (hp.union hq)
  refine ⟨D*(S+T), by positivity, fun r hr L U hReal hVal hDer u => ?_⟩
  obtain ⟨hU, hSup, hLip⟩ := smoothCoefficient_bounds_of_ae_norm_firstDerivative r (hr.of_le (by simp)) U L hVal hDer
  let w (x : Space) := θ x * r x
  let r' := (show HasCompactSupport w from hθ.mul_right).toSchwartzMap ((θ.smooth ⊤).mul hr)
  have hreq (x : Space) : r' x = θ x*r x := rfl
  have hR' (x : Space) : conj (r' x) = r' x := by rw [hreq, map_mul, hθr, hReal]
  have hV' (x : Space) : ‖r' x‖ ≤ S*U := by
    rw [hreq, norm_mul]
    exact mul_le_mul (hθV x) (hSup x) (norm_nonneg _) hS
  let L' : NNReal := ⟨S*(L:ℝ)+T*U, by positivity⟩
  have hD' (x : Space) : ‖fderiv ℝ (r' : Space → ℂ) x‖ ≤ (L':ℝ) := by
    letI : NormedSpace ℂ (Space →L[ℝ] ℂ) := ContinuousLinearMap.toNormedSpace
    have hd : ‖fderiv ℝ r x‖ ≤ (L:ℝ) := norm_fderiv_le_of_lipschitz ℝ hLip
    change ‖fderiv ℝ (fun y => θ y*r y) x‖ ≤ S*(L:ℝ)+T*U
    rw [fderiv_fun_mul θ.differentiableAt ((hr.differentiable (by simp)) x)]
    calc
      _ ≤ ‖θ x‖*‖fderiv ℝ r x‖+‖r x‖*‖fderiv ℝ (θ : Space → ℂ) x‖ := by
        simpa only [norm_smul] using norm_add_le (θ x • fderiv ℝ r x) (r x • fderiv ℝ (θ : Space → ℂ) x)
      _ ≤ S*(L:ℝ)+U*T := add_le_add (mul_le_mul (hθV x) hd (norm_nonneg _) hS)
        (mul_le_mul (hSup x) (hθD x) (norm_nonneg _) hU)
      _ = _ := by ring
  let X := compactCutoffActualFourier ha p q
  let R := compactScalarMultiplier (ι := ι) r hr
  obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective u
  let W := R (X f) - X (R f)
  have hW : SymmetricEnergy.comm (compactTransportOp R) C (compactMatrixTestEquiv ι f) =
      compactMatrixTestEquiv ι W := by
    change SymmetricEnergy.comm (compactTransportOp R)
      (compactSchwartzMultiplier p * compactTransportOp (compactActualFourierOp ha) * compactSchwartzMultiplier q)
      (compactMatrixTestEquiv ι f) = _
    rw [← compactCutoffActualFourier_transport]
    simp only [SymmetricEnergy.comm, LinearMap.sub_apply, Module.End.mul_apply, compactTransportOp_apply, W, X, map_sub]
  have hLeft (x : Space) : r x*p x = r' x*p x := by
    by_cases hx : p x = 0
    · simp only [hx, mul_zero]
    · rw [hreq, hθOne x (Or.inl (subset_closure hx)), one_mul]
  have hRight (j : ι) :
      scalarSchwartzProduct q ((R f).val j) = scalarSchwartzProduct q (scalarSchwartzProduct r' (f.val j)) := by
    ext x
    simp only [R, scalarSchwartzProduct_apply, compactScalarMultiplier_apply]
    by_cases hx : q x = 0
    · simp only [hx, zero_mul]
    · rw [hreq, hθOne x (Or.inr (subset_closure hx)), one_mul]
  have hWpoint (i : ι) (x : Space) : W.val i x = matrixCoefficientCommutator c r' f.val i x := by
    change r x * (X f).val i x - (X (R f)).val i x = _
    rw [matrixCoefficientCommutator, hAct f.val, hAct (fun j => scalarSchwartzProduct r' (f.val j))]
    simp only [X, compactCutoffActualFourier_apply, hRight, ← mul_assoc, hLeft]
  have hPair := paired r' L' (S*U) (mul_nonneg hS hU) (show HasCompactSupport (r' : Space → ℂ) from hθ.mul_right)
    hR' (Eventually.of_forall hV') (Eventually.of_forall hD') f.val W.val
  have hInner : (∑ i, ∫ x, conj (W.val i x) * matrixCoefficientCommutator c r' f.val i x) =
      ⟪compactMatrixTestEquiv ι W, compactMatrixTestEquiv ι W⟫_ℂ := by
    rw [compactMatrixTestEquiv_inner]
    simp_rw [← hWpoint]
  let E := ‖compactMatrixTestEquiv ι W‖
  let F := ‖compactMatrixTestEquiv ι f‖
  have hE : 0 ≤ E := norm_nonneg _
  have hPair' : E^2 ≤ D*(S*U+(L':ℝ))*F*E := by
    rw [hInner, inner_self_eq_norm_sq_to_K, norm_pow] at hPair
    change ‖(E:ℂ)‖^2 ≤ D*(S*U+(L':ℝ))*F*E at hPair
    simpa only [Complex.norm_real, Real.norm_of_nonneg hE] using hPair
  have hNorm : E ≤ D*(S*U+(L':ℝ))*F := by
    by_cases hz : E = 0
    · rw [hz]
      positivity
    · rw [pow_two] at hPair'
      exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))).mp hPair'
  rw [hW]
  apply hNorm.trans
  have hArith : S*U+(L':ℝ) ≤ (S+T)*(U+(L:ℝ)) := by
    change S*U+(S*(L:ℝ)+T*U) ≤ (S+T)*(U+(L:ℝ))
    nlinarith only [mul_nonneg hT L.coe_nonneg]
  calc
    _ ≤ D*((S+T)*(U+(L:ℝ)))*F := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hArith hD) (norm_nonneg _)
    _ = _ := by ring

end Burnett.Analysis.CarlesonEmbedding
