import Burnett.Analysis.PrincipalEnergy.Localization.GlobalCompactMatrixPair
import Burnett.Analysis.PrincipalEnergy.Localization.ProperCommutatorSupport

set_option autoImplicit false
set_option maxHeartbeats 5800000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Set Metric Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate ContDiff InnerProductSpace NNReal

private theorem exists_schwartz_unit_cutoff_on_compact {K : Set Space} (hK : IsCompact K) :
    ∃ χ : SchwartzMap Space ℂ, HasCompactSupport (χ : Space → ℂ) ∧
      (∀ x, χ x = ((χ x).re : ℂ)) ∧ (∀ x, 0 ≤ (χ x).re ∧ (χ x).re ≤ 1) ∧
        ∀ x ∈ K, χ x = 1 := by
  obtain ⟨R, hR, hBall⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : Space)
  let b : ContDiffBump (0 : Space) := ⟨R, R+1, hR, by linarith⟩
  let z (x : Space) := (b x : ℂ)
  have hSupport : support z = support (b : Space → ℝ) := by
    ext x
    simp [z, mem_support]
  have hz : HasCompactSupport z := by
    unfold HasCompactSupport tsupport
    rw [hSupport]
    exact b.hasCompactSupport
  let χ := hz.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  refine ⟨χ, hz, ?_, ?_, ?_⟩
  · intro x
    change (b x : ℂ) = (↑((b x : ℂ).re) : ℂ)
    rw [Complex.ofReal_re]
  · intro x
    change 0 ≤ (b x : ℂ).re ∧ (b x : ℂ).re ≤ 1
    simpa only [Complex.ofReal_re] using And.intro (b.nonneg (x := x)) (b.le_one (x := x))
  · intro x hx
    change (b x : ℂ) = 1
    rw [b.one_of_mem_closedBall (hBall hx)]
    exact Complex.ofReal_one

private theorem matrixSchwartzL2Norm_unit_cutoff_le {ι : Type*} [Fintype ι]
    (χ : SchwartzMap Space ℂ) (hReal : ∀ x, χ x = ((χ x).re : ℂ))
    (hUnit : ∀ x, 0 ≤ (χ x).re ∧ (χ x).re ≤ 1)
    (g : ι → SchwartzMap Space ℂ) :
    matrixSchwartzL2Norm (fun i => scalarSchwartzProduct χ (g i)) ≤ matrixSchwartzL2Norm g := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [Fintype.sum_unique, matrixSchwartzL2Norm] using
    matrixCutoff_sum_norm_sq_le (fun _ : Unit => χ) (fun _ => hReal) (fun _ x => (hUnit x).1)
      (fun x => by simpa only [Fintype.sum_unique] using (hUnit x).2) g

private theorem dense_matrixSchwartz_toL2 {ι : Type*} [Fintype ι] :
    DenseRange (fun g : ι → SchwartzMap Space ℂ =>
      (WithLp.toLp 2 (fun i => (g i).toLp 2 volume) : PiLp 2 (fun _ : ι => ComplexL2 Space))) := by
  let e := PiLp.homeomorph 2 (fun _ : ι => ComplexL2 Space)
  have hd : DenseRange (fun g : ι → SchwartzMap Space ℂ => fun i => (g i).toLp 2 volume) :=
    DenseRange.piMap (fun _ => schwartz_toLp_denseRange (V := Space))
  exact e.symm.surjective.denseRange.comp hd e.symm.continuous

/-- The actual commutator of a properly supported finite matrix symbol with
a smooth real scalar coefficient is in L² for compact smooth inputs, with
the constant fixed for every input support. -/
theorem exists_actualMatrixCommutator_global_L2_bound_of_properSupport
    {ι : Type*} [Fintype ι] {a : ι → ι → Space → Space → ℂ}
    (ha : ∀ i j, FirstBaseFrequencyOrderOne (a i j))
    (hs : ∀ i j, ContDiff ℝ ∞ (uncurry (a i j)))
    (hb : ∀ i j (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a i j y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hSym : MatrixFirstOrderFormalSymmetry a)
    (hProper : ∀ i j, ProperKernelRelation (firstOrderKernelRelation (a i j))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      HasCompactSupport (r : Space → ℂ) → (∀ x, conj (r x) = r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r : Space → ℂ) x‖ ≤ (L : ℝ)) →
      ∀ f : ι → SchwartzMap Space ℂ,
        (∀ j, HasCompactSupport (f j : Space → ℂ)) →
        ∃ hT : ∀ i, MemLp (matrixCoefficientCommutator a r f i) 2 volume,
          ‖WithLp.toLp 2 (fun i => (hT i).toLp (matrixCoefficientCommutator a r f i))‖ ≤
            C * (U + (L : ℝ)) * matrixSchwartzL2Norm f := by
  obtain ⟨C, hC, hPairBound⟩ := exists_actualMatrixCommutator_global_compactPair_bound ha hs hb hSym
  refine ⟨C, hC, fun r L U hr hR hVal hDer f hf => ?_⟩
  obtain ⟨hU, hSup, hLip⟩ := smoothCoefficient_bounds_of_ae_norm_firstDerivative r (r.smooth 1) U L hVal hDer
  choose K hK hEntry using fun i j => exists_actualScalarCommutator_output_support_of_properSupport
    (ha i j) (hs i j).continuous (hProper i j) (f j) (hf j)
  have hT (i : ι) : MemLp (matrixCoefficientCommutator a r f i) 2 volume := by
    rw [show matrixCoefficientCommutator a r f i =
        (fun x => ∑ j, actualCoefficientCommutator (a i j) r (f j) x) from
      funext (matrixCoefficientCommutator_apply a r f i)]
    exact memLp_finset_sum Finset.univ fun j _ => (hEntry i j r L U hLip hSup).2
  let S := ⋃ i, ⋃ j, K i j
  have hS : IsCompact S := isCompact_iUnion (fun i => isCompact_iUnion (hK i))
  have hZero (i : ι) {x : Space} (hx : x ∉ S) : matrixCoefficientCommutator a r f i x = 0 := by
    rw [matrixCoefficientCommutator_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_contra hne
    have hi := (hEntry i j r L U hLip hSup).1 (subset_closure hne)
    exact hx (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, hi⟩⟩)
  obtain ⟨χ, hχ, hχReal, hχUnit, hχOne⟩ := exists_schwartz_unit_cutoff_on_compact hS
  let T : PiLp 2 (fun _ : ι => ComplexL2 Space) :=
    WithLp.toLp 2 (fun i => (hT i).toLp (matrixCoefficientCommutator a r f i))
  let D := C * (U + (L : ℝ)) * matrixSchwartzL2Norm f
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hC (add_nonneg hU L.coe_nonneg)) (norm_nonneg _)
  have testBound (g : ι → SchwartzMap Space ℂ) :
      ‖actualMatrixCommutatorPair a r f g‖ ≤ D * matrixSchwartzL2Norm g := by
    let g' (i : ι) := scalarSchwartzProduct χ (g i)
    have hg' (i : ι) : HasCompactSupport (g' i : Space → ℂ) := by
      change HasCompactSupport (fun x => χ x * g i x)
      exact hχ.mul_right
    have hCut : actualMatrixCommutatorPair a r f g = actualMatrixCommutatorPair a r f g' := by
      unfold actualMatrixCommutatorPair
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ S
      · simp only [g', scalarSchwartzProduct_apply, hχOne x hx, one_mul]
      · simp only [hZero i hx, mul_zero]
    rw [hCut]
    exact (hPairBound r L U hr hR hVal hDer f g' hf hg').trans
      (mul_le_mul_of_nonneg_left (matrixSchwartzL2Norm_unit_cutoff_le χ hχReal hχUnit g) hD)
  have pairing (g : ι → SchwartzMap Space ℂ) :
      ⟪WithLp.toLp 2 (fun i => (g i).toLp 2 volume), T⟫_ℂ = actualMatrixCommutatorPair a r f g := by
    unfold actualMatrixCommutatorPair
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(g i).coeFn_toLp 2 volume, MemLp.coeFn_toLp (hT i)] with x hg hTx
    change inner ℂ (((g i).toLp 2 volume) x) (((hT i).toLp _) x) = _
    rw [hg, hTx, RCLike.inner_apply']
  have hAll (v : PiLp 2 (fun _ : ι => ComplexL2 Space)) : ‖⟪v,T⟫_ℂ‖ ≤ D * ‖v‖ := by
    apply dense_matrixSchwartz_toL2.induction_on (p := fun v => ‖⟪v,T⟫_ℂ‖ ≤ D * ‖v‖) v
    · exact isClosed_le (continuous_id.inner continuous_const).norm (continuous_const.mul continuous_norm)
    · intro g
      change ‖⟪WithLp.toLp 2 (fun i => (g i).toLp 2 volume), T⟫_ℂ‖ ≤ D * matrixSchwartzL2Norm g
      rw [pairing]
      exact testBound g
  refine ⟨hT, ?_⟩
  change ‖T‖ ≤ D
  have h := hAll T
  rw [inner_self_eq_norm_sq_to_K, norm_pow] at h
  change ‖((‖T‖ : ℝ) : ℂ)‖^2 ≤ D * ‖T‖ at h
  rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), pow_two] at h
  by_cases hz : ‖T‖=0
  · rw [hz]
    exact hD
  · have hp : 0<‖T‖ := lt_of_le_of_ne (norm_nonneg T) (fun he => hz he.symm)
    exact (mul_le_mul_iff_left₀ hp).mp h

end Burnett.Analysis.CarlesonEmbedding
