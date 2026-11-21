import Burnett.Analysis.PrincipalEnergy.Localization.GlobalMatrixL2
import Burnett.Analysis.PrincipalEnergy.Localization.ProperActionLocalization

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Set Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate ContDiff NNReal

/-- Smooth scalar multiplication on an individual compact Schwartz input. -/
def smoothScalarSchwartzProduct (r : Space → ℂ) (hr : ContDiff ℝ ∞ r)
    (f : SchwartzMap Space ℂ) (hf : HasCompactSupport (f : Space → ℂ)) : SchwartzMap Space ℂ :=
  (show HasCompactSupport (fun x => r x * f x) from hf.mul_left).toSchwartzMap
    (hr.mul (f.smooth ⊤))

/-- The actual Fourier commutator after smooth multiplication of its
compact input. The coefficient can be noncompact. -/
def smoothMatrixCoefficientCommutator {ι : Type*} [Fintype ι] (a : ι → ι → Space → Space → ℂ)
    (r : Space → ℂ) (hr : ContDiff ℝ ∞ r) (f : ι → SchwartzMap Space ℂ)
    (hf : ∀ i, HasCompactSupport (f i : Space → ℂ)) (i : ι) (x : Space) : ℂ :=
  r x * matrixFirstOrderAction a f i x -
    matrixFirstOrderAction a (fun j => smoothScalarSchwartzProduct r hr (f j) (hf j)) i x

/-- A bound with the original smooth bounded coefficient in both slots.
Proper support permits one spatially cut version of that coefficient on
the joint support of the compact field and its actual full Fourier action. -/
theorem exists_smoothMatrixCoefficientCommutator_global_L2_bound
    {ι : Type*} [Fintype ι] {a : ι → ι → Space → Space → ℂ}
    (ha : ∀ i j, FirstBaseFrequencyOrderOne (a i j))
    (hs : ∀ i j, ContDiff ℝ ∞ (uncurry (a i j)))
    (hb : ∀ i j (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a i j y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hSym : MatrixFirstOrderFormalSymmetry a)
    (hProper : ∀ i j, ProperKernelRelation (firstOrderKernelRelation (a i j))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Space → ℂ) (hr : ContDiff ℝ ∞ r) (L : NNReal) (U : ℝ),
      (∀ x, conj (r x) = r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ r x‖ ≤ (L : ℝ)) →
      ∀ (f : ι → SchwartzMap Space ℂ) (hf : ∀ i, HasCompactSupport (f i : Space → ℂ)),
        ∃ hT : ∀ i, MemLp (smoothMatrixCoefficientCommutator a r hr f hf i) 2 volume,
          ‖WithLp.toLp 2 (fun i => (hT i).toLp (smoothMatrixCoefficientCommutator a r hr f hf i))‖ ≤
            C * (U + (L : ℝ)) * matrixSchwartzL2Norm f := by
  obtain ⟨C, hC, bound⟩ := exists_actualMatrixCommutator_global_L2_bound_of_properSupport ha hs hb hSym hProper
  obtain ⟨S, T, hS, hT, plateau⟩ := exists_uniform_schwartz_plateau_on_compact
  refine ⟨C * (S+T), by positivity, fun r hr L U hReal hValue hDer f hf => ?_⟩
  obtain ⟨hU, hSup, hLip⟩ := smoothCoefficient_bounds_of_ae_norm_firstDerivative r (hr.of_le (by simp))
    U L hValue hDer
  choose K hK hF hOut using fun i j => exists_firstOrderAction_support_of_properSupport
    (ha i j).frequency (hProper i j) (f j) (hf j)
  let V := ⋃ i, ⋃ j, K i j
  have hV : IsCompact V := isCompact_iUnion (fun i => isCompact_iUnion (hK i))
  obtain ⟨χ, hχ, hχReal, hχSup, hχDer, hχOne⟩ := plateau V hV
  let q (x : Space) := χ x * r x
  have hQ : HasCompactSupport q := hχ.mul_right
  let r' := hQ.toSchwartzMap ((χ.smooth ⊤).mul hr)
  have hRq (x : Space) : r' x = χ x * r x := rfl
  have hReal' (x : Space) : conj (r' x) = r' x := by
    rw [hRq, map_mul, hχReal, hReal]
  have hVal' (x : Space) : ‖r' x‖ ≤ S*U := by
    rw [hRq, norm_mul]
    exact mul_le_mul (hχSup x) (hSup x) (norm_nonneg _) hS
  let L' : NNReal := ⟨S*(L : ℝ)+T*U, by positivity⟩
  have hDer' (x : Space) : ‖fderiv ℝ (r' : Space → ℂ) x‖ ≤ (L' : ℝ) := by
    letI : NormedSpace ℂ (Space →L[ℝ] ℂ) := ContinuousLinearMap.toNormedSpace
    have hd : ‖fderiv ℝ r x‖ ≤ (L : ℝ) := norm_fderiv_le_of_lipschitz ℝ hLip
    change ‖fderiv ℝ (fun y => χ y * r y) x‖ ≤ S*(L : ℝ)+T*U
    rw [fderiv_fun_mul χ.differentiableAt (((hr.differentiable (by simp)) x))]
    calc
      _ ≤ ‖χ x‖ * ‖fderiv ℝ r x‖ + ‖r x‖ * ‖fderiv ℝ (χ : Space → ℂ) x‖ := by
        simpa only [norm_smul] using
          norm_add_le (χ x • fderiv ℝ r x) (r x • fderiv ℝ (χ : Space → ℂ) x)
      _ ≤ S*(L : ℝ)+U*T :=
        add_le_add (mul_le_mul (hχSup x) hd (norm_nonneg _) hS)
          (mul_le_mul (hSup x) (hχDer x) (norm_nonneg _) hU)
      _ = _ := by ring
  have hSame (x : Space) (hx : x ∈ V) : r' x = r x := by rw [hRq, hχOne x hx, one_mul]
  have hProduct : (fun j => scalarSchwartzProduct r' (f j)) =
      fun j => smoothScalarSchwartzProduct r hr (f j) (hf j) := by
    funext j
    ext x
    change r' x * f j x = r x * f j x
    by_cases hx : f j x = 0
    · simp only [hx, mul_zero]
    · have hxV : x ∈ V := mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨j, hF j j (subset_closure hx)⟩⟩
      rw [hSame x hxV]
  have hZero (i : ι) (x : Space) (hx : x ∉ V) : matrixFirstOrderAction a f i x = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_contra hne
    exact hx (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, hOut i j (subset_closure hne)⟩⟩)
  have hEq (i : ι) : matrixCoefficientCommutator a r' f i =
      smoothMatrixCoefficientCommutator a r hr f hf i := by
    funext x
    simp only [matrixCoefficientCommutator, smoothMatrixCoefficientCommutator, hProduct]
    by_cases hx : x ∈ V
    · rw [hSame x hx]
    · simp only [hZero i x hx, mul_zero]
  obtain ⟨hA, hAest⟩ := bound r' L' (S*U) hQ hReal' (Eventually.of_forall hVal')
    (Eventually.of_forall hDer') f hf
  have hMem (i : ι) : MemLp (smoothMatrixCoefficientCommutator a r hr f hf i) 2 volume := by
    rw [← hEq i]
    exact hA i
  refine ⟨hMem, ?_⟩
  have hLp (i : ι) : (hMem i).toLp (smoothMatrixCoefficientCommutator a r hr f hf i) =
      (hA i).toLp (matrixCoefficientCommutator a r' f i) :=
    MemLp.toLp_congr (hMem i) (hA i) (EventuallyEq.of_eq (hEq i).symm)
  simp_rw [hLp]
  refine hAest.trans ?_
  have hArith : S*U+(L' : ℝ) ≤ (S+T)*(U+(L : ℝ)) := by
    change S*U+(S*(L : ℝ)+T*U) ≤ (S+T)*(U+(L : ℝ))
    nlinarith only [mul_nonneg hT L.coe_nonneg]
  calc
    _ ≤ C * ((S+T)*(U+(L : ℝ))) * matrixSchwartzL2Norm f :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hArith hC) (norm_nonneg _)
    _ = _ := by ring

end Burnett.Analysis.CarlesonEmbedding
