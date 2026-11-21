import Burnett.Analysis.PrincipalEnergy.Localization.GlobalComplexScalarCoefficient

set_option autoImplicit false
set_option maxHeartbeats 5500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ContDiff NNReal

theorem firstOrderAction_finset_sum {κ : Type*} {a : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (s : Finset κ) (v : κ → SchwartzMap Space ℂ) (x : Space) :
    firstOrderAction a (∑ j ∈ s, v j : SchwartzMap Space ℂ) x =
      ∑ j ∈ s, firstOrderAction a (v j) x := by
  classical
  have hZero : firstOrderAction a (0 : SchwartzMap Space ℂ) x = 0 := by
    simpa only [smul_zero, sub_self, one_mul] using
      firstOrderAction_sub_smul a ha x (0 : SchwartzMap Space ℂ) 0 1
  have hAdd (f g : SchwartzMap Space ℂ) :
      firstOrderAction a (f+g : SchwartzMap Space ℂ) x = firstOrderAction a f x+firstOrderAction a g x := by
    simpa only [neg_one_smul, neg_one_mul, sub_neg_eq_add] using
      firstOrderAction_sub_smul a ha x f g (-1)
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, hZero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, hAdd, ih]

/-- The original multiplication by a finite coefficient matrix, with the
same scalar Fourier operator on every field component. -/
def smoothFiniteCoefficientCommutator {ι κ : Type*} [Fintype κ] (a : Space → Space → ℂ)
    (r : ι → κ → Space → ℂ) (hr : ∀ i j, ContDiff ℝ ∞ (r i j)) (f : κ → SchwartzMap Space ℂ)
    (hf : ∀ j, HasCompactSupport (f j : Space → ℂ)) (i : ι) (x : Space) : ℂ :=
  (∑ j, r i j x * firstOrderAction a (f j) x) -
    firstOrderAction a (∑ j, smoothScalarSchwartzProduct (r i j) (hr i j) (f j) (hf j) : SchwartzMap Space ℂ) x

theorem smoothFiniteCoefficientCommutator_eq_sum {ι κ : Type*} [Fintype κ]
    {a : Space → Space → ℂ} (ha : FrequencyOrderOne a)
    (r : ι → κ → Space → ℂ) (hr : ∀ i j, ContDiff ℝ ∞ (r i j)) (f : κ → SchwartzMap Space ℂ)
    (hf : ∀ j, HasCompactSupport (f j : Space → ℂ)) (i : ι) (x : Space) :
    smoothFiniteCoefficientCommutator a r hr f hf i x =
      ∑ j, smoothCoefficientCommutator a (r i j) (hr i j) (f j) (hf j) x := by
  simp only [smoothFiniteCoefficientCommutator, smoothCoefficientCommutator,
    firstOrderAction_finset_sum ha, Finset.sum_sub_distrib]

private theorem finite_coeFn_L2_sum {κ : Type*} (s : Finset κ) (f : κ → ComplexL2 Space) :
    ((∑ j ∈ s, f j : ComplexL2 Space) : Space → ℂ) =ᵐ[volume] fun x => ∑ j ∈ s, f j x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 volume
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (f j) (∑ k ∈ s, f k), ih] with x hx hy
    change _ = f j x+(∑ k ∈ s, f k x)
    rw [hx, Pi.add_apply, hy]

/-- The exact L² bound for smooth matrix-valued coefficients when the full
order-one symbol is scalar on the field components. -/
theorem exists_smoothFiniteCoefficientCommutator_global_L2_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ] {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hs : ContDiff ℝ ∞ (uncurry a))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hSym : FirstOrderFormalSymmetry a) (hProper : ProperKernelRelation (firstOrderKernelRelation a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ι → κ → Space → ℂ) (hr : ∀ i j, ContDiff ℝ ∞ (r i j)) (L : NNReal) (U : ℝ),
      0 ≤ U →
      (∀ i j, ∀ᵐ x ∂(volume : Measure Space), ‖r i j x‖ ≤ U) →
      (∀ i j, ∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r i j) x‖ ≤ (L : ℝ)) →
      ∀ (f : κ → SchwartzMap Space ℂ) (hf : ∀ j, HasCompactSupport (f j : Space → ℂ)),
        ∃ g : PiLp 2 (fun _ : ι => ComplexL2 Space),
          (∀ i, (g i : Space → ℂ) =ᵐ[volume] smoothFiniteCoefficientCommutator a r hr f hf i) ∧
          ‖g‖ ≤ C * (U + (L : ℝ)) * matrixSchwartzL2Norm f := by
  obtain ⟨C, hC, hBound⟩ := exists_complex_smoothCoefficientCommutator_global_L2_bound ha hs hb hSym hProper
  let I := Real.sqrt (Fintype.card ι : ℝ)
  let J := (Fintype.card κ : ℝ)
  have hI : 0 ≤ I := Real.sqrt_nonneg _
  have hJ : 0 ≤ J := Nat.cast_nonneg _
  refine ⟨I*J*C, by positivity, fun r hr L U hU hV hD f hf => ?_⟩
  choose hT hbnd using fun i j => hBound (r i j) (hr i j) L U (hV i j) (hD i j) (f j) (hf j)
  let T (i : ι) (j : κ) := smoothCoefficientCommutator a (r i j) (hr i j) (f j) (hf j)
  let P (i : ι) (j : κ) : ComplexL2 Space := (hT i j).toLp (T i j)
  let g : PiLp 2 (fun _ : ι => ComplexL2 Space) := WithLp.toLp 2 (fun i => ∑ j, P i j)
  let D := C * (U + (L : ℝ))
  have hDN : 0 ≤ D := mul_nonneg hC (add_nonneg hU L.coe_nonneg)
  let A := J*D*matrixSchwartzL2Norm f
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hJ hDN) (norm_nonneg _)
  refine ⟨g, ?_, ?_⟩
  · intro i
    have hP : ∀ᵐ x ∂(volume : Measure Space), ∀ j : κ, P i j x = T i j x :=
      ae_all_iff.mpr (fun j => (hT i j).coeFn_toLp)
    filter_upwards [finite_coeFn_L2_sum Finset.univ (P i), hP] with x hx h
    change (∑ j, P i j : ComplexL2 Space) x = _
    rw [hx, smoothFiniteCoefficientCommutator_eq_sum ha.frequency]
    exact Finset.sum_congr rfl fun j _ => h j
  · have hRow (i : ι) : ‖g i‖ ≤ A := by
      change ‖∑ j, P i j‖ ≤ A
      have hEntry (j : κ) : ‖P i j‖ ≤ D * matrixSchwartzL2Norm f := by
        exact (hbnd i j).trans (mul_le_mul_of_nonneg_left
          (PiLp.norm_apply_le (WithLp.toLp 2 (fun k => (f k).toLp 2 volume)) j) hDN)
      calc
        _ ≤ ∑ j, ‖P i j‖ := norm_sum_le _ _
        _ ≤ ∑ _j : κ, D * matrixSchwartzL2Norm f := Finset.sum_le_sum fun j _ => hEntry j
        _ = A := by simp only [A, J, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
    calc
      ‖g‖ ≤ Real.sqrt ((Fintype.card ι : ℝ)*A^2) := by
        rw [PiLp.norm_eq_of_L2]
        apply Real.sqrt_le_sqrt
        calc
          _ ≤ ∑ _i : ι, A^2 := Finset.sum_le_sum fun i _ =>
            pow_le_pow_left₀ (norm_nonneg _) (hRow i) _
          _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = I*A := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hA]
      _ = _ := by dsimp only [A, D]; ring

end Burnett.Analysis.CarlesonEmbedding
