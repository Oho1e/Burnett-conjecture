import Burnett.Analysis.PrincipalEnergy.Localization.CoefficientTailKernel
import Burnett.Analysis.PrincipalEnergy.Localization.CutoffMatrixLocalBound

set_option autoImplicit false
set_option maxHeartbeats 4500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Burnett.Analysis.FirstOrderDyadic
open scoped NNReal ComplexConjugate InnerProductSpace BigOperators

universe u

/-- The Lebesgue pairing with the actual left-quantized coefficient commutator. -/
def actualScalarCommutatorPair (a : Space → Space → ℂ)
    (r f g : SchwartzMap Space ℂ) : ℂ :=
  ∫ x, conj (g x) * actualCoefficientCommutator a r f x

/-- The kernel multiplier produced by the retained pairs of cutoff factors. -/
def separatedCutoffWeight {ι : Type*} (far : Finset (ι × ι))
    (α : ι → SchwartzMap Space ℂ) (p : Space × Space) : ℝ :=
  ∑ e ∈ far, (α e.1 p.1).re * (α e.2 p.2).re

theorem separatedCutoffWeight_bounds {ι : Type*} [Fintype ι]
    (far : Finset (ι × ι)) (α : ι → SchwartzMap Space ℂ)
    (hPositive : ∀ i x, 0 ≤ (α i x).re)
    (hSubpartition : ∀ x, ∑ i, (α i x).re ≤ 1) (d : ℝ)
    (hGap : ∀ e ∈ far, ∀ x y, α e.1 x ≠ 0 → α e.2 y ≠ 0 → d ≤ ‖x-y‖) :
    Continuous (separatedCutoffWeight far α) ∧
      (∀ p, 0 ≤ separatedCutoffWeight far α p) ∧
      (∀ p, separatedCutoffWeight far α p ≤ 1) ∧
      (∀ p : Space × Space, ‖p.1-p.2‖ < d → separatedCutoffWeight far α p = 0) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact continuous_finset_sum far fun e _ =>
      ((Complex.continuous_re.comp (α e.1).continuous).comp continuous_fst).mul
        ((Complex.continuous_re.comp (α e.2).continuous).comp continuous_snd)
  · intro p
    exact Finset.sum_nonneg fun e _ => mul_nonneg (hPositive e.1 p.1) (hPositive e.2 p.2)
  · intro p
    calc
      separatedCutoffWeight far α p ≤ ∑ e : ι × ι, (α e.1 p.1).re * (α e.2 p.2).re :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ far) fun e _ _ =>
          mul_nonneg (hPositive e.1 p.1) (hPositive e.2 p.2)
      _ = (∑ i, (α i p.1).re) * ∑ j, (α j p.2).re := by
        rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_mul]
        simp only [Finset.mul_sum]
      _ ≤ 1 := by
        simpa using mul_le_mul (hSubpartition p.1) (hSubpartition p.2)
          (Finset.sum_nonneg fun j _ => hPositive j p.2) (zero_le_one : (0 : ℝ) ≤ 1)
  · intro p hp
    apply Finset.sum_eq_zero
    intro e he
    by_cases hx : α e.1 p.1 = 0
    · simp [hx]
    have hy : α e.2 p.2 = 0 := by
      by_contra hy
      exact (not_le_of_gt hp) (hGap e he _ _ hx hy)
    simp [hy]

/-- Separate the actual cut input and test, then sum their exact double-integral
identities. The equality includes every selected pair and its own cut factors. -/
theorem actualSeparatedCutoffPair_eq_weightedKernel {ι : Type*}
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (r f g : SchwartzMap Space ℂ)
    (L : NNReal) (U : ℝ) (hLip : LipschitzWith L r) (hR : ∀ x, ‖r x‖ ≤ U)
    (hf : HasCompactSupport (f : Space → ℂ))
    (far : Finset (ι × ι)) (α : ι → SchwartzMap Space ℂ)
    (hReal : ∀ i x, α i x = ((α i x).re : ℂ))
    (d : ℝ) (hd : 0 < d)
    (hGap : ∀ e ∈ far, ∀ x y, α e.1 x ≠ 0 → α e.2 y ≠ 0 → d ≤ ‖x-y‖) :
    (∑ e ∈ far, actualScalarCommutatorPair a r
        (scalarSchwartzProduct (α e.2) f) (scalarSchwartzProduct (α e.1) g)) =
      ∫ x, conj (g x) * ∫ y, weightedCoefficientKernel a r (separatedCutoffWeight far α) x y * f y := by
  let K := fullCoefficientKernel a r
  let F (e : ι × ι) := scalarSchwartzProduct (α e.2) f
  let G (e : ι × ι) := scalarSchwartzProduct (α e.1) g
  let μ : Measure (Space × Space) := (volume : Measure Space).prod volume
  let H (e : ι × ι) (p : Space × Space) :=
    conj (G e p.1) * (K p.1 p.2 * F e p.2)
  let W (p : Space × Space) :=
    conj (g p.1) * (weightedCoefficientKernel a r (separatedCutoffWeight far α) p.1 p.2 * f p.2)
  have hF (e : ι × ι) : HasCompactSupport (F e : Space → ℂ) := by
    change HasCompactSupport (fun x => α e.2 x * f x)
    simpa only [mul_comm] using hf.mul_right (f' := (α e.2 : Space → ℂ))
  have hDist (e : ι × ι) (he : e ∈ far) (x y : Space)
      (hy : F e y ≠ 0) (hx : G e x ≠ 0) : d ≤ ‖x-y‖ := by
    apply hGap e he x y
    · exact fun h => hx (by simp [G, scalarSchwartzProduct_apply, h])
    · exact fun h => hy (by simp [F, scalarSchwartzProduct_apply, h])
  obtain ⟨C, _, hKernel⟩ := exists_fullCoefficientKernel_bounds ha
  have hInt (e : ι × ι) (he : e ∈ far) : Integrable (H e) μ :=
    integrable_separated_kernel_pair (hKernel r L hLip) (F e) (G e) d hd (hDist e he)
  have hSum (p : Space × Space) : (∑ e ∈ far, H e p) = W p := by
    change (∑ e ∈ far, conj (G e p.1) * (K p.1 p.2 * F e p.2)) =
      conj (g p.1) * (separatedCutoffWeight far α p • K p.1 p.2 * f p.2)
    rw [Algebra.smul_def]
    change (∑ e ∈ far, H e p) =
      conj (g p.1) * ((separatedCutoffWeight far α p : ℂ) * K p.1 p.2 * f p.2)
    rw [separatedCutoffWeight, Complex.ofReal_sum]
    rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    dsimp only [H, F, G]
    simp only [scalarSchwartzProduct_apply, map_mul, Complex.ofReal_mul]
    have hC : conj (α e.1 p.1) = ((α e.1 p.1).re : ℂ) := by
      calc
        _ = conj ((α e.1 p.1).re : ℂ) := congrArg (starRingEnd ℂ) (hReal e.1 p.1)
        _ = _ := Complex.conj_ofReal _
    rw [hC]
    conv_lhs => rw [hReal e.2 p.2]
    ring
  have hW : Integrable W μ := by
    have hIntSum := integrable_finset_sum far hInt
    exact hIntSum.congr (Eventually.of_forall fun p => by simpa only [Finset.sum_apply] using hSum p)
  calc
    (∑ e ∈ far, actualScalarCommutatorPair a r (F e) (G e)) =
        ∑ e ∈ far, ∫ p, H e p ∂μ := by
      apply Finset.sum_congr rfl
      intro e he
      exact actualCoefficientCommutator_separated_pair_eq_kernel ha hCont r (F e) (G e)
        L U hLip hR (hF e) d hd (hDist e he)
    _ = ∫ p, ∑ e ∈ far, H e p ∂μ := (integral_finset_sum far hInt).symm
    _ = ∫ p, W p ∂μ := integral_congr_ae (Eventually.of_forall hSum)
    _ = ∫ x, conj (g x) * ∫ y, weightedCoefficientKernel a r (separatedCutoffWeight far α) x y * f y := by
      rw [integral_prod W hW]
      apply integral_congr_ae
      filter_upwards with x
      simpa only [W] using
        integral_const_mul (μ := (volume : Measure Space)) (conj (g x))
          (fun y => weightedCoefficientKernel a r (separatedCutoffWeight far α) x y * f y)

/-- All separated cutoff pairs of the same fields are bounded together. The
constant has no dependence on the number of cutoffs or separated pairs. -/
theorem exists_actualSeparatedCutoffPair_norm_le {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hCont : Continuous (Function.uncurry a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] (far : Finset (ι × ι))
      (α : ι → SchwartzMap Space ℂ),
      (∀ i x, α i x = ((α i x).re : ℂ)) →
      (∀ i x, 0 ≤ (α i x).re) →
      (∀ x, ∑ i, (α i x).re ≤ 1) →
      ∀ (d : ℝ), 0 < d →
      (∀ e ∈ far, ∀ x y, α e.1 x ≠ 0 → α e.2 y ≠ 0 → d ≤ ‖x-y‖) →
      ∀ (r f g : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ), LipschitzWith L r → 0 ≤ U →
      (∀ x, ‖r x‖ ≤ U) → HasCompactSupport (f : Space → ℂ) →
      ‖∑ e ∈ far, actualScalarCommutatorPair a r
        (scalarSchwartzProduct (α e.2) f) (scalarSchwartzProduct (α e.1) g)‖ ≤
        C * U * d⁻¹ * ‖f.toLp 2 volume‖ * ‖g.toLp 2 volume‖ := by
  obtain ⟨C, hC, hAction⟩ := exists_weightedCoefficientTail_L2_action_bound ha
  refine ⟨C, hC, ?_⟩
  intro ι _ far α hReal hPositive hSubpartition d hd hGap r f g L U hLip hU hR hf
  obtain ⟨hwCont, hwPositive, hwBound, hwGap⟩ :=
    separatedCutoffWeight_bounds far α hPositive hSubpartition d hGap
  obtain ⟨hLp, hNorm⟩ := hAction r L U hLip hU hR d hd
    (separatedCutoffWeight far α) hwCont hwPositive hwBound hwGap f
  let W (x : Space) := ∫ y, weightedCoefficientKernel a r (separatedCutoffWeight far α) x y * f y
  let v := hLp.toLp W
  have hInner : ⟪g.toLp 2 volume,v⟫_ℂ = ∫ x, conj (g x) * W x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [g.coeFn_toLp 2 volume, MemLp.coeFn_toLp hLp] with x hg hv
    change inner ℂ ((g.toLp 2 volume) x) ((hLp.toLp W) x) = _
    rw [hg, hv, RCLike.inner_apply']
  rw [actualSeparatedCutoffPair_eq_weightedKernel ha hCont r f g L U hLip hR hf
    far α hReal d hd hGap, ← hInner]
  calc
    ‖⟪g.toLp 2 volume,v⟫_ℂ‖ ≤ ‖g.toLp 2 volume‖ * ‖v‖ := norm_inner_le_norm _ _
    _ ≤ ‖g.toLp 2 volume‖ * (C * U * d⁻¹ * ‖f.toLp 2 volume‖) :=
      mul_le_mul_of_nonneg_left hNorm (norm_nonneg _)
    _ = _ := by ring

end Burnett.Analysis.CarlesonEmbedding
