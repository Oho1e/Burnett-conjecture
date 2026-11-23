import Burnett.Analysis.Microlocal.Overlap.SupportedWeakFourier
import Burnett.Analysis.Microlocal.SeparableSquareOperators

set_option autoImplicit false
set_option maxHeartbeats 1700000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Microlocal.AngularCommutator
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol radialCore radialCore_eq_zero)
open Burnett.Microlocal.SeparablePositive
open scoped BigOperators ComplexConjugate ContDiff InnerProduct Topology

/-- The base symbol induced by the two coefficient slots. -/
def weightedSlotBaseSymbol (b a c : BoundedSymbol E) : BoundedSymbol E :=
  productSymbol (productSymbol (conjugateSymbol a) b) c

theorem weightedSlotBaseSymbol_apply (b a c : BoundedSymbol E) (x : E) :
    weightedSlotBaseSymbol b a c x = b x * conj (a x) * c x := by
  simp only [weightedSlotBaseSymbol, productSymbol_apply, conjugateSymbol_apply]
  rw [mul_comm (conj (a x)) (b x)]

theorem weightedSlotBaseSymbol_continuous (b a c : BoundedSymbol E)
    (hb : Continuous (b : E → ℂ)) (ha : Continuous (a : E → ℂ))
    (hc : Continuous (c : E → ℂ)) :
    Continuous (weightedSlotBaseSymbol b a c : E → ℂ) := by
  exact ((Complex.continuous_conj.comp ha).mul hb).mul hc

/-- Moving the right coefficient through the angular multiplier leaves
the commutator and a fixed change of the frequency symbol. -/
def weightedSlotFrequencyError (m mReg c : BoundedSymbol E) (u : ComplexL2 E) : ComplexL2 E :=
  cutoffCommutator m c u + fourierMultiplier (symbolDifference mReg m) (symbolCLM c u)

theorem weightedSlot_pairing_eq_add_error
    (b m mReg a c : BoundedSymbol E) (u v : ComplexL2 E) :
    inner ℂ (symbolCLM a u) (separableOperator b mReg (symbolCLM c v)) =
      inner ℂ u (separableOperator (weightedSlotBaseSymbol b a c) m v) +
        inner ℂ (symbolCLM a u) (symbolCLM b (weightedSlotFrequencyError m mReg c v)) := by
  have hSplit :
      fourierMultiplier mReg (symbolCLM c v) =
        symbolCLM c (fourierMultiplier m v) + weightedSlotFrequencyError m mReg c v := by
    simp only [weightedSlotFrequencyError, cutoffCommutator, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, fourierMultiplier_symbolDifference]
    abel
  have hMain :
      inner ℂ (symbolCLM a u) (symbolCLM b (symbolCLM c (fourierMultiplier m v))) =
        inner ℂ u (separableOperator (weightedSlotBaseSymbol b a c) m v) := by
    rw [inner_symbolCLM_left, ← symbolCLM_product, ← symbolCLM_product]
    rfl
  change inner ℂ (symbolCLM a u) (symbolCLM b (fourierMultiplier mReg (symbolCLM c v))) = _
  rw [hSplit, map_add, inner_add_right, hMain]

/-- The exact two-slot expansion for any finite coefficient families. -/
theorem weightedSlot_sum_pairing_eq_add_error {I J : Type*} [Fintype I] [Fintype J]
    (b m mReg : BoundedSymbol E) (a : I → BoundedSymbol E) (c : J → BoundedSymbol E)
    (u : I → ComplexL2 E) (v : J → ComplexL2 E) :
    inner ℂ (∑ i, symbolCLM (a i) (u i))
      (separableOperator b mReg (∑ j, symbolCLM (c j) (v j))) =
        (∑ i, ∑ j, inner ℂ (u i)
          (separableOperator (weightedSlotBaseSymbol b (a i) (c j)) m (v j))) +
        ∑ i, ∑ j, inner ℂ (symbolCLM (a i) (u i))
          (symbolCLM b (weightedSlotFrequencyError m mReg (c j) (v j))) := by
  rw [sum_inner]
  simp only [map_sum, inner_sum]
  simp_rw [weightedSlot_pairing_eq_add_error b m mReg, Finset.sum_add_distrib]

private def cutoffSchwartz (c : BoundedSymbol E) (hc : ContDiff ℝ ∞ (c : E → ℂ))
    (hcs : HasCompactSupport (c : E → ℂ)) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  (show HasCompactSupport (fun x => c x * f x) from hcs.mul_right).toSchwartzMap (hc.mul f.smooth')

private theorem cutoffSchwartz_toLp_eq (c : BoundedSymbol E) (hc : ContDiff ℝ ∞ (c : E → ℂ))
    (hcs : HasCompactSupport (c : E → ℂ)) (f : SchwartzMap E ℂ) :
    (cutoffSchwartz c hc hcs f).toLp 2 volume = symbolCLM c (f.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(cutoffSchwartz c hc hcs f).coeFn_toLp 2 volume,
    symbolL2_ae c (f.toLp 2 volume), f.coeFn_toLp 2 volume] with x hx hy hz
  change (cutoffSchwartz c hc hcs f).toLp 2 volume x = symbolL2 c (f.toLp 2 volume) x
  rw [hx, hy, hz]
  rfl

private theorem compactFrequency_after_cutoff_of_supported_weakL2
    (q c : BoundedSymbol E) (R : ℝ)
    (hq : ∀ ξ, ξ ∉ Metric.closedBall (0 : E) R → q ξ = 0)
    (hc : ContDiff ℝ ∞ (c : E → ℂ)) (hcs : HasCompactSupport (c : E → ℂ))
    (K : Set E) (hK : IsCompact K) (f : ℕ → SchwartzMap E ℂ)
    (hfS : ∀ n, tsupport (f n : E → ℂ) ⊆ K)
    (B : ℝ) (hB : ∀ n, ‖(f n).toLp 2 volume‖ ≤ B)
    (hw : ∀ w : ComplexL2 E, Tendsto (fun n => inner ℂ w ((f n).toLp 2 volume)) atTop (𝓝 0)) :
    Tendsto (fun n => fourierMultiplier q (symbolCLM c ((f n).toLp 2 volume))) atTop (𝓝 0) := by
  let F (n : ℕ) := cutoffSchwartz c hc hcs (f n)
  have hEq (n : ℕ) : (F n).toLp 2 volume = symbolCLM c ((f n).toLp 2 volume) :=
    cutoffSchwartz_toLp_eq c hc hcs (f n)
  have hS (n : ℕ) : tsupport (F n : E → ℂ) ⊆ K :=
    tsupport_mul_subset_right.trans (hfS n)
  have hN (n : ℕ) : ‖(F n).toLp 2 volume‖ ≤ c.bound * B := by
    rw [hEq]
    exact (symbolL2_norm_le c ((f n).toLp 2 volume)).trans
      (mul_le_mul_of_nonneg_left (hB n) c.bound_nonneg)
  have hWeak (w : ComplexL2 E) :
      Tendsto (fun n => inner ℂ w ((F n).toLp 2 volume)) atTop (𝓝 0) := by
    have hP (n : ℕ) : inner ℂ w ((F n).toLp 2 volume) =
        inner ℂ (symbolCLM (conjugateSymbol c) w) ((f n).toLp 2 volume) := by
      rw [hEq, inner_symbolCLM_left, conjugateSymbol_conjugateSymbol]
    simpa only [hP] using hw (symbolCLM (conjugateSymbol c) w)
  have hLow := low_frequency_energy_tendsto_zero_of_supported_weakL2 K hK F hS
    (c.bound * B) hN hWeak R
  simpa only [hEq] using fourierMultiplier_schwartz_tendsto_zero q
    Metric.isClosed_closedBall.measurableSet hq F hLow

/-- On the same target fields the commutator error tends to zero. The
regularized multiplier may differ from the angular one in a fixed ball. -/
theorem weightedSlot_sum_pairing_difference_tendsto_zero {I J : Type*} [Fintype I] [Fintype J]
    (b m mReg : BoundedSymbol E) (mSmooth : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (mDegree : DegreeZero (m : E → ℂ)) (R : ℝ)
    (hReg : ∀ ξ, ξ ∉ Metric.closedBall (0 : E) R → mReg ξ = m ξ)
    (a : I → BoundedSymbol E) (c : J → BoundedSymbol E)
    (hc : ∀ j, ContDiff ℝ ∞ (c j : E → ℂ)) (hcs : ∀ j, HasCompactSupport (c j : E → ℂ))
    (K : Set E) (hK : IsCompact K) (u : ℕ → I → ComplexL2 E) (f : ℕ → J → SchwartzMap E ℂ)
    (hfS : ∀ n j, tsupport (f n j : E → ℂ) ⊆ K)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hU : ∀ n i, ‖u n i‖ ≤ B₁)
    (hF : ∀ n j, ‖(f n j).toLp 2 volume‖ ≤ B₂)
    (hw : ∀ j w, Tendsto (fun n => inner ℂ w ((f n j).toLp 2 volume)) atTop (𝓝 0)) :
    Tendsto (fun n =>
      inner ℂ (∑ i, symbolCLM (a i) (u n i))
        (separableOperator b mReg (∑ j, symbolCLM (c j) ((f n j).toLp 2 volume))) -
        ∑ i, ∑ j, inner ℂ (u n i)
          (separableOperator (weightedSlotBaseSymbol b (a i) (c j)) m ((f n j).toLp 2 volume)))
      atTop (𝓝 0) := by
  let e (j : J) (n : ℕ) := weightedSlotFrequencyError m mReg (c j) ((f n j).toLp 2 volume)
  have hE (j : J) : Tendsto (e j) atTop (𝓝 0) := by
    have hComm := cutoffCommutator_tendsto_zero_of_supported_weakL2 m (c j) mSmooth mDegree
      (hc j) (hcs j) K hK (fun n => f n j) (fun n => hfS n j) B₂ (fun n => hF n j) (hw j)
    have hSmall := compactFrequency_after_cutoff_of_supported_weakL2 (symbolDifference mReg m)
      (c j) R (fun ξ hξ => sub_eq_zero.mpr (hReg ξ hξ)) (hc j) (hcs j)
      K hK (fun n => f n j) (fun n => hfS n j) B₂ (fun n => hF n j) (hw j)
    simpa only [e, weightedSlotFrequencyError, add_zero] using hComm.add hSmall
  let Q (i : I) (j : J) (n : ℕ) := inner ℂ (symbolCLM (a i) (u n i)) (symbolCLM b (e j n))
  have hQ (i : I) (j : J) : Tendsto (Q i j) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hLim : Tendsto (fun n => ((a i).bound * B₁ * b.bound) * ‖e j n‖) atTop (𝓝 0) := by
      simpa only [norm_zero, mul_zero] using (hE j).norm.const_mul ((a i).bound * B₁ * b.bound)
    apply squeeze_zero (fun _ => norm_nonneg _) _ hLim
    intro n
    have hL : ‖symbolCLM (a i) (u n i)‖ ≤ (a i).bound * B₁ :=
      (symbolL2_norm_le (a i) (u n i)).trans (mul_le_mul_of_nonneg_left (hU n i) (a i).bound_nonneg)
    calc
      ‖Q i j n‖ ≤ ‖symbolCLM (a i) (u n i)‖ * ‖symbolCLM b (e j n)‖ := norm_inner_le_norm _ _
      _ ≤ ((a i).bound * B₁) * (b.bound * ‖e j n‖) := mul_le_mul hL
        (symbolL2_norm_le b (e j n)) (norm_nonneg _) (mul_nonneg (a i).bound_nonneg hB₁)
      _ = _ := (mul_assoc _ _ _).symm
  have hSum (i : I) : Tendsto (fun n => ∑ j, Q i j n) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun j _ => hQ i j)
  have hAll : Tendsto (fun n => ∑ i, ∑ j, Q i j n) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun i _ => hSum i)
  apply hAll.congr
  intro n
  rw [weightedSlot_sum_pairing_eq_add_error]
  exact (add_sub_cancel_left _ _).symm

theorem normalizedAngularSymbol_eq_outside_ball (m : BoundedSymbol E) (ξ : E)
    (h : ξ ∉ Metric.closedBall (0 : E) 2) :
    normalizedAngularSymbol m ξ = m ξ := by
  have hξ : 2 ≤ ‖ξ‖ := (lt_of_not_ge (by simpa only [Metric.mem_closedBall, dist_zero_right] using h)).le
  change ((1 : ℂ) - (radialCore ((1 : ℝ) • ξ) : ℂ)) * m ξ = m ξ
  simp only [one_smul, radialCore_eq_zero ξ hξ, Complex.ofReal_zero, sub_zero, one_mul]

end Burnett.Microlocal.Overlap
