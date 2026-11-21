import Burnett.Analysis.CubicEnergy.CompleteEnergy.SymbolSeminormLow
import Burnett.Analysis.CubicEnergy.JointMultiplier.MikhlinPartition

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Metric Set
open scoped ContDiff

private def referenceAnnulus : Set E := {ξ | 1/2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2}

private theorem annulus_closed : IsClosed referenceAnnulus :=
  (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)

private theorem annulus_compact : IsCompact referenceAnnulus :=
  (isCompact_closedBall (0 : E) 2).of_isClosed_subset annulus_closed
    (fun x hx => by simpa only [mem_closedBall, dist_zero_right] using hx.2)

private theorem annulus_nonzero : referenceAnnulus ⊆ {x : E | x ≠ 0} := by
  intro x hx
  exact norm_pos_iff.mp ((by norm_num : 0 < (1 : ℝ)/2).trans_le hx.1)

/-- The original scalar Mikhlin profile has uniformly controlled joint pointwise
and integrated derivative bounds of every fixed order. The input seminorm uses
derivatives on the unit sphere of the uncut homogeneous symbol. -/
theorem mikhlin_profile_derivative_bound (d N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : E → ℝ), ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ ξ, m (t • ξ) = t^d * m ξ) → ∀ (D : ℝ), 0 ≤ D →
      (∀ n : ℕ, n ≤ N → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n m ξ‖ ≤ D) →
      ∀ (a : SchwartzMap E ℂ), (∀ ξ, a ξ = ((mikhlinWindow ξ * m ξ : ℝ) : ℂ)) →
      (∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) →
      ∀ i : ℕ, i ≤ N →
        (∀ ξ, ‖iteratedFDeriv ℝ i (a : E → ℂ) ξ‖ ≤ C * D) ∧
        (∫ ξ, ‖iteratedFDeriv ℝ i (a : E → ℂ) ξ‖) ≤ C * D := by
  let U : Set E := {x | x ≠ 0}
  have UOpen : IsOpen U := isClosed_singleton.isOpen_compl
  have smoothCut : ContDiff ℝ ∞ mikhlinWindow :=
    mikhlinBall.contDiff.sub (mikhlinBall.contDiff.comp (contDiff_const.smul contDiff_id))
  obtain ⟨K, K0, cutoff⟩ := compact_derivative_bound N annulus_compact UOpen annulus_nonzero _
    smoothCut.contDiffOn
  obtain ⟨L, L0, annulus⟩ := symbol_sphere_jet_to_annulus (X := E) d N (1/2) 2 (by norm_num) (by norm_num)
  let A := (2 : ℝ)^N * K * L
  let W := max 1 (volume.real referenceAnnulus)
  have A0 : 0 ≤ A := mul_nonneg (mul_nonneg (by positivity) K0) L0
  have W1 : 1 ≤ W := le_max_left _ _
  refine ⟨A * W, mul_nonneg A0 (zero_le_one.trans W1), ?_⟩
  intro m hm hom D D0 mass a shape cut i hi
  have order : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have support : tsupport (a : E → ℂ) ⊆ referenceAnnulus :=
    closure_minimal (fun ξ hx => ⟨(cut ξ hx).1.le, (cut ξ hx).2.le⟩) annulus_closed
  let g := fun ξ => ‖iteratedFDeriv ℝ i (a : E → ℂ) ξ‖
  have zero (ξ : E) (hx : ξ ∉ referenceAnnulus) : g ξ = 0 := by
    have outside : ξ ∉ tsupport (iteratedFDeriv ℝ i (a : E → ℂ)) :=
      fun h => hx (support (tsupport_iteratedFDeriv_subset i h))
    simp only [g, image_eq_zero_of_notMem_tsupport outside, norm_zero]
  have localBound (ξ : E) (hx : ξ ∈ referenceAnnulus) : g ξ ≤ A * D := by
    let f := fun x => mikhlinWindow x * m x
    have eq : (a : E → ℂ) = Complex.ofRealLI ∘ f := funext shape
    have smooth : ContDiffAt ℝ ∞ f ξ :=
      smoothCut.contDiffAt.mul (hm.contDiffAt (UOpen.mem_nhds (annulus_nonzero hx)))
    dsimp only [g]
    rw [eq, Complex.ofRealLI.norm_iteratedFDeriv_comp_left smooth order]
    have bound := product_jet_bound UOpen smoothCut.contDiffOn hm (annulus_nonzero hx) hi K0 (mul_nonneg L0 D0)
      (fun n hn => cutoff n hn ξ hx) (fun n hn => annulus m hm hom D D0 mass n hn ξ hx.1 hx.2)
    exact bound.trans_eq (mul_assoc ..).symm
  constructor
  · intro ξ
    change g ξ ≤ A * W * D
    by_cases h : ξ ∈ referenceAnnulus
    · exact (localBound ξ h).trans (mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right A0 W1) D0)
    · rw [zero ξ h]
      exact mul_nonneg (mul_nonneg A0 (zero_le_one.trans W1)) D0
  · change (∫ ξ, g ξ) ≤ A * W * D
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero zero]
    have b := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure E)) (f := g)
      annulus_compact.measure_lt_top
      (fun ξ h => by simpa only [g, Real.norm_of_nonneg (norm_nonneg _)] using localBound ξ h)
    have pos : 0 ≤ ∫ ξ in referenceAnnulus, g ξ := integral_nonneg (fun _ => norm_nonneg _)
    rw [Real.norm_of_nonneg pos] at b
    have scaled : (A * D) * volume.real referenceAnnulus ≤ (A * D) * W :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (mul_nonneg A0 D0)
    exact b.trans (scaled.trans_eq (mul_right_comm A D W))

end Burnett.A02.FrequencySplit
