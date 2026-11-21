import Burnett.Analysis.CubicEnergy.JointMultiplier.SymbolSeminormSphere
import Burnett.Analysis.CubicEnergy.CompleteEnergy.SymbolSeminormIntegral

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Metric Set Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped ContDiff Interval Topology

def lowJetSafe : Set Freq8 := {u | 2 * ‖(splitFreq u).1‖ < ‖(splitFreq u).2‖}

theorem lowJetSafe_open : IsOpen lowJetSafe :=
  isOpen_lt (continuous_const.mul (continuous_fst.comp splitFreq.continuous).norm)
    (continuous_snd.comp splitFreq.continuous).norm

private def atTime (t : ℝ) : Freq8 →L[ℝ] E :=
  ((ContinuousLinearMap.snd ℝ E E) + t • ContinuousLinearMap.fst ℝ E E).comp
    splitFreq.toContinuousLinearMap

private theorem atTime_apply (t : ℝ) (u : Freq8) :
    atTime t u = (splitFreq u).2 + t • (splitFreq u).1 := rfl

private theorem atTime_nonzero {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) {u : Freq8} (hu : u ∈ lowJetSafe) :
    atTime t u ≠ 0 := by
  rw [atTime_apply]
  intro h
  have hn := congrArg norm (eq_neg_of_add_eq_zero_left h)
  rw [norm_neg, norm_smul, Real.norm_eq_abs] at hn
  exact (not_le_of_gt hu) (hn.trans_le (mul_le_mul_of_nonneg_right (abs_lt.mpr ht).le (norm_nonneg _)))

private abbrev forwardNorm : ℝ := max 1 ‖splitFreq.toContinuousLinearMap‖
private abbrev inverseNorm : ℝ := 1 + ‖splitFreq.symm.toContinuousLinearMap‖

private theorem atTime_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖atTime t‖ ≤ 2 * forwardNorm := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by unfold forwardNorm; positivity)
  intro u
  have h : ‖splitFreq u‖ ≤ forwardNorm * ‖u‖ :=
    (splitFreq.toContinuousLinearMap.le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) _) (norm_nonneg u))
  have h₁ : ‖(splitFreq u).1‖ ≤ forwardNorm * ‖u‖ :=
    (le_max_left _ _).trans (by simpa only [Prod.norm_def] using h)
  have h₂ : ‖(splitFreq u).2‖ ≤ forwardNorm * ‖u‖ :=
    (le_max_right _ _).trans (by simpa only [Prod.norm_def] using h)
  rw [atTime_apply]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  linarith [mul_le_mul_of_nonneg_right ht.2 (norm_nonneg (splitFreq u).1)]

private theorem atTime_annulus {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {u : Freq8} (hu : u ∈ lowJetSafe)
    (un : ‖u‖ = 1) : 1 / (2 * inverseNorm) ≤ ‖atTime t u‖ ∧ ‖atTime t u‖ ≤ 2 * forwardNorm := by
  constructor
  · change 2 * ‖(splitFreq u).1‖ < ‖(splitFreq u).2‖ at hu
    have hp : ‖(splitFreq u).1‖ ≤ ‖(splitFreq u).2‖ := by
      linarith [norm_nonneg (splitFreq u).1]
    have hInv : 1 ≤ inverseNorm * ‖(splitFreq u).2‖ := by
      calc
        1 = ‖splitFreq.symm (splitFreq u)‖ := by rw [ContinuousLinearEquiv.symm_apply_apply, un]
        _ ≤ ‖splitFreq.symm.toContinuousLinearMap‖ * ‖splitFreq u‖ :=
          splitFreq.symm.toContinuousLinearMap.le_opNorm _
        _ ≤ inverseNorm * ‖(splitFreq u).2‖ := by
          rw [Prod.norm_def, max_eq_right hp]
          exact mul_le_mul_of_nonneg_right (by unfold inverseNorm; linarith) (norm_nonneg _)
    have hpos : 0 < inverseNorm := by unfold inverseNorm; positivity
    have hξ : 1 / inverseNorm ≤ ‖(splitFreq u).2‖ :=
      (div_le_iff₀ hpos).mpr (by simpa only [mul_comm] using hInv)
    have hl := norm_sub_le ((splitFreq u).2 + t • (splitFreq u).1) (t • (splitFreq u).1)
    rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hl
    rw [atTime_apply, div_mul_eq_div_div_swap]
    linarith [mul_le_mul_of_nonneg_right ht.2 (norm_nonneg (splitFreq u).1)]
  · calc
      _ ≤ ‖atTime t‖ * ‖u‖ := (atTime t).le_opNorm u
      _ ≤ _ := by rw [un, mul_one]; exact atTime_bound ht

private theorem segment_smooth (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (j : Index) : ContDiffOn ℝ ∞
      (fun z : Freq8 × ℝ => fderiv ℝ b (atTime z.2 z.1) (coordinateBasis j))
      (lowJetSafe ×ˢ Ioo (-2 : ℝ) 2) := by
  have ho : IsOpen {x : E | x ≠ 0} := isClosed_singleton.isOpen_compl
  have hs : ContDiff ℝ ∞ (fun z : Freq8 × ℝ => atTime z.2 z.1) := by
    simp only [atTime_apply]
    exact (contDiff_snd.comp (splitFreq.contDiff.comp contDiff_fst)).add
      (contDiff_snd.smul (contDiff_fst.comp (splitFreq.contDiff.comp contDiff_fst)))
  exact ((hb.fderiv_of_isOpen ho (by simp)).comp hs.contDiffOn
    (fun z hz => atTime_nonzero hz.2 hz.1)).clm_apply contDiffOn_const

theorem low_derivative_average_contDiffOn (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (j : Index) : ContDiffOn ℝ ∞ (fun u => derivComponent b j (splitFreq u).1 (splitFreq u).2)
      lowJetSafe :=
  SymbolSeminorm.interval_average_contDiffOn lowJetSafe_open _ (segment_smooth b hb j)

/-- The uncut low-frequency average uses at most one extra derivative of the original
degree-one symbol on the unit sphere. The annular bounds are uniform in the time
parameter and the two input frequencies at every point of the safe unit region. -/
theorem low_derivative_average_jet (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ (s : ℝ), 0 < s → ∀ x, b (s • x) = s * b x) → ∀ (D : ℝ), 0 ≤ D →
      (∀ i : ℕ, i ≤ N+1 → ∀ x ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ i b x‖ ≤ D) →
      ∀ (j : Index) (i : ℕ), i ≤ N → ∀ u ∈ sphere (0 : Freq8) 1, u ∈ lowJetSafe →
      ‖iteratedFDeriv ℝ i (fun w => derivComponent b j (splitFreq w).1 (splitFreq w).2) u‖ ≤ K * D := by
  have normTwo : 1 ≤ 2 * forwardNorm := by
    have h : (1 : ℝ) ≤ forwardNorm := le_max_left _ _
    linarith
  obtain ⟨K, K0, ringBound⟩ := symbol_sphere_jet_to_annulus (X := E) 1 (N+1)
    (1 / (2 * inverseNorm)) (2 * forwardNorm) (by unfold inverseNorm; positivity)
    (zero_le_one.trans normTwo)
  refine ⟨K * (2 * forwardNorm)^N, mul_nonneg K0 (pow_nonneg (zero_le_one.trans normTwo) _), ?_⟩
  intro b hb hom D D0 sphereBound j i hi u un uSafe
  let U : Set E := {x | x ≠ 0}
  have UOpen : IsOpen U := isClosed_singleton.isOpen_compl
  let G := fun x : E => fderiv ℝ b x (coordinateBasis j)
  have hsG : ContDiffOn ℝ ∞ G U := (hb.fderiv_of_isOpen UOpen (by simp)).clm_apply contDiffOn_const
  have hhom : ∀ (s : ℝ), 0 < s → ∀ x, b (s • x) = s^1 * b x := by simpa only [pow_one] using hom
  have stepOrder : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have scaleNorm : ‖u‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using un
  apply SymbolSeminorm.interval_jet_norm_le i lowJetSafe_open
    (fun z : Freq8 × ℝ => G (atTime z.2 z.1)) (segment_smooth b hb j) u uSafe _
  intro t ht
  have ht' : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hx : atTime t u ∈ U := atTime_nonzero ht' uSafe
  have AOpen : IsOpen (atTime t ⁻¹' U) := UOpen.preimage (atTime t).continuous
  have e := (atTime t).iteratedFDerivWithin_comp_right hsG UOpen.uniqueDiffOn
    AOpen.uniqueDiffOn (x := u) hx stepOrder
  rw [iteratedFDerivWithin_of_isOpen i AOpen (show u ∈ atTime t ⁻¹' U from hx),
    iteratedFDerivWithin_of_isOpen i UOpen hx] at e
  have chain : ‖iteratedFDeriv ℝ i (G ∘ atTime t) u‖ ≤
      ‖iteratedFDeriv ℝ i G (atTime t u)‖ * ‖atTime t‖^i := by
    rw [e]
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (iteratedFDeriv ℝ i G (atTime t u)).norm_compContinuousLinearMap_le (fun _ => atTime t)
  obtain ⟨lower, upper⟩ := atTime_annulus ht uSafe scaleNorm
  have fieldBound : ‖iteratedFDeriv ℝ i G (atTime t u)‖ ≤ K * D := by
    have derivativeSmooth : ContDiffOn ℝ ∞ (fderiv ℝ b) U := hb.fderiv_of_isOpen UOpen (by simp)
    have diff := derivativeSmooth.contDiffAt (UOpen.mem_nhds hx)
    have act := norm_iteratedFDeriv_clm_apply_const (c := coordinateBasis j) diff stepOrder
    have basisNorm : ‖coordinateBasis j‖ = 1 := by
      simpa only [coordinateBasis, OrthonormalBasis.coe_toBasis] using
        (EuclideanSpace.basisFun Index ℝ).orthonormal.norm_eq_one j
    rw [basisNorm, one_mul, norm_iteratedFDeriv_fderiv] at act
    exact act.trans (ringBound b hb hhom D D0 sphereBound (i+1) (by omega) _ lower upper)
  have power : ‖atTime t‖^i ≤ (2 * forwardNorm)^N :=
    (pow_le_pow_left₀ (norm_nonneg _) (atTime_bound ht) i).trans (pow_le_pow_right₀ normTwo hi)
  have product := mul_le_mul fieldBound power (pow_nonneg (norm_nonneg _) _) (mul_nonneg K0 D0)
  exact chain.trans (product.trans_eq (by ring))

end Burnett.A02.FrequencySplit
