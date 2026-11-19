import Burnett.Analysis.CubicEnergy.JointMultiplier.SymbolSeminormDecay
import Burnett.Analysis.CubicEnergy.JointMultiplier.AnnularBound

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory Metric Set Filter
open scoped ContDiff FourierTransform

def symbolReferenceShell : Set Freq8 := {ξ | 1/2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2}

private theorem shell_closed : IsClosed symbolReferenceShell :=
  (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)

private theorem shell_compact : IsCompact symbolReferenceShell :=
  (isCompact_closedBall (0:Freq8) 2).of_isClosed_subset shell_closed
    (fun ξ h => by simpa only [mem_closedBall,dist_zero_right] using h.2)

/-- The closed reference shell controls derivatives as well as values for
the actual compact annular cutoff, including the two boundary spheres. -/
theorem symbolBlock_reference_support (m : Joint → ℝ) :
    tsupport (fun ξ => symbolBlock m (splitFreq ξ)) ⊆ symbolReferenceShell := by
  apply closure_minimal _ shell_closed
  intro ξ hξ
  by_contra bad
  have h : ‖ξ‖ < 1/2 ∨ 2 < ‖ξ‖ := by
    change ¬(1/2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2) at bad
    by_cases l : 1/2 ≤ ‖ξ‖
    · exact Or.inr (lt_of_not_ge fun r => bad ⟨l,r⟩)
    · exact Or.inl (lt_of_not_ge l)
  have disk (z : Freq8) (hz : ‖z‖ ≤ 1) : ballWindow z = 1 :=
    ballWindow.one_of_mem_closedBall (by simpa only [mem_closedBall,dist_zero_right] using hz)
  have ext (z : Freq8) (hz : 2 ≤ ‖z‖) : ballWindow z = 0 :=
    ballWindow.zero_of_le_dist (by simpa only [dist_zero_right] using hz)
  have nd : ‖(2:ℝ) • ξ‖ = 2*‖ξ‖ := by rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
  have mask : annularWindow ξ = 0 := by
    rcases h with l|r
    · rw [annularWindow,disk _ (by linarith),disk _ (by rw [nd]; linarith),sub_self]
    · rw [annularWindow,ext _ r.le,ext _ (by rw [nd]; linarith),sub_self]
  exact hξ (by simp [symbolBlock,mask])

private theorem derivative_mass (A : SchwartzMap Freq8 ℂ) (hs : tsupport (A : Freq8 → ℂ) ⊆ symbolReferenceShell)
    (i : ℕ) (D : ℝ) (hD : ∀ ξ ∈ symbolReferenceShell, ‖iteratedFDeriv ℝ i (A : Freq8 → ℂ) ξ‖ ≤ D) :
    (∫ ξ, ‖iteratedFDeriv ℝ i (A : Freq8 → ℂ) ξ‖) ≤ D*(volume.real symbolReferenceShell) := by
  let g := fun ξ => ‖iteratedFDeriv ℝ i (A : Freq8 → ℂ) ξ‖
  have zero (ξ : Freq8) (hξ : ξ ∉ symbolReferenceShell) : g ξ = 0 := by
    have nn : ξ ∉ tsupport (iteratedFDeriv ℝ i (A : Freq8 → ℂ)) := fun h => hξ (hs (tsupport_iteratedFDeriv_subset i h))
    simp only [g,image_eq_zero_of_notMem_tsupport nn,norm_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero zero]
  have b := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure Freq8)) (f := g) shell_compact.measure_lt_top
    (fun ξ h => by simpa only [g,Real.norm_of_nonneg (norm_nonneg _)] using hD ξ h)
  have pos : 0 ≤ ∫ ξ in symbolReferenceShell, g ξ := integral_nonneg (fun _ => norm_nonneg _)
  simpa only [Real.norm_of_nonneg pos, mul_comm] using b

/-- Uniform bound on the actual split kernel from sup bounds on the reference
shell. No derivative condition is required at the origin. -/
theorem symbolBlock_mixed_moment_finite_derivatives (j k : ℕ) : ∃ C : ℝ, 0≤C ∧
    ∀ (m : Joint → ℝ) (_hm : ContDiffOn ℝ ∞ m {z | z ≠ 0}) (D : ℝ), 0≤D →
      (∀ i : ℕ, i≤j+k+9 → ∀ ξ ∈ symbolReferenceShell,
        ‖iteratedFDeriv ℝ i (fun u => symbolBlock m (splitFreq u)) ξ‖ ≤ D) →
      (∫ y : Joint, (1+‖y.1‖)^j*(1+‖y.2‖)^k*‖blockKernel (symbolBlock m) y‖) ≤ C*D := by
  obtain ⟨K,hK,dec⟩ := symbol_inverse_weighted_L1 (j+k)
  let v := volume.real symbolReferenceShell
  have vn : 0≤v := ENNReal.toReal_nonneg
  refine ⟨K*v,mul_nonneg hK vn,?_⟩
  intro m hm D hd der
  obtain ⟨hc,hs⟩ := symbolBlock_regular m hm
  let a := symbolBlock m
  let A : SchwartzMap Freq8 ℂ :=
    (hc.comp_homeomorph splitFreq.toHomeomorph).toSchwartzMap (hs.comp splitFreq.contDiff)
  have cut : tsupport (A : Freq8 → ℂ) ⊆ symbolReferenceShell := symbolBlock_reference_support m
  have b (i : ℕ) (hi : i≤j+k+9) : (∫ ξ, ‖iteratedFDeriv ℝ i (A : Freq8 → ℂ) ξ‖) ≤ D*v :=
    derivative_mass A cut i D (der i hi)
  let F := fun u : Freq8 => (1+‖u‖)^(j+k)*‖𝓕⁻ (A : Freq8 → ℂ) u‖
  let H := fun y : Joint => (1+‖y.1‖)^j*(1+‖y.2‖)^k*‖blockKernel a y‖
  have moment : (∫ u, F u) ≤ K*(D*v) := dec A (D*v) (mul_nonneg hd vn) b
  have bound (u : Freq8) : H (splitFreq u) ≤ F u := by
    have e := splitFreq_inner u u
    simp only [real_inner_self_eq_norm_sq] at e
    have left : ‖(splitFreq u).1‖ ≤ ‖u‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith only [e,sq_nonneg ‖(splitFreq u).2‖])
    have right : ‖(splitFreq u).2‖ ≤ ‖u‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith only [e,sq_nonneg ‖(splitFreq u).1‖])
    have e' : blockKernel a (splitFreq u) = 𝓕⁻ (A : Freq8 → ℂ) u := by simp only [blockKernel,ContinuousLinearEquiv.symm_apply_apply]; rfl
    dsimp only [H,F]; rw [e',pow_add]
    gcongr
  have iH := splitFreq_preserves_volume.integrable_comp_of_integrable (blockKernel_mixed_moment a hc hs j k)
  have iF : Integrable F := by
    let G := (SchwartzMap.fourierTransformCLE ℂ).symm A
    have e : (G : Freq8 → ℂ) = 𝓕⁻ (A : Freq8 → ℂ) := SchwartzMap.fourierTransformCLE_symm_apply _ _
    have addb (r : ℝ) (hr : 0≤r) (n : ℕ) : (1+r)^n ≤ 2^n * (1+r^n) := by
      by_cases h : r≤1
      · exact (pow_le_pow_left₀ (by positivity : 0≤1+r) (by linarith : 1+r≤2) n).trans
          (le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hr n]))
      · calc
          _ ≤ (2*r)^n := by gcongr; linarith
          _ = 2^n*r^n := mul_pow ..
          _ ≤ _ := by gcongr; linarith
    have dom := (G.integrable.norm.add (G.integrable_pow_mul volume (j+k))).const_mul ((2:ℝ)^(j+k))
    change Integrable (fun u : Freq8 => (1+‖u‖)^(j+k)*‖𝓕⁻ (A : Freq8 → ℂ) u‖)
    rw [← e]
    refine dom.mono' (by fun_prop) (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_right (addb _ (norm_nonneg u) _) (norm_nonneg (G u))).trans_eq (by dsimp; ring)
  change (∫ y, H y) ≤ _
  rw [← splitFreq_preserves_volume.integral_comp splitFreq.toHomeomorph.measurableEmbedding H]
  exact (integral_mono iH iF bound).trans (moment.trans_eq (by ring))

end Burnett.A02.FrequencySplit
