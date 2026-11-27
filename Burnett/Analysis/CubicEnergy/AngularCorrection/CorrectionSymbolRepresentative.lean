import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalAngularPairing

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.A08

open Filter MeasureTheory Metric Set Burnett.A06 Burnett.A07 Burnett.A02.FrequencySplit

open private ae_lowFrequency_ne_zero exists_norm_bound_on_nonnegative_of_tail_const
  from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalAngularPairing

/-- Off the null-measure low-frequency axis, the actual symbol uses only
values on the compact independent-variable profile domain. -/
theorem exists_borelOriginalRegularizedAngularSymbol
    (η χ : ℝ → ℝ) {ρ R : ℝ} (hρ : 0 ≤ ρ)
    (hη : Continuous η) (hone : ∀ x ≥ R, η x = 1)
    (hχ : Continuous χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0)
    {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)}
    (hK : (closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1) ×ˢ sphere (0 : RotationSpace) 1 ⊆ W)
    (hF : ContinuousOn F W) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z ∈ (closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1) ×ˢ sphere (0 : RotationSpace) 1,
      ‖F z‖ ≤ M) :
    ∃ (b : Joint → ℂ) (B : ℝ), 0 ≤ B ∧ Measurable b ∧
      (∀ p, ‖b p‖ ≤ B * (1 + ‖p.1‖ + ‖p.2‖)) ∧
      b =ᵐ[volume] originalRegularizedAngularSymbol η χ F := by
  classical
  obtain ⟨U,hU⟩ := exists_norm_bound_on_nonnegative_of_tail_const hη R 1 hone
  obtain ⟨V,hV⟩ := exists_norm_bound_on_nonnegative_of_tail_const hχ (ρ^2) 0 hcut
  have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU 0 le_rfl)
  have hV0 : 0 ≤ V := (norm_nonneg _).trans (hV 0 le_rfl)
  let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
  let K := Q ×ˢ sphere (0 : RotationSpace) 1
  let F₀ := K.piecewise F (fun _ => 0)
  let z (p : Joint) := normalizedHighPair p
  let coord (p : Joint) := (z p, roundSphereRadialNormalize p.1)
  let a (p : Joint) := η ‖p.2‖ * ‖p.2‖ * χ (‖(z p).1‖^2)
  let b (p : Joint) := a p • F₀ (coord p)
  have hMeasK : MeasurableSet K :=
    (measurableSet_closedBall.prod isClosed_sphere.measurableSet).prod isClosed_sphere.measurableSet
  have hMeasF : Measurable F₀ := (hF.mono hK).measurable_piecewise continuousOn_const hMeasK
  have hMeasZ : Measurable z := by
    exact (measurable_snd.norm.inv.smul measurable_fst).prodMk
      (measurable_snd.norm.inv.smul measurable_snd)
  have hMeasCoord : Measurable coord :=
    hMeasZ.prodMk ((measurable_norm.inv.smul measurable_id).comp measurable_fst)
  have hMeasA : Measurable a :=
    ((hη.measurable.comp measurable_snd.norm).mul measurable_snd.norm).mul
      (hχ.measurable.comp ((measurable_fst.comp hMeasZ).norm.pow_const _))
  refine ⟨b, U*V*M, by positivity, hMeasA.smul (hMeasF.comp hMeasCoord), ?_, ?_⟩
  · intro p
    have hF₀ : ‖F₀ (coord p)‖ ≤ M := by
      by_cases hz : coord p ∈ K
      · simpa only [F₀, piecewise_eq_of_mem K F (fun _ => 0) hz] using hbound (coord p) hz
      · simp only [F₀, piecewise_eq_of_notMem K F (fun _ => 0) hz, norm_zero]
        exact hM
    change ‖a p • F₀ (coord p)‖ ≤ _
    simp only [norm_smul, a, norm_mul, norm_norm]
    calc
      _ ≤ U * ‖p.2‖ * V * M := by
        gcongr
        · exact hU _ (norm_nonneg _)
        · exact hV _ (by positivity)
      _ ≤ U * V * M * (1 + ‖p.1‖ + ‖p.2‖) := by
        rw [show U * ‖p.2‖ * V * M = U*V*M*‖p.2‖ by ring]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
  · filter_upwards [ae_lowFrequency_ne_zero] with p hp
    have original : originalRegularizedAngularSymbol η χ F p = a p • F (coord p) := by
      simp only [originalRegularizedAngularSymbol, regularizedLowCartesianSymbol, lowCartesianSymbol,
        smul_smul, a, coord, z, mul_assoc]
    rw [original]
    change a p • F₀ (coord p) = _
    by_cases ha : a p = 0
    · simp only [ha, zero_smul]
    · have hq : p.2 ≠ 0 := by intro h; exact ha (by simp [a, h])
      have hχ₀ : χ (‖(z p).1‖ ^ 2) ≠ 0 := by intro h; exact ha (by simp [a, h])
      have hpρ : ‖(z p).1‖ ≤ ρ := by
        by_contra! h
        exact hχ₀ (hcut _ (pow_le_pow_left₀ hρ h.le 2))
      have hpt : coord p ∈ K := ⟨
        ⟨mem_closedBall_zero_iff.mpr hpρ, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℝ) hq)⟩,
        mem_sphere_zero_iff_norm.mpr (roundSphereRadialNormalize_norm hp)⟩
      simp only [F₀, piecewise_eq_of_mem K F (fun _ => 0) hpt]

theorem radianHighPair_congr_ae_symbol {b c : Joint → ℂ}
    (h : b =ᵐ[volume] c) (H u w : E → ℂ) :
    radianHighPair b H u w = radianHighPair c H u w := by
  unfold radianHighPair
  congr 1
  apply integral_congr_ae
  filter_upwards [h] with p hp
  simp only [radianHighPairWeight, hp]

theorem radianHighCommutatorPair_congr_ae_symbol {b c : Joint → ℂ}
    (h : b =ᵐ[volume] c) (d : E → ℝ) (H u w : E → ℂ) :
    radianHighCommutatorPair b d H u w = radianHighCommutatorPair c d H u w := by
  simp only [radianHighCommutatorPair, radianHighPair_congr_ae_symbol h]

end Burnett.A08
