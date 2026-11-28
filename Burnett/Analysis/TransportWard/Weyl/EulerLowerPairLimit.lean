import Burnett.Analysis.TransportWard.Weyl.UniformEulerJetBounds
import Burnett.Analysis.PrincipalEnergy.Energy.CompactSchwartzDomain

/-! The lower Euler remainder in fixed-window Lebesgue pairings. -/

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.V03

open Filter MeasureTheory Set Burnett.Analysis.CarlesonEmbedding Burnett.Analysis.TransportWardSymbol
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace Matrix.Norms.Elementwise Topology

/-- A uniform local bound on the real lower remainder, paired with any
uniformly L²-bounded test, gives the required local imaginary limit.
The estimate is for the entire complex pairing. -/
theorem tendsto_metricEulerJetLowerRemainder_window_pair
    {ι : Type*} [Fintype ι] (S : ι → Mat) {K : Set Mat}
    (hK : IsCompact K) (hKdet : K ⊆ nonsingularMetricDomain)
    {W : Set Space} (hW : IsCompact W)
    (G : Space → Mat) (H : ℕ → Space → Mat)
    (p : Space → ActionSlot ι → ℝ) (dp : ℕ → Space → ActionSlot ι → ℝ)
    (q : Space → Fin 4 → ActionSlot ι → ℝ)
    (hseg : ∀ n, ∀ x ∈ W, ∀ t ∈ Icc (0 : ℝ) 1, fieldSegment (G x) (H n x) t ∈ K)
    (ε : ℕ → ℝ) (he : ∀ n, 0 ≤ ε n) (hsmall : ∀ n, ∀ x ∈ W, ‖H n x‖ ≤ ε n)
    (hlim : Tendsto ε atTop (𝓝 0))
    (P D Q : ℝ) (hP : 0 ≤ P) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hp : ∀ x ∈ W, ∀ s, ‖p x s‖ ≤ P) (hdp : ∀ n, ∀ x ∈ W, ∀ s, ‖dp n x s‖ ≤ D)
    (hq : ∀ x ∈ W, ∀ a s, ‖q x a s‖ ≤ Q)
    (L : ℕ → ι → Space → ℂ)
    (hl : ∀ n i, MemLp (L n i) 2 volume)
    (T : ℝ) (hT : 0 ≤ T) (hlT : ∀ n i, ‖(hl n i).toLp (L n i)‖ ≤ T)
    (hMeas : ∀ n i, AEStronglyMeasurable (fun x =>
      (metricEulerJetLowerRemainder S (G x) (H n x) (p x) (dp n x) (q x) i : ℂ))
      ((volume : Measure Space).restrict W)) :
    Tendsto (fun n => ∑ i, ∫ x in W, conj (L n i x) *
      (metricEulerJetLowerRemainder S (G x) (H n x) (p x) (dp n x) (q x) i : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨M,hM,estimate⟩ := exists_metricEulerJetLowerRemainder_uniform_bounds S hK hKdet
  let nS : ℝ := Fintype.card (ActionSlot ι)
  let Z (n : ℕ) := nS^2 *
      (M * (ε n)^3 * P^2 + 2 * (M * (ε n)^2) * P * D + M * ε n * D^2) +
        (4 * nS) * (M * (ε n)^3 * Q)
  have hZ (n : ℕ) : 0 ≤ Z n := by have hn := he n; dsimp [Z, nS]; positivity
  have zlim : Tendsto Z atTop (𝓝 0) := by
    have t₁ := ((hlim.pow 3).const_mul M).mul_const (P^2)
    have t₂ := ((((hlim.pow 2).const_mul M).const_mul 2).mul_const P).mul_const D
    have t₃ := (hlim.const_mul M).mul_const (D^2)
    have t₄ := (((hlim.pow 3).const_mul M).mul_const Q).const_mul (4*nS)
    simpa only [Z, zero_pow (show 2 ≠ 0 by decide), zero_pow (show 3 ≠ 0 by decide),
      zero_mul, mul_zero, add_zero] using (((t₁.add t₂).add t₃).const_mul (nS^2)).add t₄
  let μ : Measure Space := volume.restrict W
  have hμ : μ Set.univ < ⊤ := by simpa [μ] using hW.measure_lt_top (μ := (volume : Measure Space))
  letI : IsFiniteMeasure μ := ⟨hμ⟩
  let V := ((μ Set.univ) ^ ((2 : ℝ≥0∞).toReal⁻¹)).toReal
  let r (n : ℕ) (i : ι) (x : Space) :=
    (metricEulerJetLowerRemainder S (G x) (H n x) (p x) (dp n x) (q x) i : ℂ)
  have hrB (n : ℕ) (i : ι) : ∀ᵐ x ∂μ, ‖r n i x‖ ≤ Z n := by
    apply (ae_restrict_iff' hW.measurableSet).mpr
    filter_upwards with x hx
    simpa only [r, Complex.norm_real] using
      (estimate (G x) (H n x) (p x) (dp n x) (q x) i (hseg n x hx) (hp x hx) (hdp n x hx) (hq x hx)).trans
        (show _ ≤ Z n by dsimp only [Z, nS]; gcongr <;> exact hsmall n x hx)
  have hr (n : ℕ) (i : ι) : MemLp (r n i) 2 μ := MemLp.of_bound (hMeas n i) (Z n) (hrB n i)
  have hlμ (n : ℕ) (i : ι) : MemLp (L n i) 2 μ := (hl n i).mono_measure Measure.restrict_le_self
  have pairB (n : ℕ) (i : ι) : ‖∫ x, conj (L n i x) * r n i x ∂μ‖ ≤ T * (V * Z n) := by
    have pair : ⟪(hlμ n i).toLp (L n i), (hr n i).toLp (r n i)⟫_ℂ =
        ∫ x, conj (L n i x) * r n i x ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hlμ n i).coeFn_toLp, (hr n i).coeFn_toLp] with x hx hy
      rw [hx, hy, RCLike.inner_apply']
    have hl' : ‖(hlμ n i).toLp (L n i)‖ ≤ T := by
      refine (show ‖(hlμ n i).toLp (L n i)‖ ≤ ‖(hl n i).toLp (L n i)‖ from ?_).trans (hlT n i)
      simp only [Lp.norm_toLp]
      exact ENNReal.toReal_mono (hl n i).eLpNorm_ne_top
        (eLpNorm_mono_measure _ Measure.restrict_le_self)
    have hr' : ‖(hr n i).toLp (r n i)‖ ≤ V * Z n := by
      have htop : μ Set.univ ^ ((2 : ℝ≥0∞).toReal⁻¹) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by positivity) hμ.ne
      rw [Lp.norm_toLp, ← ENNReal.toReal_ofReal (hZ n), ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top htop ENNReal.ofReal_ne_top)
        (eLpNorm_le_of_ae_bound (hrB n i))
    rw [← pair]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul hl' hr' (norm_nonneg _) hT)
  apply squeeze_zero_norm (a := fun n => (Fintype.card ι : ℝ) * (T * (V * Z n)))
  · intro n
    calc
      _ ≤ ∑ i, ‖∫ x, conj (L n i x) * r n i x ∂μ‖ := norm_sum_le _ _
      _ ≤ ∑ _ : ι, T * (V * Z n) := Finset.sum_le_sum fun i _ => pairB n i
      _ = _ := by simp
  · simpa only [mul_zero] using ((zlim.const_mul V).const_mul T).const_mul (Fintype.card ι : ℝ)

end Burnett.V03
