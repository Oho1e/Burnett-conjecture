import Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedInfraredStructure

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.C04

open Function Filter Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped ContDiff Topology

/-- The same fixed infrared Fourier multiplier is applied at every base
point, with the canonical covector identified with its radian coordinates. -/
def sharedInfraredTransportSymbol (cut : SchwartzMap E ℂ) (a : E → Covector → ℝ)
    (x : E) (ξ : Covector) : ℝ :=
  fixedInfraredSymbol cut 0 (fun ζ => a x (WithLp.ofLp ζ)) (WithLp.toLp 2 ξ)

theorem sharedInfraredTransportSymbol_apply (cut : SchwartzMap E ℂ) (a : E → Covector → ℝ)
    (x : E) (ξ : Covector) :
    sharedInfraredTransportSymbol cut a x ξ = (1 - fixedRadianProfile cut (WithLp.toLp 2 ξ)) * a x ξ := by
  simp [sharedInfraredTransportSymbol, fixedInfraredSymbol, fixedRadianProfile]

/-- Joint smoothness at the excluded zero fiber comes from the fixed
infrared window. Outside that window the original degree-one test is recovered. -/
theorem sharedInfraredTransportSymbol_properties
    (cut : SchwartzMap E ℂ) (a : E → Covector → ℝ) (L : Set E)
    (hLow : ∀ ζ : E, ‖ζ‖ ≤ 1 / 2 → fixedRadianProfile cut ζ = 1)
    (hHigh : ∀ ζ : E, 1 < ‖ζ‖ → fixedRadianProfile cut ζ = 0)
    (ha : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set Covector)))
    (hSupp : ∀ x ∉ L, ∀ ξ, a x ξ = 0) :
    let β := sharedInfraredTransportSymbol cut a
    ContDiff ℝ ∞ (uncurry β) ∧ (∀ x ∉ L, ∀ ξ, β x ξ = 0) ∧
      ∀ x (ξ : Covector), 1 < ‖(WithLp.toLp 2 ξ : E)‖ → β x ξ = a x ξ := by
  intro β
  let T : Covector ≃L[ℝ] E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm
  let c := fixedRadianProfile cut ∘ T
  have hProfile : ContDiff ℝ ∞ (fixedRadianProfile cut) :=
    Complex.reCLM.contDiff.comp ((cut.smooth _).comp (contDiff_const.smul contDiff_id))
  have hCSmooth := hProfile.comp T.contDiff
  have hBeta (z : E × Covector) :
      uncurry β z = (1 - c z.2) * uncurry a z :=
    sharedInfraredTransportSymbol_apply cut a z.1 z.2
  refine ⟨contDiff_iff_contDiffAt.mpr (fun z => ?_), ?_, ?_⟩
  · by_cases hz : z.2 = 0
    · have hOpen : IsOpen ((fun p : E × Covector => T p.2) ⁻¹' Metric.ball (0 : E) (1 / 2)) :=
        Metric.isOpen_ball.preimage (T.continuous.comp continuous_snd)
      have hzBall : z ∈ (fun p : E × Covector => T p.2) ⁻¹' Metric.ball (0 : E) (1 / 2) := by
        change T z.2 ∈ Metric.ball (0 : E) (1 / 2)
        rw [hz, map_zero]
        exact Metric.mem_ball_self (by norm_num)
      have hEq : uncurry β =ᶠ[𝓝 z] fun _ : E × Covector => (0 : ℝ) := by
        filter_upwards [hOpen.mem_nhds hzBall] with p hp
        have hpNorm : ‖T p.2‖ < 1 / 2 := by simpa using hp
        rw [hBeta, show c p.2 = 1 from hLow (T p.2) hpNorm.le, sub_self, zero_mul]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hEq
    · have hOpen : IsOpen (univ ×ˢ ({0}ᶜ : Set Covector) : Set (E × Covector)) :=
        isOpen_univ.prod isOpen_compl_singleton
      have hza : ContDiffAt ℝ ∞ (uncurry a) z := ha.contDiffAt (hOpen.mem_nhds ⟨trivial, hz⟩)
      have hcz : ContDiffAt ℝ ∞ (fun p : E × Covector => c p.2) z :=
        (hCSmooth.comp contDiff_snd).contDiffAt
      exact ((contDiffAt_const.sub hcz).mul hza).congr_of_eventuallyEq (Eventually.of_forall hBeta)
  · intro x hx ξ
    rw [show β x ξ = (1 - c ξ) * a x ξ from hBeta (x, ξ), hSupp x hx ξ, mul_zero]
  · intro x ξ hξ
    exact fixedInfraredSymbol_outside cut 0 (fun ζ => a x (WithLp.ofLp ζ)) _
      (hHigh _ hξ) (by simp [fixedRadianProfile])

/-- Read the exact same symbol in radian coordinates for the actual Weyl
kernel and retain degree one jointly in the whole high-frequency region. -/
theorem sharedInfraredTransportSymbol_radian_properties
    (cut : SchwartzMap E ℂ) (a : E → Covector → ℝ) (L : Set E)
    (hLow : ∀ ζ : E, ‖ζ‖ ≤ 1 / 2 → fixedRadianProfile cut ζ = 1)
    (hHigh : ∀ ζ : E, 1 < ‖ζ‖ → fixedRadianProfile cut ζ = 0)
    (ha : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set Covector)))
    (hSupp : ∀ x ∉ L, ∀ ξ, a x ξ = 0)
    (hHom : ∀ x (t : ℝ), 0 < t → ∀ ξ : Covector, ξ ≠ 0 → a x (t • ξ) = t * a x ξ) :
    let β (x ζ : E) := (sharedInfraredTransportSymbol cut a x (WithLp.ofLp ζ) : ℂ)
    ContDiff ℝ ∞ (uncurry β) ∧ (∀ x ∉ L, ∀ ζ, β x ζ = 0) ∧
      ∀ x ζ, 1 < ‖ζ‖ → ∀ t : ℝ, 1 ≤ t → β x (t • ζ) = t • β x ζ := by
  intro β
  let T : E ≃L[ℝ] Covector := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)
  obtain ⟨hSmooth, hOff, hMatch⟩ := sharedInfraredTransportSymbol_properties cut a L hLow hHigh ha hSupp
  have hR (x ζ : E) (hζ : 1 < ‖ζ‖) : β x ζ = (a x (T ζ) : ℂ) := by
    have hEq : (WithLp.toLp 2 (T ζ) : E) = ζ := by
      change WithLp.toLp 2 (WithLp.ofLp ζ) = ζ
      simp
    have hLarge : 1 < ‖(WithLp.toLp 2 (T ζ) : E)‖ := by rw [hEq]; exact hζ
    exact congrArg Complex.ofReal (hMatch x (T ζ) hLarge)
  let A (p : E × E) : E × Covector := (p.1, T p.2)
  have hA : ContDiff ℝ ∞ A :=
    (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : E × E → E)).prodMk
      (T.contDiff.comp (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : E × E → E)))
  have hRadian : ContDiff ℝ ∞ (fun p : E × E => sharedInfraredTransportSymbol cut a p.1 (T p.2)) :=
    hSmooth.comp hA
  refine ⟨Complex.ofRealCLM.contDiff.comp hRadian, ?_, ?_⟩
  · intro x hx ζ
    change (sharedInfraredTransportSymbol cut a x (T ζ) : ℂ) = 0
    rw [hOff x hx, Complex.ofReal_zero]
  · intro x ζ hζ t ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    have hζt : 1 < ‖t • ζ‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht0.le]
      exact hζ.trans_le (le_mul_of_one_le_left (norm_nonneg _) ht)
    have h0 : T ζ ≠ 0 := by
      intro h
      have hz := T.injective (h.trans T.map_zero.symm)
      rw [hz, norm_zero] at hζ
      linarith
    rw [hR x _ hζt, hR x ζ hζ, map_smul, hHom x t ht0 (T ζ) h0]
    simp only [Complex.ofReal_mul, Complex.real_smul]

end Burnett.C04
