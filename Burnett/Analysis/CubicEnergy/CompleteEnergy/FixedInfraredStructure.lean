import Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedInfrared

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Filter Metric
open scoped ContDiff ENNReal FourierTransform RealInnerProductSpace Topology

/-- A concrete inhomogeneous symbol. A low cutoff equal to one near zero
removes the nonsmooth homogeneous core there. An optional smooth profile
can specify a different symbol on that fixed infrared region. -/
def fixedInfraredSymbol (cut add : SchwartzMap E ℂ) (b : E → ℝ) (ζ : E) : ℝ :=
  (1 - fixedRadianProfile cut ζ) * b ζ + fixedRadianProfile add ζ

theorem fixedInfraredSymbol_outside (cut add : SchwartzMap E ℂ) (b : E → ℝ)
    (ζ : E) (hc : fixedRadianProfile cut ζ = 0) (ha : fixedRadianProfile add ζ = 0) :
    fixedInfraredSymbol cut add b ζ = b ζ := by
  simp [fixedInfraredSymbol, hc, ha]

private theorem fixed_radian_profile_smooth (a : SchwartzMap E ℂ) :
    ContDiff ℝ ∞ (fixedRadianProfile a) :=
  Complex.reCLM.contDiff.comp ((a.smooth _).comp (contDiff_const.smul contDiff_id))

theorem fixedInfraredSymbol_smooth (cut add : SchwartzMap E ℂ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hzero : ∀ᶠ ζ in 𝓝 (0 : E), fixedRadianProfile cut ζ = 1) :
    ContDiff ℝ ∞ (fixedInfraredSymbol cut add b) := by
  apply contDiff_iff_contDiffAt.mpr
  intro ζ
  by_cases hζ : ζ = 0
  · subst ζ
    apply (fixed_radian_profile_smooth add).contDiffAt.congr_of_eventuallyEq
    filter_upwards [hzero] with x hx
    simp [fixedInfraredSymbol, hx]
  · have hbAt : ContDiffAt ℝ ∞ b ζ := hb.contDiffAt
      (isClosed_singleton.isOpen_compl.mem_nhds hζ)
    exact ((contDiffAt_const.sub (fixed_radian_profile_smooth cut).contDiffAt).mul hbAt).add
      (fixed_radian_profile_smooth add).contDiffAt

private theorem fixed_homogeneous_spectrum_integrable (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (f : SchwartzMap E ℂ) :
    Integrable (radianActionSpectrum b f) := by
  let B : E → ℝ := fun x => b (tau • x)
  have ht : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have hB : ContDiffOn ℝ ∞ B {x | x ≠ 0} := hb.comp
    (contDiff_const.smul contDiff_id).contDiffOn (fun _ hx => smul_ne_zero ht.ne' hx)
  have hHom : ∀ t : ℝ, 0 < t → ∀ x, B (t • x) = t * B x := by
    intro t h x
    change b (tau • (t • x)) = t * b (tau • x)
    rw [smul_comm tau t x, hom t h]
  exact orderOne_spectrum_integrable B hB hHom f

/-- The regularized multiplier is an equality of the actual Fourier actions. -/
theorem fixedInfraredSymbol_action (cut add : SchwartzMap E ℂ)
    (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ) (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (f : SchwartzMap E ℂ) :
    radianAction (fixedInfraredSymbol cut add b) f =
      radianAction b f - radianAction (fun ζ => fixedRadianProfile cut ζ * b ζ) f +
        radianAction (fixedRadianProfile add) f := by
  let B := radianActionSpectrum b f
  let L := radianActionSpectrum (fun ζ => fixedRadianProfile cut ζ * b ζ) f
  let R := radianActionSpectrum (fixedRadianProfile add) f
  have hB : Integrable B := fixed_homogeneous_spectrum_integrable b hb hom f
  have hL : Integrable L := by
    have shape : L = fun ξ => cut ξ * B ξ := by
      funext ξ
      simp only [L, B, radianActionSpectrum, fixedRadianProfile_scaled, Complex.ofReal_mul, hcut, mul_assoc]
    rw [shape]
    exact hB.bdd_mul cut.continuous.aestronglyMeasurable ⟨_, SchwartzMap.norm_le_seminorm ℝ cut⟩
  have hR : Integrable R := by
    let F := energyProduct add (SchwartzMap.fourierTransformCLE ℂ f)
    have shape : R = (F : E → ℂ) := by
      funext ξ
      simp only [R, F, radianActionSpectrum, fixedRadianProfile_scaled, hadd, energyProduct_apply]
      rfl
    rw [shape]
    exact F.integrable
  funext x
  let W := fun ξ : E => Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I)
  have wc : Continuous W := by dsimp only [W]; fun_prop
  have wb (ξ : E) : ‖W ξ‖ ≤ 1 := by simp [W, Complex.norm_exp]
  have weight {F : E → ℂ} (hF : Integrable F) : Integrable (fun ξ => W ξ * F ξ) :=
    hF.bdd_mul wc.aestronglyMeasurable ⟨1, wb⟩
  have wsub : Integrable (fun ξ => W ξ * B ξ - W ξ * L ξ) := (weight hB).sub (weight hL)
  simp only [Pi.sub_apply, Pi.add_apply, ← radianActionSpectrum_inverse,
    Real.fourierIntegralInv_eq', smul_eq_mul]
  change (∫ ξ, W ξ * radianActionSpectrum (fixedInfraredSymbol cut add b) f ξ) =
    (∫ ξ, W ξ * B ξ) - (∫ ξ, W ξ * L ξ) + ∫ ξ, W ξ * R ξ
  rw [← integral_sub (weight hB) (weight hL), ← integral_add wsub (weight hR)]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [fixedInfraredSymbol, B, L, R, radianActionSpectrum,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- The regularized test is bounded by the homogeneous derivative term and
the fixed undifferentiated terms on each Schwartz input. -/
theorem fixedInfraredSymbol_W1p_bound (cut add : SchwartzMap E ℂ)
    (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ) (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ)
    (p : ℝ) (hp : 1 < p) :
    ∃ Kd Kc Ka : ℝ≥0∞, Kd < ⊤ ∧ Kc < ⊤ ∧ Ka < ⊤ ∧
      ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ f : SchwartzMap E ℂ,
        MemLp (radianAction (fixedInfraredSymbol cut add b) f) (ENNReal.ofReal p) volume ∧
        eLpNorm (radianAction (fixedInfraredSymbol cut add b) f) (ENNReal.ofReal p) volume ≤
          Kd * ENNReal.ofReal D * eLpNorm (fderiv ℝ (f : E → ℂ)) (ENNReal.ofReal p) volume +
            (Kc * ENNReal.ofReal D + Ka) * eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume := by
  obtain ⟨Kd, hd, derivative⟩ := radian_degree_one_gradient_sphere_bound p hp
  obtain ⟨Kc, hc, correction⟩ := fixed_infrared_sphere_bound cut hcut p hp
  obtain ⟨Ka, ha, additive⟩ := fixedRadianProfile_Lp add hadd p hp
  refine ⟨Kd, Kc, Ka, hd, hc, ha, ?_⟩
  intro b hb hom D hD jet f
  have p1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  obtain ⟨mB, bdB⟩ := derivative b hb hom D hD jet f
  obtain ⟨mC, bdC⟩ := correction b hb hom D hD jet f
  obtain ⟨mA, bdA⟩ := additive f
  rw [fixedInfraredSymbol_action cut add hcut hadd b hb hom f]
  refine ⟨(mB.sub mC).add mA, ?_⟩
  exact (eLpNorm_add_le (mB.sub mC).1 mA.1 p1).trans
    ((add_le_add ((eLpNorm_sub_le mB.1 mC.1 p1).trans (add_le_add bdB bdC)) bdA).trans_eq (by rw [add_mul, add_assoc]))

end Burnett.A02.FrequencySplit
