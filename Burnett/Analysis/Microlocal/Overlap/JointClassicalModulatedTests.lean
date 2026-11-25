import Burnett.Analysis.Fourier.Modulation
import Burnett.Analysis.PrincipalEnergy.Localization.FourierPhaseJets
import Burnett.Analysis.Microlocal.Overlap.AngularLocalClassical
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-! Fixed compact profiles modulated along a ray are weakly zero in the actual whole-space L². -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 4300000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Filter MeasureTheory Set Burnett.Fourier Burnett.Geometry.ConnectionDifference
open Burnett.Analysis.CarlesonEmbedding (fourier_phase_contDiff_and_derivative_bound)
open scoped ComplexConjugate ContDiff FourierTransform InnerProduct RealInnerProductSpace Topology

local notation "E" => CoordinateSpace

open private compactOperator_tendsto_zero_of_weakL2
  from Burnett.Analysis.Microlocal.Overlap.AngularLocalClassical

/-- The modulation of a compactly supported Schwartz profile, with the exact
physical-frequency increment in the Fourier convention of the quantization. -/
def compactModulatedSchwartz (k : E) (f : SchwartzMap E ℂ) (hf : HasCompactSupport (f : E → ℂ)) :
    SchwartzMap E ℂ := by
  let φ (x : E) := (Real.fourierChar ⟪x, k⟫ : ℂ)
  have hφ : ContDiff ℝ ∞ φ := by
    let ψ (x : E) := (Real.fourierChar ⟪k, x⟫ : ℂ)
    have he : φ = ψ := funext fun x => by simp only [φ, ψ, real_inner_comm x k]
    rw [he]
    exact (fourier_phase_contDiff_and_derivative_bound k).1
  exact hf.mul_left.toSchwartzMap (hφ.mul (f.smooth ⊤))

theorem compactModulatedSchwartz_apply (k : E) (f : SchwartzMap E ℂ)
    (hf : HasCompactSupport (f : E → ℂ)) (x : E) :
    compactModulatedSchwartz k f hf x = modulate k f x := rfl

theorem compactModulatedSchwartz_tsupport (k : E) (f : SchwartzMap E ℂ)
    (hf : HasCompactSupport (f : E → ℂ)) :
    tsupport (compactModulatedSchwartz k f hf : E → ℂ) ⊆ tsupport (f : E → ℂ) :=
  tsupport_mul_subset_right

theorem norm_compactModulatedSchwartz_toLp (k : E) (f : SchwartzMap E ℂ)
    (hf : HasCompactSupport (f : E → ℂ)) :
    ‖(compactModulatedSchwartz k f hf).toLp 2 volume‖ = ‖f.toLp 2 volume‖ := by
  let g := compactModulatedSchwartz k f hf
  have h : ∀ᵐ x ∂(volume : Measure E), ‖g.toLp 2 volume x‖ = ‖f.toLp 2 volume x‖ := by
    filter_upwards [g.coeFn_toLp 2 volume, f.coeFn_toLp 2 volume] with x hg hx
    rw [hg, hx]
    change ‖(Real.fourierChar ⟪x, k⟫ : ℂ) * f x‖ = ‖f x‖
    simp
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (h.mono fun _ he => he.le))
    (Lp.norm_le_norm_of_ae_le (h.mono fun _ he => he.ge))

private theorem tendsto_neg_nat_smul_cocompact (ξ : E) (hξ : ξ ≠ 0) :
    Tendsto (fun n : ℕ => -((n : ℝ) • ξ)) atTop (cocompact E) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
  apply tendsto_atTop.mpr
  intro C
  have hNorm := norm_pos_iff.mpr hξ
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (C / ‖ξ‖)] with n hn
  rw [norm_neg, norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg n)]
  exact (div_le_iff₀ hNorm).mp hn

/-- Weak whole-space convergence of the actual modulations for any ambient
L² test, by Riemann–Lebesgue on its ordinary product with the profile. -/
theorem tendsto_inner_compactModulatedSchwartz (ξ : E) (hξ : ξ ≠ 0)
    (f : SchwartzMap E ℂ) (hf : HasCompactSupport (f : E → ℂ)) (w : ComplexL2 E) :
    Tendsto (fun n : ℕ => inner ℂ w ((compactModulatedSchwartz ((n : ℝ) • ξ) f hf).toLp 2 volume))
      atTop (𝓝 0) := by
  let F (x : E) := conj (w x) * f x
  have hF : Tendsto (𝓕 F) (cocompact E) (𝓝 0) := by
    simpa only [Real.fourierIntegral_eq] using tendsto_integral_exp_inner_smul_cocompact F
  have h := hF.comp (tendsto_neg_nat_smul_cocompact ξ hξ)
  refine h.congr (fun n => ?_)
  let k : E := (n : ℝ) • ξ
  let g := compactModulatedSchwartz k f hf
  change (𝓕 F) (-k) = inner ℂ w (g.toLp 2 volume)
  rw [Real.fourierIntegral_eq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [g.coeFn_toLp 2 volume] with x hx
  rw [hx, RCLike.inner_apply', inner_neg_right, neg_neg]
  change (Real.fourierChar ⟪x, k⟫ : ℂ) * (conj (w x) * f x) =
    conj (w x) * ((Real.fourierChar ⟪x, k⟫ : ℂ) * f x)
  ring

/-- Every actual compact correction vanishes on the same fixed modulated profile. -/
theorem tendsto_compactOperator_compactModulatedSchwartz (ξ : E) (hξ : ξ ≠ 0)
    (f : SchwartzMap E ℂ) (hf : HasCompactSupport (f : E → ℂ))
    (R : ComplexL2 E →L[ℂ] ComplexL2 E) (hR : IsCompactOperator R) :
    Tendsto (fun n : ℕ => R ((compactModulatedSchwartz ((n : ℝ) • ξ) f hf).toLp 2 volume))
      atTop (𝓝 0) :=
  compactOperator_tendsto_zero_of_weakL2 R hR _ ‖f.toLp 2 volume‖
    (fun n => (norm_compactModulatedSchwartz_toLp ((n : ℝ) • ξ) f hf).le)
    (tendsto_inner_compactModulatedSchwartz ξ hξ f hf)

end Burnett.Microlocal.AtlasOverlapKernel
