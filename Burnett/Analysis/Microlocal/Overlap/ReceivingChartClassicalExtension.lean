import Burnett.Analysis.Microlocal.Overlap.AngularLocalClassical

/-! Extend the separated receiving-window tests to the actual joint left
Fourier principal action and any represented compact remainder. -/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 3000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol radialCore radialCore_contDiff)
open Burnett.Microlocal.SeparablePositive (separableOperator)
open scoped ContDiff FourierTransform InnerProduct Topology

open private norm_baseMode_pairing_le from Burnett.Analysis.Microlocal.Overlap.AngularBilateralPrincipal
open private compactOperator_tendsto_zero_of_weakL2 inner_tendsto_zero_of_bounded_of_tendsto_zero
  from Burnett.Analysis.Microlocal.Overlap.AngularLocalClassical

/-- Knowing the normalized receiving Fourier multipliers on the fixed
pair of input sequences determines their limit for the given represented
joint classical operator, including its actual compact remainder. -/
theorem tendsto_receivingClassicalPairing_of_separated
    {P : Type*} [MeasurableSpace P] (τ : Measure P) [SFinite τ]
    (base ξ : P → E) (hBase : Measurable base) (hξ : Measurable ξ)
    (ρ : P → ℂ) (hρ : Integrable ρ τ)
    (a : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (hSupport : ∀ ζ, tsupport (fun x => a x ζ) ⊆ S)
    (hJoint : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (hZero : ContDiff ℝ ∞ (fun x => a x 0))
    (hDegree : ∀ x, DegreeZero (a x))
    (u v : ℕ → SchwartzMap E ℂ) (L : Set E)
    (hVSupp : ∀ n, tsupport (v n : E → ℂ) ⊆ L)
    (C D : ℝ) (hU : ∀ n, ‖(u n).toLp 2 volume‖ ≤ C) (hV : ∀ n, ‖(v n).toLp 2 volume‖ ≤ D)
    (hW : ∀ w : ComplexL2 E, Tendsto (fun n => inner ℂ w ((v n).toLp 2 volume)) atTop (𝓝 0))
    (hSep : ∀ k : E, ∀ (m : BoundedSymbol E),
      ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E) → DegreeZero (m : E → ℂ) →
      Tendsto (fun n => inner ℂ ((u n).toLp 2 volume)
        (separableOperator (baseFourierPhaseSymbol k) (normalizedAngularSymbol m) ((v n).toLp 2 volume)))
        atTop (𝓝 (∫ p, baseFourierPhase k (base p) * m (ξ p) * ρ p ∂τ)))
    (T : ComplexL2 E →L[ℂ] ComplexL2 E) (hT : HasLocalClassicalRepresentation T a L) :
    Tendsto (fun n => inner ℂ ((u n).toLp 2 volume) (T ((v n).toLp 2 volume)))
      atTop (𝓝 (∫ p, a (base p) (ξ p) * ρ p ∂τ)) := by
  have hSmooth := contDiff_baseAngularSection a hJoint hZero
  have hAng (x : E) : ContinuousOn (a x) ({0}ᶜ : Set E) :=
    hJoint.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hζ => ⟨mem_univ x, hζ⟩)
  have hOrder := exists_uniform_baseDerivative_of_homogeneousAngular a S hS hSupport hJoint hZero hDegree
  obtain ⟨m, g, hg, hnorm, hm, _⟩ :=
    exists_compactBaseAngular_leftFourier_pairing ⟨S, hS, hSupport⟩ hSmooth hOrder hAng
  let M (k : E) := normalizedAngularSymbol (m k)
  have hMeas : Measurable (fun w : E × E => m w.1 w.2) := by
    simp only [hm]
    exact measurable_baseFourierCoefficient
      (measurable_baseAngularSymbol (fun ζ => (hSmooth ζ).continuous) hAng)
  have hM (k ζ : E) : M k ζ = (1 - (radialCore ζ : ℂ)) * m k ζ := by
    change (1 - (radialCore ((1 : ℝ) • ζ) : ℂ)) * m k ζ = _
    rw [one_smul]
  have hMMeas : Measurable (fun w : E × E => M w.1 w.2) := by
    simp only [hM]
    exact (measurable_const.sub ((Complex.continuous_ofReal.comp radialCore_contDiff.continuous).measurable.comp
      measurable_snd)).mul hMeas
  have hMBound (k : E) : (M k).bound ≤ 2 * g k := by
    change (1 + 1) * (m k).bound ≤ 2 * g k
    rw [hnorm k]
    norm_num
  have hCoef := compactBaseOrderOne_frequencyWeight ⟨S, hS, hSupport⟩ hSmooth hOrder
  have hInv (x ζ : E) : (𝓕⁻ (fun k => M k ζ)) x = infraredAngularPrincipal a x ζ := by
    have ha := baseFourierCoefficient_inverse hCoef x ζ
    rw [Real.fourierIntegralInv_eq'] at ha ⊢
    simp only [hM, smul_eq_mul, infraredAngularPrincipal]
    rw [← ha, ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun k => by simp only [hm, smul_eq_mul]; ring
  let G (k : E) (z : P) : ℂ := baseFourierPhase k (base z) * m k (ξ z) * ρ z
  let F (n : ℕ) (k : E) : ℂ := inner ℂ ((u n).toLp 2 volume)
    (separableOperator (baseFourierPhaseSymbol k) (M k) ((v n).toLp 2 volume))
  have hForm (n : ℕ) := firstOrderAction_pairing_eq_integral_separable_baseFourier
    (infraredAngularPrincipal a) M hMMeas (fun k => 2 * g k) (hg.const_mul 2) hMBound hInv (v n) (u n)
  have hC : 0 ≤ C := (norm_nonneg _).trans (hU 0)
  have hD : 0 ≤ D := (norm_nonneg _).trans (hV 0)
  have hg₀ (k : E) : 0 ≤ g k := hnorm k ▸ (m k).bound_nonneg
  have hPoint (k : E) : Tendsto (fun n => F n k) atTop (𝓝 (∫ z, G k z ∂τ)) := by
    have hmS : ContDiffOn ℝ ∞ (m k : E → ℂ) ({0}ᶜ : Set E) := by
      rw [funext (hm k)]
      exact contDiffOn_baseFourierCoefficient a S hS hSupport hJoint k
    have hmD : DegreeZero (m k : E → ℂ) := by
      rw [funext (hm k)]
      exact degreeZero_baseFourierCoefficient hDegree k
    exact hSep k (m k) hmS hmD
  have hDom : Tendsto (fun n => ∫ k, F n k) atTop (𝓝 (∫ k, ∫ z, G k z ∂τ)) := by
    apply tendsto_integral_of_dominated_convergence (bound := fun k => (2 * C * D) * g k)
      (fun n => (hForm n).1.aestronglyMeasurable) (hg.const_mul _)
    · intro n
      filter_upwards with k
      calc
        _ ≤ ‖(u n).toLp 2 volume‖ * ((M k).bound * ‖(v n).toLp 2 volume‖) :=
          norm_baseMode_pairing_le _ _ _ _
        _ ≤ C * ((2 * g k) * D) :=
          mul_le_mul (hU n)
            (mul_le_mul (hMBound k) (hV n) (norm_nonneg _) (mul_nonneg (by norm_num) (hg₀ k)))
            (mul_nonneg (M k).bound_nonneg (norm_nonneg _)) hC
        _ = _ := by ring
    · exact Eventually.of_forall hPoint
  have hInt : Integrable (uncurry G) (volume.prod τ) := by
    apply (hg.mul_prod hρ.norm).mono'
    · exact ((baseFourierPhase_continuous.measurable.comp (measurable_fst.prodMk (hBase.comp measurable_snd))).mul
        (hMeas.comp (measurable_fst.prodMk (hξ.comp measurable_snd)))).aestronglyMeasurable.mul
          (hρ.aestronglyMeasurable.comp_snd (μ := volume))
    · filter_upwards with z
      simp only [uncurry, G, norm_mul, baseFourierPhase_norm, one_mul]
      exact mul_le_mul_of_nonneg_right ((m z.1).norm_le (ξ z.2) |>.trans_eq (hnorm z.1)) (norm_nonneg _)
  have hSwap : (∫ k, ∫ z, G k z ∂τ) = ∫ z, a (base z) (ξ z) * ρ z ∂τ := by
    rw [integral_integral_swap hInt]
    apply integral_congr_ae
    filter_upwards with z
    change (∫ k, (baseFourierPhase k (base z) * m k (ξ z)) * ρ z) = _
    rw [integral_mul_const, ← baseFourierCoefficient_inverse hCoef (base z) (ξ z), Real.fourierIntegralInv_eq']
    simp only [hm, baseFourierPhase, smul_eq_mul]
  obtain ⟨R, hR, hTR⟩ := hT
  have hComp := compactOperator_tendsto_zero_of_weakL2 R hR (fun n => (v n).toLp 2 volume) D hV hW
  have hErr := inner_tendsto_zero_of_bounded_of_tendsto_zero (fun n => (u n).toLp 2 volume)
    (fun n => R ((v n).toLp 2 volume)) C hU hComp
  rw [hSwap] at hDom
  have h := hDom.add hErr
  rw [add_zero] at h
  exact h.congr fun n => by
    rw [hTR _ _ (hVSupp n), (hForm n).2]

end Burnett.Microlocal.Overlap
