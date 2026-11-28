import Burnett.Analysis.TransportWard.Weyl.DensityWeylActionSplit
import Burnett.Analysis.TransportWard.Weyl.DensityWeylCanonicalSymbol

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 1650

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter Set MeasureTheory Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Bianchi.RayIdentification (canonicalBracket)
open Burnett.Microlocal.HminusReverse (schwartzH1Energy)
open scoped ContDiff Topology ComplexConjugate InnerProductSpace BigOperators

local notation "J" => Fin 4 × Fin 4

theorem variableDensityCompactWeylCommutator_eq_canonical_add_residual {ι : Type*} [Fintype ι]
    (S : ι → Mat) (G : E → Mat) (c : ι → ι → J → SchwartzMap E ℂ)
    (θ : E → ℝ) (β : E → E → ℝ) (R : ℝ) (hs : ContDiff ℝ ∞ (uncurry β))
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ (fun x ξ => (β x ξ : ℂ))) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ (fun x ξ => (β x ξ : ℂ))))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol (fun x ξ => (β x ξ : ℂ))))
    (u : ι → SchwartzMap E ℂ) (i : ι) (x : E)
    (hC : ∀ y ∈ tsupport θ, ∀ (j : ι) (d : J),
      DifferentiableAt ℝ (fun z => metricActionCoefficient S (d.1,i) (d.2,j) (G z)) y)
    (hc : ∀ y ∈ tsupport θ, ∀ (j : ι) (d : J), (fun z => c i j d z) =ᶠ[𝓝 y]
      fun z => (metricActionCoefficient S (d.1,i) (d.2,j) (G z) : ℂ)) :
    let a := windowedWeylLeftSymbol θ (fun y ζ => (β y ζ : ℂ)) R h
    let b := normalizedWeylSymbol (fun y ζ => (β y ζ : ℂ))
    variableDensityWeylCommutator c a u i x = ∑ j,
      (firstOrderAction (fun y ξ => (canonicalBracket (fun z q => frozenDensityPrincipalPhase S (G z) q i j)
        (fun z q => β z (WithLp.toLp 2 q)) y (physicalRadianCovector ξ) : ℂ)) (u j) x +
          firstOrderAction (densityWeylResidualSymbol c a b i j) (u j) x) := by
  intro a b
  have hp (y ν : E) : (β y ν : ℂ) ≠ 0 → θ y = 1 :=
    fun hn => hPlateau y ν (fun he => hn (by rw [he, Complex.ofReal_zero]))
  rw [variableDensityCompactWeylCommutator_eq_leading_add_residual c θ (fun y ν => (β y ν : ℂ)) R h hAmp hp hβ]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have he := densityWeylLeadingSymbol_eq_canonicalBracket S G c θ β hs hPlateau i j
    (fun y hy => hC y hy j) (fun y hy => hc y hy j)
  rw [funext (fun y => funext (he y))]

/-- The actual residual pairing costs only the coordinate H¹ norm of
the input and the L² norm of the test. -/
theorem exists_densityWeylResidual_pair_bound {ι : Type*}
    (c : ι → ι → J → SchwartzMap E ℂ) (i j : ι)
    (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ) (hθ : HasCompactSupport θ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol β)) :
    let a := windowedWeylLeftSymbol θ β R h
    let b := normalizedWeylSymbol β
    let p := densityWeylResidualSymbol c a b i j
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : SchwartzMap E ℂ,
      ‖∫ x, conj (v x) * firstOrderAction p u x‖ ≤ C * Real.sqrt (schwartzH1Energy u) * ‖v.toLp 2 volume‖ := by
  intro a b p
  obtain ⟨C,hC,hBound⟩ := exists_densityWeylResidualAction_h1_to_l2 c i j θ β R hθ h hAmp hPlateau hβ
  refine ⟨C,hC,fun u v => ?_⟩
  obtain ⟨hL,hL₂⟩ := hBound u
  let T := hL.toLp (firstOrderAction p u)
  have hE : 0 ≤ schwartzH1Energy u := by
    unfold schwartzH1Energy
    exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hT : ‖T‖ ≤ C * Real.sqrt (schwartzH1Energy u) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt hE]
    exact hL₂
  have hEq : ⟪v.toLp 2 volume,T⟫_ℂ = ∫ x, conj (v x) * firstOrderAction p u x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [v.coeFn_toLp 2 volume, MemLp.coeFn_toLp hL] with x hv ht
    change inner ℂ ((v.toLp 2 volume) x) ((hL.toLp _) x) = _
    rw [hv, ht, RCLike.inner_apply']
  rw [← hEq]
  exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
    ((mul_le_mul_of_nonneg_left hT (norm_nonneg _)).trans_eq (mul_comm _ _))

theorem tendsto_densityWeylResidual_pair_zero_of_uniform_H1 {ι : Type*}
    (c : ι → ι → J → SchwartzMap E ℂ) (i j : ι)
    (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ) (hθ : HasCompactSupport θ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol β))
    (u v : ℕ → SchwartzMap E ℂ) (M : ℝ) (hM : ∀ n, Real.sqrt (schwartzH1Energy (u n)) ≤ M)
    (hv : Tendsto (fun n => ‖(v n).toLp 2 volume‖) atTop (𝓝 0)) :
    let a := windowedWeylLeftSymbol θ β R h
    let b := normalizedWeylSymbol β
    let p := densityWeylResidualSymbol c a b i j
    Tendsto (fun n => ∫ x, conj (v n x) * firstOrderAction p (u n) x) atTop (𝓝 0) := by
  intro a b p
  obtain ⟨C,hC,hPair⟩ := exists_densityWeylResidual_pair_bound c i j θ β R hθ h hAmp hPlateau hβ
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hZero : Tendsto (fun n => C*M*‖(v n).toLp 2 volume‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hv.const_mul (C*M)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hZero
  exact (hPair (u n) (v n)).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hM n) hC) (norm_nonneg _))

theorem tendsto_densityWeylResidual_matrixPair_zero_of_uniform_H1 {ι : Type*} [Fintype ι]
    (c : ι → ι → J → SchwartzMap E ℂ)
    (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ) (hθ : HasCompactSupport θ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol β))
    (u v : ℕ → ι → SchwartzMap E ℂ)
    (hU : ∀ j, ∃ M : ℝ, ∀ n, Real.sqrt (schwartzH1Energy (u n j)) ≤ M)
    (hV : ∀ i, Tendsto (fun n => ‖(v n i).toLp 2 volume‖) atTop (𝓝 0)) :
    let a := windowedWeylLeftSymbol θ β R h
    let b := normalizedWeylSymbol β
    Tendsto (fun n => ∑ i, ∑ j, ∫ x, conj (v n i x) *
      firstOrderAction (densityWeylResidualSymbol c a b i j) (u n j) x) atTop (𝓝 0) := by
  intro a b
  let T (i j : ι) (n : ℕ) := ∫ x, conj (v n i x) *
    firstOrderAction (densityWeylResidualSymbol c a b i j) (u n j) x
  have hT (i j : ι) : Tendsto (T i j) atTop (𝓝 0) := by
    obtain ⟨M,hM⟩ := hU j
    exact tendsto_densityWeylResidual_pair_zero_of_uniform_H1 c i j θ β R hθ h hAmp hPlateau hβ
      (fun n => u n j) (fun n => v n i) M hM (hV i)
  have hI (i : ι) : Tendsto (fun n => ∑ j, T i j n) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun j _ => hT i j)
  simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun i _ => hI i)

end Burnett.V03.Palatini
