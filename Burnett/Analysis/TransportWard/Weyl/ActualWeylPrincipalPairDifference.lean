import Burnett.Analysis.TransportWard.Weyl.VariableWeylScalarRemainder
import Burnett.Analysis.TransportWard.Weyl.DensityWeylResidualBound
import Burnett.Analysis.TransportWard.Weyl.DensityWeylCanonicalSymbol
import Burnett.Analysis.TransportWard.Weyl.WeylLeadingProfile
import Burnett.Analysis.TransportWard.Weyl.DensityWeylActionSplit
import Burnett.Analysis.TransportWard.Weyl.DensityWeylRemainderPair
import Burnett.Analysis.TransportWard.Weyl.ActualChartWeylResidualPacket

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 2500

noncomputable section

namespace Burnett.V03.Palatini

open Filter Function MeasureTheory Set Burnett.A03 Burnett.A02.FrequencySplit Burnett.RicciSymbol
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Analysis.CarlesonEmbedding (integrable_schwartz_weighted)
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Bianchi.RayIdentification (canonicalBracket)
open Burnett.Microlocal.HminusReverse (schwartzH1Energy)
open scoped ContDiff Topology ComplexConjugate FourierTransform BigOperators

local notation "J" => Fin 4 × Fin 4
local notation "W" => radianFrequencyWeight

private theorem measurable_leftAction_of_joint {a : E → E → ℂ}
    (ha : Continuous (uncurry a)) (u : SchwartzMap E ℂ) :
    StronglyMeasurable (firstOrderAction a u) := by
  let F := SchwartzMap.fourierTransformCLM ℂ u
  let φ : E × E → ℂ := uncurry patchFourierPhase ∘ (Prod.swap : E × E → E × E)
  have hPh : Continuous φ := patch_fourier_phase_continuous.comp continuous_swap
  have hFourier : Continuous (fun z : E × E => F z.2) := F.continuous.comp continuous_snd
  have hJoint : Continuous (uncurry (leftActionIntegrand a u)) := by
    change Continuous (fun z : E × E => φ z * a z.1 z.2 * F z.2)
    exact (hPh.mul ha).mul hFourier
  rw [show firstOrderAction a u = fun x => ∫ ξ, leftActionIntegrand a u x ξ from
    funext (firstOrderAction_eq_leftActionIntegrand a u)]
  exact hJoint.measurable.stronglyMeasurable.integral_prod_right'

private theorem norm_leftAction_le_of_growth {a : E → E → ℂ}
    (m : ℕ) (C : ℝ) (hC : ∀ x ξ, ‖a x ξ‖ ≤ C * (W ξ)^m)
    (u : SchwartzMap E ℂ) (x : E) :
    ‖firstOrderAction a u x‖ ≤ ∫ ξ, C * ((W ξ)^m * ‖(SchwartzMap.fourierTransformCLM ℂ u) ξ‖) := by
  let F := SchwartzMap.fourierTransformCLM ℂ u
  have hI : Integrable (fun ξ => (W ξ)^m * ‖F ξ‖) volume := integrable_schwartz_weighted F m
  rw [firstOrderAction_eq_leftActionIntegrand]
  refine norm_integral_le_of_norm_le (hI.const_mul C) (.of_forall fun ξ => ?_)
  rw [show ‖leftActionIntegrand a u x ξ‖ = ‖a x ξ‖ * ‖F ξ‖ by
    simp only [leftActionIntegrand,norm_mul,patch_fourier_phase_norm,one_mul,F,SchwartzMap.fourierTransformCLM_apply]]
  change ‖a x ξ‖ * ‖F ξ‖ ≤ C * ((W ξ)^m * ‖F ξ‖)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC x ξ) (norm_nonneg _)

private theorem integrable_schwartz_pair_leftAction_of_growth {a : E → E → ℂ}
    (ha : Continuous (uncurry a)) (m : ℕ) (C : ℝ) (hC : ∀ x ξ, ‖a x ξ‖ ≤ C * (W ξ)^m)
    (u v : SchwartzMap E ℂ) :
    Integrable (fun x => conj (v x) * firstOrderAction a u x) volume := by
  have hMeas := measurable_leftAction_of_joint ha u
  let M : ℝ := ∫ ξ, C * ((W ξ)^m * ‖(SchwartzMap.fourierTransformCLM ℂ u) ξ‖)
  refine (v.integrable.norm.mul_const M).mono'
    ((Complex.continuous_conj.comp v.continuous).aestronglyMeasurable.mul hMeas.aestronglyMeasurable) ?_
  filter_upwards with x
  rw [norm_mul,Complex.norm_conj]
  exact mul_le_mul_of_nonneg_left (norm_leftAction_le_of_growth m C hC u x) (norm_nonneg _)

private theorem densityWeylLeadingSymbol_profile {ι : Type*}
    (c : ι → ι → J → SchwartzMap E ℂ) {b : E → E → ℂ} (hb : ScaledJointOrderOne b)
    (i j : ι) :
    ContDiff ℝ ∞ (uncurry (densityWeylLeadingSymbol c b i j)) ∧
      BaseDerivativeBounds (densityWeylLeadingSymbol c b i j) (fun ξ => (W ξ)^2) := by
  have hF (d : J) := frozenSecondWeylLeading_profile hb d.1 d.2
  have hV (d : J) := variableSecondWeylLeading_profile hb (c i j d) d
  refine ⟨?_,?_⟩
  · change ContDiff ℝ ∞ (fun z : E × E =>
      ∑ d : J, (c i j d z.1 * frozenSecondWeylLeading b d.1 d.2 z.1 z.2 +
        variableSecondWeylLeading b (c i j d) d z.1 z.2))
    exact ContDiff.sum (s := Finset.univ) (fun d _ =>
      (((c i j d).smooth'.comp contDiff_fst).mul (hF d).1).add (hV d).1)
  · exact BaseDerivativeBounds.sum _ (fun d =>
      (((BaseDerivativeBounds.schwartz_coefficient (c i j d)).mul (hF d).2 (fun _ => zero_le_one)).weight_congr
        (fun ξ => one_mul ((W ξ)^2))).add (hV d).2)

/-- The exact test of the variable second-order Euler Weyl commutator differs
from its canonical Poisson test by a vanishing pairing on the same sequence. -/
theorem tendsto_actual_variableDensityWeyl_pair_sub_canonical_zero {ι : Type*} [Fintype ι]
    (S : ι → Mat) (G : E → Mat) (c : ι → ι → J → SchwartzMap E ℂ)
    (θ : E → ℝ) (β : E → E → ℝ) (R : ℝ) (hθ : HasCompactSupport θ)
    (hs : ContDiff ℝ ∞ (uncurry β))
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ (fun x ξ => (β x ξ : ℂ))) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ (fun x ξ => (β x ξ : ℂ))))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol (fun x ξ => (β x ξ : ℂ))))
    (hC : ∀ y ∈ tsupport θ, ∀ (i j : ι) (d : J),
      DifferentiableAt ℝ (fun z => metricActionCoefficient S (d.1,i) (d.2,j) (G z)) y)
    (hc : ∀ y ∈ tsupport θ, ∀ (i j : ι) (d : J), (fun z => c i j d z) =ᶠ[𝓝 y]
      fun z => (metricActionCoefficient S (d.1,i) (d.2,j) (G z) : ℂ))
    (u v : ℕ → ι → SchwartzMap E ℂ)
    (hU : ∀ j, ∃ M : ℝ, ∀ n, Real.sqrt (schwartzH1Energy (u n j)) ≤ M)
    (hV : ∀ i, Tendsto (fun n => ‖(v n i).toLp 2 volume‖) atTop (𝓝 0)) :
    let a := windowedWeylLeftSymbol θ (fun x ξ => (β x ξ : ℂ)) R h
    let P (i j : ι) (x ξ : E) :=
      (canonicalBracket (fun y ζ => frozenDensityPrincipalPhase S (G y) ζ i j)
        (fun y ζ => β y (WithLp.toLp 2 ζ)) x (physicalRadianCovector ξ) : ℂ)
    Tendsto (fun n => (∑ i, ∫ x, conj (v n i x) * variableDensityWeylCommutator c a (u n) i x) -
      ∑ i, ∑ j, ∫ x, conj (v n i x) * firstOrderAction (P i j) (u n j) x) atTop (𝓝 0) := by
  intro a P
  let b := normalizedWeylSymbol (fun x ξ => (β x ξ : ℂ))
  let Q := densityWeylResidualSymbol c a b
  have hReal (x ξ : E) : (β x ξ : ℂ) ≠ 0 → θ x = 1 :=
    fun hn => hPlateau x ξ (fun hz => hn (by rw [hz,Complex.ofReal_zero]))
  have hResidual := tendsto_densityWeylResidual_matrixPair_zero_of_uniform_H1
    c θ (fun x ξ => (β x ξ : ℂ)) R hθ h hAmp hReal hβ u v hU hV
  have hP (i j : ι) : ContDiff ℝ ∞ (uncurry (P i j)) ∧
      BaseDerivativeBounds (P i j) (fun ξ => (W ξ)^2) := by
    have he : densityWeylLeadingSymbol c b i j = P i j := funext (fun x =>
      funext (densityWeylLeadingSymbol_eq_canonicalBracket S G c θ β hs
        hPlateau i j (fun y hy => hC y hy i j) (fun y hy => hc y hy i j) x))
    rw [← he]
    exact densityWeylLeadingSymbol_profile c hβ i j
  have hPI (n : ℕ) (i j : ι) : Integrable (fun x => conj (v n i x) * firstOrderAction (P i j) (u n j) x) volume := by
    obtain ⟨C,_,hB⟩ := (hP i j).2.bound 0
    exact integrable_schwartz_pair_leftAction_of_growth (hP i j).1.continuous 2 C (fun x ξ => by
      simpa only [norm_iteratedFDeriv_zero] using hB x ξ) (u n j) (v n i)
  have hQI (n : ℕ) (i j : ι) : Integrable (fun x => conj (v n i x) * firstOrderAction (Q i j) (u n j) x) volume := by
    obtain ⟨hS,hQ⟩ := densityWeylResidualSymbol_profile c i j θ (fun x ξ => (β x ξ : ℂ)) R hθ h hAmp hReal hβ
    obtain ⟨C,_,hB⟩ := hQ.order 0
    exact integrable_schwartz_pair_leftAction_of_growth hS.continuous 1 C (fun x ξ => by
      simpa only [norm_iteratedFDeriv_zero,pow_one] using hB x ξ) (u n j) (v n i)
  refine hResidual.congr (fun n => ?_)
  have hRow (i : ι) :
      (∫ x, conj (v n i x) * variableDensityWeylCommutator c a (u n) i x) =
        ∑ j, ((∫ x, conj (v n i x) * firstOrderAction (P i j) (u n j) x) +
          ∫ x, conj (v n i x) * firstOrderAction (Q i j) (u n j) x) := by
    have he (x : E) : variableDensityWeylCommutator c a (u n) i x =
        ∑ j, (firstOrderAction (P i j) (u n j) x + firstOrderAction (Q i j) (u n j) x) :=
      variableDensityCompactWeylCommutator_eq_canonical_add_residual
      S G c θ β R hs h hAmp hPlateau hβ (u n) i x
      (fun y hy => hC y hy i) (fun y hy => hc y hy i)
    have hFn : (fun x => conj (v n i x) * variableDensityWeylCommutator c a (u n) i x) =
        fun x => ∑ j, (conj (v n i x) * firstOrderAction (P i j) (u n j) x +
          conj (v n i x) * firstOrderAction (Q i j) (u n j) x) := by
      funext x
      rw [he x,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => mul_add _ _ _)
    rw [hFn]
    let B (j : ι) (x : E) := conj (v n i x) * firstOrderAction (P i j) (u n j) x +
      conj (v n i x) * firstOrderAction (Q i j) (u n j) x
    have hBI (j : ι) : Integrable (B j) volume := (hPI n i j).add (hQI n i j)
    calc
      (∫ x, ∑ j, B j x) = ∑ j, ∫ x, B j x := integral_finset_sum Finset.univ (fun j _ => hBI j)
      _ = _ := Finset.sum_congr rfl (fun j _ => integral_add (hPI n i j) (hQI n i j))
  simp only [hRow,Finset.sum_add_distrib]
  abel

end Burnett.V03.Palatini
