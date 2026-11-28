import Burnett.Analysis.TransportWard.Weyl.WeylLeadingProfile

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 1900

noncomputable section

namespace Burnett.V03.Palatini

open Function Set Filter MeasureTheory Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open scoped ContDiff BigOperators

local notation "J" => Fin 4 × Fin 4
local notation "W" => radianFrequencyWeight

private theorem integrable_leftActionIntegrand_of_profile {a : E → E → ℂ} {m : ℕ}
    (hs : ContDiff ℝ ∞ (uncurry a)) (h : BaseDerivativeBounds a (fun ξ => (W ξ)^m))
    (u : SchwartzMap E ℂ) (x : E) : Integrable (leftActionIntegrand a u x) (volume : Measure E) := by
  obtain ⟨C,_,hC⟩ := h.bound 0
  exact leftActionIntegrand_integrable_of_growth u x
    (hs.continuous.comp (continuous_const.prodMk continuous_id)) m
    (fun ξ => by simpa only [norm_iteratedFDeriv_zero] using hC x ξ)

private theorem leftActionIntegrand_symbol_add (a b : E → E → ℂ) (u : SchwartzMap E ℂ) (x ξ : E) :
    leftActionIntegrand (fun y ν => a y ν+b y ν) u x ξ = leftActionIntegrand a u x ξ + leftActionIntegrand b u x ξ := by
  simp only [leftActionIntegrand]
  ring

private theorem leftActionIntegrand_symbol_mul_left (c : E → ℂ) (a : E → E → ℂ)
    (u : SchwartzMap E ℂ) (x ξ : E) :
    leftActionIntegrand (fun y ν => c y*a y ν) u x ξ = c x*leftActionIntegrand a u x ξ := by
  simp only [leftActionIntegrand]
  ring

private theorem integrable_symbol_add {a b : E → E → ℂ} {u : SchwartzMap E ℂ} {x : E}
    (ha : Integrable (leftActionIntegrand a u x) (volume : Measure E))
    (hb : Integrable (leftActionIntegrand b u x) (volume : Measure E)) :
    Integrable (leftActionIntegrand (fun y ν => a y ν+b y ν) u x) (volume : Measure E) := by
  have he : leftActionIntegrand (fun y ν => a y ν+b y ν) u x =
      leftActionIntegrand a u x + leftActionIntegrand b u x :=
    funext (leftActionIntegrand_symbol_add a b u x)
  rw [he]
  exact ha.add hb

private theorem firstOrderAction_symbol_mul_left (c : E → ℂ) (a : E → E → ℂ)
    (u : SchwartzMap E ℂ) (x : E) :
    firstOrderAction (fun y ν => c y*a y ν) u x = c x*firstOrderAction a u x := by
  simp only [firstOrderAction_eq_leftActionIntegrand,leftActionIntegrand_symbol_mul_left,integral_const_mul]

private theorem firstOrderAction_symbol_sum {ι : Type*} [Fintype ι] (a : ι → E → E → ℂ)
    (u : SchwartzMap E ℂ) (x : E)
    (h : ∀ i, Integrable (leftActionIntegrand (a i) u x) (volume : Measure E)) :
    firstOrderAction (fun y ν => ∑ i, a i y ν) u x = ∑ i, firstOrderAction (a i) u x := by
  have he (ξ : E) : leftActionIntegrand (fun y ν => ∑ i, a i y ν) u x ξ =
      ∑ i, leftActionIntegrand (a i) u x ξ := by
    simp only [leftActionIntegrand,Finset.mul_sum,Finset.sum_mul]
  simp only [firstOrderAction_eq_leftActionIntegrand,he,integral_finset_sum Finset.univ (fun i _ => h i)]

/-- The literal two-window commutator splits into the left actions of its
complete leading symbol and the same compact order-one remainder. -/
theorem variableDensityCompactWeylCommutator_eq_leading_add_residual {ι : Type*} [Fintype ι]
    (c : ι → ι → J → SchwartzMap E ℂ) (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol β)) (u : ι → SchwartzMap E ℂ) (i : ι) (x : E) :
    let a := windowedWeylLeftSymbol θ β R h
    let b := normalizedWeylSymbol β
    variableDensityWeylCommutator c a u i x =
      ∑ j, (firstOrderAction (densityWeylLeadingSymbol c b i j) (u j) x +
        firstOrderAction (densityWeylResidualSymbol c a b i j) (u j) x) := by
  intro a b
  let F (d : J) := frozenSecondCommutatorSymbol a d.1 d.2
  let F₀ (d : J) := frozenSecondWeylLeading b d.1 d.2
  let V (j : ι) (d : J) := variableCoefficientSecondSymbol a (c i j d) d
  let V₀ (j : ι) (d : J) := variableSecondWeylLeading b (c i j d) d
  let T (d : J) (y ξ : E) := F d y ξ - F₀ d y ξ
  let U (j : ι) (d : J) (y ξ : E) := V j d y ξ - V₀ j d y ξ
  let mainTerm (j : ι) (d : J) (y ξ : E) := c i j d y * F₀ d y ξ + V₀ j d y ξ
  let remainderTerm (j : ι) (d : J) (y ξ : E) := c i j d y * T d y ξ + U j d y ξ
  have hF (j : ι) (d : J) : Integrable (leftActionIntegrand (F₀ d) (u j) x) volume := by
    obtain ⟨hs,hB⟩ := frozenSecondWeylLeading_profile hβ d.1 d.2
    exact integrable_leftActionIntegrand_of_profile hs hB (u j) x
  have hV (j : ι) (d : J) : Integrable (leftActionIntegrand (V₀ j d) (u j) x) volume := by
    obtain ⟨hs,hB⟩ := variableSecondWeylLeading_profile hβ (c i j d) d
    exact integrable_leftActionIntegrand_of_profile hs hB (u j) x
  have hT (j : ι) (d : J) : Integrable (leftActionIntegrand (T d) (u j) x) volume := by
    obtain ⟨hs,hB⟩ := frozenSecondCompactWeylSymbol_sub_leading_profile θ β R h hAmp hPlateau hβ d.1 d.2
    exact integrable_leftActionIntegrand_of_profile hs (hB.weight_congr (fun ξ => (pow_one (W ξ)).symm)) (u j) x
  have hU (j : ι) (d : J) : Integrable (leftActionIntegrand (U j d) (u j) x) volume := by
    obtain ⟨hs,hB⟩ := variableCoefficientSecondSymbol_sub_normalizedWeylLeading_profile θ β R
      (c i j d) d h hAmp hPlateau hβ
    exact integrable_leftActionIntegrand_of_profile hs (hB.weight_congr (fun ξ => (pow_one (W ξ)).symm)) (u j) x
  have hMul (a' : E → E → ℂ) (j : ι) (d : J)
      (hI : Integrable (leftActionIntegrand a' (u j) x) (volume : Measure E)) :
      Integrable (leftActionIntegrand (fun y ξ => c i j d y * a' y ξ) (u j) x) volume := by
    have he : leftActionIntegrand (fun y ξ => c i j d y * a' y ξ) (u j) x =
        fun ξ => c i j d x * leftActionIntegrand a' (u j) x ξ :=
      funext (leftActionIntegrand_symbol_mul_left (c i j d) a' (u j) x)
    rw [he]
    exact hI.const_mul _
  have hM (j : ι) (d : J) : Integrable (leftActionIntegrand (mainTerm j d) (u j) x) volume := by
    exact integrable_symbol_add (hMul (F₀ d) j d (hF j d)) (hV j d)
  have hR (j : ι) (d : J) : Integrable (leftActionIntegrand (remainderTerm j d) (u j) x) volume := by
    exact integrable_symbol_add (hMul (T d) j d (hT j d)) (hU j d)
  have hPair (j : ι) (d : J) : c i j d x * firstOrderAction (F d) (u j) x + firstOrderAction (V j d) (u j) x =
      firstOrderAction (mainTerm j d) (u j) x + firstOrderAction (remainderTerm j d) (u j) x := by
    have hf : F d = fun y ξ => F₀ d y ξ + T d y ξ := by funext y ξ; dsimp only [T]; ring
    have hv : V j d = fun y ξ => V₀ j d y ξ + U j d y ξ := by funext y ξ; dsimp only [U]; ring
    rw [hf,hv,firstOrderAction_symbol_add _ _ (hF j d) (hT j d),
      firstOrderAction_symbol_add _ _ (hV j d) (hU j d)]
    dsimp only [mainTerm,remainderTerm]
    rw [firstOrderAction_symbol_add _ _ (hMul (F₀ d) j d (hF j d)) (hV j d),
      firstOrderAction_symbol_add _ _ (hMul (T d) j d (hT j d)) (hU j d)]
    simp only [firstOrderAction_symbol_mul_left]
    ring
  calc
    _ = ∑ d : J, ∑ j, (c i j d x * firstOrderAction (F d) (u j) x + firstOrderAction (V j d) (u j) x) :=
      variableDensityCompactWeylCommutator_eq_exact_leftActions c θ β R h hAmp hPlateau hβ u i x
    _ = ∑ d : J, ∑ j, (firstOrderAction (mainTerm j d) (u j) x +
        firstOrderAction (remainderTerm j d) (u j) x) :=
      Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun j _ => hPair j d
    _ = ∑ j, ∑ d : J, (firstOrderAction (mainTerm j d) (u j) x +
        firstOrderAction (remainderTerm j d) (u j) x) := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_add_distrib,← firstOrderAction_symbol_sum (mainTerm j) (u j) x (hM j),
        ← firstOrderAction_symbol_sum (remainderTerm j) (u j) x (hR j)]
      rfl

end Burnett.V03.Palatini
