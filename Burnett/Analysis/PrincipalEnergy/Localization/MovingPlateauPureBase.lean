import Burnett.Analysis.PrincipalEnergy.Localization.MovingPlateauPureIntegrand
import Burnett.Analysis.PrincipalEnergy.Localization.ProductPartialJets

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Metric Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped ContDiff FourierTransform

/-- The exact moving sandwich has uniformly controlled pure base derivatives of
every order. The smoothness and the estimates hold for all frequencies. -/
theorem movingPlateauSymbol_uniform_pureBaseOrder {a : Space → Space → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a))
    (hPure : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (χ : SchwartzMap Space ℂ) :
    (∀ c ξ, ContDiff ℝ ∞ (fun x => movingPlateauSymbol a χ c x ξ)) ∧
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ c x ξ,
      ‖iteratedFDeriv ℝ n (fun y => movingPlateauSymbol a χ c y ξ) x‖ ≤ C * (1 + ‖ξ‖) := by
  choose C hC hBound using fun n => exists_movingPlateauBaseIntegrand_derivative_bound ha hPure χ n
  let F := SchwartzMap.fourierTransformCLM ℂ χ
  let w (n : ℕ) (η : Space) := (1 + ‖η‖)^(n + 1) * ‖F η‖
  have hW (n : ℕ) : Integrable (w n) (volume : Measure Space) := integrable_schwartz_weighted F _
  have hIW (n : ℕ) : 0 ≤ ∫ η, w n η := integral_nonneg (fun η => by dsimp [w]; positivity)
  have jets (c ξ : Space) :
      ContDiff ℝ ∞ (fun x => movingPlateauSymbol a χ c x ξ) ∧ ∀ (n : ℕ) x,
      iteratedFDeriv ℝ n (fun y => movingPlateauSymbol a χ c y ξ) x =
        ∫ η, iteratedFDeriv ℝ n (sandwichBaseIntegrand (fun y => a (y+c)) χ ξ η) x := by
    let U := sandwichBaseIntegrand (fun y => a (y+c)) χ ξ
    have hz : ContDiff ℝ ∞ (fun p : Space × Space => ξ + p.2) := contDiff_const.add contDiff_snd
    have hA : ContDiff ℝ ∞ (fun p : Space × Space => a (p.1+c) (ξ+p.2)) :=
      (contDiff_symbol_translate_base ha c).comp (contDiff_fst.prodMk hz)
    have hJoint : ContDiff ℝ ∞ (fun p : Space × Space => U p.2 p.1) := by
      convert (contDiff_sandwichFrequencyFactor χ).mul hA using 1
      funext p
      simp only [U, sandwichBaseIntegrand, Function.uncurry, sandwichFrequencyFactor, smul_eq_mul]
      ring
    have hSmooth (η : Space) : ContDiff ℝ ∞ (U η) := by
      have hP : ContDiff ℝ ∞ (fun x : Space => (x, η)) := contDiff_id.prodMk contDiff_const
      change ContDiff ℝ ∞ ((fun p : Space × Space => U p.2 p.1) ∘ (fun x : Space => (x, η)))
      exact hJoint.comp hP
    have hMeas (n : ℕ) (x : Space) :
        AEStronglyMeasurable (fun η => iteratedFDeriv ℝ n (U η) x) (volume : Measure Space) := by
      have hJ : ContDiff ℝ ∞ (fun p : Space × Space => iteratedFDeriv ℝ n (U p.2) p.1) :=
        contDiff_firstPartialJet hJoint n
      have hP : Continuous (fun η : Space => (x, η)) := continuous_const.prodMk continuous_id
      letI : SecondCountableTopologyEither Space (ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ) :=
        secondCountableTopologyEither_of_left _ _
      change AEStronglyMeasurable
        ((fun p : Space × Space => iteratedFDeriv ℝ n (U p.2) p.1) ∘ (fun η : Space => (x, η))) volume
      exact (hJ.continuous.comp hP).aestronglyMeasurable
    have hDom (n : ℕ) (x : Space) : ∃ b : Space → ℝ,
        Integrable b (volume : Measure Space) ∧
          ∀ η y, y ∈ ball x 1 → ‖iteratedFDeriv ℝ n (U η) y‖ ≤ b η :=
      ⟨fun η => (C n * (1 + ‖ξ‖)) * w n η, (hW n).const_mul _, fun η y _ => hBound n c y ξ η⟩
    rw [show (fun x => movingPlateauSymbol a χ c x ξ) = (fun x => ∫ η, U η x) from
      funext fun x => cutoffSandwichSymbol_eq_baseIntegral (fun y => a (y+c)) χ x ξ]
    exact contDiff_integral_of_locally_dominated_jets (volume : Measure Space) U hSmooth hMeas hDom
  refine ⟨fun c ξ => (jets c ξ).1, fun n => ?_⟩
  refine ⟨C n * (∫ η, w n η), mul_nonneg (hC n) (hIW n), fun c x ξ => ?_⟩
  rw [(jets c ξ).2 n x]
  calc
    _ ≤ ∫ η, (C n * (1 + ‖ξ‖)) * w n η :=
      norm_integral_le_of_norm_le ((hW n).const_mul _) (Eventually.of_forall fun η => hBound n c x ξ η)
    _ = _ := by rw [integral_const_mul]; ring

end Burnett.Analysis.CarlesonEmbedding
