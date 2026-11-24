import Burnett.Analysis.Microlocal.Overlap.SameChartBallInclusion
import Burnett.Analysis.Microlocal.Overlap.SeparableSetIntegralExt

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.SmoothAngularTests (complexRationalAngularSymbol)
open Burnett.Microlocal.SmoothBaseTests
open Burnett.X02.SobolevTestJet (Space)

private theorem term_sameChartBallInclusion {L K : BallData} (hLK : L.closedBall ⊆ K.closedBall)
    (b m : Space → ℂ) (p : Chart L) :
    b (sameChartBallInclusion (L := L) (K := K) hLK p).1 *
      m (sameChartBallInclusion (L := L) (K := K) hLK p).2 = b p.1 * m p.2 := by
  rcases p with ⟨⟨x, hx⟩, ξ⟩
  change b x * m ξ = b x * m ξ
  rfl

private theorem integral_weight_mul {X : Type*} [MeasurableSpace X] (ν : Measure X) (b w m g : X → ℂ) :
    (∫ p, b p * w p * m p * g p ∂ν) = ∫ p, (b p * m p) * (w p * g p) ∂ν :=
  integral_congr_ae (Filter.Eventually.of_forall fun p =>
    (congrArg (fun a => a * g p) (mul_right_comm (b p) (w p) (m p))).trans
      (mul_assoc (b p * m p) (w p) (g p)))

/-- On nested phase balls, agreement on individual chart terms identifies
the weighted Borel-set integrals. -/
theorem sameChart_weighted_setIntegral_eq_of_terms {L K : BallData} (hLK : L.closedBall ⊆ K.closedBall)
    (μ : Measure (Chart L)) (ν : Measure (Chart K)) (f : Chart L → ℂ) (g w : Chart K → ℂ)
    (hf : Integrable f μ) (hg : Integrable (fun p => w p * g p) ν)
    (hTests : ∀ t : TermParameters,
      (∫ p : Chart L, baseSymbol K t.1 p.1 * complexRationalAngularSymbol t.2 p.2 * f p ∂μ) =
        ∫ p : Chart K, baseSymbol K t.1 p.1 * w p * complexRationalAngularSymbol t.2 p.2 * g p ∂ν)
    (S : Set (Chart K)) (hS : MeasurableSet S) :
    (∫ p in sameChartBallInclusion hLK ⁻¹' S, f p ∂μ) = ∫ p in S, w p * g p ∂ν := by
  have hT := (continuous_sameChartBallInclusion hLK).measurable
  refine setIntegral_preimage_eq_of_weightedChartTerms K μ ν (sameChartBallInclusion hLK)
    hT f (fun p => w p * g p) hf hg ?_ S hS
  intro t
  have hPull : (∫ p : Chart L, (baseSymbol K t.1 (sameChartBallInclusion hLK p).1 *
      complexRationalAngularSymbol t.2 (sameChartBallInclusion hLK p).2) * f p ∂μ) =
      (∫ p : Chart L, baseSymbol K t.1 p.1 * complexRationalAngularSymbol t.2 p.2 * f p ∂μ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun p =>
      congrArg (fun a => a * f p) (term_sameChartBallInclusion hLK
        (baseSymbol K t.1) (complexRationalAngularSymbol t.2) p))
  exact hPull.trans ((hTests t).trans (integral_weight_mul ν
    (fun p => baseSymbol K t.1 p.1) w (fun p => complexRationalAngularSymbol t.2 p.2) g))

end Burnett.Microlocal.Overlap
